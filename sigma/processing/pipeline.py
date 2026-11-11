from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass, field
import dataclasses
from enum import Enum
from functools import partial
import hashlib
import json
import os
import re
from typing import (
    Literal,
    Mapping,
    Any,
    Callable,
    Iterable,
    Tuple,
    Optional,
    Type,
    Union,
    cast,
    TYPE_CHECKING,
)

from sigma.processing.condition_expressions import (
    ConditionAND,
    ConditionExpression,
    ConditionIdentifier,
    ConditionNOT,
    ConditionOR,
    parse_condition_expression,
)
from sigma.processing.conditions.base import ProcessingCondition
from sigma.processing.finalization import Finalizer, NestedFinalizer, finalizers
from sigma.processing.templates import TemplateBase
from sigma.processing.tracking import FieldMappingTracking
from sigma.processing.transformations import transformations
from sigma.processing.transformations.external import ExternalSourceBaseTransformation
from sigma.rule import SigmaDetectionItem, SigmaRule
from sigma.rule.base import check_alias_expansion
from sigma.correlations import SigmaCorrelationRule
from sigma.processing.transformations.base import PreprocessingTransformation, Transformation
from sigma.processing.postprocessing import (
    NestedQueryPostprocessingTransformation,
    QueryPostprocessingTransformation,
    query_postprocessing_transformations,
)
from sigma.processing.conditions import (
    rule_conditions,
    RuleProcessingCondition,
    detection_item_conditions,
    DetectionItemProcessingCondition,
    field_name_conditions,
    FieldNameProcessingCondition,
)
from sigma.exceptions import (
    SigmaConfigurationError,
    SigmaPolicyError,
    SigmaProcessingItemError,
    SigmaPipelineConditionError,
    SigmaTypeError,
    SigmaPipelineParsingError,
)
import yaml

from sigma.types import SigmaFieldReference, SigmaType

if TYPE_CHECKING:
    from sigma.policy.regex_engine import RegexEngine
    from sigma.policy import SigmaPolicy


@dataclass
class ProcessingItemBase:
    transformation: Transformation
    rule_condition_linking: Callable[[Iterable[bool]], bool] | None = None  # any or all
    rule_condition_negation: bool = False
    rule_conditions: list[RuleProcessingCondition] | dict[str, RuleProcessingCondition] = field(
        default_factory=list
    )
    rule_condition_expression: ConditionExpression | None = (
        None  # Full rule condition expression mutually exclusive to linking
    )

    identifier: str | None = None
    policy: "SigmaPolicy | None" = field(default=None, compare=False)
    _pipeline: "ProcessingPipeline" | None = field(init=False, compare=False, default=None)
    _identifier_explicit: bool = field(init=False, compare=False, repr=False, default=False)

    @classmethod
    def _base_args_from_dict(
        cls,
        d: dict[str, Any],
        transformations: dict[str, Type[Transformation]],
        policy: "SigmaPolicy | None" = None,
    ) -> dict[str, Any]:
        """Return class instantiation parameters for attributes contained in base class for further
        usage in similar methods of classes inherited from this class."""
        rule_conds = cls._parse_conditions(
            cast(
                dict[
                    str,
                    Type[ProcessingCondition],
                ],
                rule_conditions,
            ),
            d.get("rule_conditions", list()),
        )
        rule_cond_expr_str = d.get("rule_cond_expr", None)
        if rule_cond_expr_str is not None:
            rule_cond_expr = parse_condition_expression(rule_cond_expr_str)
        else:
            rule_cond_expr = None
        return {
            "identifier": d.get("id", None),
            "rule_conditions": rule_conds,
            "rule_condition_expression": rule_cond_expr,
            "rule_condition_linking": cls._parse_condition_linking(d, "rule_cond_op"),
            "rule_condition_negation": d.get("rule_cond_not", False),
            "transformation": cls._instantiate_transformation(
                d,
                transformations,
                policy=policy,
            ),
        }

    def _check_conditions(
        self,
        expression_attr: str,
        linking_attr: str,
        conditions_attr: str,
        expected_condition_class: Type[ProcessingCondition],
        name: str,
    ) -> None:
        """
        This method conducts various checks of the conditions provided to the processing item:
        * That the condition expressions are mutually exclusive to the linking attribute.
        * That the conditions are provided as a list or dict.
        * That the conditions are of the expected condition class.
        In addition to the checks it sets the linking attribute to `all` if no logic value is provided.
        """
        expr = self.__getattribute__(expression_attr)
        conditions = self.__getattribute__(conditions_attr)
        # Check if logic is mutually exclusive to linking and conditions are provided as dict if
        # condition logic expression is given.
        if expr is not None:
            if self.__getattribute__(linking_attr) is not None:
                raise SigmaPipelineConditionError(
                    f"{name} expression is mutually exclusive to linking."
                )
            if not isinstance(conditions, dict):
                raise SigmaPipelineConditionError(
                    f"{name}s must be provided as mapping from identifiers to conditions if condition expression is provided."
                )
        else:  # In case no expression is provided, set linking to all if not provided and simplify condition dict to list.
            if self.__getattribute__(linking_attr) is None:
                self.__setattr__(linking_attr, all)
            if isinstance(conditions, dict):
                self.__setattr__(conditions_attr, list(conditions.values()))

        if not isinstance(conditions, (list, dict)):
            raise SigmaTypeError(f"{name}s must be provided as list or dict")
        if isinstance(conditions, dict):
            conditions_list = list(conditions.values())
        else:
            conditions_list = conditions
        for condition in conditions_list:
            if not isinstance(condition, expected_condition_class):
                raise SigmaTypeError(
                    f"{name} '{str(condition)}' is not a {expected_condition_class.__name__}"
                )

    def __post_init__(self) -> None:
        self._check_conditions(
            "rule_condition_expression",
            "rule_condition_linking",
            "rule_conditions",
            RuleProcessingCondition,
            "Rule condition",
        )
        self.transformation.set_processing_item(
            self
        )  # set processing item in transformation object after it is instantiated
        self._resolve_condition_expression(
            self.rule_condition_expression,
            cast(dict[str, ProcessingCondition], self.rule_conditions),
            "Rule condition",
        )
        self._identifier_explicit = self.identifier is not None and self.identifier != ""
        self._ensure_identifier()

    def _ensure_identifier(self) -> None:
        """Set an automatic identifier if no explicit non-empty identifier was provided."""
        if not self._identifier_explicit:
            self.identifier = self._generate_identifier()

    @classmethod
    def _canonical_identifier_value(
        cls,
        value: Any,
        seen: set[int] | None = None,
    ) -> Any:
        """Convert a value into a deterministic, JSON-serializable representation.

        Runtime-only fields such as pipeline and processing-item back-references are excluded.
        Dataclass fields that take part in equality are included, which captures transformation
        and condition parameters without depending on object ``repr`` output.
        """
        if seen is None:
            seen = set()

        if value is None or isinstance(value, (str, bool, int)):
            return value
        if isinstance(value, float):
            return ["float", repr(value)]
        if isinstance(value, bytes):
            return ["bytes", value.hex()]
        if isinstance(value, Enum):
            return [
                "enum",
                f"{type(value).__module__}.{type(value).__qualname__}",
                value.name,
            ]
        if isinstance(value, ConditionExpression):
            return cls._canonical_condition_expression(value)
        if isinstance(value, dict):
            value_id = id(value)
            if value_id in seen:
                return ["recursive", type(value).__name__]
            seen.add(value_id)
            try:
                entries = [
                    [
                        cls._canonical_identifier_value(key, seen),
                        cls._canonical_identifier_value(item, seen),
                    ]
                    for key, item in value.items()
                ]
                entries.sort(
                    key=lambda entry: json.dumps(
                        entry[0], sort_keys=True, separators=(",", ":"), ensure_ascii=True
                    )
                )
                return ["mapping", entries]
            finally:
                seen.remove(value_id)
        if isinstance(value, (list, tuple)):
            value_id = id(value)
            if value_id in seen:
                return ["recursive", type(value).__name__]
            seen.add(value_id)
            try:
                return [
                    "sequence",
                    [cls._canonical_identifier_value(item, seen) for item in value],
                ]
            finally:
                seen.remove(value_id)
        if isinstance(value, (set, frozenset)):
            value_id = id(value)
            if value_id in seen:
                return ["recursive", type(value).__name__]
            seen.add(value_id)
            try:
                items = [cls._canonical_identifier_value(item, seen) for item in value]
                items.sort(
                    key=lambda item: json.dumps(
                        item, sort_keys=True, separators=(",", ":"), ensure_ascii=True
                    )
                )
                return [type(value).__name__, items]
            finally:
                seen.remove(value_id)
        if isinstance(value, SigmaType):
            try:
                plain_value = value.to_plain()
            except Exception:
                pass
            else:
                if plain_value is not value and not isinstance(plain_value, SigmaType):
                    return [
                        "sigma_type",
                        f"{type(value).__module__}.{type(value).__qualname__}",
                        cls._canonical_identifier_value(plain_value, seen),
                    ]
        if dataclasses.is_dataclass(value) and not isinstance(value, type):
            value_id = id(value)
            if value_id in seen:
                return ["recursive", f"{type(value).__module__}.{type(value).__qualname__}"]
            seen.add(value_id)
            try:
                fields = []
                for dataclass_field in dataclasses.fields(value):
                    if dataclass_field.name in {"processing_item", "pipeline", "_pipeline"}:
                        continue
                    if dataclass_field.name.startswith("_") and dataclass_field.name != (
                        "_nested_pipeline"
                    ):
                        continue
                    if not dataclass_field.compare:
                        continue
                    if (
                        not dataclass_field.init
                        and not dataclass_field.repr
                        and dataclass_field.name != "_nested_pipeline"
                    ):
                        continue
                    fields.append(
                        [
                            dataclass_field.name,
                            cls._canonical_identifier_value(
                                getattr(value, dataclass_field.name), seen
                            ),
                        ]
                    )
                return [
                    "dataclass",
                    f"{type(value).__module__}.{type(value).__qualname__}",
                    fields,
                ]
            finally:
                seen.remove(value_id)
        if callable(value):
            if value is any:
                return ["callable", "any"]
            if value is all:
                return ["callable", "all"]
            return [
                "callable",
                f"{getattr(value, '__module__', '')}.{getattr(value, '__qualname__', repr(value))}",
            ]
        if isinstance(value, re.Pattern):
            return ["regex", value.pattern]
        if hasattr(value, "__dict__"):
            value_id = id(value)
            if value_id in seen:
                return ["recursive", f"{type(value).__module__}.{type(value).__qualname__}"]
            seen.add(value_id)
            try:
                public_state = {
                    key: item for key, item in vars(value).items() if not key.startswith("_")
                }
                if public_state:
                    return [
                        "object",
                        f"{type(value).__module__}.{type(value).__qualname__}",
                        cls._canonical_identifier_value(public_state, seen),
                    ]
            finally:
                seen.remove(value_id)
        representation = re.sub(r"0x[0-9a-fA-F]+", "0x…", repr(value))
        return [
            "value",
            f"{type(value).__module__}.{type(value).__qualname__}",
            representation,
        ]

    @classmethod
    def _canonical_condition_expression(
        cls,
        expression: ConditionExpression,
    ) -> Any:
        """Serialize a condition expression without source locations or whitespace."""
        if isinstance(expression, ConditionIdentifier):
            return ["identifier", expression.identifier]
        if isinstance(expression, ConditionNOT):
            return ["not", cls._canonical_condition_expression(expression.condition)]
        if isinstance(expression, (ConditionAND, ConditionOR)):
            operator = "and" if isinstance(expression, ConditionAND) else "or"
            return [
                operator,
                cls._canonical_condition_expression(expression.left),
                cls._canonical_condition_expression(expression.right),
            ]
        if dataclasses.is_dataclass(expression):
            return [
                "condition_expression",
                f"{type(expression).__module__}.{type(expression).__qualname__}",
                [
                    [
                        dataclass_field.name,
                        cls._canonical_identifier_value(getattr(expression, dataclass_field.name)),
                    ]
                    for dataclass_field in dataclasses.fields(expression)
                    if dataclass_field.compare
                    and dataclass_field.name not in {"location", "expression", "pipeline"}
                    and not dataclass_field.name.startswith("_")
                ],
            ]
        return cls._canonical_identifier_value(expression)

    @classmethod
    def _canonical_conditions(
        cls,
        conditions: list[ProcessingCondition] | dict[str, ProcessingCondition],
        expression: ConditionExpression | None,
    ) -> Any:
        """Serialize condition definitions, retaining expression reference keys."""
        if isinstance(conditions, dict):
            if expression is None:
                return ["list", [cls._canonical_identifier_value(c) for c in conditions.values()]]
            return cls._canonical_identifier_value(conditions)
        return cls._canonical_identifier_value(conditions)

    @classmethod
    def _canonical_linking(
        cls,
        linking: Callable[[Iterable[bool]], bool] | None,
        expression: ConditionExpression | None,
    ) -> Any:
        """Serialize condition linking while accounting for the default ``all`` linking."""
        if expression is None and linking is None:
            return "all"
        return cls._canonical_identifier_value(linking)

    def _generate_identifier(self) -> str:
        """Generate a deterministic identifier covering the complete item semantics."""
        content: dict[str, Any] = {
            "transformation": self._canonical_identifier_value(self.transformation),
        }

        condition_sets = (
            (
                "rule",
                "rule_conditions",
                "rule_condition_expression",
                "rule_condition_linking",
                "rule_condition_negation",
            ),
            (
                "detection_item",
                "detection_item_conditions",
                "detection_item_condition_expression",
                "detection_item_condition_linking",
                "detection_item_condition_negation",
            ),
            (
                "field_name",
                "field_name_conditions",
                "field_name_condition_expression",
                "field_name_condition_linking",
                "field_name_condition_negation",
            ),
        )
        for prefix, conditions_attr, expression_attr, linking_attr, negation_attr in condition_sets:
            if not hasattr(self, conditions_attr):
                continue
            conditions = getattr(self, conditions_attr)
            expression = getattr(self, expression_attr, None)
            linking = getattr(self, linking_attr, None)
            negation = getattr(self, negation_attr, False)
            content[prefix] = {
                "conditions": self._canonical_conditions(conditions, expression),
                "expression": (
                    self._canonical_condition_expression(expression)
                    if expression is not None
                    else None
                ),
                "linking": self._canonical_linking(linking, expression),
                "negation": negation,
            }

        content_str = json.dumps(
            content,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        )
        return hashlib.sha256(content_str.encode()).hexdigest()[:16]

    def _resolve_condition_expression(
        self,
        expr: ConditionExpression | None,
        conditions: dict[str, ProcessingCondition] | list[ProcessingCondition],
        name: str,
    ) -> None:
        if expr is not None:
            if isinstance(conditions, dict):
                refids = expr.resolve(conditions)
                if len(refids) < len(conditions):
                    raise SigmaPipelineConditionError(
                        f"{name} contains unreferenced condition items: {', '.join(set(conditions.keys()) - refids)}",
                        expr.expression,
                        expr.location,
                    )
            else:
                raise SigmaPipelineConditionError(
                    f"{name} conditions must be provided as a dict.",
                    expr.expression,
                    expr.location,
                )

    @classmethod
    def _parse_condition(
        cls,
        condition_class_mapping: Mapping[
            str,
            Type[ProcessingCondition],
        ],
        cond_def: dict[str, Any],
        ref: str,
    ) -> ProcessingCondition:
        try:
            cond_type = cond_def["type"]
        except KeyError:
            raise SigmaConfigurationError(f"Missing condition type defined in condition {ref}")

        try:
            cond_class = condition_class_mapping[cond_type]
        except KeyError:
            raise SigmaConfigurationError(
                f"Unknown condition type '{cond_type}' in condition {ref}"
            )

        cond_params = {k: v for k, v in cond_def.items() if k != "type"}
        try:
            return cond_class(**cond_params)
        except (SigmaConfigurationError, TypeError) as e:
            raise SigmaConfigurationError(f"Error in condition {ref}: {str(e)}") from e

    @classmethod
    def _parse_conditions(
        self,
        condition_class_mapping: Mapping[
            str,
            Type[ProcessingCondition],
        ],
        cond_defs: dict[str, dict[str, Any]],
    ) -> list[ProcessingCondition] | dict[str, ProcessingCondition]:
        """Parse dict of conditions into list or dict of condition object instances.

        :param condition_class_mapping: Mapping between condition type identifiers and condition classes.
        :type condition_class_mapping: dict[str, Type[RuleProcessingCondition] | Type[DetectionItemProcessingCondition] | Type[FieldNameProcessingCondition]]
        :param cond_defs: Definition of conditions for the pipeline.
        :type cond_defs: dict[str, Dict]
        :return: List or dict of condition classes as defined in dict.
        :rtype: list[RuleProcessingCondition] | dict[str, RuleProcessingCondition] | list[DetectionItemProcessingCondition] | dict[str, DetectionItemProcessingCondition] | list[FieldNameProcessingCondition] | dict[str, FieldNameProcessingCondition]
        """
        if isinstance(cond_defs, dict):
            return {
                k: self._parse_condition(condition_class_mapping, v, k)
                for k, v in cond_defs.items()
            }
        elif isinstance(cond_defs, list):
            return [
                self._parse_condition(condition_class_mapping, cond_def, str(i + 1))
                for i, cond_def in enumerate(cond_defs)
            ]
        else:
            raise SigmaTypeError("Conditions must be provided as list or dict")

    @classmethod
    def _parse_condition_linking(
        cls, d: dict[str, Any], op_name: str
    ) -> Callable[[Iterable[bool]], bool] | None:
        condition_linking = {
            "or": any,
            "and": all,
            None: None,
        }
        return condition_linking.get(d.get(op_name, None))

    @classmethod
    def _instantiate_transformation(
        cls,
        d: dict[str, Any],
        transformations: dict[str, Type[Transformation]],
        policy: "SigmaPolicy | None" = None,
    ) -> Transformation:
        try:
            transformation_class_name = d["type"]
        except KeyError:
            raise SigmaConfigurationError("Missing transformation type")

        try:
            transformation_class = transformations[transformation_class_name]
        except KeyError:
            raise SigmaConfigurationError(
                f"Unknown transformation type '{transformation_class_name}'"
            )

        params = {
            k: v
            for k, v in d.items()
            if k
            not in {
                "rule_conditions",
                "rule_cond_expr",
                "rule_cond_op",
                "rule_cond_not",
                "detection_item_conditions",
                "detection_item_cond_expr",
                "detection_item_cond_op",
                "detection_item_cond_not",
                "field_name_conditions",
                "field_name_cond_expr",
                "field_name_cond_op",
                "field_name_cond_not",
                "type",
                "id",
                "allow_template_vars",
                "vars_allowed_paths",
                "allow_external_sources",
                "restrict_template_path",
                "policy",
            }
        }
        import sigma as _sigma

        effective_policy = policy or _sigma.policy.default_policy
        if issubclass(transformation_class, TemplateBase):
            params["policy"] = policy
            params["restrict_template_path"] = not effective_policy.allow_external_sources
        if issubclass(transformation_class, ExternalSourceBaseTransformation):
            params["policy"] = policy
        try:
            if (
                transformation_class is NestedQueryPostprocessingTransformation
                and "items" in params
            ):
                params["items"] = [
                    (
                        QueryPostprocessingItem.from_dict(
                            item,
                            policy=policy,
                        )
                        if isinstance(item, dict)
                        else item
                    )
                    for item in params["items"]
                ]
            return transformation_class(**params)
        except (SigmaConfigurationError, TypeError) as e:
            raise SigmaConfigurationError("Error in transformation: " + str(e)) from e

    def match_rule_conditions(self, rule: SigmaRule | SigmaCorrelationRule) -> bool:
        if self.rule_condition_expression is not None:  # rule condition expression
            cond_result = self.rule_condition_expression.match(rule)
        elif self.rule_condition_linking is not None and isinstance(
            self.rule_conditions, list
        ):  # simplified conditional linking of conditions
            cond_result = self.rule_condition_linking(
                [condition.match(rule) for condition in self.rule_conditions]
            )
        else:
            raise SigmaPipelineConditionError(
                "No rule condition expression or linking defined for processing item."
            )

        if self.rule_condition_negation:
            cond_result = not cond_result
        return not self.rule_conditions or cond_result

    def set_pipeline(self, pipeline: "ProcessingPipeline") -> None:
        if self._pipeline is None:
            self._pipeline = pipeline
        else:
            raise SigmaProcessingItemError("Pipeline for processing item was already set.")

        self.transformation.set_pipeline(pipeline)
        if isinstance(self.rule_conditions, list):
            for rule_condition in self.rule_conditions:
                rule_condition.set_pipeline(self._pipeline)
        elif isinstance(self.rule_conditions, dict):
            for rule_condition in self.rule_conditions.values():
                rule_condition.set_pipeline(self._pipeline)

    def _clear_pipeline(self) -> None:
        self._pipeline = None
        self.transformation._clear_pipeline()
        if isinstance(self.rule_conditions, list):
            for rule_condition in self.rule_conditions:
                rule_condition._clear_pipeline()
        elif isinstance(self.rule_conditions, dict):
            for rule_condition in self.rule_conditions.values():
                rule_condition._clear_pipeline()


@dataclass
class ProcessingItem(ProcessingItemBase):
    """
    A processing item consists of an optional condition and a transformation that is applied in the case that
    the condition evaluates to true against the given Sigma rule or if the condition is not present.

    Processing items are instantiated by the processing pipeline for a whole collection that is about to be
    converted by a backend.
    """

    transformation: PreprocessingTransformation

    detection_item_condition_linking: Callable[[Iterable[bool]], bool] | None = None  # any or all
    detection_item_condition_negation: bool = False
    detection_item_conditions: (
        list[DetectionItemProcessingCondition] | dict[str, DetectionItemProcessingCondition]
    ) = field(default_factory=list)
    detection_item_condition_expression: ConditionExpression | None = None
    field_name_condition_linking: Callable[[Iterable[bool]], bool] | None = None  # any or all
    field_name_condition_negation: bool = False
    field_name_conditions: (
        list[FieldNameProcessingCondition] | dict[str, FieldNameProcessingCondition]
    ) = field(default_factory=list)
    field_name_condition_expression: ConditionExpression | None = None

    @classmethod
    def from_dict(
        cls,
        d: dict[str, Any],
        policy: "SigmaPolicy | None" = None,
    ) -> "ProcessingItem":
        """Instantiate processing item from parsed definition and variables."""
        kwargs = super()._base_args_from_dict(
            d,
            transformations,
            policy=policy,
        )

        detection_item_conds = cls._parse_conditions(
            cast(Mapping[str, Type[ProcessingCondition]], detection_item_conditions),
            d.get("detection_item_conditions", list()),
        )
        detection_item_cond_expr_str = d.get("detection_item_cond_expr", None)
        if detection_item_cond_expr_str is not None:
            detection_item_cond_expr = parse_condition_expression(detection_item_cond_expr_str)
        else:
            detection_item_cond_expr = None

        field_name_conds = cls._parse_conditions(
            field_name_conditions, d.get("field_name_conditions", list())
        )
        field_name_cond_expr_str = d.get("field_name_cond_expr", None)
        if field_name_cond_expr_str is not None:
            field_name_cond_expr = parse_condition_expression(field_name_cond_expr_str)
        else:
            field_name_cond_expr = None

        kwargs.update(
            {
                "detection_item_conditions": detection_item_conds,
                "detection_item_condition_expression": detection_item_cond_expr,
                "detection_item_condition_linking": cls._parse_condition_linking(
                    d, "detection_item_cond_op"
                ),
                "detection_item_condition_negation": d.get("detection_item_cond_not", False),
                "field_name_conditions": field_name_conds,
                "field_name_condition_expression": field_name_cond_expr,
                "field_name_condition_linking": cls._parse_condition_linking(
                    d, "field_name_cond_op"
                ),
                "field_name_condition_negation": d.get("field_name_cond_not", False),
            }
        )

        return cls(**kwargs)

    def __post_init__(self) -> None:
        super().__post_init__()
        self._check_conditions(
            "detection_item_condition_expression",
            "detection_item_condition_linking",
            "detection_item_conditions",
            DetectionItemProcessingCondition,
            "Detection item condition",
        )
        self._resolve_condition_expression(
            self.detection_item_condition_expression,
            cast(
                dict[str, ProcessingCondition] | list[ProcessingCondition],
                self.detection_item_conditions,
            ),
            "Detection item condition",
        )
        self._check_conditions(
            "field_name_condition_expression",
            "field_name_condition_linking",
            "field_name_conditions",
            FieldNameProcessingCondition,
            "Field name condition",
        )
        self._resolve_condition_expression(
            self.field_name_condition_expression,
            cast(
                dict[str, ProcessingCondition] | list[ProcessingCondition],
                self.field_name_conditions,
            ),
            "Field name condition",
        )
        if not self._identifier_explicit:
            self._ensure_identifier()

    def set_pipeline(self, pipeline: "ProcessingPipeline") -> None:
        super().set_pipeline(pipeline)
        if isinstance(self.detection_item_conditions, dict):
            detection_item_conditions = list(self.detection_item_conditions.values())
        else:
            detection_item_conditions = self.detection_item_conditions
        for detection_item_condition in detection_item_conditions:
            detection_item_condition.set_pipeline(pipeline)

        if isinstance(self.field_name_conditions, dict):
            field_name_conditions = list(self.field_name_conditions.values())
        else:
            field_name_conditions = self.field_name_conditions
        for field_name_condition in field_name_conditions:
            field_name_condition.set_pipeline(pipeline)

    def _clear_pipeline(self) -> None:
        super()._clear_pipeline()
        if isinstance(self.detection_item_conditions, dict):
            detection_item_conditions = list(self.detection_item_conditions.values())
        else:
            detection_item_conditions = self.detection_item_conditions
        for detection_item_condition in detection_item_conditions:
            detection_item_condition._clear_pipeline()

        if isinstance(self.field_name_conditions, dict):
            field_name_conditions = list(self.field_name_conditions.values())
        else:
            field_name_conditions = self.field_name_conditions
        for field_name_condition in field_name_conditions:
            field_name_condition._clear_pipeline()

    def apply(self, rule: SigmaRule | SigmaCorrelationRule) -> bool:
        """
        Matches condition against rule and performs transformation if condition is true or not present.
        Returns Sigma rule and bool if transformation was applied.
        """
        if self.match_rule_conditions(
            rule
        ):  # apply transformation if conditions match or no condition defined
            self.transformation.apply(rule)
            return True
        else:  # just pass rule through
            return False

    def match_detection_item(self, detection_item: SigmaDetectionItem) -> bool:
        """
        Evalutates detection item and field name conditions from processing item to detection item
        and returns result.
        """
        if (
            self.detection_item_condition_expression is not None
        ):  # detection item condition expression
            detection_item_cond_result = self.detection_item_condition_expression.match(
                detection_item
            )
        elif self.detection_item_condition_linking is not None and isinstance(
            self.detection_item_conditions, list
        ):  # simplified detection item condition
            detection_item_cond_result = self.detection_item_condition_linking(
                [condition.match(detection_item) for condition in self.detection_item_conditions]
            )
        else:
            raise SigmaPipelineConditionError(
                "No detection item condition expression or linking defined for processing item."
            )
        if self.detection_item_condition_negation:
            detection_item_cond_result = not detection_item_cond_result

        if self.field_name_condition_expression is not None:  # field name condition expression
            field_name_cond_result = self.field_name_condition_expression.match_detection_item(
                detection_item
            )
        elif self.field_name_condition_linking is not None and isinstance(
            self.field_name_conditions, list
        ):
            field_name_cond_result = self.field_name_condition_linking(
                [
                    condition.match_detection_item(detection_item)
                    for condition in self.field_name_conditions
                ]
            )
        else:  # no field name condition expression or linking defined
            raise SigmaPipelineConditionError(
                "No field name condition expression or linking defined for processing item."
            )
        if self.field_name_condition_negation:
            field_name_cond_result = not field_name_cond_result

        return detection_item_cond_result and field_name_cond_result

    def match_field_name(self, field: str | None) -> bool:
        """
        Evaluate field name conditions on field names and return result.
        """
        if self.field_name_condition_expression is not None:  # field name condition expression
            field_name_cond_result = self.field_name_condition_expression.match_field_name(field)
        elif self.field_name_condition_linking is not None and isinstance(
            self.field_name_conditions, list
        ):  # simplified field name condition
            field_name_cond_result = self.field_name_condition_linking(
                [condition.match_field_name(field) for condition in self.field_name_conditions]
            )
        else:  # no field name condition expression or linking defined
            raise SigmaPipelineConditionError(
                "No field name condition expression or linking defined for processing item."
            )

        if self.field_name_condition_negation:
            field_name_cond_result = not field_name_cond_result

        return field_name_cond_result

    def match_field_in_value(self, value: SigmaType) -> bool:
        """
        Evaluate field name conditions in field reference values and return result.
        """
        if isinstance(value, SigmaFieldReference):
            if self.field_name_condition_expression is not None:  # field name condition expression
                field_name_cond_result = self.field_name_condition_expression.match_field_name(
                    value.field
                )
            elif self.field_name_condition_linking is not None and isinstance(
                self.field_name_conditions, list
            ):  # simplified field name condition
                field_name_cond_result = self.field_name_condition_linking(
                    [condition.match_value(value) for condition in self.field_name_conditions]
                )
            else:  # no field name condition expression or linking defined
                raise SigmaPipelineConditionError(
                    "No field name condition expression or linking defined for processing item."
                )
            if self.field_name_condition_negation:
                field_name_cond_result = not field_name_cond_result

            return field_name_cond_result
        else:
            return False


@dataclass
class QueryPostprocessingItem(ProcessingItemBase):
    """
    A query post-processing item consists of an optional rule condition and a post-processing
    transformation that operates on the queries that were emitted by a backend for a given rule
    in the case that a transformation that is applied the condition evaluates to true against the
    given Sigma rule or if the condition is not present.

    These items are instantiated by the processing pipeline for a whole collection that was
    converted by a backend.
    """

    transformation: QueryPostprocessingTransformation

    @classmethod
    def from_dict(
        cls,
        d: dict[str, Any],
        policy: "SigmaPolicy | None" = None,
    ) -> "QueryPostprocessingItem":
        """Instantiate processing item from parsed definition and variables.

        Nested post-processing definitions are parsed recursively. Already constructed
        child items are retained.
        """
        kwargs = super()._base_args_from_dict(
            d,
            cast(dict[str, Type[Transformation]], query_postprocessing_transformations),
            policy=policy,
        )
        return cls(**kwargs)

    def apply(
        self,
        rule: SigmaRule | SigmaCorrelationRule,
        query: str,
    ) -> tuple[str, bool]:
        """
        Matches condition against rule and performs transformation of query if condition is true or not present.
        Returns query and bool if transformation was applied.
        """
        if self.match_rule_conditions(
            rule
        ):  # apply transformation if conditions match or no condition defined
            result = self.transformation.apply(rule, query)
            return (result, True)
        else:  # just pass rule through
            return (query, False)


@dataclass
class ProcessingPipeline:
    """
    A processing pipeline is configured with the transformation steps that are applied on Sigma rules and
    are configured by:

    * a backend to apply a set of base preprocessing of Sigma rules (e.g. renaming of fields).
    * the user in one or multiple configurations to conduct further rule transformation to adapt the rule
      to the environment.

    A processing pipeline is instantiated once for a rule collection. Rules are processed in order of their
    appearance in a rule file or include order. Further, processing pipelines can be chained and contain
    variables that can be used from processing items.

    **Important:** When combining multiple pipelines, the ``ProcessingPipelineResolver.resolve()`` method
    should be used to respect pipeline priorities (lowest priority first). Simple addition with the ``+``
    operator does not consider priorities and concatenates pipelines in the order specified. Use the resolver
    when you have multiple pipelines with different priority values that must be applied in a specific order.
    """

    items: list[ProcessingItem] = field(default_factory=list)
    postprocessing_items: list[QueryPostprocessingItem] = field(default_factory=list)
    finalizers: list[Finalizer] = field(default_factory=list)
    vars: dict[str, Any] = field(default_factory=dict)
    priority: int = field(default=0)
    name: str | None = field(default=None)
    allowed_backends: frozenset[str] = field(
        default_factory=frozenset
    )  # Set of identifiers of backends (from the backends mapping) that are allowed to use this processing pipeline. This can be used by frontends like Sigma CLI to warn the user about inappropriate usage.
    policy: "SigmaPolicy | None" = field(default=None, compare=False)
    # The following items are reset for each invocation of apply().
    # TODO: move this to parameters or return values of apply().
    applied: list[bool] = field(
        init=False, compare=False, default_factory=list
    )  # list of applied items as booleans. If True, the corresponding item at the same position was applied
    applied_ids: set[str] = field(
        init=False, compare=False, default_factory=set
    )  # set of identifiers of applied items, doesn't contains items without identifier
    field_name_applied_ids: dict[str, set[str]] = field(
        init=False, compare=False, default_factory=partial(defaultdict, set)
    )  # Mapping of field names from rule fields list to set of applied processing items
    field_mappings: FieldMappingTracking = field(
        init=False, compare=False, default_factory=FieldMappingTracking
    )  # Mapping between initial field names and finally mapped field name.
    state: dict[str, Any] = field(
        init=False, compare=False, default_factory=dict
    )  # pipeline state: allows to set variables that can be used in conversion (e.g. indices, data model names etc.)

    @staticmethod
    def _validate_explicit_identifiers(
        items: Iterable[ProcessingItem | QueryPostprocessingItem],
        nested_collection: Literal["items", "postprocessing_items"],
    ) -> None:
        """Reject duplicate explicit identifiers within a preprocessing/postprocessing tree."""
        seen: set[str] = set()
        visited_pipelines: set[int] = set()

        def visit(processing_items: Iterable[ProcessingItem | QueryPostprocessingItem]) -> None:
            for processing_item in processing_items:
                if processing_item._identifier_explicit and processing_item.identifier is not None:
                    if processing_item.identifier in seen:
                        raise SigmaConfigurationError(
                            f"Duplicate explicit processing item identifier "
                            f"'{processing_item.identifier}': explicit identifiers must be "
                            f"unique within a processing pipeline, including nested pipelines."
                        )
                    seen.add(processing_item.identifier)

                nested_pipeline = getattr(processing_item.transformation, "_nested_pipeline", None)
                if isinstance(nested_pipeline, ProcessingPipeline):
                    pipeline_id = id(nested_pipeline)
                    if pipeline_id not in visited_pipelines:
                        visited_pipelines.add(pipeline_id)
                        visit(getattr(nested_pipeline, nested_collection))

        visit(items)

    def __post_init__(self) -> None:
        if self.items and not all((isinstance(item, ProcessingItem) for item in self.items)):
            raise TypeError(
                "Each item in a processing pipeline must be a ProcessingItem - don't use processing classes directly!"
            )
        if self.postprocessing_items and not all(
            (isinstance(item, QueryPostprocessingItem) for item in self.postprocessing_items)
        ):
            raise TypeError(
                "Each item in a postprocessing pipeline must be a QueryPostprocessingItem - don't use processing classes directly!"
            )
        if self.finalizers and not all(
            (isinstance(finalizer, Finalizer) for finalizer in self.finalizers)
        ):
            raise TypeError("Each item in a finalizer pipeline must be a Finalizer")

        self._validate_explicit_identifiers(self.items, "items")
        self._validate_explicit_identifiers(self.postprocessing_items, "postprocessing_items")

        # Initialize contained items with just instantiated processing pipeline as context.
        self.set_pipeline()

    def set_pipeline(self) -> None:
        for processing_item in self.items:
            processing_item.set_pipeline(self)
        for postprocessing_item in self.postprocessing_items:
            postprocessing_item.set_pipeline(self)
        for finalizer in self.finalizers:
            finalizer.set_pipeline(self)

    def _clear_pipeline(self) -> None:
        for processing_item in self.items:
            processing_item._clear_pipeline()
        for postprocessing_item in self.postprocessing_items:
            postprocessing_item._clear_pipeline()
        for finalizer in self.finalizers:
            finalizer._pipeline = None

    def resolve_policy(self) -> "SigmaPolicy":
        """Return the effective policy for this pipeline.

        Prefer the policy attached to this pipeline and fall back to the
        global default policy only if no pipeline policy is set.
        """
        from sigma.policy import default_policy

        return self.policy or default_policy

    def resolve_regex_engine(self) -> "RegexEngine":
        """Return the effective regex engine for this pipeline."""
        return self.resolve_policy().regex_engine

    @classmethod
    def from_dict(
        cls,
        d: dict[str, Any],
        policy: "SigmaPolicy | None" = None,
    ) -> "ProcessingPipeline":
        """Instantiate processing pipeline from a parsed processing item description."""

        # Validate aliases once at the pipeline root so nested from_dict calls don't
        # repeatedly traverse already checked substructures.
        check_alias_expansion(d, SigmaConfigurationError)

        custom_keys = [
            k
            for k in d.keys()
            if k
            not in (
                "vars",
                "transformations",
                "postprocessing",
                "finalizers",
                "priority",
                "name",
                "allowed_backends",
            )
        ]
        if custom_keys:
            raise SigmaConfigurationError(f"Unkown keys {custom_keys}")

        import sigma as _sigma

        effective_policy = policy or _sigma.policy.default_policy

        vars = d.get("vars", dict())  # default: no variables

        items = d.get("transformations", list())  # default: no transformation
        processing_items = list()
        for i, item in enumerate(items):
            try:
                processing_item = ProcessingItem.from_dict(item, policy=policy)
                processing_items.append(processing_item)
            except SigmaConfigurationError as e:
                raise SigmaConfigurationError(f"Error in processing rule {i + 1}: {str(e)}") from e

        items = d.get("postprocessing", list())  # default: no transformation
        postprocessing_items = list()
        for i, item in enumerate(items):
            try:
                postprocessing_items.append(
                    QueryPostprocessingItem.from_dict(
                        item,
                        policy=policy,
                    )
                )
            except SigmaConfigurationError as e:
                raise SigmaConfigurationError(f"Error in processing rule {i + 1}: {str(e)}") from e

        fds = d.get("finalizers", list())  # no default transformation
        fs: list[Finalizer] = list()
        for fd in fds:
            fd = fd.copy()
            fd.pop("allow_template_vars", None)  # Strip untrusted YAML value
            fd.pop("vars_allowed_paths", None)  # Strip untrusted YAML value
            fd.pop("allow_external_sources", None)  # Strip untrusted YAML value
            fd.pop("restrict_template_path", None)  # Strip untrusted YAML value
            fd.pop("policy", None)  # Strip untrusted YAML value
            try:
                finalizer_type = fd.pop("type")
            except KeyError:
                raise SigmaConfigurationError(
                    "Finalizer type must be specified in 'type' attribute"
                )

            try:
                finalizer_cls = finalizers[finalizer_type]
            except KeyError:
                raise SigmaConfigurationError(f"Finalizer '{finalizer_type}' is unknown")

            if issubclass(finalizer_cls, TemplateBase):
                fd["policy"] = policy
                fd["restrict_template_path"] = not effective_policy.allow_external_sources
                fs.append(finalizer_cls.from_dict(fd))
            elif finalizer_cls is NestedFinalizer:
                fs.append(
                    NestedFinalizer.from_dict(
                        fd,
                        policy=policy,
                    )
                )
            else:
                fs.append(finalizer_cls.from_dict(fd))

        priority = d.get("priority", 0)
        name = d.get("name", None)
        allowed_backends = frozenset(d.get("allowed_backends", frozenset()))

        return cls(
            processing_items,
            postprocessing_items,
            fs,
            vars,
            priority,
            name,
            allowed_backends,
            policy,
        )

    @classmethod
    def from_yaml(
        cls,
        processing_pipeline: str,
        source_path: str | None = None,
        policy: "SigmaPolicy | None" = None,
    ) -> "ProcessingPipeline":
        """Convert YAML input string into processing pipeline.

        If *source_path* is provided and *policy.vars_allowed_paths* is ``None``, the
        directory containing *source_path* is automatically used as the only
        allowed base directory for template vars files. This prevents a
        pipeline YAML from referencing vars files outside its own directory
        tree.
        """
        import dataclasses
        import sigma as _sigma

        effective_policy = policy or _sigma.policy.default_policy
        if effective_policy.vars_allowed_paths is None and source_path is not None:
            policy = dataclasses.replace(
                effective_policy,
                vars_allowed_paths=(os.path.dirname(os.path.realpath(source_path)),),
            )
        try:
            parsed_pipeline = yaml.safe_load(processing_pipeline)
        except yaml.parser.ParserError as e:
            raise SigmaPipelineParsingError("Error in parsing of a Sigma processing pipeline")
        return cls.from_dict(
            parsed_pipeline,
            policy=policy,
        )

    def apply(self, rule: SigmaRule | SigmaCorrelationRule) -> SigmaRule | SigmaCorrelationRule:
        """Apply processing pipeline on Sigma rule."""
        self.applied = list()
        self.applied_ids = set()
        self.field_name_applied_ids = defaultdict(set)
        self.field_mappings = FieldMappingTracking()
        self.state = dict()
        for item in self.items:
            applied = item.apply(rule)
            self.applied.append(applied)
            if applied and (itid := item.identifier):
                self.applied_ids.add(itid)
        return rule

    def postprocess_query(self, rule: SigmaRule | SigmaCorrelationRule, query: Any) -> Any:
        """Post-process queries with postprocessing_items."""
        for item in self.postprocessing_items:
            query, applied = item.apply(rule, query)
            if applied and (itid := item.identifier):
                self.applied_ids.add(itid)
        return query

    def finalize(self, output: Any) -> Any:
        for finalizer in self.finalizers:
            output = finalizer.apply(output)
        return output

    def track_field_processing_items(
        self, src_field: str, dest_field: list[str], processing_item_id: str | None
    ) -> None:
        """
        Track processing items that were applied to field names. This adds the processing_item_id to
        the set of applied processing items from src_field and assigns a copy of this set ass
        tracking set to all fields in dest_field.
        """
        if [src_field] != dest_field:  # Only add if source field was mapped to something different.
            applied_identifiers: set[str] = self.field_name_applied_ids[src_field]
            if processing_item_id is not None:
                applied_identifiers.add(processing_item_id)
            del self.field_name_applied_ids[src_field]
            for field in dest_field:
                self.field_name_applied_ids[field] = applied_identifiers.copy()

    def field_was_processed_by(self, field: str | None, processing_item_id: str) -> bool:
        """
        Check if field name was processed by a particular processing item.
        """
        if field is None:
            return False
        return processing_item_id in self.field_name_applied_ids[field]

    def __add__(self, other: "ProcessingPipeline" | None) -> "ProcessingPipeline":
        """
        Concatenate two processing pipelines and merge their variables.

        **Note:** This method concatenates pipelines in the order specified and does NOT respect
        pipeline priorities. For combining multiple pipelines with different priority values,
        use ``ProcessingPipelineResolver.resolve()`` which sorts pipelines by priority before merging.
        """
        if other is None:
            return self
        if not isinstance(other, self.__class__):
            raise TypeError("Processing pipeline must be merged with another one.")
        merged_policy: "SigmaPolicy | None"
        if self.policy is not None and other.policy is not None:
            if self.policy == other.policy:
                merged_policy = self.policy
            else:
                # Allow merging when the only difference is vars_allowed_paths; combine the paths.
                import dataclasses

                p1, p2 = self.policy, other.policy
                if (
                    p1.regex_engine == p2.regex_engine
                    and p1.allow_template_vars == p2.allow_template_vars
                    and p1.allow_external_sources == p2.allow_external_sources
                ):
                    # Merge vars_allowed_paths: union of both (None means "no restriction").
                    if p1.vars_allowed_paths is None or p2.vars_allowed_paths is None:
                        merged_paths = None
                    else:
                        seen: set[str] = set()
                        merged_paths = tuple(
                            p
                            for p in p1.vars_allowed_paths + p2.vars_allowed_paths
                            if not (p in seen or seen.add(p))  # type: ignore[func-returns-value]
                        )
                    merged_policy = dataclasses.replace(p1, vars_allowed_paths=merged_paths)
                else:
                    raise SigmaPolicyError(
                        "Processing pipelines with different SigmaPolicy objects can't be merged."
                    )
        else:
            merged_policy = self.policy or other.policy

        self._clear_pipeline()
        other._clear_pipeline()

        return self.__class__(
            items=self.items + other.items,
            postprocessing_items=self.postprocessing_items + other.postprocessing_items,
            finalizers=self.finalizers + other.finalizers,
            vars={**self.vars, **other.vars},
            policy=merged_policy,
        )

    def __radd__(self, other: Literal[0]) -> "ProcessingPipeline":
        """Ignore integer 0 on addition to make sum of list of ProcessingPipelines working."""
        if other == 0:
            return self
        else:
            return NotImplemented
