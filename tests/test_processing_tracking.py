import pytest
from sigma.processing.condition_expressions import parse_condition_expression
from sigma.processing.pipeline import ProcessingItem, ProcessingPipeline
from sigma.processing.tracking import FieldMappingTracking
from tests.test_processing_pipeline import RuleConditionTrue, TransformationAppend
from tests.test_rule import sigma_rule


@pytest.fixture
def field_mapping_tracking():
    return FieldMappingTracking()


def test_field_mapping_tracking_single(field_mapping_tracking: FieldMappingTracking):
    field_mapping_tracking.add_mapping("fieldA", "mappedA")
    assert field_mapping_tracking["fieldA"] == {"mappedA"}


def test_field_mapping_tracking_cascaded(field_mapping_tracking: FieldMappingTracking):
    field_mapping_tracking.add_mapping("fieldA", "mappedA")
    field_mapping_tracking.add_mapping("mappedA", "mappedB")
    assert field_mapping_tracking["fieldA"] == {"mappedB"}
    assert field_mapping_tracking["mappedA"] == {"mappedB"}


def test_field_mapping_tracking_listitem_replaced(
    field_mapping_tracking: FieldMappingTracking,
):
    field_mapping_tracking.add_mapping("fieldA", ["mappedA", "mappedB", "mappedC"])
    field_mapping_tracking.add_mapping("mappedB", "mappedD")
    assert field_mapping_tracking["fieldA"] == {"mappedA", "mappedC", "mappedD"}


def test_field_mapping_tracking_merge():
    field_mapping_tracking = FieldMappingTracking()
    field_mapping_tracking.add_mapping("fieldA", "mappedA")
    field_mapping_tracking.add_mapping("mappedA", "mappedB")
    field_mapping_tracking.add_mapping("fieldB", "mappedC")

    other_field_mapping_tracking = FieldMappingTracking()
    other_field_mapping_tracking.add_mapping("mappedB", "mappedD")
    other_field_mapping_tracking.add_mapping("fieldC", "mappedE")

    field_mapping_tracking.merge(other_field_mapping_tracking)

    assert field_mapping_tracking["fieldA"] == {"mappedD"}
    assert field_mapping_tracking["fieldB"] == {"mappedC"}
    assert field_mapping_tracking["fieldC"] == {"mappedE"}


def test_pipeline_tracks_distinct_automatic_identifiers(sigma_rule):
    first = ProcessingItem(
        transformation=TransformationAppend(s="Test"),
        rule_conditions={"cond": RuleConditionTrue(dummy="same-condition-value")},
        rule_condition_expression=parse_condition_expression("cond"),
    )
    second = ProcessingItem(
        transformation=TransformationAppend(s="Test"),
        rule_conditions={"cond": RuleConditionTrue(dummy="same-condition-value")},
        rule_condition_expression=parse_condition_expression("not cond"),
    )
    pipeline = ProcessingPipeline(items=[first, second])

    pipeline.apply(sigma_rule)

    assert first.identifier != second.identifier
    assert sigma_rule.was_processed_by(first.identifier)
    assert not sigma_rule.was_processed_by(second.identifier)
    assert pipeline.applied_ids == {first.identifier}
