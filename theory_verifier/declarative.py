from __future__ import annotations

import json
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path


JsonObject = dict[str, object]


@dataclass(frozen=True)
class DeclarativeIssue:
    code: str
    message: str

    def to_jsonable(self) -> dict[str, str]:
        return {"code": self.code, "message": self.message}


@dataclass(frozen=True)
class DeclarativeReport:
    specification_documents: tuple[str, ...]
    verification_rules_checked: int
    issues: tuple[DeclarativeIssue, ...]

    @property
    def ok(self) -> bool:
        return not self.issues

    def to_jsonable(self) -> dict[str, object]:
        return {
            "ok": self.ok,
            "specification_documents": list(self.specification_documents),
            "verification_rules_checked": self.verification_rules_checked,
            "issues": [issue.to_jsonable() for issue in self.issues],
        }


class DeclarativeRuleError(ValueError):
    pass


def load_json_file(path: Path) -> JsonObject:
    raw = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise DeclarativeRuleError(f"{path}: root must be an object")
    output: JsonObject = {}
    for key, value in raw.items():
        if not isinstance(key, str):
            raise DeclarativeRuleError(f"{path}: root keys must be strings")
        output[key] = value
    return output


def load_rule_documents(path: Path) -> tuple[JsonObject, ...]:
    if path.is_file():
        return (load_json_file(path),)
    if not path.is_dir():
        raise DeclarativeRuleError(f"{path}: rule path must be a file or directory")
    return tuple(load_json_file(item) for item in sorted(path.rglob("*.idtl.json")))


def verify_declarative_rule_documents(
    manifest: JsonObject,
    rule_documents: Sequence[JsonObject],
    workspace: Path,
) -> DeclarativeReport:
    issues: list[DeclarativeIssue] = []
    document_ids: list[str] = []
    rules_checked = 0
    index = build_reference_index(manifest)

    for document_index, document in enumerate(rule_documents):
        document_id = require_string(document.get("id"), f"documents[{document_index}].id")
        document_ids.append(document_id)
        kind = require_string(document.get("kind"), f"{document_id}.kind")
        if kind != "verification_specification":
            issues.append(
                DeclarativeIssue(
                    "declarative_specification_kind_mismatch",
                    f"{document_id}: kind must be 'verification_specification', got {kind!r}",
                )
            )
        language_version = require_string(
            document.get("language_version"),
            f"{document_id}.language_version",
        )
        if not language_version.startswith("v8."):
            issues.append(
                DeclarativeIssue(
                    "declarative_language_version_mismatch",
                    f"{document_id}: language_version must be v8.x, got {language_version!r}",
                )
            )
        issues.extend(check_controlled_vocabulary(document_id, document))
        rules = require_list(
            document.get("verification_rules"),
            f"{document_id}.verification_rules",
        )
        for rule_index, raw_rule in enumerate(rules):
            rule = require_mapping(raw_rule, f"{document_id}.verification_rules[{rule_index}]")
            rules_checked += 1
            issues.extend(evaluate_rule(manifest, index, document_id, rule, workspace))

    return DeclarativeReport(
        specification_documents=tuple(document_ids),
        verification_rules_checked=rules_checked,
        issues=tuple(issues),
    )


def check_controlled_vocabulary(document_id: str, document: JsonObject) -> list[DeclarativeIssue]:
    vocabulary = require_list(document.get("controlled_vocabulary"), f"{document_id}.controlled_vocabulary")
    issues: list[DeclarativeIssue] = []
    allowed_statuses = {"standard", "project_local", "proposed_term"}
    for index, raw_entry in enumerate(vocabulary):
        entry = require_mapping(raw_entry, f"{document_id}.controlled_vocabulary[{index}]")
        term = require_string(entry.get("term"), f"{document_id}.controlled_vocabulary[{index}].term")
        status = require_string(entry.get("status"), f"{document_id}.controlled_vocabulary[{index}].status")
        if status not in allowed_statuses:
            issues.append(
                DeclarativeIssue(
                    "declarative_vocabulary_status_unknown",
                    f"{document_id}: vocabulary term {term!r} has unknown status {status!r}",
                )
            )
        for required_field in ("domain", "definition"):
            value = entry.get(required_field)
            if not isinstance(value, str) or not value.strip():
                issues.append(
                    DeclarativeIssue(
                        "declarative_vocabulary_field_missing",
                        f"{document_id}: vocabulary term {term!r} must define {required_field}",
                    )
                )
        if status == "proposed_term" and entry.get("approval_required") is not True:
            issues.append(
                DeclarativeIssue(
                    "declarative_proposed_term_without_approval_gate",
                    f"{document_id}: proposed term {term!r} must set approval_required=true",
                )
            )
    return issues


def evaluate_rule(
    manifest: JsonObject,
    index: Mapping[str, frozenset[str]],
    document_id: str,
    rule: JsonObject,
    workspace: Path,
) -> list[DeclarativeIssue]:
    rule_id = require_string(rule.get("id"), f"{document_id}.rule.id")
    selector = require_mapping(rule.get("applies_to"), f"{rule_id}.applies_to")
    collection = require_string(selector.get("collection"), f"{rule_id}.applies_to.collection")
    objects = select_objects(manifest, collection)
    where = selector.get("where")
    if where is not None:
        predicate = require_mapping(where, f"{rule_id}.applies_to.where")
        objects = tuple(item for item in objects if predicate_matches(item, predicate))
    assertions = require_list(rule.get("assertions"), f"{rule_id}.assertions")

    issues: list[DeclarativeIssue] = []
    for item in objects:
        for assertion_index, raw_assertion in enumerate(assertions):
            assertion = require_mapping(raw_assertion, f"{rule_id}.assertions[{assertion_index}]")
            issues.extend(evaluate_assertion(index, rule_id, collection, item, assertion, workspace))
    return issues


def evaluate_assertion(
    index: Mapping[str, frozenset[str]],
    rule_id: str,
    collection: str,
    item: JsonObject,
    assertion: JsonObject,
    workspace: Path,
) -> list[DeclarativeIssue]:
    operation = require_string(assertion.get("predicate"), f"{rule_id}.assertion.predicate")
    if operation == "field_required":
        return check_field_required(rule_id, collection, item, assertion)
    if operation == "field_non_empty":
        return check_field_non_empty(rule_id, collection, item, assertion)
    if operation == "field_in":
        return check_field_in(rule_id, collection, item, assertion)
    if operation == "field_not_in":
        return check_field_not_in(rule_id, collection, item, assertion)
    if operation == "equals_field":
        return check_equals_field(rule_id, collection, item, assertion)
    if operation == "refs_exist":
        return check_refs_exist(index, rule_id, collection, item, assertion)
    if operation == "list_contains_all":
        return check_list_contains_all(rule_id, collection, item, assertion)
    if operation == "every_field_equals":
        return check_every_field_equals(rule_id, collection, item, assertion)
    if operation == "file_exists":
        return check_file_exists(rule_id, collection, item, assertion, workspace)
    if operation == "no_intersection":
        return check_no_intersection(rule_id, collection, item, assertion)
    raise DeclarativeRuleError(f"{rule_id}: unknown assertion op {operation!r}")


def check_field_required(
    rule_id: str,
    collection: str,
    item: JsonObject,
    assertion: JsonObject,
) -> list[DeclarativeIssue]:
    path = require_string(assertion.get("field_path"), f"{rule_id}.field_path")
    if values_at_path(item, path):
        return []
    return [issue(rule_id, collection, item, "declarative_field_missing", f"missing field {path}")]


def check_field_non_empty(
    rule_id: str,
    collection: str,
    item: JsonObject,
    assertion: JsonObject,
) -> list[DeclarativeIssue]:
    path = require_string(assertion.get("field_path"), f"{rule_id}.field_path")
    values = values_at_path(item, path)
    if values and all(is_non_empty(value) for value in values):
        return []
    return [issue(rule_id, collection, item, "declarative_field_empty", f"{path} must be non-empty")]


def check_field_in(
    rule_id: str,
    collection: str,
    item: JsonObject,
    assertion: JsonObject,
) -> list[DeclarativeIssue]:
    path = require_string(assertion.get("field_path"), f"{rule_id}.field_path")
    allowed = frozenset(
        require_string_list(assertion.get("allowed_values"), f"{rule_id}.allowed_values")
    )
    bad = [value for value in values_at_path(item, path) if not isinstance(value, str) or value not in allowed]
    if not bad:
        return []
    return [
        issue(
            rule_id,
            collection,
            item,
            "declarative_field_value_not_allowed",
            f"{path} has value outside {sorted(allowed)}",
        )
    ]


def check_field_not_in(
    rule_id: str,
    collection: str,
    item: JsonObject,
    assertion: JsonObject,
) -> list[DeclarativeIssue]:
    path = require_string(assertion.get("field_path"), f"{rule_id}.field_path")
    forbidden = frozenset(
        require_string_list(assertion.get("forbidden_values"), f"{rule_id}.forbidden_values")
    )
    bad = [value for value in values_at_path(item, path) if isinstance(value, str) and value in forbidden]
    if not bad:
        return []
    return [
        issue(
            rule_id,
            collection,
            item,
            "declarative_forbidden_field_value",
            f"{path} contains forbidden value(s) {sorted(set(bad))}",
        )
    ]


def check_equals_field(
    rule_id: str,
    collection: str,
    item: JsonObject,
    assertion: JsonObject,
) -> list[DeclarativeIssue]:
    path = require_string(assertion.get("field_path"), f"{rule_id}.field_path")
    other_path = require_string(assertion.get("other_field_path"), f"{rule_id}.other_field_path")
    values = values_at_path(item, path)
    other_values = values_at_path(item, other_path)
    if len(values) == 1 and len(other_values) == 1 and values[0] == other_values[0]:
        return []
    return [
        issue(
            rule_id,
            collection,
            item,
            "declarative_field_mismatch",
            f"{path} must equal {other_path}",
        )
    ]


def check_refs_exist(
    index: Mapping[str, frozenset[str]],
    rule_id: str,
    collection: str,
    item: JsonObject,
    assertion: JsonObject,
) -> list[DeclarativeIssue]:
    path = require_string(assertion.get("field_path"), f"{rule_id}.field_path")
    collections = require_string_list(
        assertion.get("reference_collections"),
        f"{rule_id}.reference_collections",
    )
    allowed_refs = collect_allowed_refs(index, collections)
    missing = [
        value
        for value in values_at_path(item, path)
        if not isinstance(value, str) or value not in allowed_refs
    ]
    if not missing:
        return []
    return [
        issue(
            rule_id,
            collection,
            item,
            "declarative_unknown_ref",
            f"{path} contains unknown reference(s) {sorted(str(value) for value in missing)}",
        )
    ]


def check_list_contains_all(
    rule_id: str,
    collection: str,
    item: JsonObject,
    assertion: JsonObject,
) -> list[DeclarativeIssue]:
    path = require_string(assertion.get("field_path"), f"{rule_id}.field_path")
    required = frozenset(
        require_string_list(assertion.get("required_values"), f"{rule_id}.required_values")
    )
    actual = {value for value in values_at_path(item, path) if isinstance(value, str)}
    missing = sorted(required - actual)
    if not missing:
        return []
    return [
        issue(
            rule_id,
            collection,
            item,
            "declarative_required_values_missing",
            f"{path} is missing {missing}",
        )
    ]


def check_every_field_equals(
    rule_id: str,
    collection: str,
    item: JsonObject,
    assertion: JsonObject,
) -> list[DeclarativeIssue]:
    path = require_string(assertion.get("field_path"), f"{rule_id}.field_path")
    field = require_string(assertion.get("nested_field"), f"{rule_id}.nested_field")
    expected = require_string(assertion.get("expected_value"), f"{rule_id}.expected_value")
    values = values_at_path(item, path)
    bad_ids: list[str] = []
    for value in values:
        value_map = require_mapping(value, f"{rule_id}.{path}[]")
        actual = value_map.get(field)
        if actual != expected:
            bad_ids.append(object_identifier(value_map))
    if not bad_ids:
        return []
    return [
        issue(
            rule_id,
            collection,
            item,
            "declarative_nested_field_mismatch",
            f"{path}[].{field} must be {expected!r}; mismatched ids={bad_ids}",
        )
    ]


def check_file_exists(
    rule_id: str,
    collection: str,
    item: JsonObject,
    assertion: JsonObject,
    workspace: Path,
) -> list[DeclarativeIssue]:
    path = require_string(assertion.get("field_path"), f"{rule_id}.field_path")
    missing: list[str] = []
    for value in values_at_path(item, path):
        if not isinstance(value, str):
            missing.append(str(value))
            continue
        candidate = Path(value)
        if not candidate.is_absolute():
            candidate = workspace / candidate
        if not candidate.exists():
            missing.append(value)
    if not missing:
        return []
    return [
        issue(
            rule_id,
            collection,
            item,
            "declarative_missing_file",
            f"{path} contains missing file(s) {missing}",
        )
    ]


def check_no_intersection(
    rule_id: str,
    collection: str,
    item: JsonObject,
    assertion: JsonObject,
) -> list[DeclarativeIssue]:
    path = require_string(assertion.get("field_path"), f"{rule_id}.field_path")
    forbidden = frozenset(
        require_string_list(assertion.get("forbidden_values"), f"{rule_id}.forbidden_values")
    )
    actual = {value for value in values_at_path(item, path) if isinstance(value, str)}
    overlap = sorted(actual & forbidden)
    if not overlap:
        return []
    return [
        issue(
            rule_id,
            collection,
            item,
            "declarative_forbidden_intersection",
            f"{path} contains forbidden value(s) {overlap}",
        )
    ]


def select_objects(manifest: JsonObject, collection: str) -> tuple[JsonObject, ...]:
    if collection == "symbols":
        symbols = require_mapping(manifest.get("symbols"), "symbols")
        objects: list[JsonObject] = []
        for identifier, value in symbols.items():
            value_map = require_mapping(value, f"symbols.{identifier}")
            enriched = dict(value_map)
            enriched.setdefault("id", identifier)
            objects.append(enriched)
        return tuple(objects)
    raw_collection = manifest.get(collection)
    items = require_list(raw_collection, collection)
    return tuple(require_mapping(item, f"{collection}[]") for item in items)


def predicate_matches(item: JsonObject, predicate: JsonObject) -> bool:
    path = require_string(predicate.get("field_path"), "predicate.field_path")
    values = values_at_path(item, path)
    if "equals" in predicate:
        return any(value == predicate["equals"] for value in values)
    if "in" in predicate:
        allowed = frozenset(require_string_list(predicate.get("in"), "predicate.in"))
        return any(isinstance(value, str) and value in allowed for value in values)
    raise DeclarativeRuleError("predicate must define equals or in")


def values_at_path(root: object, path: str) -> list[object]:
    values: list[object] = [root]
    if not path:
        return values
    for segment in path.split("."):
        expand = segment.endswith("[]")
        key = segment[:-2] if expand else segment
        next_values: list[object] = []
        for value in values:
            if not isinstance(value, dict):
                continue
            child = value.get(key)
            if expand:
                if isinstance(child, list):
                    next_values.extend(child)
                continue
            if child is not None:
                next_values.append(child)
        values = next_values
    return values


def build_reference_index(manifest: JsonObject) -> dict[str, frozenset[str]]:
    index: dict[str, frozenset[str]] = {}
    symbols = require_mapping(manifest.get("symbols"), "symbols")
    index["symbols"] = frozenset(symbols)
    for collection in (
        "equations",
        "derivations",
        "finite_gates",
        "qm_experiments",
        "qm_universal_patterns",
        "qm_core_proof_obligations",
        "theorem_cards",
    ):
        collection_refs: set[str] = set()
        for item in require_list(manifest.get(collection), collection):
            item_map = require_mapping(item, f"{collection}[]")
            identifier = item_map.get("id")
            if isinstance(identifier, str):
                collection_refs.add(identifier)
        index[collection] = frozenset(collection_refs)
    all_refs: set[str] = set()
    for known_refs in index.values():
        all_refs.update(known_refs)
    index["*"] = frozenset(all_refs)
    return index


def collect_allowed_refs(index: Mapping[str, frozenset[str]], collections: Sequence[str]) -> frozenset[str]:
    refs: set[str] = set()
    for collection in collections:
        known = index.get(collection)
        if known is None:
            raise DeclarativeRuleError(f"unknown reference collection {collection!r}")
        refs.update(known)
    return frozenset(refs)


def is_non_empty(value: object) -> bool:
    if isinstance(value, str):
        return bool(value.strip())
    if isinstance(value, list | dict):
        return bool(value)
    return value is not None


def require_mapping(value: object, field: str) -> JsonObject:
    if not isinstance(value, dict):
        raise DeclarativeRuleError(f"{field} must be an object")
    output: JsonObject = {}
    for key, item in value.items():
        if not isinstance(key, str):
            raise DeclarativeRuleError(f"{field} keys must be strings")
        output[key] = item
    return output


def require_list(value: object, field: str) -> list[object]:
    if not isinstance(value, list):
        raise DeclarativeRuleError(f"{field} must be a list")
    return list(value)


def require_string(value: object, field: str) -> str:
    if not isinstance(value, str):
        raise DeclarativeRuleError(f"{field} must be a string")
    return value


def require_string_list(value: object, field: str) -> tuple[str, ...]:
    items = require_list(value, field)
    strings: list[str] = []
    for index, item in enumerate(items):
        strings.append(require_string(item, f"{field}[{index}]"))
    return tuple(strings)


def object_identifier(item: Mapping[str, object]) -> str:
    identifier = item.get("id")
    if isinstance(identifier, str):
        return identifier
    return "<unknown>"


def issue(
    rule_id: str,
    collection: str,
    item: Mapping[str, object],
    code: str,
    message: str,
) -> DeclarativeIssue:
    return DeclarativeIssue(
        code=code,
        message=f"{rule_id}: {collection}.{object_identifier(item)}: {message}",
    )
