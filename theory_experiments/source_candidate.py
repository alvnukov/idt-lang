"""Source-backed proposals are retained inputs, not executable physical models."""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass
from pathlib import PurePosixPath

from theory_experiments.primitive_screen import (
    Check,
    bounded_int,
    candidate_id,
    object_fields,
)

ROLES = frozenset({"primitive_base", "lower_law", "legacy_scaffold", "semantic_contract",
                   "realization", "route", "law_family_collection"})
FAMILY = "source_theory"


def _text(value: object, maximum: int) -> str:
    if not isinstance(value, str) or not value.strip() or len(value) > maximum:
        raise ValueError("nonempty bounded source-candidate text required")
    return value


def _strings(value: object) -> tuple[str, ...]:
    if not isinstance(value, list) or not 1 <= len(value) <= 48:
        raise ValueError("source-candidate list must contain 1 to 48 strings")
    result = tuple(_text(item, 1000) for item in value)
    if len(set(result)) != len(result):
        raise ValueError("duplicate source-candidate list entry")
    return result


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def source_path(value: object) -> str:
    name = _text(value, 250)
    path = PurePosixPath(name)
    if (path.is_absolute() or ".." in path.parts or "\\" in name
            or path.parts[0] not in ("Proofs", "sections", "scripts", "theory_experiments")
            or path.suffix not in (".lean", ".md", ".py") or str(path) != name):
        raise ValueError("source snapshot path must be an allowed repository source")
    return name


def source_digest(value: object) -> str:
    if not isinstance(value, str) or re.fullmatch(r"[0-9a-f]{64}", value) is None:
        raise ValueError("source snapshot requires a SHA-256 digest")
    return value


@dataclass(frozen=True)
class SourceSnapshot:
    path: str
    first_line: int
    last_line: int
    file_sha256: str
    text: str

    def specification(self) -> dict[str, object]:
        return {"path": self.path, "first_line": self.first_line, "last_line": self.last_line,
                "file_sha256": self.file_sha256, "text": self.text,
                "text_sha256": sha256_text(self.text)}


def parse_snapshot(value: object) -> SourceSnapshot:
    row = object_fields(value, {"path", "first_line", "last_line", "file_sha256", "text", "text_sha256"})
    first = bounded_int(row["first_line"], 1, 50000)
    last = bounded_int(row["last_line"], first, first + 1000)
    text = _text(row["text"], 65536)
    if len(text.splitlines()) != last - first + 1 or sha256_text(text) != row["text_sha256"]:
        raise ValueError("source snapshot span/digest mismatch")
    return SourceSnapshot(source_path(row["path"]), first, last, source_digest(row["file_sha256"]), text)


@dataclass(frozen=True)
class SourceCandidate:
    id: str
    role: str
    components: tuple[str, ...]
    declared_status: str
    missing_bridges: tuple[str, ...]
    sources: tuple[SourceSnapshot, ...]

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "family": FAMILY, "role": self.role,
                "components": list(self.components), "declared_status": self.declared_status,
                "missing_bridges": list(self.missing_bridges),
                "sources": [source.specification() for source in self.sources]}


def parse_source_candidate(value: object) -> SourceCandidate:
    row = object_fields(value, {"id", "family", "role", "components", "declared_status", "missing_bridges", "sources"})
    role = _text(row["role"], 32)
    sources = row["sources"]
    if row["family"] != FAMILY or role not in ROLES:
        raise ValueError("invalid source-candidate family/role")
    if not isinstance(sources, list) or not 1 <= len(sources) <= 8:
        raise ValueError("source candidate requires 1 to 8 retained snapshots")
    snapshots = tuple(parse_snapshot(source) for source in sources)
    if len({(source.path, source.first_line, source.last_line) for source in snapshots}) != len(snapshots):
        raise ValueError("duplicate source snapshot")
    return SourceCandidate(candidate_id(row["id"]), role, _strings(row["components"]),
                           _text(row["declared_status"], 2000), _strings(row["missing_bridges"]), snapshots)


def evaluate_source_candidate(candidate: SourceCandidate) -> tuple[tuple[Check, ...], dict[str, object]]:
    check = Check("primitive_prediction_adapter", "unsupported", 0, 0,
                  "requires_a_reviewed_executable_prediction_map", (
                      "source_preservation_does_not_supply_physical_predictions",
                      "historical_status_is_not_a_current_checker_verdict",
                      "no_implicit_QM_SM_or_gravity_adapter"), None)
    return (check,), {"adapter_status": "missing", "scientific_status": "unassessed",
        "role": candidate.role, "missing_bridges": list(candidate.missing_bridges),
        "declared_status_at_capture": candidate.declared_status,
        "untested": ["predictions_from_these_primitives", "QM", "SM", "gravity", "empirical_data"],
        "source_boundary": "snapshots_are_retained_input_not_executed_code_or_checked_proof"}
