"""Exact continuation certificates for a supplied total finite deterministic model.

Readouts are rational labels, not stochastic measurements. Every action word is
legal. Certificates concern only this declared model, not a physical candidate.
The certificate schema accepts at most N² pairs or N² action letters; longer
genuine witnesses are outside the supported input limits, not disproved.
"""

from __future__ import annotations

import hashlib
from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

from theory_experiments import primitive_screen
from theory_experiments.primitive_screen import (
    bounded_int,
    canonical_json,
    exact_fraction,
    object_fields,
)

MODEL_SCHEMA = "idt-continuation-model/1"
CERTIFICATE_SCHEMA = "idt-continuation-certificate/1"
SCOPE = "declared_total_finite_model_all_words_Astar_only"
LOADED_MODULE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
LOADED_HELPER_SHA256 = hashlib.sha256(Path(primitive_screen.__file__).read_bytes()).hexdigest()
Pair = tuple[int, int]


def _array(value: object, minimum: int, maximum: int) -> list[object]:
    if not isinstance(value, list):
        raise TypeError("expected JSON array")
    bounded_int(len(value), minimum, maximum)
    return value


@dataclass(frozen=True)
class _Model:
    transitions: tuple[tuple[int, ...], ...]
    readouts: tuple[tuple[Fraction, ...], ...]
    adapter: tuple[int, ...]

    def specification(self) -> dict[str, object]:
        return {"schema": MODEL_SCHEMA,
                "transitions": [list(row) for row in self.transitions],
                "readouts": [list(map(str, row)) for row in self.readouts],
                "adapter": list(self.adapter)}


def _parse_model(value: object) -> _Model:
    row = object_fields(value, {"schema", "transitions", "readouts", "adapter"})
    if row["schema"] != MODEL_SCHEMA:
        raise ValueError("unsupported continuation model schema")
    raw_readouts = _array(row["readouts"], 1, 64)
    size = len(raw_readouts)
    readouts = tuple(tuple(exact_fraction(x) for x in _array(raw, 1, 16))
                     for raw in raw_readouts)
    if any(len(raw) != len(readouts[0]) for raw in readouts):
        raise ValueError("readout vectors must have equal width")
    transitions = tuple(tuple(bounded_int(x, 0, size - 1) for x in _array(raw, size, size))
                        for raw in _array(row["transitions"], 0, 16))
    adapter = tuple(bounded_int(x, -(2**31), 2**31 - 1)
                    for x in _array(row["adapter"], size, size))
    return _Model(transitions, readouts, adapter)


def normalize_model(value: object) -> dict[str, object]:
    """Validate strict input and canonicalize exact rational readout strings."""
    return _parse_model(value).specification()


def _digest(model: _Model) -> str:
    return hashlib.sha256(canonical_json(model.specification()).encode()).hexdigest()


def _search(model: _Model) -> dict[str, object]:
    size = len(model.adapter)
    predecessors: dict[Pair, tuple[Pair, int] | None] = {
        (left, right): None for left in range(size) for right in range(size)
        if model.adapter[left] == model.adapter[right]
    }
    queue = deque(predecessors)
    common: dict[str, object] = {"schema": CERTIFICATE_SCHEMA, "model_sha256": _digest(model)}
    # ponytail: O(A*N²), N<=64/A<=16; no minimizer or arbitrary depth cutoff needed.
    while queue:
        pair = queue.popleft()
        left, right = pair
        if model.readouts[left] != model.readouts[right]:
            word: list[int] = []
            previous = predecessors[pair]
            while previous is not None:
                pair, action = previous
                word.append(action)
                previous = predecessors[pair]
            return {**common, "kind": "distinguishing_word", "origin": list(pair),
                    "word": list(reversed(word))}
        for action, row in enumerate(model.transitions):
            successor = (row[left], row[right])
            if successor not in predecessors:
                predecessors[successor] = (pair, action)
                queue.append(successor)
    return {**common, "kind": "stable_relation",
            "pairs": [list(pair) for pair in sorted(predecessors)]}


def _pair(value: object, size: int) -> Pair:
    raw = _array(value, 2, 2)
    return bounded_int(raw[0], 0, size - 1), bounded_int(raw[1], 0, size - 1)


def verify_certificate(expected_model: object, certificate: object) -> bool:
    """Check evidence directly against independent expected input, never search.

    False means not accepted (invalid or outside schema/resource limits), not
    necessarily false evidence and never a model or candidate rejection.
    """
    try:
        model = _parse_model(expected_model)
        size = len(model.adapter)
        row = object_fields(certificate)
        if row.get("schema") != CERTIFICATE_SCHEMA or row.get("model_sha256") != _digest(model):
            return False
        common = {"schema", "model_sha256", "kind"}
        if row.get("kind") == "stable_relation":
            object_fields(row, common | {"pairs"})
            raw_pairs = _array(row["pairs"], 1, size * size)
            pairs = {_pair(raw, size) for raw in raw_pairs}
            if len(pairs) != len(raw_pairs):
                return False
            if any((left, right) not in pairs for left in range(size) for right in range(size)
                   if model.adapter[left] == model.adapter[right]):
                return False
            return all(model.readouts[left] == model.readouts[right]
                       and all((action[left], action[right]) in pairs for action in model.transitions)
                       for left, right in pairs)
        if row.get("kind") == "distinguishing_word":
            object_fields(row, common | {"origin", "word"})
            left, right = _pair(row["origin"], size)
            if model.adapter[left] != model.adapter[right]:
                return False
            # A shortest witness never repeats a pair, so generation needs <N² letters.
            # Verification accepts any replayable word within this declared resource cap.
            word = _array(row["word"], 0, size * size)
            for raw_action in word:
                action = model.transitions[bounded_int(raw_action, 0, len(model.transitions) - 1)]
                left, right = action[left], action[right]
            return model.readouts[left] != model.readouts[right]
        return False
    except (TypeError, ValueError, KeyError, OverflowError):
        return False


def _adapter_update(model: _Model) -> dict[str, object]:
    for left in range(len(model.adapter)):
        for right in range(len(model.adapter)):
            if model.adapter[left] != model.adapter[right]:
                continue
            for action, row in enumerate(model.transitions):
                if model.adapter[row[left]] != model.adapter[row[right]]:
                    return {"status": "structural_update_failure", "pair": [left, right],
                            "action": action, "successors": [row[left], row[right]]}
    return {"status": "stable"}


def analyze(value: object) -> dict[str, object]:
    """Decide all declared continuations, independently verifying the certificate."""
    model = _parse_model(value)
    certificate = _search(model)
    if not verify_certificate(model.specification(), certificate):
        raise ValueError("generated certificate failed independent verification; checker error")
    return {"schema": "idt-continuation-analysis/1", "model_sha256": _digest(model),
            "status": ("predictively_sufficient_for_declared_words"
                       if certificate["kind"] == "stable_relation" else "observable_counterexample"),
            "adapter_update": _adapter_update(model), "certificate": certificate,
            "certificate_valid": True, "candidate_verdict": "unchanged",
            "proof_status": "concrete_certificate_not_lean_checked",
            "empirical_status": "not_tested", "scope": SCOPE}


def demo_models() -> dict[str, object]:
    """Small supplied mathematical fixtures, not empirical or primitive models."""
    def model(transitions: list[list[int]], readouts: list[str], adapter: list[int]) -> dict[str, object]:
        return {"schema": MODEL_SCHEMA, "transitions": transitions,
                "readouts": [[x] for x in readouts], "adapter": adapter}

    return {
        "constant_readout_cycle": model([[1, 2, 0]], ["7", "7", "7"], [0, 0, 0]),
        "predictive_pass_update_failure": model([[2, 3, 2, 3]], ["0", "0", "1", "1"], [0, 0, 1, 2]),
        # States denote (2,0), (1,1), (1,-1); labels are supplied, not inferred.
        "three_state_phase_flip": model([[0, 2, 1]], ["4/5", "4/5", "0"], [2, 2, 0]),
    }
