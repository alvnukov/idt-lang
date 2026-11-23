"""Programmed classical readouts embedded in one symmetric Boolean relation.

The substrate, role tags, initialized bonds/rails, and serial offer words are
supplied. No copy of the source bit is required by the two-comparison reader.
This is not a quantum cloning or Born result, autonomous gate selection, or
inherent universality of the raw dynamics.

Run: python3 -m scripts.probe_embedded_relation_reader
"""

from __future__ import annotations

import json
import sys
from collections import Counter
from dataclasses import asdict, dataclass
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_single_relation_quartet import (
    PARITY_WORD,
    Relation,
    Rule,
    State,
    Word,
)

Quartet = tuple[int, int, int, int]


def quartet_word(ports: Quartet) -> Word:
    """Relabel the frozen four-site offer word onto four distinct ports."""
    if len(set(ports)) != 4:
        raise ValueError("quartet ports must be distinct")
    return tuple((ports[i], ports[j]) for i, j in PARITY_WORD)


def star_bonds(leaves: tuple[int, ...], hub: int) -> Word:
    """Prepare links, not offer them; a mutation may choose an odd leaf count."""
    if hub in leaves or len(set(leaves)) != len(leaves):
        raise ValueError("star leaves must be distinct from each other and the hub")
    return tuple((leaf, hub) for leaf in leaves)


def comparator_word(c: int, k: int, p: int, q: int, hub: int) -> Word:
    """On an even star and opposite rails, toggle rail orientation iff c != k."""
    if hub in (c, k, p, q):
        raise ValueError("comparator hub must be distinct from its leaf ports")
    # The quartet complements c,k,p,q only when c != k (the rails have weight
    # one). Then c,k have exchanged positions. Shuttle them back via the hub.
    return quartet_word((c, k, p, q)) + ((c, hub), (k, hub), (c, hub))


_SOURCE = (0, 1, 2, 3)
_REFERENCE = 4
_RAILS = (5, 6)
_SPARE = 7
_HUB = 8
_RAIL_MASK = (1 << _RAILS[0]) | (1 << _RAILS[1])
_SOURCE_WORD = quartet_word(_SOURCE)
_COMPARE = comparator_word(0, _REFERENCE, *_RAILS, _HUB)
_EVEN_BONDS = star_bonds(tuple(range(_HUB)), _HUB)
RECORD_WORD = _COMPARE + _SOURCE_WORD + _COMPARE
DESTRUCTIVE_WORD = _SOURCE_WORD + ((0, 4),)
_TOFFOLI_COMPARE = comparator_word(2, _REFERENCE, *_RAILS, _HUB)
_UNCOMPUTE = _SOURCE_WORD[::-1]
TOFFOLI_WORD = _SOURCE_WORD + _TOFFOLI_COMPARE + _UNCOMPUTE


@dataclass(frozen=True)
class OffsetCensus:
    correct_by_mask: tuple[int, ...]
    histogram: dict[int, int]
    exact_masks: tuple[int, ...]


@dataclass(frozen=True)
class ReadoutCensus:
    raw_offers: int
    changed: int
    unchanged: int


@dataclass(frozen=True)
class RecordCensus(ReadoutCensus):
    initially_unequal_reference: int


@dataclass(frozen=True)
class DestructiveCensus(ReadoutCensus):
    source_back_actions: int


@dataclass(frozen=True)
class Witness:
    initial: State
    actual: State
    expected: State


@dataclass(frozen=True)
class MutationCensus:
    cases: int
    failures: int
    first_failure: Witness


def _bit(sites: int, tag: int) -> int:
    return (sites >> tag) & 1


def _source_target(sites: int) -> int:
    return sites ^ 15 if (sites & 15).bit_count() == 2 else sites


def _record_target(sites: int) -> tuple[int, bool]:
    target = _source_target(sites)
    change = bool((target ^ sites) & 1)
    return target ^ (_RAIL_MASK if change else 0), change


def _check_state(actual: State, expected: State, case: str) -> None:
    if actual != expected:
        raise RuntimeError(f"{case}: {actual!r} != {expected!r}")


def _rails_opposite(sites: int) -> bool:
    return _bit(sites, _RAILS[0]) != _bit(sites, _RAILS[1])


def offset_census() -> OffsetCensus:
    """Cross all 16 exterior degree-parity masks with 16 clean quartet inputs.

    No exterior contacts are offered. An exterior bond offset is therefore
    fixed. A common parity offset cancels in each core pair comparison, step
    by step, while the core bond being offered and both diagonals agree with
    the isolated replay. The finite census also tests unequal offset masks.
    """
    layout = Relation(5)
    apply = layout.compile_word(_SOURCE_WORD, Rule.PARITY)
    counts = []
    for mask in range(16):
        bonds = star_bonds(tuple(j for j in _SOURCE if _bit(mask, j)), 4)
        counts.append(
            sum(
                apply(layout.state(sites, bonds))
                == layout.state(_source_target(sites), bonds)
                for sites in range(16)
            )
        )
    return OffsetCensus(
        tuple(counts),
        dict(sorted(Counter(counts).items())),
        tuple(mask for mask, correct in enumerate(counts) if correct == 16),
    )


def comparator_census() -> ReadoutCensus:
    """Replay the quartet and hub shuttle, retaining other leaves and bonds."""
    layout = Relation(9)
    apply = layout.compile_word(_COMPARE, Rule.PARITY)
    changed = unchanged = 0
    for sites in range(1 << layout.size):
        if not _rails_opposite(sites):
            continue
        difference = _bit(sites, 0) != _bit(sites, _REFERENCE)
        expected = sites ^ (_RAIL_MASK if difference else 0)
        _check_state(
            apply(layout.state(sites, _EVEN_BONDS)),
            layout.state(expected, _EVEN_BONDS),
            f"compare input {sites}",
        )
        changed += difference
        unchanged += not difference
    return ReadoutCensus(len(_COMPARE), changed, unchanged)


def record_census() -> RecordCensus:
    """Program M; F; M: XOR the old and new comparisons to one arbitrary k."""
    layout = Relation(9)
    apply = layout.compile_word(RECORD_WORD, Rule.PARITY)
    changed = unchanged = reference_unequal = 0
    for sites in range(1 << layout.size):
        if not _rails_opposite(sites):
            continue
        expected, change = _record_target(sites)
        _check_state(
            apply(layout.state(sites, _EVEN_BONDS)),
            layout.state(expected, _EVEN_BONDS),
            f"record input {sites}",
        )
        changed += change
        unchanged += not change
        reference_unequal += _bit(sites, 0) != _bit(sites, _REFERENCE)
    return RecordCensus(len(RECORD_WORD), changed, unchanged, reference_unequal)


def destructive_census() -> DestructiveCensus:
    """Copied reference leaves let one real bond offer flag and undo a change."""
    layout = Relation(6)
    bonds: Word = ((0, 4), (0, 5))
    source = layout.compile_word(_SOURCE_WORD, Rule.PARITY)
    compare = layout.compile_word(DESTRUCTIVE_WORD[len(_SOURCE_WORD) :], Rule.PARITY)
    changed = unchanged = back_actions = 0
    for sites in range(16):
        old_c = _bit(sites, 0)
        initialized = sites | (old_c << 4) | (old_c << 5)
        source_target = _source_target(initialized)
        change = _bit(source_target, 0) != old_c
        source_after = source(layout.state(initialized, bonds))
        _check_state(
            source_after,
            layout.state(source_target, bonds),
            f"destructive control clean source input {sites}",
        )
        after = compare(source_after)
        expected = source_target ^ ((1 | (1 << 4)) if change else 0)
        _check_state(
            after, layout.state(expected, bonds), f"destructive control input {sites}"
        )
        changed += _bit(after.sites, 4) != old_c
        unchanged += _bit(after.sites, 4) == old_c
        back_actions += _bit(after.sites, 0) != _bit(source_after.sites, 0)
    return DestructiveCensus(len(DESTRUCTIVE_WORD), changed, unchanged, back_actions)


def toffoli_census() -> ReadoutCensus:
    """Conjunction into zero workspace, compare to zero, then reverse the word."""
    layout = Relation(9)
    source = layout.compile_word(_SOURCE_WORD, Rule.PARITY)
    compare = layout.compile_word(_TOFFOLI_COMPARE, Rule.PARITY)
    uncompute = layout.compile_word(_UNCOMPUTE, Rule.PARITY)
    changed = unchanged = 0
    workspace_and_reference = (1 << 2) | (1 << 3) | (1 << _REFERENCE)
    for sites in range(1 << layout.size):
        if sites & workspace_and_reference or not _rails_opposite(sites):
            continue
        conjunction = bool(_bit(sites, 0) & _bit(sites, 1))
        before = layout.state(sites, _EVEN_BONDS)
        flag = source(before)
        _check_state(
            flag,
            layout.state(sites ^ (15 if conjunction else 0), _EVEN_BONDS),
            f"Toffoli flag input {sites}",
        )
        mark = compare(flag)
        pointer_change = _RAIL_MASK if conjunction else 0
        _check_state(
            mark,
            layout.state(flag.sites ^ pointer_change, _EVEN_BONDS),
            f"Toffoli mark input {sites}",
        )
        _check_state(
            uncompute(mark),
            layout.state(sites ^ pointer_change, _EVEN_BONDS),
            f"Toffoli cleanup input {sites}",
        )
        changed += conjunction
        unchanged += not conjunction
    return ReadoutCensus(len(TOFFOLI_WORD), changed, unchanged)


def _mutation(bonds: Word, *, opposite: bool) -> MutationCensus:
    layout = Relation(9)
    apply = layout.compile_word(RECORD_WORD, Rule.PARITY)
    cases = failures = 0
    first = None
    for sites in range(1 << layout.size):
        if _rails_opposite(sites) != opposite:
            continue
        cases += 1
        before = layout.state(sites, bonds)
        expected = layout.state(_record_target(sites)[0], bonds)
        after = apply(before)
        if after != expected:
            failures += 1
            if first is None:
                first = Witness(before, after, expected)
    if first is None:
        raise RuntimeError("mutated program unexpectedly has no distinguishing input")
    return MutationCensus(cases, failures, first)


def mutation_controls() -> tuple[MutationCensus, MutationCensus]:
    """Break parity at the hub or leave the dual-rail code, holding words fixed.

    For equal rails, the oracle is only a diagnostic extension by bitwise
    complement of both rails; equal pairs have no logical orientation.
    """
    odd_bonds = star_bonds(tuple(range(_SPARE)), _HUB)
    return _mutation(odd_bonds, opposite=True), _mutation(_EVEN_BONDS, opposite=False)


def _mutation_report(result: MutationCensus) -> dict[str, object]:
    first = result.first_failure
    return {
        "cases": result.cases,
        "failures": result.failures,
        "first_failure": {
            "initial": first.initial._asdict(),
            "actual": first.actual._asdict(),
            "expected": first.expected._asdict(),
        },
    }


def report() -> dict[str, object]:
    odd_bus, equal_rails = mutation_controls()
    return {
        "scope": "finite programmed classical relation probe; not quantum cloning, Born, or inherent universality",
        "supplied": [
            "role tags",
            "star bonds",
            "rail initialization",
            "serialized offer words",
        ],
        "offset_census": asdict(offset_census()),
        "comparator": asdict(comparator_census()),
        "record": asdict(record_census()),
        "destructive_copy_control": asdict(destructive_census()),
        "programmed_toffoli": asdict(toffoli_census()),
        "mutations": {
            "odd_bus_isolates_spare_leaf": _mutation_report(odd_bus),
            "equal_rails_vs_diagnostic_bit_complement_oracle": _mutation_report(
                equal_rails
            ),
        },
    }


if __name__ == "__main__":
    print(json.dumps(report(), indent=2, sort_keys=True))
