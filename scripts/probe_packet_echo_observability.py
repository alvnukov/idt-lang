"""One extra calibrated wire operation makes packet transparency observable.

Use the frozen six-species deterministic memoryless model: one unordered pair
of DISTINCT marks, fixed port partition {0,1}|{2,3}, and final coarse count
h=number of marks in port0. Allowed pure preparations are e01 and e23; each
is unique given its coarse count in this model. No hidden-leg readout, signed
amplitude, norm, Born probability, postselection or statistical inference enters.
The two-run minimality calculation conditions on the eight-table shortlist from
the earlier ALL-SIX-INPUT coarse screens. Its two-run observations alone do not
establish that shortlist. A separate full-census bridge below uses only pure
preparations and does not rely on those earlier input capabilities.

The eight coarse-echo survivors have one of two moving cycles
01->03->23->12->01 or its inverse, and an arbitrary self-map of {02,13}:
identity, swap, or either reset. Only the two identity choices are transparent.
F and the supplied whole-port swap S preserve the moving/fixed partition.
Pure preparations never enter the hidden pair, so unlimited F/S words cannot
distinguish these maps. This is an accessibility wall, not failed predictions.

Add the independently implemented internal involution V0=(01). It reads no
leg, but it is a genuinely additional addressed routing operation, not a word
in F and S. Apply W=F V F V F LEFT TO RIGHT, then read h. The two preparations
give transparent (0,2), nontransparent rotations (2,0), and resets (2,2) or
(0,0). Three F events and two V events per trial suffice. All distinguishable
pairs first separate at length5. Full joint automaton closure has30 states:
no single word with ONE fixed pure preparation and ONE final measurement
separates the intended pair from every rival. Two length5 experiments are a
minimal cover, cost10 operations excluding preparation/readout. Intermediate
nondestructive records, multiple packets, ancillas or mixed-preparation
statistics are different resources, not ruled out by that minimality claim.

PURE-INPUT FULL-CENSUS BRIDGE. Among all46656 tables, FF on both pure inputs
with outputs(0,2) leaves432; adding FSF with outputs(2,0) leaves72; adding W
with outputs(0,2) leaves precisely the intended2. These six runs cost20
operations. In fact, both W runs plus ONE FF run and ONE FSF run already
suffice, whichever pure input is chosen for each shorter word: four runs,
cost15. Four is the minimum number of controls selected FROM THIS SIX-TEST
SUITE, not a claimed global optimum over arbitrary words or other resources.
The full bridge uses the independently calibrated S as well as V. Without S,
the other port's internal swap conjugates an intended root to an outside-table
countercontrol while preserving every pure-input F/V observation.

Gauge: G=(01)(23) fixes both preparations and h, commutes with V0 and S, and
conjugates the two orientations (also interchanging reset labels). Induction
on words proves all-word indistinguishability of those paired models. Product
automaton BFS is a finite exhaustive decision, not a bounded-depth guess:
once all reachable product states are explored, no future word can add a new
distinction. F-only and F+S give one class; F+V and F+S+V give four classes.

WEAKER CALIBRATION CERTIFICATE. Specific V0 wiring is sufficient, not necessary.
If V is ANY independently supplied involution and W exchanges both pure inputs,
write m=F(p). The desired final pure packet has m as its unique F-preimage
among all eight survivors. Therefore V F V m=m, hence F(Vm)=Vm. The two m are
distinct, as are their V images, forcing two fixed points of F. Only the
transparent survivors have two. All ten coarse-preserving involutions are
checked below. Coarse preservation plus reversibility alone is insufficient:
a four-cycle fake V with the rotation F reproduces the two-run results and
passes every V-only coarse test on pure preparations, but is not involutive.

PREPARATION/OPERATION WALLS. Unknown preparation can let the rotation counterfeit
the intended pair by exchanging the two inputs. (The two opposite pure outputs
still cannot both come from either reset under W; not every weaker observation
is useless.) The exact target identification is ineligible without calibrated
pure preparations and an independent control contract. Missing controls are
reported as inaccessible, not as a physical rejection. Simulated tables are
not observed data. No public status, Lean proof or full-QM claim is upgraded.
"""

from __future__ import annotations

import sys
from collections import deque
from dataclasses import dataclass
from itertools import combinations, permutations, product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from theory_experiments.unsigned_pair_packet import (
    BY_PORT,
    EDGES,
    FIX,
    ID,
    SWAP,
    Table,
    after,
    check_table,
    leg_table,
)

V = leg_table((1, 0, 2, 3))
GAUGE = leg_table((1, 0, 3, 2))
PREPARATIONS = (0, 5)
WORD = "FVFVF"


def need(ok: bool, reason: str) -> None:
    if not ok:
        raise ArithmeticError(reason)


@dataclass(frozen=True)
class Candidate:
    orientation: int
    hidden: str
    table: Table


def candidates() -> tuple[Candidate, ...]:
    out = []
    for orientation, cycle in ((1, (0, 2, 5, 3)), (-1, (0, 3, 5, 2))):
        for label, hidden in (
            ("id", (1, 4)),
            ("swap", (4, 1)),
            ("reset02", (1, 1)),
            ("reset13", (4, 4)),
        ):
            table = list(ID)
            for a, b in zip(cycle, cycle[1:] + cycle[:1], strict=True):
                table[a] = b
            table[1], table[4] = hidden
            out.append(Candidate(orientation, label, tuple(table)))
    coarse = {
        f
        for f in product(range(6), repeat=6)
        if all(BY_PORT[f[f[i]]] == BY_PORT[SWAP[i]] for i in range(6))
        and all(BY_PORT[f[i]] == BY_PORT[i] for i in FIX)
    }
    need(
        coarse == {c.table for c in out} and len(coarse) == 8,
        "complete coarse survivors of all46656 tables",
    )
    need(
        sum(check_table(c.table)["transparent_root"] for c in out) == 2,
        "only two transparent packet roots",
    )
    return tuple(out)


def advance(f: Table, state: int, op: str, internal: Table = V) -> int:
    if op == "F":
        return f[state]
    if op == "V":
        return internal[state]
    if op == "S":
        return SWAP[state]
    raise ValueError("operations are F, V and S")


def read_word(f: Table, preparation: int, word: str, internal: Table = V) -> int:
    state = preparation
    for op in word:
        state = advance(f, state, op, internal)
    return BY_PORT[state]


@dataclass(frozen=True)
class Probe:
    preparation: int
    word: str
    states: tuple[int, ...]

    @property
    def outputs(self) -> tuple[int, ...]:
        return tuple(BY_PORT[x] for x in self.states)


def explore(tables: tuple[Table, ...], alphabet: str) -> tuple[Probe, ...]:
    """Multi-source BFS, complete finite product-automaton closure."""
    queue = deque(Probe(p, "", (p,) * len(tables)) for p in PREPARATIONS)
    seen = {p.states for p in queue}
    probes = []
    while queue:
        probe = queue.popleft()
        probes.append(probe)
        for op in alphabet:
            states = tuple(
                advance(f, x, op) for f, x in zip(tables, probe.states, strict=True)
            )
            if states not in seen:
                seen.add(states)
                queue.append(Probe(probe.preparation, probe.word + op, states))
    need(len(seen) <= 6 ** len(tables), "finite product-state bound")
    return tuple(probes)


def witness(a: Table, b: Table, alphabet: str) -> Probe | None:
    return next(
        (p for p in explore((a, b), alphabet) if p.outputs[0] != p.outputs[1]), None
    )


def classes(tables: tuple[Table, ...], alphabet: str) -> tuple[tuple[int, ...], ...]:
    remaining = set(range(len(tables)))
    result = []
    while remaining:
        first = min(remaining)
        block = tuple(
            j
            for j in sorted(remaining)
            if witness(tables[first], tables[j], alphabet) is None
        )
        result.append(block)
        remaining.difference_update(block)
    return tuple(result)


def elimination_mask(probe: Probe) -> int:
    outputs = probe.outputs
    need(outputs[0] == outputs[4], "orientation cannot be resolved by this interface")
    return sum(1 << i for i, value in enumerate(outputs) if value != outputs[0])


def minimal_cover(probes: tuple[Probe, ...]) -> tuple[Probe, ...] | None:
    """First minimize number of experiments, then total operation count."""
    selected: dict[int, Probe] = {}
    for p in probes:
        mask = elimination_mask(p)
        if mask and (
            mask not in selected
            or (len(p.word), p.preparation, p.word)
            < (
                len(selected[mask].word),
                selected[mask].preparation,
                selected[mask].word,
            )
        ):
            selected[mask] = p
    target = sum(1 << i for i in range(8) if i not in (0, 4))
    for size in range(1, len(selected) + 1):
        covers = []
        for group in combinations(selected.items(), size):
            union = 0
            for mask, _ in group:
                union |= mask
            if union == target:
                covers.append(tuple(p for _, p in group))
        if covers:
            return min(
                covers,
                key=lambda group: (
                    sum(len(p.word) for p in group),
                    tuple((p.preparation, p.word) for p in group),
                ),
            )
    return None


def automaton_controls(family: tuple[Candidate, ...]) -> None:
    tables = tuple(c.table for c in family)
    for alphabet in ("F", "FS", "FV", "FSV"):
        partition = classes(tables, alphabet)
        joint = explore(tables, alphabet)
        cover = minimal_cover(joint)
        if "V" not in alphabet:
            need(
                partition == (tuple(range(8)),) and len(joint) == 4 and cover is None,
                "unlimited inaccessible hidden map under F/S",
            )
        else:
            need(
                partition == ((0, 4), (1, 5), (2, 7), (3, 6)),
                "exact four observational classes",
            )
            need(
                len(joint) == 30 and cover is not None,
                "complete joint closure and separator cover",
            )
            if cover is None:
                raise ArithmeticError("missing cover")
            need(
                len(cover) == 2 and sum(len(p.word) for p in cover) == 10,
                "minimal two-experiment cost10",
            )
            need(
                {(p.preparation, p.word) for p in cover} == {(0, WORD), (5, WORD)},
                "common cheapest analyzer word",
            )
            for i, j in combinations(range(8), 2):
                found = witness(tables[i], tables[j], alphabet)
                need(
                    found is None or len(found.word) == 5,
                    "every distinguishable pair first differs at length5",
                )
        print(
            f"Operations {alphabet}: classes={partition}; reachable joint states={len(joint)}; minimum target cover={'inaccessible' if cover is None else '2 experiments, 10 operations'}."
        )
    expected = ((0, 2), (2, 0), (2, 2), (0, 0), (0, 2), (2, 0), (0, 0), (2, 2))
    need(
        tuple(tuple(read_word(f, p, WORD) for p in PREPARATIONS) for f in tables)
        == expected,
        "all eight two-preparation signatures",
    )


def gauge_controls(family: tuple[Candidate, ...]) -> None:
    need(
        after(GAUGE, GAUGE) == ID
        and after(GAUGE, V) == after(V, GAUGE)
        and after(GAUGE, SWAP) == after(SWAP, GAUGE),
        "control-compatible orientation gauge",
    )
    need(
        all(GAUGE[p] == p for p in PREPARATIONS)
        and all(BY_PORT[GAUGE[i]] == BY_PORT[i] for i in range(6)),
        "preparation/readout gauge invariance",
    )
    for i, j in enumerate((4, 5, 7, 6, 0, 1, 3, 2)):
        need(
            after(GAUGE, after(family[i].table, GAUGE)) == family[j].table,
            "exact conjugacy proves equality of every word",
        )
    moving = {0, 2, 3, 5}
    need(
        all(f.table[i] in moving and SWAP[i] in moving for f in family for i in moving),
        "F/S cannot access hidden sector",
    )
    need(
        V[2] not in moving and V[3] not in moving,
        "new operation crosses the accessibility wall",
    )


def scope(preparation_known: bool, involution_supplied: bool) -> str:
    return (
        "eligible_conditional"
        if preparation_known and involution_supplied
        else "inaccessible_not_rejected"
    )


def calibration_controls(family: tuple[Candidate, ...]) -> None:
    need(
        {i for i in range(6) if BY_PORT[i] == 2} == {0}
        and {i for i in range(6) if BY_PORT[i] == 0} == {5},
        "coarse pure preparation uniquely specifies a packet",
    )
    involutions = tuple(
        (0, *middle, 5)
        for middle in permutations((1, 2, 3, 4))
        if after((0, *middle, 5), (0, *middle, 5)) == ID
    )
    need(len(involutions) == 10, "all coarse-preserving involutions")
    accepted = 0
    for f, internal in product(family, involutions):
        observed = tuple(read_word(f.table, p, WORD, internal) for p in PREPARATIONS)
        if observed == (0, 2):
            accepted += 1
            need(
                f.hidden == "id",
                "weaker involution calibration still excludes all rivals",
            )
            fixed = tuple(internal[f.table[p]] for p in PREPARATIONS)
            need(
                len(set(fixed)) == 2 and all(f.table[x] == x for x in fixed),
                "two fixed points forced by the observed exchange",
            )
    need(accepted == 4, "two orientation choices times two successful involutions")
    rotation = family[1].table
    need(
        tuple(read_word(rotation, p, WORD) for p in reversed(PREPARATIONS)) == (0, 2),
        "uncalibrated exchanged preparations counterfeit the result",
    )
    fake = (0, 2, 4, 1, 3, 5)
    need(
        sorted(fake) == list(ID)
        and all(BY_PORT[fake[i]] == BY_PORT[i] for i in range(6)),
        "reversible coarse-preserving fake control",
    )
    need(
        all(fake[p] == p for p in PREPARATIONS) and after(fake, fake) != ID,
        "V-only pure-input observations do not certify involution",
    )
    need(
        tuple(read_word(rotation, p, WORD, fake) for p in PREPARATIONS) == (0, 2),
        "uncalibrated control counterfeits the proposed experiment",
    )
    outside = (1, 5, 2, 3, 0, 4)
    need(
        not check_table(outside)["coarse_transparent"]
        and tuple(read_word(outside, p, WORD) for p in PREPARATIONS) == (0, 2),
        "two-run pure-port protocol does not itself establish the prior shortlist",
    )
    other_port = leg_table((0, 1, 3, 2))
    need(
        after(other_port, after(family[0].table, other_port)) == outside
        and after(other_port, V) == after(V, other_port)
        and all(other_port[p] == p for p in PREPARATIONS)
        and all(BY_PORT[other_port[i]] == BY_PORT[i] for i in range(6)),
        "outside model is indistinguishable for every pure-input F/V word",
    )
    need(
        after(other_port, SWAP) != after(SWAP, other_port)
        and read_word(outside, 0, "FSF") != read_word(family[0].table, 0, "FSF"),
        "independently calibrated S separates the extra frame ambiguity",
    )
    for c in (family[2], family[3]):
        available = {read_word(c.table, p, WORD) for p in range(6)}
        need(
            not {0, 2} <= available,
            "opposite pure outputs still exclude either reset regardless of preparation",
        )
    need(
        scope(False, True) == scope(True, False) == "inaccessible_not_rejected",
        "missing operations or preparation are not physical rejection",
    )


def pure_input_bridge(family: tuple[Candidate, ...]) -> None:
    checks = (
        (0, "FF", 0),
        (5, "FF", 2),
        (0, "FSF", 2),
        (5, "FSF", 0),
        (0, WORD, 0),
        (5, WORD, 2),
    )
    patterns: dict[int, int] = {}
    survivors = set()
    for f in product(range(6), repeat=6):
        mask = sum(
            1 << i
            for i, (p, word, wanted) in enumerate(checks)
            if read_word(f, p, word) == wanted
        )
        patterns[mask] = patterns.get(mask, 0) + 1
        if mask == 63:
            survivors.add(f)

    def remaining(required: int) -> int:
        return sum(
            count
            for observed, count in patterns.items()
            if observed & required == required
        )

    need(
        sum(patterns.values()) == 46656
        and tuple(remaining(mask) for mask in (3, 15, 63)) == (432, 72, 2),
        "complete pure-input six-run census",
    )
    need(
        survivors == {c.table for c in family if c.hidden == "id"},
        "full census selects exactly the intended two",
    )
    minimum_subsets = []
    for size in range(1, 7):
        for subset in combinations(range(6), size):
            if remaining(sum(1 << i for i in subset)) == 2:
                minimum_subsets.append(subset)
        if minimum_subsets:
            break
    need(
        set(minimum_subsets)
        == {(0, 2, 4, 5), (0, 3, 4, 5), (1, 2, 4, 5), (1, 3, 4, 5)},
        "four controls are minimal within this six-control suite only",
    )
    need(
        all(sum(len(checks[i][1]) for i in subset) == 15 for subset in minimum_subsets),
        "four-run sufficient cost15",
    )
    print(
        "Pure-input full census: 46656 ->432 (two FF) ->72 (two FSF) ->2 (two FVFVF). Both FVFVF runs plus one FF and one FSF also suffice: four runs, cost15; no global minimality claim."
    )


def main() -> None:
    family = candidates()
    automaton_controls(family)
    gauge_controls(family)
    calibration_controls(family)
    pure_input_bridge(family)
    print(
        f"Use {WORD} left-to-right on {EDGES[0]} and {EDGES[5]}, then count port0 marks: intended(0,2), rotations(2,0), resets(2,2)/(0,0). No hidden-leg readout."
    )
    print(
        "Trusted involution control suffices; a reversible non-involution and unknown preparation counterfeit the finite test. Orientation remains gauge-equivalent."
    )
    print(
        "Exact deterministic packet classification only; missing controls are inaccessible, not rejected, and no simulated result is empirical evidence."
    )


if __name__ == "__main__":
    main()
