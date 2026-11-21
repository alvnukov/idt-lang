"""Verify finite hidden-label shutter certificates, not a wave or QM derivation.

The fair preparations and visibility predicate are supplied. Each witness is
calibrated to one gate table, with no claim of synthesis or minimal length.
"""

import sys
from fractions import Fraction
from itertools import product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_middle_order_echo import (
    EXTREMES,
    WEIGHTS,
    H,
    L,
    Triple,
    X,
    Y,
    conserved_gates,
    run,
)
from scripts.probe_reference_fanout import Gate, GateSignature, check
from scripts.probe_reference_weight_tradeoff import PAIRS, STATES

Mask = tuple[bool, bool]
Rates = tuple[Fraction, Fraction]
ZERO, QUARTER, HALF, ONE = Fraction(0), Fraction(1, 4), Fraction(1, 2), Fraction(1)
ARMS = (0, 1)
MASKS = ((True, True), (True, False), (False, True), (False, False))
CODE = frozenset((a, b, X) for a, b in PAIRS if not (a in EXTREMES and b in EXTREMES))
NORMAL = ((L, X, X), (X, L, X), (H, Y, X), (Y, H, X))
REVERSED = ((L, Y, X), (Y, L, X), (H, X, X), (X, H, X))

# Table numbers are 0-based in lexicographic order of signatures over PAIRS.
# Words are chronological, A=T01 and B=T12, after the shutters.
WORDS = {
    0: "BAAABBBAAABABABBBABBBAAABBBAAABBBAAABBBAAABBBAAABABBBABBBAAABBBABBB",
    2: "BAAABBBAAABABABBBABBBAAABBBAAABBBAAABBBAAABBBAAABABBBABBBAAABBBABBBAA",
    3: "ABAABABABABAABAAABABBBABABABABAABAAABABABA",
    4: "BABABABAAABAABABABBABAAABABABABABABABBBA",
    5: "BBBABABBBAAABBBAAABAAABABABABABABBBAAABAAABABAAABAA",
    7: "BBBABABBBAAABBBAAABAAABABABABABABBBAAABAAABABAAAB",
}
BLOCKED_TABLES = (1, 6)
PACKED_F = {
    3: 43,
    5: 53,
    6: 39,
    9: 45,
    10: 15,
    12: 46,
    17: 29,
    18: 27,
    20: 23,
    24: 30,
    33: 57,
    34: 51,
    36: 54,
    40: 60,
    48: 58,
}


def gate_tables() -> tuple[Gate, ...]:
    distinct: dict[GateSignature, Gate] = {
        tuple(gate[pair] for pair in PAIRS): gate for gate in conserved_gates()
    }
    check(len(distinct) == 8, "wrong deduplicated table count")
    return tuple(distinct[signature] for signature in sorted(distinct))


def weight(cells: tuple[int, ...]) -> int:
    return sum(WEIGHTS[cell] for cell in cells)


def shutter_trial(gate: Gate, word: str, state: Triple, opened: Mask) -> Mask:
    """Swap each blocked arm into its own ready-X dump and seal both dumps."""
    arms = list(state[:2])
    dumps = [X, X]
    for arm in ARMS:
        if not opened[arm]:
            arms[arm], dumps[arm] = gate[gate[arms[arm], dumps[arm]]]
            check((arms[arm], dumps[arm]) == (X, state[arm]), "shutter is not a swap")
    out = run(gate, word, (arms[0], arms[1], state[2]))
    check(out in CODE, "recombiner did not reset X and stay in the code")
    check(weight(out + tuple(dumps)) == weight(state + (X, X)), "raw weight changed")
    visible = out[0] in EXTREMES, out[1] in EXTREMES
    expected_count = sum(opened[arm] and state[arm] in EXTREMES for arm in ARMS)
    check(sum(visible) == expected_count, "visible exit count disagrees with shutter")
    return visible


def fair_rates(gate: Gate, word: str, prep: tuple[Triple, ...], opened: Mask) -> Rates:
    rows = [shutter_trial(gate, word, state, opened) for state in prep]
    return (
        Fraction(sum(row[0] for row in rows), len(rows)),
        Fraction(sum(row[1] for row in rows), len(rows)),
    )


def check_word(gate: Gate, word: str) -> None:
    for state, opened in product(CODE, MASKS):
        shutter_trial(gate, word, state, opened)
    tail = ((QUARTER, QUARTER), (QUARTER, QUARTER), (ZERO, ZERO))
    for prep, both_open in ((NORMAL, (ZERO, ONE)), (REVERSED, (ONE, ZERO))):
        rates = tuple(fair_rates(gate, word, prep, opened) for opened in MASKS)
        check(rates == (both_open, *tail), f"wrong fair-preparation rates: {rates}")


def unpack(index: int) -> Triple:
    return index // 16, index // 4 % 4, index % 4


def port_code(species: int, port: int) -> set[Triple]:
    return {state for state in CODE if state[port] == species}


def check_intertwiner(gate: Gate) -> tuple[tuple[int, int], ...]:
    """Check F on entire weight sectors and compare input/output capacities."""
    triples = tuple((a, b, c) for a, b, c in product(STATES, repeat=3))
    low = {state for state in triples if weight(state) == 2}
    high = {state for state in triples if weight(state) == 4}
    f = {unpack(source): unpack(target) for source, target in PACKED_F.items()}
    inv = {target: source for source, target in f.items()}
    check(len(low) == len(high) == 15, "wrong sectors for the intertwiner")
    check(f.keys() == low and inv.keys() == high, "F is not a sector bijection")
    for source, target in f.items():
        for move in "AB":
            next_source, next_target = run(gate, move, source), run(gate, move, target)
            check(next_source in low and next_target in high, "generator left a sector")
            check(f[next_source] == next_target, f"{move} does not intertwine with F")
    check(
        {source: f[source] for source in CODE & low}
        == {
            (L, X, X): (H, X, X),
            (L, Y, X): (Y, H, X),
            (X, L, X): (X, H, X),
            (Y, L, X): (H, Y, X),
        },
        "unexpected F on the low charged code",
    )
    sizes: list[tuple[int, int]] = []
    for prep, port in ((NORMAL, 1), (NORMAL, 0), (REVERSED, 1), (REVERSED, 0)):
        # A common word induces one injective permutation of the low sector.
        # By intertwining, the high-sector constraints become low-sector ones.
        inputs = (low & set(prep)) | {inv[state] for state in high & set(prep)}
        low_outputs, high_outputs = port_code(L, port), port_code(H, port)
        outputs = low_outputs | {inv[state] for state in high_outputs}
        check(
            (len(inputs), len(outputs)) == (4, 3),
            "wrong input/available-output sizes for the injection obstruction",
        )
        sizes.append((len(inputs), len(outputs)))
    return tuple(sizes)


def check_fixed_species_control() -> None:
    """With a perfect fringe, one fixed extreme leaves at most one state per arm."""
    for species, port in product(EXTREMES, ARMS):
        check(len(port_code(species, port)) == 2, "wrong fixed-species capacity")
    # A perfect both-open fringe with either species can use only the two
    # distinct outputs at that port, by injectivity and conserved weight.
    # With support in both input arms that allows just one input per arm.
    # Conditioning on transmission with either single arm open then leaves a
    # deterministic trial, which cannot give fair conditional exit rates.


def plate(state: Triple, arms: tuple[int, ...]) -> Triple:
    """Supply X↔Y on the selected arm(s); no gate synthesis is asserted."""
    labels = list(state)
    for arm in arms:
        labels[arm] = Y if state[arm] == X else X if state[arm] == Y else state[arm]
    return labels[0], labels[1], labels[2]


def check_local_phase_control(gate: Gate, word: str) -> None:
    # If all auxiliaries return unchanged, locality and conservation force the
    # affected cell to retain its weight. L and H each have a unique weight.
    for extreme in EXTREMES:
        check(
            {label for label in STATES if weight((label,)) == weight((extreme,))}
            == {extreme},
            "visible weight is not unique",
        )
    both_open = MASKS[0]
    for arm in ARMS:
        check(sum(state[arm] in EXTREMES for state in NORMAL) == 2, "unbalanced arms")
        prep = tuple(plate(state, (arm,)) for state in NORMAL)
        for before, after in zip(NORMAL, prep, strict=True):
            check(weight(before) == weight(after), "plate changed the weight")
            check((before == after) == (before[arm] in EXTREMES), "wrong plate action")
        check(
            fair_rates(gate, word, prep, both_open) == (HALF, HALF), "wrong plate rates"
        )
    both_flipped = tuple(plate(state, ARMS) for state in NORMAL)
    check(both_flipped == REVERSED, "two plates did not reverse the preparation")
    check(
        fair_rates(gate, word, both_flipped, both_open) == (ONE, ZERO),
        "wrong two-plate rates",
    )


def main() -> None:
    tables = gate_tables()
    check((L, X, Y, H) == (0, 1, 2, 3), "packed labels changed")
    check(len(CODE) == 12, "wrong code size")
    check(set(WORDS).isdisjoint(BLOCKED_TABLES), "overlapping classifications")
    check(
        set(WORDS).union(BLOCKED_TABLES) == set(range(len(tables))), "incomplete census"
    )
    print("Fixed-table certificates; indices sort deduplicated signatures over PAIRS.")
    print("Words are chronological A=T01, B=T12; lengths are not certified minimal.")
    for index, gate in enumerate(tables):
        if index in WORDS:
            word = WORDS[index]
            check_word(gate, word)
            print(f"  #{index}: {word} (length {len(word)})")
        else:
            sizes = check_intertwiner(gate)
            normal_right, normal_left, reversed_right, reversed_left = sizes
            print(
                f"  #{index}: F intertwines both generators on 15 triples per sector;"
            )
            print(
                f"      inputs vs available outputs: normal R {normal_right}, L {normal_left};"
            )
            print(
                f"      reversed R {reversed_right}, L {reversed_left}; no common word."
            )
    print("All 12 code states x 4 masks per witness: reset X, vacuum silent,")
    print(
        "  exactly one visible exit iff the occupied arm is open, total weight conserved."
    )
    print("Raw (left,right) rates: both open (0,1) normal, (1,0) reversed;")
    print("  either arm alone (1/4,1/4), neither (0,0), for both preparations.")
    print("  Conditional on transmission with one arm open: (1/2,1/2).")
    check_fixed_species_control()
    print("One fixed extreme cannot combine a perfect fringe with fair conditional")
    print("  single-arm exits here: at most one supported input per arm remains.")
    check_local_phase_control(tables[4], WORDS[4])
    print("A clean local one-arm plate cannot change a visible label, leaving at least")
    print("  half the fair ensemble unchanged. It cannot fully reverse the fringe.")
    print("For #4 a supplied X/Y relabeling on either arm gives (1/2,1/2);")
    print(
        "  both relabelings reproduce the reversed preparation; no gate synthesis claimed."
    )


if __name__ == "__main__":
    main()
