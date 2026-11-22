"""Exact finite path records at the shared AB cut of two order echoes.

Supply the gate, both extreme stocks, and cell routes. The original protocol
also supplies a comparison reference matched to the original m. Separate runs
of fixed BAAAB supply the pointer-ready label and marker-analyzer reference.
Only the respective middle cells enter the contact or analyzer; the other
preparation outputs are not used. The pointer is detached during both suffixes.
In a separate endpoint protocol, two clean writes preserve the system and leave
each outgoing pointer equal to m on this preparation family. One pointer then
replaces the external matched reference, leaving a second marker readable.

If contact preserves the source c, conservation gives
w(c) + w(a) = w(c) + w(pointer). Thus the bare pointer weight stays w(a)
and cannot record the branch at fixed ready a; the middle label can still
carry a record that a separate analyzer reads. This finite model does not
derive physical path measurement, outcome actualization, or quantum mechanics.
"""

import sys
from fractions import Fraction
from itertools import product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_middle_order_echo import (
    EXTREMES,
    MIDDLE,
    UV,
    VU,
    WEIGHTS,
    H,
    L,
    Triple,
    U,
    X,
    Y,
    conserved_gates,
    run,
)
from scripts.probe_reference_fanout import Gate, Pair, check
from scripts.probe_reference_weight_tradeoff import STATES

PREPARE = "BAAAB"
CUT = 2
Marked = tuple[Triple, int]
DualMarked = tuple[Triple, Pair]
Echo = tuple[bool, bool]
Matched = tuple[Echo, Echo, Echo, Echo]
Endpoint = tuple[Echo, Echo, Echo]
Rates = tuple[Fraction, Fraction]


def power(gate: Gate, pair: Pair, turns: int) -> Pair:
    for _ in range(turns):
        pair = gate[pair]
    return pair


def contact(gate: Gate, cells: Marked, turns: int) -> Marked:
    (left, middle, right), pointer = cells
    right, pointer = power(gate, (right, pointer), turns)
    return (left, middle, right), pointer


def detect(gate: Gate, label: int, reference: int) -> bool:
    return WEIGHTS[gate[label, reference][0]] != 1


def echo(gate: Gate, system: Triple, reference: int) -> Echo:
    # The same final analyzer acts in both schedules, even at an extreme center.
    # The pointer never enters these three-cell suffixes.
    uv_center = run(gate, UV[CUT:], system)[1]
    vu_center = run(gate, VU[CUT:], system)[1]
    return detect(gate, uv_center, reference), detect(gate, vu_center, reference)


def check_inverse(gate: Gate) -> None:
    for c, a in product(STATES, repeat=2):
        for turns in (1, 2, 3):
            pair = power(gate, (c, a), turns)
            check(power(gate, pair, 4 - turns) == (c, a), "contact inverse failed")


def check_restore(
    gate: Gate, initial: Marked, marked: Marked, turns: int, m: int, baseline: Echo
) -> None:
    # Reverse the contact on the still-intact pointer, before either suffix or readout.
    restored = contact(gate, marked, 4 - turns)
    check(restored == initial, "undo did not restore the system and pointer")
    check(echo(gate, restored[0], m) == baseline, "undo did not restore E")


def dual_contact(gate: Gate, cells: DualMarked, turns: int) -> DualMarked:
    system, (near, far) = cells
    system, near = contact(gate, (system, near), turns)
    # Route the second pointer to the contact site by swapping the registers.
    near, far = power(gate, (near, far), 2)
    system, near = contact(gate, (system, near), turns)
    return system, (near, far)


def check_endpoint(
    gate: Gate, checkpoint: Triple, ready_pointers: Pair, reference: int, m: int
) -> Endpoint:
    blank = checkpoint, ready_pointers
    ready = ready_pointers[0]
    written = dual_contact(gate, blank, 1)
    check(written == (checkpoint, (m, m)), "two writes did not retain both copies of m")
    # This is an alternative run, with no readout before the inverse. T² is
    # self-inverse, and the reverse sequence of contacts is T³, swap, T³.
    erased = dual_contact(gate, written, 3)
    check(erased == blank, "undo did not restore the system and both ready pointers")

    # No original-m reference is supplied to any of these endpoint analyzers.
    no_write_echo = echo(gate, blank[0], blank[1][0])
    retained_echo = echo(gate, written[0], written[1][0])
    undo_echo = echo(gate, erased[0], erased[1][0])
    check(
        no_write_echo == undo_echo == (m == ready, m != ready), "wrong blank-pointer E"
    )
    check(retained_echo == (True, False), "endogenous pointer did not recover the echo")
    check(
        detect(gate, written[1][1], reference) == (m != ready),
        "remaining marker lost D",
    )
    return no_write_echo, retained_echo, undo_echo


def check_trial(
    gate: Gate, r: int, ready_pointers: Pair, reference: int, m: int
) -> tuple[Matched, Endpoint]:
    k = ready_pointers[0]
    right_branch = m == k
    other = Y if k == X else X
    left_branch = not right_branch
    checkpoint = run(gate, U, (r, m, r))
    expected_checkpoint = (r, r, k) if right_branch else (k, r, r)
    check(checkpoint == expected_checkpoint, "wrong branch at the common AB checkpoint")

    uncontacted = checkpoint, k
    baseline = echo(gate, uncontacted[0], m)
    check(baseline == (True, False), "no-contact control lost the echo")
    check(
        not detect(gate, uncontacted[1], reference), "no-contact pointer gave a record"
    )

    preserved = contact(gate, uncontacted, 1)
    check_restore(gate, uncontacted, preserved, 1, m, baseline)
    check(preserved[0] == checkpoint, "middle-ready contact changed a raw system cell")
    check(
        preserved[1] == (other if left_branch else k),
        "wrong middle-ready pointer label",
    )
    check(preserved[1] == m, "clean pointer did not carry the original m")
    check(WEIGHTS[preserved[1]] == 1, "bare middle-ready pointer weight varied")
    check(detect(gate, preserved[1], reference) == left_branch, "wrong middle-ready D")
    preserved_echo = echo(gate, preserved[0], m)
    check(preserved_echo == baseline, "middle-ready contact changed E")
    extreme_ready = checkpoint, r
    one = contact(gate, extreme_ready, 1)
    check_restore(gate, extreme_ready, one, 1, m, baseline)
    check(
        one == ((checkpoint[0], checkpoint[1], other if right_branch else r), r),
        "extreme-ready contact did not change only the occupied right cell",
    )
    one_echo = echo(gate, one[0], m)
    check(one_echo == (True, right_branch), "wrong extreme-ready contact E")
    swapped = contact(gate, extreme_ready, 2)
    check_restore(gate, extreme_ready, swapped, 2, m, baseline)
    check(
        swapped == ((checkpoint[0], checkpoint[1], r), checkpoint[2]),
        "swap did not transfer the source to the pointer and reset it to r",
    )
    check(detect(gate, swapped[1], reference) == left_branch, "wrong swap D")
    swap_echo = echo(gate, swapped[0], m)
    check(swap_echo == one_echo, "extreme-ready T and swap differ on this trial's E")
    matched = baseline, preserved_echo, one_echo, swap_echo
    return matched, check_endpoint(gate, checkpoint, ready_pointers, reference, m)


def fair_rates(first: Echo, second: Echo) -> Rates:
    return Fraction(first[0] + second[0], 2), Fraction(first[1] + second[1], 2)


def check_setting(gate: Gate, r: int) -> bool:
    # Fresh cells in separate slots, with the same fixed preparation word.
    pointer_stock = run(gate, PREPARE, (r, L, H))
    spare_pointer_stock = run(gate, PREPARE, (r, L, H))
    analyzer_stock = run(gate, PREPARE, (r, L, H))
    ready_pointers = pointer_stock[1], spare_pointer_stock[1]
    ready, spare = ready_pointers
    reference = analyzer_stock[1]

    # Verify the fixed protocol against the unique table criterion, not vice versa.
    candidates = [s for s in MIDDLE if gate[r, s][0] == r]
    check(
        candidates == [ready] and spare == reference == ready,
        "fixed preparation missed the unique source-preserving ready label",
    )
    for stocks in ((r, L, H), (r, H, L)):
        first = run(gate, PREPARE[:1], stocks)
        check(set(first[1:]) == set(MIDDLE), "first preparation gate did not make X,Y")
        check(
            run(gate, PREPARE[1:], first)[1] == ready,
            "preparation depended on the order of the extreme stocks",
        )

    # X and Y have equal trial weight, and exactly one of them equals ready.
    # Check rates here, before tallying across gate/background settings.
    matched_x, endpoint_x = check_trial(gate, r, ready_pointers, reference, X)
    matched_y, endpoint_y = check_trial(gate, r, ready_pointers, reference, Y)
    rates = tuple(fair_rates(a, b) for a, b in zip(matched_x, matched_y, strict=True))
    baseline = (Fraction(1), Fraction(0))
    changed = (Fraction(1), Fraction(1, 2))
    check(
        rates == (baseline, baseline, changed, changed), "wrong per-setting echo rates"
    )
    endpoint_rates = tuple(
        fair_rates(a, b) for a, b in zip(endpoint_x, endpoint_y, strict=True)
    )
    unresolved = (Fraction(1, 2), Fraction(1, 2))
    check(
        endpoint_rates == (unresolved, baseline, unresolved),
        "wrong per-setting endpoint rates",
    )
    return ready == X


def main() -> None:
    check(U == "AB" == UV[:CUT] == VU[:CUT], "wrong common cut")
    check(UV[CUT:] != VU[CUT:], "suffixes must differ")
    settings = fixed_x_hits = 0
    for gate in conserved_gates():
        check_inverse(gate)
        for r in EXTREMES:
            fixed_x_hits += check_setting(gate, r)
            settings += 1
    check((settings, fixed_x_hits) == (96, 48), "wrong fixed-X calibration census")

    print(f"{settings} gate/background settings; common AB cut in {UV} and {VU}.")
    print("Right branch iff original m=k; checkpoint is (r,r,k) vs left (k,r,r).")
    print("Separate fixed BAAAB preparations supply ready k and marker reference k.")
    print(f"Fixed X matches k in {fixed_x_hits}/{settings}; no trials discarded.")
    print("Per setting, matched original-m analyzer E (UV,VU):")
    print("  No contact: (1,0); pointer has no branch information.")
    print(
        "  One T, ready k: (1,0); system unchanged, pointer weight always 1, D=1 iff left."
    )
    print("  One T, ready r: (1,1/2); pointer exactly r, no branch information.")
    print(
        "  Two T, ready r: (1,1/2); swap records D=1 iff left, same E trial by trial."
    )
    print(
        "Undo before readout restores all cells and E; inverse checked on all 16 inputs."
    )
    print(
        "Separate endpoint protocol: use a pointer in place of the supplied original-m reference."
    )
    print(
        "  No write / two clean writes / fully undone: (1/2,1/2) / (1,0) / (1/2,1/2)."
    )
    print(
        "  Clean writes produce two m pointers; one feeds E and the other remains readable by D."
    )
    print("Finite supplied-resource model; no quantum-mechanical derivation.")


if __name__ == "__main__":
    main()
