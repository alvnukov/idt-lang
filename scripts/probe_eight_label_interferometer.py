"""Finite two-mode interferometer with native plates and sealed shutters.

Labels specify binary occupation and one of four internal colors. A source,
independent fair vacuum phases, and the occupation readout are supplied.
Only colors 0 and 1 are inputs at the source and shutters, with color 2
serving as the plate reference; the coupler is defined on all raw colors.
The probe checks exact frequencies of this finite circuit, not a derivation of
quantum probabilities. One plate flips the accessible phase of both occupied
and vacant labels; two plates restore the routed occupation, not the raw tags.
"""

from collections.abc import Sequence
from fractions import Fraction
from itertools import product

Pair = tuple[int, int]
Triple = tuple[int, int, int]
Mask = tuple[bool, bool]
Rates = tuple[Fraction, Fraction, Fraction]

LABELS = range(8)
PHASES = range(2)
OPERATING_LABELS = (0, 1, 4, 5)
MASKS: tuple[Mask, ...] = ((True, True), (True, False), (False, True), (False, False))
REFERENCE = 2  # Vacuum of color 2, restored exactly by the native plate word.
A, B = (0, 1), (1, 2)
PLATE_WORD = (A, B, A, B, B, A)  # Chronological, not right-to-left composition.


def check(condition: bool, reason: str) -> None:
    if not condition:
        raise AssertionError(reason)


def cycle_map(cycles: Sequence[tuple[int, int, int, int]]) -> tuple[int, ...]:
    table = list(range(16))
    for cycle in cycles:
        for before, after in zip(cycle, (*cycle[1:], cycle[0]), strict=True):
            table[before] = after
    return tuple(table)


H = cycle_map(((1, 2, 4, 8), (3, 14, 12, 11), (6, 13, 9, 7)))
H_VACUUM_XOR = cycle_map(((2, 7, 8, 13), (1, 3, 4, 12), (6, 11, 9, 14)))


def number(label: int) -> int:
    return label // 4


def phase(label: int) -> int:
    return label % 2


def total_number(labels: Sequence[int]) -> int:
    return sum(map(number, labels))


def coupler(pair: Pair, homogeneous: tuple[int, ...] = H) -> Pair:
    left, right = pair
    left_n, left_c = divmod(left, 4)
    right_n, right_c = divmod(right, 4)
    if left_n == right_n:
        a, b = divmod(homogeneous[4 * left_c + right_c], 4)
        return 4 * left_n + a, 4 * right_n + b
    occupied, vacant = (left_c, right_c) if left_n else (right_c, left_c)
    new_position = (1 - left_n) ^ (phase(occupied) ^ phase(vacant))
    moved = 4 + (occupied ^ 1)
    return (vacant, moved) if new_position else (moved, vacant)


def verify_raw_coupler(homogeneous: tuple[int, ...] = H) -> None:
    pairs = list(product(LABELS, LABELS))
    images = {coupler(pair, homogeneous) for pair in pairs}
    check(images == set(pairs), "T is not a bijection of the 64 raw pairs")
    for pair in pairs:
        first = coupler(pair, homogeneous)
        check(coupler(first, homogeneous) == pair[::-1], f"T² is not swap: {pair}")
        check(
            total_number(first) == total_number(pair), f"T changed occupation: {pair}"
        )
        if pair[0] == pair[1]:
            check(first == pair, f"T did not fix diagonal {pair}")
        if number(pair[0]) != number(pair[1]):
            occupied_arm = 1 - number(pair[0])
            occupied, vacant = pair[occupied_arm], pair[1 - occupied_arm]
            destination = occupied_arm ^ phase(occupied) ^ phase(vacant)
            check(
                first[destination] == occupied ^ 1 and first[1 - destination] == vacant,
                f"wrong raw mixed-sector routing: {pair}",
            )


def plate(target: int) -> Triple:
    cells = [REFERENCE, target, REFERENCE]
    for i, j in PLATE_WORD:
        cells[i], cells[j] = coupler((cells[i], cells[j]))
        check(total_number(cells) == number(target), "plate leaked visible occupation")
    return cells[0], cells[1], cells[2]


def verify_plate() -> tuple[int, ...]:
    images = tuple(plate(target) for target in LABELS)
    outputs = tuple(image[1] for image in images)
    check(outputs == (1, 0, 2, 3, 5, 4, 7, 6), "wrong full raw plate map")
    for target, (left, output, right) in zip(LABELS, images, strict=True):
        check(
            (left, right) == (REFERENCE, REFERENCE),
            f"plate changed a reference on {target}",
        )
        if target in OPERATING_LABELS:
            check(output == target ^ 1, f"plate is not a phase flip on {target}")
    return outputs


def source_pair(port: int, particle_phase: int, vacuum_phase: int) -> Pair:
    occupied = 4 + particle_phase
    return (vacuum_phase, occupied) if port else (occupied, vacuum_phase)


def trial(
    source: int,
    particle_phase: int,
    vacuum_phase: int,
    dump_phases: Pair,
    plates: Mask,
    opened: Mask,
    *,
    recycle_phase: bool = False,
) -> Triple:
    incoming = source_pair(source, particle_phase, vacuum_phase)
    arms = list(coupler(incoming))
    path = source ^ particle_phase ^ vacuum_phase
    check(
        tuple(arms) == source_pair(path, particle_phase ^ 1, vacuum_phase),
        "wrong first-coupler route",
    )

    # Both arms have the same layout. Enabled plates run before the shutters;
    # disabled plates bypass the same two unchanged local vacuum references.
    refs: list[int] = []
    for arm, enabled in enumerate(plates):
        target = arms[arm]
        check(target in OPERATING_LABELS, "plate target is outside the operating code")
        left_ref, arms[arm], right_ref = (
            plate(target) if enabled else (REFERENCE, target, REFERENCE)
        )
        check(
            (left_ref, right_ref) == (REFERENCE, REFERENCE), "plate reference changed"
        )
        refs.extend((left_ref, right_ref))
    particle_after_plate = particle_phase ^ 1 ^ int(plates[path])
    vacuum_after_plate = vacuum_phase ^ int(plates[1 - path])
    check(
        tuple(arms) == source_pair(path, particle_after_plate, vacuum_after_plate),
        "wrong local plate action",
    )
    check(total_number((*arms, *refs)) == 1, "number changed across the plates")

    # Negative control only: prepare a correlated replacement from the arm's
    # prior hidden phase, so closing an empty arm leaves that tag unchanged.
    dumps = [
        phase(arms[i]) if recycle_phase and not opened[i] else dump_phases[i]
        for i in range(2)
    ]
    replacements = tuple(dumps)
    check(total_number((*arms, *refs, *dumps)) == 1, "dump stock was not vacuum")
    for arm, is_open in enumerate(opened):
        if not is_open:
            before = arms[arm], dumps[arm]
            arms[arm], dumps[arm] = coupler(coupler(before))
            check(
                (arms[arm], dumps[arm]) == before[::-1],
                "shutter did not swap full tags",
            )
            check(
                total_number((*arms, *refs, *dumps)) == 1,
                "shutter changed total number",
            )

    # The identical final T always runs, including on trials with no survivor.
    # Its only inputs are the two arms; the detectors read number, not tags.
    detectors = coupler((arms[0], arms[1]))
    d0, d1 = map(number, detectors)
    lost = total_number(dumps)
    check(lost == int(not opened[path]), "occupation went to the wrong shutter")
    if opened[path]:
        other = 1 - path
        analyzer_vacuum = vacuum_after_plate if opened[other] else replacements[other]
        destination = path ^ particle_after_plate ^ analyzer_vacuum
        check(
            detectors
            == source_pair(destination, particle_after_plate ^ 1, analyzer_vacuum),
            "wrong final-coupler route or tags",
        )
    check(
        d0 + d1 + lost + total_number(refs) == 1,
        "detectors, dumps and refs lost number",
    )
    check(d0 + d1 + lost == 1, "outcome is not exactly one detection or one dump loss")
    return d0, d1, lost


def frequencies(outcomes: Sequence[Triple]) -> Rates:
    return (
        Fraction(sum(row[0] for row in outcomes), len(outcomes)),
        Fraction(sum(row[1] for row in outcomes), len(outcomes)),
        Fraction(sum(row[2] for row in outcomes), len(outcomes)),
    )


def routed_rates(port: int, weight: Fraction = Fraction(1)) -> Rates:
    return (
        (Fraction(0), weight, 1 - weight) if port else (weight, Fraction(0), 1 - weight)
    )


def verify_trials() -> tuple[int, int]:
    split = (Fraction(1, 4), Fraction(1, 4), Fraction(1, 2))
    dark = (Fraction(0), Fraction(0), Fraction(1))
    standard_trials = recycled_trials = 0
    for source, plates, opened in product(PHASES, MASKS, MASKS):
        routed_port = source ^ 1 ^ int(plates[0]) ^ int(plates[1])
        expected = (
            routed_rates(routed_port) if all(opened) else split if any(opened) else dark
        )
        fair_particle: list[Triple] = []
        for particle_phase in PHASES:
            base = list(product(PHASES, PHASES, PHASES))
            outcomes = [
                trial(source, particle_phase, vacuum, (dump0, dump1), plates, opened)
                for vacuum, dump0, dump1 in base
            ]
            standard_trials += len(outcomes)
            fair_particle.extend(outcomes)
            setting = source, particle_phase, plates, opened
            check(
                frequencies(outcomes) == expected, f"wrong fixed-tag rates at {setting}"
            )
            if sum(opened) == 1:
                recycled = [
                    trial(
                        source,
                        particle_phase,
                        vacuum,
                        (dump0, dump1),
                        plates,
                        opened,
                        recycle_phase=True,
                    )
                    for vacuum, dump0, dump1 in base
                ]
                recycled_trials += len(recycled)
                rates = frequencies(recycled)
                check(
                    rates == routed_rates(routed_port, Fraction(1, 2))
                    and rates != split,
                    f"phase-recycling control did not break the singleton split at {setting}",
                )
        check(frequencies(fair_particle) == expected, "wrong fair-particle rates")
    return standard_trials, recycled_trials


def verify_minimality() -> None:
    """On each number sector, swap must be even because it is a square.

    Its transposition counts are C(d0, 2), d0*d1, C(d1, 2), where di counts
    labels of occupation i. The phase-stock requirement is di >= 2 at both
    occupations. The necessary parity conditions exclude every smaller table;
    the 64-pair raw table checked above attains (4, 4).
    """
    allowed = []
    max_total = len(LABELS)
    for d0 in range(2, max_total - 1):
        for d1 in range(2, max_total + 1 - d0):
            counts = (d0 * (d0 - 1) // 2, d0 * d1, d1 * (d1 - 1) // 2)
            if all(count % 2 == 0 for count in counts):
                allowed.append((d0, d1))
    check(allowed == [(4, 4)], "wrong necessary swap-parity bound")


def verify_alternative() -> None:
    """An exact T²=swap with the same mixed routing need not allow this plate.

    The alternative conserves XOR of the phases of vacant cells. Thus no word
    of its couplers can flip the phase of a vacant target while returning all
    other cells exactly. This concerns native implementation, not statistics.
    """

    def vacancy_xor(pair: Pair) -> int:
        left, right = pair
        return (phase(left) if not number(left) else 0) ^ (
            phase(right) if not number(right) else 0
        )

    verify_raw_coupler(H_VACUUM_XOR)
    for pair in product(LABELS, LABELS):
        check(
            vacancy_xor(coupler(pair, H_VACUUM_XOR)) == vacancy_xor(pair),
            f"alternative did not conserve vacancy XOR on {pair}",
        )


def main() -> None:
    verify_raw_coupler()
    plate_map = verify_plate()
    standard_trials, recycled_trials = verify_trials()
    verify_minimality()
    verify_alternative()
    print(
        "Raw coupler: 64 pairs; bijective, T²=swap, diagonals fixed, occupation conserved."
    )
    print(
        f"Native ABABBA plate: center map {list(plate_map)}; clean on {OPERATING_LABELS}."
    )
    print(
        f"MZI: {standard_trials} emitted trials, both source ports and each fixed or fair phase."
    )
    print("Both open: zero/two plates route opposite input; one plate routes to input.")
    print("Either single arm: (1/4, 1/4, 1/2 loss); neither: (0, 0, 1 loss).")
    print(
        f"No postselection; {recycled_trials} control trials recycle the closed arm's phase."
    )
    print("Control: one detector receives 1/2, the other 0, with 1/2 loss.")
    print(
        "Eight labels are minimal under the square, number, and two-phase-stock requirements."
    )
    print(
        "Alternative exact root conserves vacancy XOR and forbids a clean vacuum phase flip."
    )


if __name__ == "__main__":
    main()
