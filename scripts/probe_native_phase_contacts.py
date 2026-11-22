"""Can literal point contacts read the six-phase row away from the calibration orbit?

Use the frozen 216-site four-port quotient of probe_joint_relay_phase. There
are 108 sites of each role, NOT 216 per role. On role zero the pulse A=(0,1)
raises the relative cell symbol phi by one. There are eighteen A-orbits.
The spectator word (1,3) leaves BOTH cells used by phi alone modulo the
common representative shift, but translates the signal to a different orbit.
The same four skip-or-step histories and relative analyzer give the same
row on every copy. A three-contact point marker gives that row at the origin
and zero on all seventeen other copies. No coordinate is read by the marker.

Contact contract: one unknown role-zero full site, one independent ready
point marker, and fixed reversible address schedules. The reader gets no
copy, setting or source-ticket side information. The only observation
at a nominated time is coincidence of the entire sites. At that time the
signal update is injective and the marker has a definite position, so at
most one initial site can hit. After k comparisons at least 108-k sites
share the all-miss transcript. There are 54 bright and 54 dark inputs:
even an arbitrary final decoding needs k>=54 for exact classification.
The same necessity follows if only the rows on all copies are demanded:
probability one at pulse zero forces all three prepared points per copy
bright, and probability zero at pulse three forces the opposite three dark.
Conditioning on input-independent randomness cannot evade these exact
endpoints on a finite domain. This is NOT a bound on general detectors.

Sharp witness: leave the signal still. One ready marker follows a fixed
open-loop port program with 54 scheduled comparisons; each coincidence
toggles one local ready output bit. No comparison controls the route, no
early exit, no per-site flags and no phase query are needed. The marker
visits every desired point once AT THE SCHEDULED TIMES; incidental contacts
while moving do not count. The 112 port visits are an upper bound, not an
optimized path length. Reverse traversal without comparisons restores the
marker if desired. The equality sensor, its gated reversible output latch,
the timing program, addressed moves, common origin, four-ticket source and
access to translated preparations are all supplied, not derived physical
interactions. Premarking the 54 bright sites lets a distributed detector
test them in parallel but supplies the whole window in its initial layout.
A carrier of cell symbols would instead change which local information can
reach the detector. Numerical results below are finite checks.

Run: python3 -B -O -m scripts.probe_native_phase_contacts
"""

from __future__ import annotations

from collections.abc import Callable
from itertools import product

from scripts.probe_joint_relay_phase import BRIGHT, ROW, A, Model, model
from scripts.probe_shuttle_local_reunions import Ports, Word, need, walk

C: Word = (1, 3)  # translates cell 1 against cell 3
D: Word = (0, 1, 2, 1)  # advances cells 0 and 2 equally against cell 1
Sweep = tuple[Word, ...]  # each word moves the marker, THEN arms one comparison
THREE: Sweep = (A[::-1], A, A)


def all_copy_sweep() -> Sweep:
    # Visit a 6 x 3 array of orbit centers in a snake. Alternate the
    # direction of the three offset samples so no rewind is needed.
    words: list[Word] = []
    for strip, col in product(range(3), range(6)):
        transit: Word
        if strip == col == 0:
            transit = A[::-1]
        elif col == 0:
            transit = D
        else:
            transit = C if strip % 2 == 0 else C[::-1]
        scan = A if col % 2 == 0 else A[::-1]
        words.extend((transit, scan, scan))
    return tuple(words)


def contact(
    ports: Ports, signal: int, schedule: Sweep, initial_bit: bool = False
) -> bool:
    """Actual observer: only address updates and a gated full-site coincidence."""
    marker, output_bit = 0, initial_bit
    for leg in schedule:
        marker = walk(ports, marker, leg)
        output_bit ^= marker == signal
    return output_bit


def measurement_row(
    m: Model, center: int, reader: Callable[[int], bool]
) -> tuple[int, ...]:
    stock = tuple(
        walk(m.ports, center, A[::-1] + A * (i + j))
        for i, j in product(range(2), repeat=2)
    )
    return tuple(sum(reader(walk(m.ports, s, A * n)) for s in stock) for n in range(6))


def scheduled_sites(ports: Ports, schedule: Sweep) -> tuple[int, ...]:
    """Audit trace only. No saved positions are made available to the reader."""
    s = 0
    points = []
    for leg in schedule:
        s = walk(ports, s, leg)
        points.append(s)
    back = tuple(p for leg in reversed(schedule) for p in reversed(leg))
    need(walk(ports, s, back) == 0, "marker did not return under the reversed route")
    return tuple(points)


def main() -> None:
    m = model(6, identify=True)
    states = set(range(len(m.reps)))
    role0 = {s for s in states if m.role(s) == 0}
    need(len(states) == 216 and len(role0) == 108, "wrong relay or role sector")
    need(all({g[s] for s in states} == states for g in m.ports), "nonbijective port")
    for s in role0:
        cs, ds = (walk(m.ports, s, w) for w in (C, D))
        need(m.phase(cs) == m.phase(ds) == m.phase(s), "spectator changed phase")
        # The representative can move by a common +3. Check the actual
        # four slot displacements modulo JUST this known diagonal shift.
        for t, offsets in ((cs, (0, 1, 0, -1)), (ds, (1, -2, 1, 0))):
            residuals = {
                (m.symbol(t, p) - m.symbol(s, p) - delta) % 6
                for p, delta in enumerate(offsets)
            }
            need(residuals in ({0}, {3}), "spectator word changed the wrong slots")

    centers = tuple(
        walk(m.ports, 0, C * i + D * j) for j, i in product(range(3), range(6))
    )
    orbits = tuple(tuple(walk(m.ports, r, A * n) for n in range(6)) for r in centers)
    need(
        {s for orbit in orbits for s in orbit} == role0
        and all(
            tuple(m.phase(s) for s in orbit) == tuple(range(6)) for orbit in orbits
        ),
        "fixed words did not reach the eighteen distinct six-phase copies",
    )

    def relative(s: int) -> bool:
        # Test oracle only, not a subroutine of either contact detector.
        return m.phase(s) in BRIGHT

    needed = {s for s in role0 if relative(s)}
    forced_bright = {orbit[i] for orbit in orbits for i in (5, 0, 1)}
    forced_dark = {orbit[i] for orbit in orbits for i in (2, 3, 4)}
    need(needed == forced_bright and role0 - needed == forced_dark, "endpoint support")
    need(len(needed) == len(role0 - needed) == 54, "not the balanced contact task")

    full = all_copy_sweep()
    need(
        full[:3] == THREE and (len(full), sum(map(len, full))) == (54, 112),
        "route cost",
    )
    for schedule, targets in (
        (THREE, {orbits[0][i] for i in (5, 0, 1)}),
        (full, needed),
    ):
        taps = scheduled_sites(m.ports, schedule)
        need(
            set(taps) == targets and len(taps) == len(targets), "missed or repeated tap"
        )
        for s, bit in product(role0, (False, True)):
            need(
                contact(m.ports, s, schedule, bit) == (bit ^ (s in targets)),
                "wrong latch",
            )
    for index, r in enumerate(centers):
        need(measurement_row(m, r, relative) == ROW, "relative analyzer changed row")
        need(
            measurement_row(m, r, lambda s: contact(m.ports, s, THREE))
            == (ROW if index == 0 else (0,) * 6),
            "calibration and spectator copies not distinguished",
        )
        need(
            measurement_row(m, r, lambda s: contact(m.ports, s, full)) == ROW,
            "fixed sweep did not transfer to all roots",
        )
    need(centers[1] == walk(m.ports, 0, C) != 0, "wrong held-out spectator control")
    print("216 relay sites; role zero: 108 sites = 18 disjoint six-phase pulse orbits.")
    print(f"Origin quarters: {ROW} for both relative and three-contact readers.")
    print(f"Held-out (1,3): relative {ROW}; three literal contacts {(0,) * 6}.")
    print("Three-contact reader: origin passes; all 17 other copies give six zeros.")
    print("All-copy exact point-contact minimum: 54 comparisons (54 bright, 54 dark).")
    print(
        "One fixed 112-port marker walk attains 54; optional reset retraces 112 ports."
    )
    print(
        "The sensor, latch, schedule and preparation are supplied; no native detector derived."
    )


if __name__ == "__main__":
    main()
