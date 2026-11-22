"""Exhaustive search: does a transparent packet-level echo already force a mixer?

Packets are unordered pairs of DISTINCT marks on four addressed legs; there
are six packet species. A deterministic memoryless table maps each species
to one such packet. Two real rails per named observed port, fixed address
meaning across both ticks, and the exchange of the ports are supplied. No
signed lattice, Hilbert norm, linearity, hidden-pairing independence, Born
law or prescribed complementary rewrite enters the search. This is a finite
classification in a particularly restrictive microscopic model.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from itertools import permutations, product

if not __package__:
    import sys
    from pathlib import Path

    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from theory_experiments.unsigned_pair_packet import (
    COMP,
    Table,
    after,
    check_table,
    leg_table,
)


@dataclass(frozen=True)
class Search:
    counts: dict[str, int]
    roots: tuple[Table, ...]
    coarse_nonraw: Table


def search() -> Search:
    count: Counter[str] = Counter()
    survivors = []
    roots = []
    mismatch = None
    preserving = set()
    for f in product(range(6), repeat=6):
        row = check_table(f)
        count["all"] += 1
        count.update(k for k, v in row.items() if v)
        if row["histogram_sufficient"] and row["bijective"]:
            preserving.add(f)
            count["bijective_histogram"] += 1
        if row["raw_echo"]:
            roots.append(f)
        if row["transparent_root"]:
            survivors.append(f)
        if row["coarse_transparent"] and not row["raw_echo"] and mismatch is None:
            mismatch = f
    leg = {leg_table(p) for p in permutations(range(4))}
    octahedral = leg | {after(COMP, p) for p in leg}
    rotation = leg_table((3, 0, 1, 2))
    both = {rotation, after(rotation, after(rotation, rotation))}
    need(
        preserving == octahedral and len(octahedral) == count["square_stock"] == 48,
        "reversible histogram classification",
    )
    need(
        set(roots) == both | {after(COMP, r) for r in both} and len(roots) == 4,
        "packet square roots",
    )
    need(
        set(survivors) == {after(COMP, r) for r in both} and len(survivors) == 2,
        "two transparent roots",
    )
    if mismatch is None:
        raise ArithmeticError("coarse comparison lacked its countercontrol")
    return Search(dict(count), tuple(survivors), mismatch)


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


def main() -> None:
    s = search()
    print("All unordered two-mark collision tables:", s.counts)
    print(
        "From the complete two-tick raw echo alone only four tables remain. Fixing the two equal-input packet species leaves precisely complement followed by either orientation of one four-cycle. Neither a norm nor histogram closure was imposed."
    )
    print("Roots as six output species in the fixed lexicographic edge order:", s.roots)
    print(
        "Coarse two-port counts do not force the packet equation; explicit surviving nonroot:",
        s.coarse_nonraw,
    )
    print(
        "Finite, deterministic, memoryless distinct-edge packets with a supplied rail exchange; no inferred individual click, physical clock, Born rule or experimental status."
    )


if __name__ == "__main__":
    main()
