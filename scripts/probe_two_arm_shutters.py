"""Exact two-arm shutter controls at the finite order echo's common AB cut.

The label model retains the original-m analyzer reference even when both arms
are empty. The separate wave control supplies complex-linear propagation and
squared-norm intensities; neither these inputs nor physical click statistics
are derived from the finite label model.
"""

import sys
from collections.abc import Callable, Sequence
from fractions import Fraction
from pathlib import Path
from typing import NamedTuple, TypeVar

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_middle_order_echo import (
    EXTREMES,
    MIDDLE,
    UV,
    VU,
    Triple,
    U,
    conserved_gates,
    run,
)
from scripts.probe_native_path_record import CUT, Echo, Rates, echo, fair_rates, power
from scripts.probe_reference_fanout import (
    HALF,
    ONE,
    ZERO,
    ComplexRational,
    Gate,
    Pair,
    check,
    complex_gate,
    squared_norm,
)

S = TypeVar("S")
Shutters = tuple[bool, bool]
CONTEXTS: tuple[tuple[str, Shutters], ...] = (
    ("both", (True, True)),
    ("L only", (True, False)),
    ("R only", (False, True)),
    ("neither", (False, False)),
)
F0, F1 = Fraction(0), Fraction(1)
NO_CONTRAST = (F0, F0)


class Trial(NamedTuple):
    raw: Echo
    transmitted: bool

    @property
    def joint(self) -> Echo:
        return self.transmitted and self.raw[0], self.transmitted and self.raw[1]


class RatesRow(NamedTuple):
    raw: Rates
    transmitted: Fraction
    joint: Rates
    conditional: Rates | None


def separate_dumps(
    arms: tuple[S, S],
    blank: S,
    opened: Shutters,
    swap: Callable[[S, S], tuple[S, S]],
) -> tuple[tuple[S, S], tuple[S, S]]:
    cells = [*arms, blank, blank]
    for arm, is_open in enumerate(opened):
        if not is_open:
            cells[arm], cells[arm + 2] = swap(cells[arm], cells[arm + 2])
            check((cells[arm], cells[arm + 2]) == (blank, arms[arm]), "not a swap")
    return (cells[0], cells[1]), (cells[2], cells[3])


def i2(rows: Sequence[tuple[Fraction | bool, Fraction | bool]]) -> Rates:
    both, left, right, neither = rows
    return (
        Fraction(both[0]) - left[0] - right[0] + neither[0],
        Fraction(both[1]) - left[1] - right[1] + neither[1],
    )


def native_trial(gate: Gate, checkpoint: Triple, r: int, m: int) -> tuple[Trial, ...]:
    def swap(arm: int, dump: int) -> Pair:
        return power(gate, (arm, dump), 2)

    left, center, right = checkpoint
    check(
        center == r
        and (left, right).count(r) == 1
        and any(arm in MIDDLE for arm in (left, right)),
        "AB did not put a unique carrier in the arms",
    )
    rows: list[Trial] = []
    for _, opened in CONTEXTS:
        arms, dumps = separate_dumps((left, right), r, opened, swap)
        dump_flags = tuple(dump != r for dump in dumps)
        remaining = sum(arm in MIDDLE for arm in arms)
        check(remaining + sum(dump_flags) == 1, "carrier count changed at shutters")
        transmitted = not any(dump_flags) and remaining == 1
        # Only the three system cells enter the fixed suffix. Dumps remain sealed.
        rows.append(Trial(echo(gate, (arms[0], center, arms[1]), m), transmitted))
    check(rows[-1].raw == (right != r, right != r), "wrong matched vacuum echo")
    check(i2([row.raw for row in rows]) == NO_CONTRAST, "raw I2 is nonzero on a trial")
    check(
        i2([row.joint for row in rows]) == NO_CONTRAST, "joint I2 is nonzero on a trial"
    )
    return tuple(rows)


def shared_dump_trial(
    gate: Gate, checkpoint: Triple, r: int, m: int, opened: Shutters, order: Pair
) -> tuple[Echo, bool]:
    left, center, right = checkpoint
    original = left, right
    arms = list(original)
    dump = r
    closed = [arm for arm in order if not opened[arm]]
    for arm in closed:
        arms[arm], dump = power(gate, (arms[arm], dump), 2)
    if len(closed) == 2:
        first, second = closed
        check(
            arms[first] == r
            and arms[second] == original[first]
            and dump == original[second],
            "shared dump did not reroute the first blocked arm into the second",
        )
    return echo(gate, (arms[0], center, arms[1]), m), any(
        arms[arm] != r for arm in closed
    )


def fair_row(first: Trial, second: Trial) -> RatesRow:
    transmitted = Fraction(first.transmitted + second.transmitted, 2)
    joint = fair_rates(first.joint, second.joint)
    conditional = (
        (joint[0] / transmitted, joint[1] / transmitted) if transmitted else None
    )
    return RatesRow(fair_rates(first.raw, second.raw), transmitted, joint, conditional)


def check_setting(gate: Gate, r: int) -> tuple[tuple[RatesRow, ...], tuple[Rates, ...]]:
    mx, my = MIDDLE
    cx, cy = run(gate, U, (r, mx, r)), run(gate, U, (r, my, r))
    check((cx[2] == r) != (cy[2] == r), "fair m did not populate both paths")
    tx, ty = native_trial(gate, cx, r, mx), native_trial(gate, cy, r, my)
    rows = tuple(fair_row(x, y) for x, y in zip(tx, ty, strict=True))
    passed = (F1, F0)
    check(
        rows
        == (
            RatesRow(passed, F1, passed, passed),
            RatesRow((F1, HALF), HALF, (HALF, F0), passed),
            RatesRow((HALF, F0), HALF, (HALF, F0), passed),
            RatesRow((HALF, HALF), F0, (F0, F0), None),
        ),
        "wrong fair-m label rates for a gate/background setting",
    )
    shared_i2: list[Rates] = []
    for order in ((0, 1), (1, 0)):
        shared_rows: list[Rates] = []
        for _, opened in CONTEXTS:
            ex, leak_x = shared_dump_trial(gate, cx, r, mx, opened, order)
            ey, leak_y = shared_dump_trial(gate, cy, r, my, opened, order)
            check(leak_x + leak_y == (not any(opened)), "wrong closed-arm leak count")
            shared_rows.append(fair_rates(ex, ey))
        check(
            shared_rows[:3] == [row.raw for row in rows[:3]],
            "shared dump changed a context with at most one closed arm",
        )
        shared_i2.append(i2(shared_rows))
    check(shared_i2 == [(F0, HALF), (-HALF, F0)], "wrong shared-dump raw I2")
    return rows, tuple(shared_i2)


def wave_control() -> tuple[tuple[tuple[Rates, Fraction], ...], Rates]:
    def swap(
        x: ComplexRational, y: ComplexRational
    ) -> tuple[ComplexRational, ComplexRational]:
        return complex_gate(*complex_gate(x, y))

    split = complex_gate(ONE, ZERO)
    results: list[tuple[Rates, Fraction]] = []
    for _, opened in CONTEXTS:
        arms, dumps = separate_dumps(split, ZERO, opened, swap)
        dark, bright = complex_gate(*arms)
        yields = squared_norm(dark), squared_norm(bright)
        loss = sum((squared_norm(dump) for dump in dumps), F0)
        check(sum(yields) + loss == 1, "wave yield plus dumped loss changed")
        results.append((yields, loss))
    quarter = Fraction(1, 4)
    check(
        results
        == [
            ((F0, F1), F0),
            ((quarter, quarter), HALF),
            ((quarter, quarter), HALF),
            ((F0, F0), F1),
        ],
        "wrong fixed-port yields in wave control",
    )
    contrast = i2([yields for yields, _ in results])
    check(contrast == (-HALF, HALF), "wave control did not produce nonzero I2")
    return tuple(results), contrast


def pair_text(pair: Rates) -> str:
    return f"({pair[0]},{pair[1]})"


def main() -> None:
    check(U == "AB" == UV[:CUT] == VU[:CUT], "wrong common cut")
    gates = conserved_gates()
    settings = [check_setting(gate, r) for gate in gates for r in EXTREMES]
    check(len(gates) == 48 and len(settings) == 96, "wrong gate/background census")
    rows, shared = settings[0]
    results, contrast = wave_control()
    print(
        f"{len(gates)} gates, {len(settings)} gate/background settings; fair m per setting."
    )
    print(f"Fixed schedules {UV}, {VU}; separate sealed dumps at the common {U} cut.")
    print("           raw E    transmission   joint(transmitted,E)   E|transmitted")
    for (name, _), row in zip(CONTEXTS, rows, strict=True):
        conditional = (
            "undefined" if row.conditional is None else pair_text(row.conditional)
        )
        print(
            f"  {name:7} {pair_text(row.raw):10} {row.transmitted!s:14} "
            f"{pair_text(row.joint):22} {conditional}"
        )
    print("Raw and joint I2=(0,0) on every trial before averaging.")
    print(
        "Vacuum raw E depends on m at fixed gate/background; its reference is matched."
    )
    print(
        f"Shared dump leaks into a closed arm: raw I2 LR={pair_text(shared[0])}, RL={pair_text(shared[1])}."
    )

    print(
        "Supplied complex-linear control: yields per emitted unit (dark,bright); dumped loss."
    )
    for (name, _), (yields, loss) in zip(CONTEXTS, results, strict=True):
        print(f"  {name:7} {pair_text(yields):12} {loss}")
    print(f"Wave I2={pair_text(contrast)}; uses supplied squared-norm intensities.")


if __name__ == "__main__":
    main()
