"""Finite coherent capture and revival using only the supplied native mixer.

Let T = ((1+i,1-i),(1-i,1+i))/2, so T^2 swaps two modes and T^4=I.
A tape is a ring of H+1 cells, with modes A_j,B_j at each cell. In one
tick swap A_j with B_j in parallel, then swap B_j with A_(j+1) in
parallel. The resulting permutation sends the A lane forward and B
backward. Start at A_0 and call A_1,...,A_H the record region. All of the
source's conserved squared norm is there from tick 1 through H, at a
different microscopic location every tick. It returns exactly at H+1.
No measurement, shutter, removal, or time-dependent switch occurs in a
capture tick. The return is not excluded by the initially dark source.

For any supplied finite-dimensional unitary U, let S be a source
subspace orthogonal to the record subspace D. If U^t S is inside D for
all 1<=t<=H, then those H translated subspaces are mutually orthogonal:
<U^i x,U^j y>=<x,U^(j-i)y>=0 for x,y in S and 1<=i<j<=H. Thus
dim(D) >= H*dim(S). The disjoint tapes saturate this bound. More generally,
if U^t S were permanently in D after some threshold, the span of those
tail subspaces would be mapped into itself by U and hence onto itself
by finite-dimensionality. It would also contain S, a contradiction.
Exact periodic revival here follows from a permutation; a general finite
unitary need not return exactly. A reset or continued access to fresh
blank sites is a separate resource, not part of this capture model.

A single T can split one input between two disjoint tapes. Then the
conserved squared norm is 1/2 in each tape, not one unit in each or an
assertion of a selected event. The returned amplitudes can be recombined.
A controlled swap to a third, initially blank mode suppresses that
recombination without discarding anything; reversing the whole protocol
recovers the unsplit input. The diversion is a separately scheduled
control, not a property of the autonomous detector.

The record here is a supplied occupancy region and conserved norm, not
a physical energy quantum, actual outcome, irreversible measurement, or
calibrated experimental detector. It does not preserve the input to copy
a label: the input amplitude is moved into the tape.
"""

from collections.abc import Iterable
from dataclasses import dataclass
from fractions import Fraction as F

Gaussian = tuple[int, int]
Layer = tuple[tuple[int, int], ...]
ZERO: Gaussian = (0, 0)


@dataclass(frozen=True)
class Field:
    nums: tuple[Gaussian, ...]
    den: int = 1


def check(condition: bool, message: str) -> None:
    """Keep every check active under python -O."""
    if not condition:
        raise AssertionError(message)


def basis(size: int, port: int) -> Field:
    return Field(tuple((1, 0) if i == port else ZERO for i in range(size)))


def same(a: Field, b: Field) -> bool:
    return len(a.nums) == len(b.nums) and all(
        x * b.den == u * a.den and y * b.den == v * a.den
        for (x, y), (u, v) in zip(a.nums, b.nums, strict=True)
    )


def weight(a: Field, ports: Iterable[int]) -> F:
    return F(sum(x * x + y * y for x, y in (a.nums[i] for i in ports)), a.den**2)


def turns(a: Field, pairs: Layer, count: int) -> Field:
    """Apply T to the matched pairs; one global factor of two per layer."""
    ports = tuple(i for pair in pairs for i in pair)
    check(len(set(ports)) == len(ports), "a layer requires disjoint pairs")
    for _ in range(count):
        out = [(2 * x, 2 * y) for x, y in a.nums]
        for j, k in pairs:
            (x, y), (u, v) = a.nums[j], a.nums[k]
            out[j] = (x - y + u + v, x + y - u + v)
            out[k] = (x + y + u - v, -x + y + u + v)
        a = Field(tuple(out), 2 * a.den)
    return a


@dataclass(frozen=True)
class Detector:
    hold: int
    tapes: int

    @property
    def period(self) -> int:
        return self.hold + 1

    @property
    def spare(self) -> int:
        return 2 * self.period * self.tapes

    @property
    def size(self) -> int:
        return self.spare + 1

    def a(self, tape: int, cell: int) -> int:
        return 2 * (self.period * tape + cell % self.period)

    def b(self, tape: int, cell: int) -> int:
        return self.a(tape, cell) + 1

    def record(self, tape: int) -> tuple[int, ...]:
        return tuple(self.a(tape, i) for i in range(1, self.period))

    def tick(self, field: Field, *, reverse: bool = False) -> Field:
        inside = tuple(
            (self.a(tape, i), self.b(tape, i))
            for tape in range(self.tapes)
            for i in range(self.period)
        )
        across = tuple(
            (self.b(tape, i), self.a(tape, i + 1))
            for tape in range(self.tapes)
            for i in range(self.period)
        )
        first, second = (across, inside) if reverse else (inside, across)
        return turns(turns(field, first, 2), second, 2)


def move(d: Detector, a: Field, ticks: int, *, reverse: bool = False) -> Field:
    for _ in range(ticks):
        a = d.tick(a, reverse=reverse)
    return a


def check_delay() -> int:
    windows = 0
    for hold in (1, 2, 3, 5, 8):
        d = Detector(hold, 2)
        ports = range(d.size)
        vac = Field((ZERO,) * d.size)
        check(same(d.tick(vac), vac), "autonomous vacuum stays vacuum")
        check(same(d.tick(basis(d.size, d.spare)), basis(d.size, d.spare)), "spare")
        distinct_storage = set()
        for tape in range(d.tapes):
            for cell in range(d.period):
                for here, dest in (
                    (d.a(tape, cell), d.a(tape, cell + 1)),
                    (d.b(tape, cell), d.b(tape, cell - 1)),
                ):
                    input_mode = basis(d.size, here)
                    out = d.tick(input_mode)
                    check(same(out, basis(d.size, dest)), "literal directed routing")
                    check(same(d.tick(out, reverse=True), input_mode), "tick inverse")
            source = d.a(tape, 0)
            a = basis(d.size, source)
            for t in range(1, 2 * d.period + 1):
                a = d.tick(a)
                check(weight(a, ports) == 1, "global conserved norm")
                if t % d.period:
                    cell = d.a(tape, t)
                    check(same(a, basis(d.size, cell)), "exact storage mode")
                    check(weight(a, d.record(tape)) == 1, "full capture")
                    check(weight(a, (source,)) == 0, "source dark during hold")
                    check(weight(a, d.record(1 - tape)) == 0, "no false record")
                    if t < d.period:
                        check(cell not in distinct_storage, "independent storage modes")
                        distinct_storage.add(cell)
                else:
                    check(same(a, basis(d.size, source)), "exact revival")
                    check(weight(a, d.record(tape)) == 0, "record has emptied")
            windows += 1
        check(len(distinct_storage) == hold * d.tapes, "tight storage dimension")
    return windows


def check_split_and_divert() -> None:
    d = Detector(5, 2)
    source0, source1 = d.a(0, 0), d.a(1, 0)
    contact: Layer = ((source0, source1),)
    initial = basis(d.size, source0)
    split = turns(initial, contact, 1)
    check(weight(split, (source0,)) == weight(split, (source1,)) == F(1, 2), "split")
    a = split
    for _ in range(d.hold):
        a = d.tick(a)
        check(weight(a, d.record(0)) == weight(a, d.record(1)) == F(1, 2), "two tapes")
        check(weight(a, (source0, source1)) == 0, "both sources dark")
    a = d.tick(a)
    check(same(a, split), "unmodified coherent revival")
    check(same(turns(a, contact, 3), initial), "unit return after inverse splitter")

    # Reversible shutter control: divert one amplitude to a blank auxiliary
    # mode and keep it in the norm accounting, rather than deleting it.
    latch: Layer = ((d.a(0, 1), d.spare),)
    after_capture = d.tick(split)
    diverted = turns(after_capture, latch, 2)
    a = move(d, diverted, d.hold)
    out = turns(a, contact, 3)
    check(
        tuple(weight(out, (p,)) for p in (source0, source1, d.spare))
        == (F(1, 4), F(1, 4), F(1, 2)),
        "unnormalized per-injection return with retained diverted branch",
    )
    check(weight(out, range(d.size)) == 1, "no lost third-port norm")
    a = move(d, turns(out, contact, 1), d.hold, reverse=True)
    check(same(a, diverted), "reverse delayed readout")
    a = turns(a, latch, 2)
    a = turns(d.tick(a, reverse=True), contact, 3)
    check(same(a, initial), "diversion is reversible")


def main() -> None:
    windows = check_delay()
    check_split_and_divert()
    print(
        f"{windows} source/tape checks: capture = 1 for H ticks; exact revival at H+1."
    )
    print("Two local T² swap layers per tick; forward tape and backward complement.")
    print("Exact holds need at least H storage modes per independent source mode.")
    print("Split input: 1/2 norm per tape; inverse splitter restores one whole unit.")
    print("Reversible diversion: 1/4, 1/4 at sources; 1/2 retained in a blank mode.")
    print("No autonomous reset, energetic quantization, or physical measurement claim.")


if __name__ == "__main__":
    main()
