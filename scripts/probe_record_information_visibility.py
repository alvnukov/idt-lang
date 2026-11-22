"""Exact finite controls for record information and recombination contrast.

If Q is the sum of nonnegative quadratic record weights Q_g, polarization
and Cauchy--Schwarz in each bin give |Q_g(u+v)-Q_g(u-v)| <=
4 sqrt(Q_g(u) Q_g(v)). Sum over bins and use Q(u)=Q(v)>0 and the
parallelogram identity for the denominator to get |V| <= H, where H is
the overlap of the two normalized record laws. The bound applies to any
such binning, with or without correlations; it does not identify signed V.
H multiplies for fresh conditional product records, not for copied samples.

These examples supply the readout maps. They do not predict frequencies
without such a map, derive QM, or describe a physical reset experiment.
"""

from collections.abc import Callable, Iterable
from fractions import Fraction
from itertools import product
from math import isqrt, prod

Word = tuple[int, ...]
Law = dict[Word, Fraction]
Amplitudes = dict[Word, int]
State = tuple[int, int, int]
Paths = dict[State, int]
BASIS = tuple(product((0, 1), (0, 1), (0, 1)))


def check(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def exact_square_root(value: Fraction) -> Fraction:
    numerator, denominator = isqrt(value.numerator), isqrt(value.denominator)
    result = Fraction(numerator, denominator)
    check(result * result == value, f"non-rational square root: {value}")
    return result


def overlap(left: Law, right: Law) -> Fraction:
    check(left.keys() == right.keys(), "record laws must use the same bins")
    return sum((exact_square_root(left[g] * right[g]) for g in left), Fraction())


def record_amplitudes(count: int, alternative: int, *, copied: bool) -> Amplitudes:
    if copied:
        return {(bit,) * count: 3 if bit == alternative else 1 for bit in (0, 1)}
    return {
        word: prod(3 if bit == alternative else 1 for bit in word)
        for word in product((0, 1), repeat=count)
    }


def record_law(amplitudes: Amplitudes, expected_total: int) -> Law:
    total = sum(amplitude**2 for amplitude in amplitudes.values())
    check(total == expected_total, f"unexpected record weight total: {total}")
    return {word: Fraction(amplitude**2, total) for word, amplitude in amplitudes.items()}


def contrast(plus: Fraction, minus: Fraction) -> Fraction:
    return (plus - minus) / (plus + minus)


def gram_contrast(left: Amplitudes, right: Amplitudes) -> Fraction:
    check(left.keys() == right.keys(), "record amplitudes must use the same bins")
    plus, minus = (sum((left[g] + sign * right[g]) ** 2 for g in left) for sign in (1, -1))
    return contrast(Fraction(plus), Fraction(minus))


def first_bit_bins(law: Law) -> Law:
    return {(bit,): sum((p for g, p in law.items() if g[0] == bit), Fraction()) for bit in (0, 1)}


def record_controls() -> tuple[Law, Law]:
    print("n | fresh (V=H) | copied (V=H) | every error marginal")
    for count in range(1, 7):
        values: list[Fraction] = []
        for copied in (False, True):
            left = record_amplitudes(count, 0, copied=copied)
            right = record_amplitudes(count, 1, copied=copied)
            total = 10 if copied else 10**count
            p, q = record_law(left, total), record_law(right, total)
            label = f"n={count}, copied={copied}"
            for outcome, law in enumerate((p, q)):
                for position in range(count):
                    error = sum(prob for word, prob in law.items() if word[position] != outcome)
                    check(error == Fraction(1, 10), f"wrong marginal: {label}, bit {position}")
            v, h = gram_contrast(left, right), overlap(p, q)
            expected = Fraction(3, 5) ** (1 if copied else count)
            check(v == h == expected, f"wrong contrast/overlap: {label}")
            coarse = overlap(first_bit_bins(p), first_bit_bins(q))
            check(abs(v) <= coarse == Fraction(3, 5), f"wrong coarse overlap: {label}")
            values.append(v)
        print(f"{count} | {values[0]} | {values[1]} | 1/10")
    left = record_amplitudes(1, 0, copied=False)
    right = record_amplitudes(1, 1, copied=False)
    flipped = {word: amplitude * (-1 if word[0] else 1) for word, amplitude in right.items()}
    check(record_law(flipped, 10) == record_law(right, 10), "flipped signs changed the record law")
    v = gram_contrast(left, flipped)
    h = overlap(record_law(left, 10), record_law(flipped, 10))
    check(v == 0 and h == Fraction(3, 5), "relative sign control failed")
    print(f"Unchanged one-record laws with a relative sign flip: V={v}, H={h}")
    return (
        record_law(record_amplitudes(2, 0, copied=False), 100),
        record_law(record_amplitudes(2, 1, copied=False), 100),
    )


def total_weight(x: Fraction, y: Fraction) -> Fraction:
    # (x + y/2)^2 + 3y^2/4 is positive except at (0,0).
    return x * x + x * y + y * y


def split_weight(p: Fraction, q: Fraction, x: Fraction, y: Fraction) -> Fraction:
    radial = x * x + y * y
    if radial == 0:
        return Fraction()
    return total_weight(x, y) * (p * x * x + q * y * y) / radial


def nonquadratic_control(p: Law, q: Law) -> None:
    def detector(g: Word, x: Fraction, y: Fraction) -> Fraction:
        return split_weight(p[g], q[g], x, y)

    zero, one = Fraction(), Fraction(1)
    grid = tuple(Fraction(t, 2) for t in range(-4, 5))
    for x, y in product(grid, repeat=2):
        weights = [detector(g, x, y) for g in p]
        check(all(w >= 0 for w in weights) and sum(weights) == total_weight(x, y), "bad weights")
    for g in p:
        check(detector(g, one, zero) == p[g] and detector(g, zero, one) == q[g], "bad calibration")
    v = contrast(total_weight(one, one), total_weight(one, -one))
    h = overlap(p, q)
    check(v == Fraction(1, 2) > h == Fraction(9, 25), "nonquadratic control did not break bound")
    g = (0, 0)
    for x, y in product(grid, repeat=2):
        # Parallelogram for u=(1,0), v=(x,y), in this one bin.
        defect = (
            detector(g, one + x, y) + detector(g, one - x, -y)
            - 2 * (detector(g, one, zero) + detector(g, x, y))
        )
        if defect != 0:
            print(f"Nonquadratic bins: V={v} > H={h}; bin {g}, u=(1,0), v=({x},{y}), defect={defect}")
            return
    raise ValueError("no parallelogram defect on grid")


def quartic(value: Fraction) -> Fraction:
    return value**4


def perfect_record_control() -> None:
    zero, one = Fraction(), Fraction(1)

    def split(x: Fraction, y: Fraction) -> tuple[Fraction, Fraction]:
        return split_weight(one, zero, x, y), split_weight(zero, one, x, y)

    for x, y in product((zero, one, -one, Fraction(3, 2)), repeat=2):
        weights = split(x, y)
        check(all(w >= 0 for w in weights) and sum(weights) == total_weight(x, y), "bad perfect split")
        # The projections x and y are additive routers into separate records;
        # the other path reaches the actual neutral element before scoring.
        for local in (abs, quartic):
            routed = (local(x + zero), local(zero + y))
            flipped = (local(x - zero), local(zero - y))
            check(routed == flipped and local(zero) == 0, "routed disjoint support interfered")
    check(split(one, zero) == (one, zero), "wrong perfect label for path 0")
    check(split(zero, one) == (zero, one), "wrong perfect label for path 1")
    plus, minus = split(one, one), split(one, -one)
    check(plus == (Fraction(3, 2),) * 2 and minus == (Fraction(1, 2),) * 2, "wrong split scores")
    v = contrast(sum(plus, zero), sum(minus, zero))
    print(f"Perfect labels: routed |s| or s^4 gives V=0; numerical zeros allow V={v}, "
          f"bin 0: {plus[0]} vs {minus[0]}")


def permute(paths: Paths, gate: Callable[[int, int, int], State]) -> Paths:
    check({gate(*state) for state in BASIS} == set(BASIS), "gate is not reversible")
    return {gate(*state): amplitude for state, amplitude in paths.items()}


def mark(p: int, m: int, e: int) -> State:
    return p, m ^ p, e


def copy_marker(p: int, m: int, e: int) -> State:
    return p, m, e ^ m


def readout(paths: Paths, gates: Iterable[Callable[[int, int, int], State]]) -> Fraction:
    for gate in gates:
        paths = permute(paths, gate)
    check(all(m == 0 for _, m, _ in paths), "marker was not unmarked")
    bins = {(m, e) for _, m, e in paths}
    plus, minus = (
        sum((paths.get((0, m, e), 0) + sign * paths.get((1, m, e), 0)) ** 2 for m, e in bins)
        for sign in (1, -1)
    )
    check(plus + minus == 2 * sum(a * a for a in paths.values()), "port weights do not resolve total")
    return Fraction(plus, plus + minus)


def reversible_control() -> None:
    retain = (mark, copy_marker, mark)
    undo = retain + retain[::-1]
    # Uncompute the whole permutation, not just its effect on prepared paths.
    basis = {state: label for label, state in enumerate(BASIS, start=1)}
    restored = basis
    for gate in undo:
        restored = permute(restored, gate)
    check(restored == basis, "full undo is not the identity on the complete basis")
    cases = (
        ("unmarked", (mark, mark), Fraction(1)),
        ("copy retained", retain, Fraction(1, 2)),
        ("full undo", undo, Fraction(1)),
    )
    print("Route | coherent plus port | 50:50 classical mix plus port")
    for name, gates, expected in cases:
        coherent = readout({(0, 0, 0): 1, (1, 0, 0): 1}, gates)
        mix = sum((Fraction(1, 2) * readout({(p, 0, 0): 1}, gates) for p in (0, 1)), Fraction())
        check(coherent == expected and mix == Fraction(1, 2), f"unexpected port scores: {name}")
        print(f"{name} | {coherent} | {mix}")


if __name__ == "__main__":
    nonquadratic_control(*record_controls())
    perfect_record_control()
    reversible_control()
