"""Can an alternating three-wire clock realize the clean +1 phase setting?

Same 216 frozen lifts, both supplied reference stocks, all six wire layouts.
Only the *addresses* are restricted: A=T01 and B=T12 must strictly alternate,
starting with either one, with a common stopping time. No feedback, new
labels or adjustable primitive gates. Every finite length, including zero,
has a unique parity and is covered for each chosen starting edge.

This tests the alternating word itself, without free SWAP prefixes/suffixes.
It does not exclude other periodic schedules, other clocks, larger stocks,
or clocks that themselves carry and evolve additional state.

Replay: python3 -B -m scripts.probe_alternating_catalyst_clock
"""

from collections import Counter
from itertools import permutations, product
from math import gcd, lcm

from scripts import probe_catalytic_six_phase_words as native

Congruence = tuple[int, int]
Cycles = tuple[list[int], list[int], list[int]]
Layout = tuple[int, ...]


def combine(a: int, n: int, b: int, m: int) -> Congruence | None:
    """Intersect k=a mod n with k=b mod m; positive (possibly noncoprime) moduli."""
    h = gcd(n, m)
    if (b - a) % h:
        return None
    step = ((b - a) // h * pow(n // h, -1, m // h)) % (m // h)
    return (a + n * step) % lcm(n, m), lcm(n, m)


def common_time(
    cycles: Cycles, xs: list[int], ys: list[int]
) -> tuple[bool, Congruence | None]:
    ids, pos, sizes = cycles
    pairs = list(zip(xs, ys, strict=True))
    if not all(ids[x] == ids[y] for x, y in pairs):
        return False, None
    time = (0, 1)
    for x, y in pairs:
        merged = combine(*time, pos[y] - pos[x], sizes[x])
        if merged is None:
            return True, None
        time = merged
    return True, time


def place(q: int, layout: Layout) -> int:
    wire = (q // 256, q // 16 % 16, q % 16)
    return 256 * wire[layout[0]] + 16 * wire[layout[1]] + wire[layout[2]]


def controls() -> None:
    # Check the solver against brute force, including incompatible,
    # compatible noncoprime, redundant and unit-modulus pairs.
    for n, m in product(range(1, 9), repeat=2):
        length = lcm(n, m)
        for residue, other in product(range(n), range(m)):
            brute = next(
                (k for k in range(length) if k % n == residue and k % m == other), None
            )
            expected = None if brute is None else (brute, length)
            native.need(
                combine(residue, n, other, m) == expected,
                "CRT/brute-force disagreement",
            )
    # Positive controls use the actual native gates, not clean +1 predictions:
    # recognize a known common clock for twelve rows with either starting edge
    # and both stopping parities. Nonzero length prevents an identity-only pass.
    maps = native.edges((1, 1, 5))
    for first in (0, 1):
        a, b = maps[first], maps[1 - first]
        undo = native.inverse(a)
        cycles = native.cycle_data([b[a[x]] for x in range(len(a))])
        for layout in permutations(range(3)):
            xs = [place(q, layout) for q in native.rows(0, 0, 0)]
            for odd in (0, 1):
                ys = xs.copy()
                for pulse in range(14 + odd):
                    g = maps[first ^ (pulse % 2)]
                    ys = [g[y] for y in ys]
                if odd:
                    ys = [undo[y] for y in ys]
                both, when = common_time(cycles, xs, ys)
                native.need(
                    both
                    and when is not None
                    and when[1] > 1
                    and (7 - when[0]) % when[1] == 0
                    and xs != ys,
                    "known fourteen/fifteen-pulse clock rejected",
                )


def main() -> None:
    controls()
    # Layout is the permutation of (target, occupied ref, vacant ref) read
    # from left to right. Stocks specify all raw tags 0..7 for each reference.
    stocks = [
        (
            layout,
            [place(q, layout) for q in native.rows(r, s, 0)],
            [place(q, layout) for q in native.rows(r, s, 1)],
        )
        for layout in permutations(range(3))
        for r, s in product(range(8), repeat=2)
    ]
    eligible: Counter[Layout] = Counter()
    checked = hits = 0
    for f in product(native.ACTIVE, repeat=3):
        maps = native.edges((f[0], f[1], f[2]))
        for first in (0, 1):
            a, b = maps[first], maps[1 - first]
            # Even timeline: P^k with P=b∘a. Odd timeline: a∘P^k,
            # hence compare against a^-1(goal), not P^-1(goal).
            cycles = native.cycle_data([b[a[x]] for x in range(len(a))])
            undo = native.inverse(a)
            for odd in (0, 1):
                for layout, xs, goals in stocks:
                    ys = [undo[y] for y in goals] if odd else goals
                    all_in_orbits, clock = common_time(cycles, xs, ys)
                    eligible[layout] += int(all_in_orbits)
                    hits += int(clock is not None)
                    checked += 1
    expected = {
        (0, 1, 2): 64,
        (2, 1, 0): 64,
        (0, 2, 1): 96,
        (1, 2, 0): 96,
        (1, 0, 2): 78,
        (2, 0, 1): 78,
    }
    native.need(
        checked == 331776 and eligible == expected, "alternating census coverage"
    )
    native.need(hits == 0, "found a shared alternating-clock time")
    print(
        "216 lifts x 64 stocks x 6 layouts x 2 starting edges x 2 parities: 331776 classes"
    )
    print("all 12 individual cycle goals reachable: 476; one joint clock time: 0")
    print(
        "positive control: known 14/15-pulse native clocks accepted for every layout/start"
    )


if __name__ == "__main__":
    main()
