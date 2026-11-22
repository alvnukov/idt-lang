"""A finite Gaussian-adic reservoir law, not an origin of random events.

Let pi=1+i and G_N=Z[i]/(pi^N). Exact division gives a set bijection
    x -> (d, (x-d)/pi), d=(Re(x)+Im(x)) mod 2,
from G_N to {0,1} x G_(N-1), using representatives d=0,1. Uniform G_N
therefore gives N independent fair digits. Consistent uniform cylinders
define the candidate inverse-limit law; this is an encoded initial iid
reservoir, not a derivation of that law or physical event actualization.
Finite stock supplies only its stated horizon. Keeping extracted records
restores reversibility; discarding the digit makes the shift two-to-one.

The law and the update are separate premises. Gaussian translation x->x+1
and rotation x->i*x preserve the same uniform law but emit, respectively,
alternating and constant first digits. Translation by 1 alone is not a
transitive odometer on G_N: its order is 2^ceil(N/2). Both +1 and +i generate
the quotient. Invariance under both translations forces the law uniform,
but at every unbounded depth that is an infinite preparation-law condition.
An equivariant deterministic finite-readable port label with FIXED ports
must be translation invariant, hence constant by transitivity. The digit
is not such a label: +1 flips it. A reference/readout contract is still needed.

Sharp approximate finite symmetry: for N=2m, L=2^m, G_N=(Z/L)^2. If
delta_1 and delta_i are TV distances from the two translated laws, then
    TV(mu, uniform) <= (L/4)*(delta_1+delta_i).
Average every translate of mu to obtain uniform; triangle inequality bounds
each shift by its shortest cyclic word length. Each coordinate's mean
distance is L/4. A uniform half-strip attains the bound: distance 1/2,
delta_1=2/L, delta_i=0. Small local defects do not uniformly certify deep Haar.

Predictable scheduling can choose the next dyadic seed size using consumed
digits only; conditional on any consumed prefix the untouched suffix remains
uniform. The same cylinder argument applies at finite stopping times, with
overflow reported for finite stock. Peeking/reusing bits invalidates the
fresh-seed conclusion. That conclusion alone does not establish conditional
uniformity of incoming event tags after adaptive cloud selection.

All checks use finite exact counts and fractions. No physical iid claim,
independent-device preparation, Born rule, or Lean proof is supplied.
Run: python3 -B -O -m scripts.probe_adic_event_reservoir
"""

from __future__ import annotations

import sys
from collections import Counter
from fractions import Fraction as F
from itertools import product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_coset_address_transport import (
    ONE,
    Gaussian,
    I,
    add,
    div_exact,
    mul,
    reduce,
    reps,
    sub,
)

PI: Gaussian = (1, 1)
Law = dict[Gaussian, F]


def need(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def pi_power(level: int) -> Gaussian:
    need(level >= 0, "nonnegative quotient depth")
    result = ONE
    for _ in range(level):
        result = mul(result, PI)
    return result


def split(address: Gaussian, level: int) -> tuple[int, Gaussian]:
    need(level > 0, "finite reservoir exhausted")
    value = reduce(address, pi_power(level))
    digit = (value[0] + value[1]) % 2
    tail = reduce(div_exact(sub(value, (digit, 0)), PI), pi_power(level - 1))
    need(
        reduce(add((digit, 0), mul(PI, tail)), pi_power(level)) == value,
        "split inverse",
    )
    return digit, tail


def digits(address: Gaussian, level: int) -> tuple[int, ...]:
    need(level >= 0, "nonnegative digit horizon")
    result = []
    for remaining in range(level, 0, -1):
        digit, address = split(address, remaining)
        result.append(digit)
    return tuple(result)


def quotient_checks() -> tuple[tuple[int, ...], ...]:
    total = 0
    for level in range(1, 11):
        modulus = pi_power(level)
        stock = reps(modulus)
        words = Counter(digits(address, level) for address in stock)
        need(
            len(stock) == 2**level
            and words == Counter(product(range(2), repeat=level)),
            "uniform digit cylinders",
        )
        reached = {(0, 0)}
        frontier = [(0, 0)]
        while frontier:
            address = frontier.pop()
            for shift in (ONE, I):
                nxt = reduce(add(address, shift), modulus)
                if nxt not in reached:
                    reached.add(nxt)
                    frontier.append(nxt)
        need(len(reached) == len(stock), "two-generator transitivity")
        address, order = (0, 0), 0
        while True:
            address = reduce(add(address, ONE), modulus)
            order += 1
            if address == (0, 0):
                break
        need(
            order == 2 ** ((level + 1) // 2),
            "one translation is not a full quotient cycle",
        )
        total += len(stock)
    print(
        f"Gaussian quotient levels 1..10: {total} addresses; exact division, inverse, uniform digit words and translation transitivity checked."
    )
    return tuple(digits(address, 8) for address in reps(pi_power(8)))


def dynamics_and_fixed_ports() -> None:
    modulus = pi_power(6)
    translated: Counter[tuple[int, ...]] = Counter()
    rotated: Counter[tuple[int, ...]] = Counter()
    for source in reps(modulus):
        for rotation, counts in ((False, translated), (True, rotated)):
            address = source
            word = []
            for _ in range(4):
                word.append(split(address, 6)[0])
                address = reduce(
                    mul(I, address) if rotation else add(address, ONE), modulus
                )
            counts[tuple(word)] += 1
    need(
        translated == Counter({(0, 1, 0, 1): 32, (1, 0, 1, 0): 32}),
        "translation gives alternating digits",
    )
    need(
        rotated == Counter({(0, 0, 0, 0): 32, (1, 1, 1, 1): 32}),
        "rotation gives constant digits",
    )
    modulus = pi_power(3)
    stock = reps(modulus)
    index = {address: j for j, address in enumerate(stock)}
    translations = tuple(
        tuple(index[reduce(add(address, shift), modulus)] for address in stock)
        for shift in (ONE, I)
    )
    invariant = 0
    for labels in product(range(2), repeat=len(stock)):
        if all(
            labels[j] == labels[action[j]]
            for action in translations
            for j in range(len(stock))
        ):
            invariant += 1
            need(len(set(labels)) == 1, "fixed-port invariant readout must be constant")
    need(invariant == 2, "exactly two invariant binary labels")
    need(
        all(
            split(reduce(add(address, ONE), modulus), 3)[0] == 1 - split(address, 3)[0]
            for address in stock
        ),
        "digit is not fixed-port translation invariant",
    )
    print(
        "Same uniform law: quotient shift yields fresh digits; +1 alternates and i-rotation repeats the first digit."
    )
    print(
        "All 256 binary readouts on G_3: only the two constants preserve fixed ports under both translations."
    )


def tv(left: Law, right: Law) -> F:
    need(left.keys() == right.keys(), "same finite carrier")
    for law in (left, right):
        need(
            all(x >= 0 for x in law.values()) and sum(law.values(), F(0)) == 1,
            "probability law",
        )
    return sum((abs(left[key] - right[key]) for key in left), F(0)) / 2


def translated_law(law: Law, size: int, shift: Gaussian) -> Law:
    dx, dy = shift
    return {((x + dx) % size, (y + dy) % size): p for (x, y), p in law.items()}


def symmetry_bound(law: Law, size: int) -> tuple[F, F, F]:
    need(size >= 2 and size & (size - 1) == 0, "even dyadic side length")
    need(set(law) == set(product(range(size), repeat=2)), "complete quotient grid")
    uniform = dict.fromkeys(law, F(1, size**2))
    delta1 = tv(law, translated_law(law, size, ONE))
    deltai = tv(law, translated_law(law, size, I))
    distance = tv(law, uniform)
    need(distance <= F(size, 4) * (delta1 + deltai), "translation TV bound")
    return distance, delta1, deltai


def approximate_symmetry() -> None:
    for exponent in range(1, 6):
        size = 2**exponent
        half_strip = {
            (x, y): F(2, size**2) if x < size // 2 else F(0)
            for x, y in product(range(size), repeat=2)
        }
        distance, delta1, deltai = symmetry_bound(half_strip, size)
        need(
            (distance, delta1, deltai) == (F(1, 2), F(2, size), F(0)),
            "half-strip exact defects",
        )
        need(distance == F(size, 4) * (delta1 + deltai), "sharp coefficient")
    # Every denominator-four probability law on the four-point quotient.
    checked = 0
    points = tuple((x, y) for x, y in product(range(2), repeat=2))
    for counts in product(range(5), repeat=4):
        if sum(counts) == 4:
            symmetry_bound(dict(zip(points, (F(n, 4) for n in counts), strict=True)), 2)
            checked += 1
    need(checked == 35, "finite distribution inventory")
    print(
        "Sharp TV bound L/4: five half-strips have distance 1/2 while translation defect shrinks to 1/16; 35 finite laws checked."
    )


def adaptive_schedule(stock: tuple[tuple[int, ...], ...]) -> None:
    need(
        len(stock) == 256 and all(len(bits) == 8 for bits in stock),
        "declared finite reservoir horizon",
    )
    counts: Counter[tuple[int, int]] = Counter()
    peek_zero = 0
    for bits in stock:
        first = bits[0] + 2 * bits[1]
        width = 1 if first < 2 else 2  # chosen only from consumed prefix
        next_seed = sum(bits[2 + j] * 2**j for j in range(width))
        counts[first, next_seed] += 1
        # This selection inspects the candidate bit before deciding which
        # bit to expose. The remaining tail can still be fresh; this chosen
        # output is not a fresh sample at a predictable starting position.
        selected = bits[0] if bits[0] == 0 else bits[1]
        peek_zero += selected == 0
    for first in range(4):
        arity = 2 if first < 2 else 4
        need(
            tuple(counts[first, seed] for seed in range(arity))
            == (64 // arity,) * arity,
            "conditional uniform seed after predictable gate choice",
        )
    need(F(peek_zero, len(stock)) == F(3, 4), "peek-selection bias")
    try:
        split((0, 0), 0)
    except ValueError as exc:
        need(str(exc) == "finite reservoir exhausted", "exhaustion reason")
    else:
        raise ValueError("silently recycled an exhausted finite reservoir")
    print(
        "Predictable choice of 2-way/4-way seed: exact conditional uniformity; peek-selected bit instead has P(0)=3/4."
    )


def run() -> None:
    stock = quotient_checks()
    dynamics_and_fixed_ports()
    approximate_symmetry()
    adaptive_schedule(stock)
    print(
        "A supplied law and consumption protocol, not a randomness origin, physical readout, or Lean proof."
    )


if __name__ == "__main__":
    run()
