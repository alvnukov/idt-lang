"""One-bit path lifts of the transparent six-literal opposition clock.

The frozen two-mark construction supplies six transparent quarter-turn
PERMUTATIONS. They generate the 24 proper signed-axis rotations, not a
spinor sign: four repetitions return every literal and every raw stock.
Here a separately supplied path-memory law doubles an orientation frame.
It does not follow from the literal permutation or its four-cycle clock.

EXACT CARRIER. Primitive nonzero integer quaternion 4-vectors, modulo only
POSITIVE scale, give 8 one-entry, 24 two-entry and 16 four-entry directions.
Normalized quaternion multiplication retains q versus -q. Conjugation on
the three signed axes projects these 48 directions two-to-one onto the
24 rotations. Choosing the first nonzero coordinate positive is an
arbitrary exact section, not a physically preferred sign convention.
Its sign cocycle is epsilon(g,h). Axis-permutation parity chi gives a
second cocycle delta(g,h)=chi(g)*chi(h) modulo two. We check FOUR candidates
 epsilon*s + delta*t, s,t in {0,1}; no exhaustive extension classification
is asserted. Each complete 48-element multiplication table is associative.

DISCRIMINATORS. Four axial quarter turns and the commutator of orthogonal
axis half turns yield the central sign (-1)^s. An edge-axis half turn,
whose axis permutation is odd, squares to (-1)^(s+t). Thus a four-tick
sign reversal does not distinguish t. The s=1 lift returns after EIGHT
quarter ticks (720 degrees), with sign reversal after four (360 degrees).
These are ticks, not eight complete four-tick clock cycles. Changing the
odd section lifts by i makes delta a U(1) coboundary. Hence t is a
projective phase convention if arbitrary operation phases are uncalibrated;
it remains distinguishable at a fixed +/- reference. Requiring the actual
unit-quaternion SU(2) lift, rather than its i-rephased U(2) version, is an
additional determinant/phase convention and selects (s,t)=(1,0).

MEMORY PRICE. The two ordered marks already have 24 possible flags, a free
orientation-frame carrier. One extra bit gives 48 states and an update
depending on the current frame and the next rotation. A fixed independent
bit flip per tick cannot produce the sign after four identical ticks.
Nor can a two-sheet cover of the SIX literals do so: an axial quarter turn
fixes its own axis literal, so it permutes that two-element fiber with
order at most two; its fourth power cannot exchange the sheets. This wall
holds for both s=1 extensions. Storing an entire frame is sufficient, not
minimal if a different endpoint carrier is allowed. For the quaternion
extension, cosets of an order-three subgroup give a faithful 16-state
permutation action projecting two-to-one onto the EIGHT cube transversals.
Its central sign is free. It is the smallest permutation carrier with
free central sign: -1 is the unique involution, so a stabilizer excluding
it has odd order, necessarily 1 or 3, and each orbit has at least 16 states.
This alternative changes the stored endpoint; it is not a 6-times-2 cover
or a derivation of a two-complex-component physical spinor.

READOUT WALL. The central element is invisible on all literal stocks.
A global sign on one isolated ray is also invisible. A relative sign can
change a coherently recombined amplitude, but coherence, an active path
coupling and phase-sensitive readout are extra premises. A classical wave
with a controlled pi phase gives the same elementary cancellation. This
finite group probe derives neither continuous spatial rotation, its
topological double cover, neutron dynamics, Born readout, nor spin-statistics.
It does not infer a physical spin rotation from a passive record relabeling.

PRIMARY HISTORY, NOT A RAW-DATA REPLAY. The APS public author abstract for
Werner, Colella, Overhauser and Eagen, Phys. Rev. Lett. 35, 1053-1055
(20 October 1975), DOI 10.1103/PhysRevLett.35.1053, explicitly identifies
the sign reversal with 2*pi magnetic precession in a neutron interferometer,
not mechanical rotation of the apparatus. Publisher-deposited Crossref
metadata also verifies Rauch, Zeilinger, Badurek, Wilfing, Bauspiess and Bonse,
"Verification of coherent spinor rotation of fermions", Physics Letters A
54, 425-427 (October 1975), DOI 10.1016/0375-9601(75)90798-7. Only metadata
was inspected for that second paper. No full subscription article, event
records, numerical fit, or new experimental significance was inspected.
The default probe is network-free. The page hash records the 2026-11-22
retrieval, not an immutable byte promise for a dynamic publisher page.

No existing source, proof/physical status, archive or manifest is changed.
Run: python3 -B -O -m scripts.probe_opposition_spin_lift
"""

from __future__ import annotations

import unittest
from collections import Counter
from dataclasses import dataclass
from itertools import product
from math import gcd

from scripts.probe_opposition_clock_scatter import FLAGS, advance, extend
from scripts.probe_three_opposition_origin import WORDS

Quaternion = tuple[int, int, int, int]
Permutation = tuple[int, ...]
Lift = tuple[int, int]

ONE: Quaternion = (1, 0, 0, 0)
MINUS_ONE: Quaternion = (-1, 0, 0, 0)
WERNER_URL = "https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.35.1053"
WERNER_HTML_SHA256 = "e7f574bea14f5ef865ae5ea0f8b5b019ac0bc3850feb3a0149170edeaa77771f"
RAUCH_DOI = "10.1016/0375-9601(75)90798-7"
SOURCE_RETRIEVED = "2026-11-22"


def primitive(q: Quaternion) -> Quaternion:
    """Divide by a positive gcd only: the central sign must survive."""
    divisor = gcd(*q)
    if divisor == 0:
        raise ValueError("zero has no quaternion direction")
    return (q[0] // divisor, q[1] // divisor, q[2] // divisor, q[3] // divisor)


def raw_product(q: Quaternion, r: Quaternion) -> Quaternion:
    a, b, c, d = q
    e, f, g, h = r
    return (a * e - b * f - c * g - d * h,
            a * f + b * e + c * h - d * g,
            a * g - b * h + c * e + d * f,
            a * h + b * g - c * f + d * e)


def multiply(q: Quaternion, r: Quaternion) -> Quaternion:
    return primitive(raw_product(q, r))


def negative(q: Quaternion) -> Quaternion:
    return (-q[0], -q[1], -q[2], -q[3])


def conjugate(q: Quaternion) -> Quaternion:
    return (q[0], -q[1], -q[2], -q[3])


def positive_section(q: Quaternion) -> Quaternion:
    q = primitive(q)
    return q if next(x for x in q if x) > 0 else negative(q)


def power(q: Quaternion, n: int) -> Quaternion:
    if n < 0:
        raise ValueError("this finite control expects a nonnegative power")
    answer = ONE
    for _ in range(n):
        answer = multiply(answer, q)
    return answer


def rotation(q: Quaternion) -> Permutation:
    """Conjugation on six signed axes; reject directions outside this action."""
    norm = sum(x * x for x in q)
    if not norm:
        raise ValueError("zero quaternion")
    images: list[int] = []
    for axis in range(3):
        basis = tuple(int(j == axis + 1) for j in range(4))
        e: Quaternion = (basis[0], basis[1], basis[2], basis[3])
        v = raw_product(raw_product(q, e), conjugate(q))
        if v[0] or any(x % norm for x in v):
            raise ValueError("not a signed-axis rotation")
        xyz = tuple(x // norm for x in v[1:])
        if sum(abs(x) for x in xyz) != 1:
            raise ValueError("not a signed-axis rotation")
        target = next(j for j, x in enumerate(xyz) if x)
        literal = 2 * target + int(xyz[target] < 0)
        images.extend((literal, literal ^ 1))
    return tuple(images)


def compose(g: Permutation, h: Permutation) -> Permutation:
    return tuple(g[x] for x in h)


def axis_parity(g: Permutation) -> int:
    p = tuple(g[2 * j] // 2 for j in range(3))
    return sum(p[i] > p[j] for i in range(3) for j in range(i + 1, 3)) % 2


def orientation(g: Permutation) -> int:
    return (-1) ** (axis_parity(g) + sum(g[2 * j] & 1 for j in range(3)))


QUATERNIONS: tuple[Quaternion, ...] = tuple(
    (q[0], q[1], q[2], q[3])
    for q in product((-1, 0, 1), repeat=4) if sum(x != 0 for x in q) in (1, 2, 4)
)
ROTATIONS = tuple(sorted({rotation(q) for q in QUATERNIONS}))
ROTATION_INDEX = {g: i for i, g in enumerate(ROTATIONS)}
SECTION = tuple(positive_section(next(q for q in QUATERNIONS if rotation(q) == g))
                for g in ROTATIONS)
IDENTITY = ROTATION_INDEX[tuple(range(6))]
GROUP_PRODUCT = tuple(tuple(ROTATION_INDEX[compose(g, h)] for h in ROTATIONS)
                      for g in ROTATIONS)
EPSILON = tuple(tuple(int(multiply(q, r) != SECTION[GROUP_PRODUCT[g][h]])
                      for h, r in enumerate(SECTION)) for g, q in enumerate(SECTION))
CHI = tuple(axis_parity(g) for g in ROTATIONS)


@dataclass(frozen=True)
class Extension:
    spin: int
    parity: int

    def __post_init__(self) -> None:
        if any(type(x) is not int or x not in (0, 1) for x in (self.spin, self.parity)):
            raise ValueError("two bits required")

    def cocycle(self, g: int, h: int) -> int:
        return (self.spin * EPSILON[g][h] + self.parity * CHI[g] * CHI[h]) % 2

    def multiply(self, x: Lift, y: Lift) -> Lift:
        g, b = x
        h, c = y
        return GROUP_PRODUCT[g][h], b ^ c ^ self.cocycle(g, h)

    def power(self, x: Lift, n: int) -> Lift:
        if n < 0:
            raise ValueError("nonnegative power required")
        answer = (IDENTITY, 0)
        for _ in range(n):
            answer = self.multiply(answer, x)
        return answer

    def inverse(self, x: Lift) -> Lift:
        return next(y for y in LIFTS if self.multiply(x, y) == (IDENTITY, 0))

    def commutator(self, x: Lift, y: Lift) -> Lift:
        return self.multiply(self.multiply(self.multiply(x, y), self.inverse(x)), self.inverse(y))

    def table(self) -> tuple[tuple[int, ...], ...]:
        return tuple(tuple(2 * g + b for y in LIFTS for g, b in [self.multiply(x, y)])
                     for x in LIFTS)


LIFTS = tuple((g, b) for g in range(24) for b in (0, 1))
EXTENSIONS = tuple(Extension(s, t) for s, t in product((0, 1), repeat=2))


def lifted(q: Quaternion) -> Lift:
    """The chosen section over q's rotation, not necessarily q itself."""
    return ROTATION_INDEX[rotation(q)], 0


def action_on_transversal(q: Quaternion) -> tuple[int, ...]:
    """Image of the (+,+,+) cube vertex, in the frozen literal convention."""
    images = rotation(q)[::2]
    return tuple(next(x for x in images if x // 2 == j) for j in range(3))


ORDER_THREE = (-1, 1, 1, 1)
SUBGROUP = tuple(power(ORDER_THREE, k) for k in range(3))
COSETS = tuple(sorted({tuple(sorted(multiply(q, h) for h in SUBGROUP)) for q in QUATERNIONS}))
COSET_INDEX = {q: i for i, coset in enumerate(COSETS) for q in coset}


def coset_action(q: Quaternion) -> Permutation:
    return tuple(COSET_INDEX[multiply(q, coset[0])] for coset in COSETS)


class OppositionSpinLiftControls(unittest.TestCase):
    def test_exact_48_positive_scale_directions_and_two_to_one_projection(self) -> None:
        self.assertEqual(len(set(QUATERNIONS)), 48)
        self.assertEqual(Counter(sum(x != 0 for x in q) for q in QUATERNIONS), {1: 8, 2: 24, 4: 16})
        self.assertEqual(set(Counter(rotation(q) for q in QUATERNIONS).values()), {2})
        self.assertEqual(len(ROTATIONS), 24)
        self.assertEqual({orientation(g) for g in ROTATIONS}, {1})
        for q, r in product(QUATERNIONS, repeat=2):
            self.assertIn(multiply(q, r), QUATERNIONS)
            self.assertEqual(rotation(multiply(q, r)), compose(rotation(q), rotation(r)))
        self.assertNotEqual(primitive((2, 0, 0, 0)), primitive((-2, 0, 0, 0)))
        self.assertEqual({q for q in QUATERNIONS if rotation(q) == tuple(range(6))}, {ONE, MINUS_ONE})

    def test_frozen_transparent_routes_generate_exactly_the_rotation_group(self) -> None:
        routes = {extend(u, v, False) for u, v in FLAGS}
        self.assertEqual(len(routes), 6)
        self.assertTrue(routes <= set(ROTATIONS))
        found = {tuple(range(6))}
        todo = list(found)
        while todo:
            g = todo.pop()
            for h in routes:
                gh = compose(g, h)
                if gh not in found:
                    found.add(gh)
                    todo.append(gh)
        self.assertEqual(found, set(ROTATIONS))
        # Every flag is a different full proper orientation frame.
        self.assertEqual({(g[0], g[2]) for g in ROTATIONS}, set(FLAGS))

    def test_all_four_complete_extension_tables_are_groups(self) -> None:
        for extension in EXTENSIONS:
            table = extension.table()
            unit = 2 * IDENTITY
            self.assertEqual(table[unit], tuple(range(48)))
            for i in range(48):
                self.assertEqual(table[i][unit], i)
                self.assertEqual(set(table[i]), set(range(48)))
                for j in range(48):
                    self.assertEqual({table[i][table[j][k]] == table[table[i][j]][k] for k in range(48)}, {True})
            for g, h in product(range(24), repeat=2):
                self.assertEqual(CHI[GROUP_PRODUCT[g][h]], CHI[g] ^ CHI[h])
        # The untwisted spin extension really is the quaternion multiplication.
        extension = Extension(1, 0)
        for g, h in product(range(24), repeat=2):
            k, b = extension.multiply((g, 0), (h, 0))
            self.assertEqual(multiply(SECTION[g], SECTION[h]), negative(SECTION[k]) if b else SECTION[k])

    def test_three_loop_discriminators_and_four_vs_eight_ticks(self) -> None:
        quarter = lifted((1, 1, 0, 0))
        half_x, half_y = lifted((0, 1, 0, 0)), lifted((0, 0, 1, 0))
        edge_half = lifted((0, 1, 1, 0))
        self.assertEqual(CHI[edge_half[0]], 1)
        # The edge half turn is not an unavailable new rotation control:
        # Q_z Q_x^2 compiles it from three transparent quarter ticks.
        self.assertEqual(multiply((1, 0, 0, 1), power((1, 1, 0, 0), 2)), (0, 1, 1, 0))
        for extension in EXTENSIONS:
            self.assertEqual(extension.power(quarter, 4), (IDENTITY, extension.spin))
            self.assertEqual(extension.power(quarter, 8), (IDENTITY, 0))
            self.assertEqual(extension.commutator(half_x, half_y), (IDENTITY, extension.spin))
            self.assertEqual(extension.power(edge_half, 2), (IDENTITY, extension.spin ^ extension.parity))
            expected_order = 8 if extension.spin else 4
            self.assertEqual(next(n for n in range(1, 9) if extension.power(quarter, n) == (IDENTITY, 0)), expected_order)
        # Equal word length and endpoint, different lift: tick count alone fails.
        extension = Extension(1, 0)
        xy, yx = extension.multiply(half_x, half_y), extension.multiply(half_y, half_x)
        self.assertEqual(xy[0], yx[0])
        self.assertNotEqual(xy[1], yx[1])

    def test_parity_twist_is_a_u1_coboundary_but_not_a_fixed_sign_relabel(self) -> None:
        for g, h in product(range(24), repeat=2):
            k = GROUP_PRODUCT[g][h]
            # i^chi(g) i^chi(h) / i^chi(gh) = (-1)^delta(g,h).
            self.assertEqual((CHI[g] + CHI[h] - CHI[k]) % 4, 2 * CHI[g] * CHI[h])
        edge_half = lifted((0, 1, 1, 0))
        for spin in (0, 1):
            for sign_relabel in (0, 1):
                x = (edge_half[0], sign_relabel)
                self.assertNotEqual(Extension(spin, 0).power(x, 2), Extension(spin, 1).power(x, 2))
        # On a two-component unit-quaternion representation, an odd i phase
        # changes determinant by -1. SU(2) versus U(2) is an extra restriction.
        self.assertEqual({(2 * chi) % 4 for chi in CHI}, {0, 2})

    def test_one_literal_bit_and_fixed_tick_flips_cannot_realize_spin_loop(self) -> None:
        quarter = rotation((1, 1, 0, 0))
        self.assertEqual(quarter[0], 0)  # Its own axis literal is fixed.
        for fiber_action in ((0, 1), (1, 0)):
            value = 0
            for _ in range(4):
                value = fiber_action[value]
            self.assertEqual(value, 0)  # Required central flip would be 1.
        for fixed_flip in (0, 1):
            self.assertEqual((4 * fixed_flip) % 2, 0)
        self.assertEqual(len(FLAGS), 24)
        self.assertEqual(len(LIFTS), 2 * len(FLAGS))

    def test_smaller_transversal_cover_is_faithful_but_changes_endpoint_carrier(self) -> None:
        self.assertEqual(power(ORDER_THREE, 3), ONE)
        self.assertEqual(len(set(SUBGROUP)), 3)
        self.assertEqual(len(COSETS), 16)
        self.assertEqual(len(COSET_INDEX), 48)
        projection = tuple(action_on_transversal(coset[0]) for coset in COSETS)
        self.assertEqual(set(projection), set(WORDS))
        self.assertEqual(set(Counter(projection).values()), {2})
        for coset in COSETS:
            self.assertEqual(len({action_on_transversal(q) for q in coset}), 1)
        self.assertEqual(len({coset_action(q) for q in QUATERNIONS}), 48)
        for q, r in product(QUATERNIONS, repeat=2):
            self.assertEqual(coset_action(multiply(q, r)), compose(coset_action(q), coset_action(r)))
        central_action = coset_action(MINUS_ONE)
        self.assertTrue(all(i != j and projection[i] == projection[j] for i, j in enumerate(central_action)))
        # Finite facts supporting the minimum: a central-free stabilizer is
        # odd by the inverse-pairing argument and unique-involution property.
        self.assertEqual({q for q in QUATERNIONS if q != ONE and power(q, 2) == ONE}, {MINUS_ONE})
        odd_divisors = [d for d in range(1, 49, 2) if 48 % d == 0]
        self.assertEqual(odd_divisors, [1, 3])
        self.assertEqual(min(48 // d for d in odd_divisors), 16)

    def test_central_memory_is_not_a_literal_or_isolated_ray_observable(self) -> None:
        for stock in tuple(tuple(int(i == j) for i in range(6)) for j in range(6)) + (tuple(range(6)),):
            self.assertEqual(advance(stock, rotation(MINUS_ONE)), stock)
        ray = (1, 2)
        minus_ray = tuple(-x for x in ray)
        self.assertEqual(tuple(x * y for x in ray for y in ray),
                         tuple(x * y for x in minus_ray for y in minus_ray))
        # A supplied coherent reference distinguishes relative signs. These
        # are amplitude sums, not a derived detector probability rule.
        self.assertEqual((1 + 1, 1 + (-1)), (2, 0))
        self.assertEqual((1 + 1) ** 2, ((-1) + (-1)) ** 2)

    def test_invalid_directions_and_extension_bits_are_rejected(self) -> None:
        with self.assertRaises(ValueError):
            primitive((0, 0, 0, 0))
        with self.assertRaises(ValueError):
            rotation((1, 2, 0, 0))
        with self.assertRaises(ValueError):
            Extension(True, 0)


def main() -> None:
    result = unittest.TextTestRunner(verbosity=1).run(
        unittest.defaultTestLoader.loadTestsFromTestCase(OppositionSpinLiftControls)
    )
    if not result.wasSuccessful():
        raise SystemExit(1)
    print("Six frozen quarter turns generate 24 rotations; positive-scale integer quaternion directions give 48 lifts.")
    print("Four associative candidate extensions: quarter^4 and half-turn commutator detect s; edge-half-turn^2 detects s XOR t. U(1) rephasing makes t a convention without calibrated operation phases.")
    print("Spin lift: four quarter ticks reverse the central sign, eight return it. One bit over 24 frames suffices; one bit over six literals cannot. A different eight-transversal cover needs 16 states.")
    print(f"Historical primary abstract: {WERNER_URL}; 2*pi magnetic spin precession and neutron interference, not a literal relabeling or mechanical apparatus rotation. No raw-data replay.")
    print("Path memory, active coherent comparison and phase-sensitive detection remain supplied. No native spin selection, continuous rotation, QM, spin-statistics or physical-status upgrade.")


if __name__ == "__main__":
    main()
