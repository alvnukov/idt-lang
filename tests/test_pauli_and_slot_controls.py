"""Small exact oracles for the four conditional Pauli and slot controls."""

import unittest
from collections import Counter
from fractions import Fraction as F
from itertools import combinations

from scripts import probe_collective_pauli_frame as collision
from scripts import probe_exchange_sign_relator as exchange
from scripts import probe_exterior_slot_minimality as exterior
from scripts import probe_five_slot_quartic_selector as quartic
from scripts.gaussian_dyadic_words import ONE, ZERO, I, eye, g


class CollisionOracles(unittest.TestCase):
    def test_two_mode_frame_and_bare_false_exclusion(self) -> None:
        frame, settings = collision.fast_frame(2)
        expected_twice = (
            (3, 0, 0, -1),
            (0, 1, 1, 0),
            (0, 1, 1, 0),
            (-1, 0, 0, 3),
        )
        basis = ((0, 0), (0, 1), (1, 0), (1, 1))
        self.assertEqual(len(settings), 2)
        self.assertEqual(
            tuple(
                tuple(frame.get(left + right, collision.ZERO) for right in basis)
                for left in basis
            ),
            tuple(tuple((F(x, 2), F(0)) for x in row) for row in expected_twice),
        )
        for sign, expected in ((1, (0, 1)), (-1, (0, 0))):
            state: collision.State = {(0, 1): collision.ONE, (1, 0): (F(sign), F(0))}
            self.assertEqual(
                tuple(
                    collision.mean_collisions(collision.collective(u, state))
                    for u in settings
                ),
                expected,
            )

    def test_internal_label_hides_totally_symmetric_state(self) -> None:
        hidden: collision.State = {
            (0, 3): collision.ONE,
            (1, 2): (F(-1), F(0)),
            (2, 1): (F(-1), F(0)),
            (3, 0): collision.ONE,
        }
        self.assertEqual(hidden, {(b, a): value for (a, b), value in hidden.items()})
        orbital = collision.native_word(2, ((0, 1),))
        orbital_only = tuple(
            tuple(
                orbital[a // 2][b // 2] if a % 2 == b % 2 else collision.ZERO
                for b in range(4)
            )
            for a in range(4)
        )
        self.assertEqual(
            collision.mean_collisions(
                collision.collective(orbital_only, hidden), orbital=True
            ),
            0,
        )
        complete = collision.native_word(4, ((0, 3),))
        self.assertEqual(
            collision.mean_collisions(collision.collective(complete, hidden)), F(1, 2)
        )


class ExchangeOracles(unittest.TestCase):
    def test_counting_phase_distinguishes_fixed_number_lifts(self) -> None:
        pair = (0, 1)
        states = exchange.masks(4, 2)
        full, empty = states.index(3), states.index(12)
        left = exchange.phase_count(4, 2, 0, g(0, -1))
        right = exchange.phase_count(4, 2, 1, I)
        z = exchange.phase_count(4, 2, 1, g(-1))
        self.assertEqual((z[full][full], z[empty][empty]), (g(-1), ONE))
        for phase in (ONE, g(-1), I, g(0, -1)):
            with self.subTest(phase=phase):
                t = exchange.local_hardcore(exchange.T, 4, 2, pair, full=phase)
                x = exchange.mul(t, t)
                c = exchange.mul(left, exchange.mul(t, right))
                actual = exchange.mul(c, exchange.mul(x, exchange.adjoint(c)))
                other_rows = tuple(j for j in range(len(states)) if j != full)
                self.assertEqual(
                    tuple(actual[j] for j in other_rows),
                    tuple(z[j] for j in other_rows),
                )
                if phase in (I, g(0, -1)):
                    self.assertEqual(actual, z)
                    projective = exchange.scaled(I, x)
                    self.assertEqual(
                        projective[full][full], g(-1) * projective[empty][empty]
                    )
                else:
                    self.assertNotEqual(actual, z)
                    self.assertEqual(actual[full], eye(len(states))[full])

    def test_local_swap_does_not_fix_nonadjacent_path(self) -> None:
        a, b, direct = (
            exchange.local_hardcore(exchange.X, 4, 2, pair, full=g(-1))
            for pair in ((0, 1), (1, 2), (0, 2))
        )
        composed = exchange.mul(a, exchange.mul(b, a))
        n = len(composed)
        loop = exchange.mul(direct, composed)
        occupied_pairs = exchange.masks(4, 2)
        self.assertEqual(loop[occupied_pairs.index(3)][occupied_pairs.index(3)], g(-1))
        self.assertEqual(loop[occupied_pairs.index(9)][occupied_pairs.index(9)], ONE)
        self.assertNotEqual(loop, eye(n))
        comparator = exchange.exterior_lift(
            exchange.one_particle_embed(exchange.X, 4, (0, 2)), 2
        )
        self.assertEqual(exchange.mul(comparator, composed), eye(n))

    def test_relator_without_hard_core_allows_positive_swap(self) -> None:
        c, x, z = (
            exchange.tensor_square(u)
            for u in (exchange.native_identity(), exchange.X, exchange.Z)
        )
        self.assertEqual(exchange.mul(c, exchange.mul(x, exchange.adjoint(c))), z)
        one_in_each = (ZERO, ONE, ONE, ZERO)
        self.assertEqual(exchange.apply(x, one_in_each), one_in_each)
        self.assertEqual(exchange.apply(c, one_in_each), (g(0, -1), ZERO, ZERO, I))


class ExteriorOracles(unittest.TestCase):
    def test_five_slot_witness_and_four_slot_self_conjugate_control(self) -> None:
        for slots, block_sizes, expected_moments in (
            ((-1, -1, 1, 1), (2, 2), (0, 0, 0)),
            ((-3, -3, 2, 2, 2), (2, 3), (0, 0, -4320)),
        ):
            with self.subTest(slots=slots):
                charges = Counter(
                    sum(selection)
                    for size in range(0, len(slots) + 1, 2)
                    for selection in combinations(slots, size)
                )
                model = exterior.ExteriorModel(*block_sizes)
                self.assertEqual(model.charges(), charges)
                self.assertEqual(
                    tuple(model.trace(d) for d in (1, 3, 5)), expected_moments
                )
                self.assertEqual(
                    charges
                    == Counter({-charge: count for charge, count in charges.items()}),
                    len(slots) == 4,
                )
                self.assertEqual(exterior.cubic_cartan_tensor(len(slots)), ())
        self.assertNotEqual(exterior.cubic_cartan_tensor(3), ())

    def test_vacuum_deletion_and_non_exterior_control(self) -> None:
        full = exterior.ExteriorModel(2, 3).charges()
        reduced = full - Counter({0: 1})
        self.assertEqual((full.total(), reduced.total()), (16, 15))
        self.assertEqual(
            tuple(
                sum(mult * q**5 for q, mult in charges.items())
                for charges in (full, reduced)
            ),
            (-4320, -4320),
        )
        alternative = exterior.alternative_thirteen_control()
        self.assertEqual(alternative["block_sizes"], [2, 2])
        self.assertEqual(alternative["dimension"], 4 + 2 + 2 + 5)
        self.assertIs(alternative["faithful_on_block_group"], True)
        self.assertEqual(alternative["su2_doublet_counts"], [4, 2])
        charges = (-18, -10, -2, 14, 16)
        self.assertEqual(alternative["singlet_charges"], list(charges))
        self.assertEqual(
            tuple(sum(q**d for q in charges) for d in (1, 3, 5)), (0, 0, -403200)
        )
        self.assertEqual(alternative["singlet_fifth_trace"], -403200)


class QuarticOracles(unittest.TestCase):
    def test_exact_extrema_and_objective_sign(self) -> None:
        critical = sorted(
            (row.fourth_ratio, row.multiplicities) for row in quartic.critical_spectra()
        )
        self.assertEqual(
            critical,
            [
                (F(7, 30), (3, 2)),
                (F(1, 4), (2, 2, 1)),
                (F(1, 2), (3, 1, 1)),
                (F(13, 20), (4, 1)),
            ],
        )
        self.assertEqual(
            quartic.radial_regime(F(1), F(1), F(1)), "nonzero minimum: 3+2"
        )
        self.assertEqual(
            quartic.radial_regime(F(1), F(1), F(-1)), "nonzero minimum: 4+1"
        )
        self.assertEqual(quartic.quartic_shape(F(0)), "entire traceless unit sphere")

    def test_cubic_tilt_and_other_slot_counts(self) -> None:
        block = quartic.Spectrum((-2, -2, -2, 3, 3))
        alternative = quartic.Spectrum((-1, -1, -1, -1, 4))
        # Bound the favorable signed cubic contribution on each unit sphere ray.
        self.assertLess(block.cubic_square, F(1, 5) ** 2)
        self.assertGreater(alternative.cubic_square, F(2, 3) ** 2)
        gap = (block.fourth_ratio - F(1, 5)) - (alternative.fourth_ratio - F(2, 3))
        self.assertGreater(gap, 0)
        self.assertEqual(quartic.cubic_tilt_control()["gap_strictly_above"], str(gap))
        self.assertEqual(
            tuple(quartic.cut_maximizers(n) for n in (4, 5, 6)), ((2,), (2, 3), (3,))
        )
