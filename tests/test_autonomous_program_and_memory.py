"""Small independent controls; no new physical or proof-status assumptions."""

import unittest
from fractions import Fraction as F

from scripts.gaussian_dyadic_words import ONE, ZERO, Matrix, eye, g
from scripts.probe_autonomous_mixer_program import apply, execute, mul, norm2, rotate
from scripts.probe_native_markov_spectrum import (
    constants,
    delta_squared,
    depth_row,
    native_returns,
    predict,
    target,
)


def rational_cosines(horizon: int) -> tuple[F, ...]:
    """Independent Chebyshev recurrence, avoiding the probe's phase algebra."""
    values = [F(1), F(1, 8)]
    while len(values) <= horizon:
        values.append(values[-1] / 4 - values[-2])
    return tuple(values[: horizon + 1])


def independent_target(horizon: int) -> tuple[F, ...]:
    return tuple((4 + 3 * value) / 7 for value in rational_cosines(horizon))


class AutonomousProgramTests(unittest.TestCase):
    def test_pilot_counterfeit_requires_negative_and_vacuum_controls(self) -> None:
        midpoint = ((g(F(1, 2)),) * 2,) * 2
        source, negative = (ONE, ZERO), (g(-1), ZERO)
        for offset, wanted in (
            ((g(F(1, 2)), g(F(-1, 2))), (ONE, ZERO)),
            ((g(F(-1, 2)), g(F(1, 2))), (ZERO, ONE)),
        ):
            positive = tuple(
                a + b for a, b in zip(apply(midpoint, source), offset, strict=True)
            )
            opposite = tuple(
                a + b for a, b in zip(apply(midpoint, negative), offset, strict=True)
            )
            self.assertEqual(positive, wanted)
            self.assertEqual(norm2(offset), F(1, 2))
            self.assertEqual(
                norm2(tuple(a + b for a, b in zip(opposite, wanted, strict=True))), 2
            )
            self.assertEqual(
                tuple(a - b for a, b in zip(positive, opposite, strict=True)),
                (ONE, ONE),
            )

    def test_fixed_programs_on_unknown_data(self) -> None:
        a, b = g(F(1, 2), F(1, 2)), g(F(1, 2), F(-1, 2))
        half, ih, mih = g(F(1, 2)), g(0, F(1, 2)), g(0, F(-1, 2))
        ab: Matrix = ((a, b, ZERO), (half, ih, b), (mih, half, a))
        ba: Matrix = ((a, half, mih), (b, ih, half), (ZERO, b, a))
        first, second = (1, 1, 0, 0, 0, 0), (0, 1, 0, 1, 0, 0)
        self.assertEqual(execute(3, first, 6), (0, first, ab))
        self.assertEqual(execute(3, second, 6), (0, second, ba))
        self.assertNotEqual(ab, ba)
        self.assertEqual(execute(3, (0,) * 6, 6)[2], eye(3))

    def test_return_is_not_halting_or_arbitrary_padding(self) -> None:
        tape = (1, 1, 0, 0, 0, 0)
        single = execute(3, tape, 6)[2]
        self.assertEqual(execute(3, tape, 12), (0, tape, mul(single, single)))
        self.assertNotEqual(mul(single, single), single)
        short = (1, 0, 0, 0)
        self.assertEqual(execute(3, short, 4)[:2], (1, short))
        self.assertNotEqual(execute(3, (1, 1, 1, 0, 0, 0), 6)[2], single)

    def test_tape_shift_moves_one_site_not_a_full_qca_claim(self) -> None:
        for position in range(6):
            tape = tuple(int(j == position) for j in range(6))
            self.assertEqual(
                rotate(tape), tuple(int(j == (position - 1) % 6) for j in range(6))
            )


class FiniteMemoryDepthTests(unittest.TestCase):
    def test_independent_recurrence_and_native_return(self) -> None:
        expected = independent_target(20)
        self.assertEqual(expected[:3], (F(1), F(5, 8), F(5, 32)))
        self.assertEqual(target(20), expected)
        self.assertEqual(native_returns(20), expected)

    def test_design_depth_rational_certificate_not_shot_count(self) -> None:
        expected = {
            1: 50,
            2: 130,
            3: 250,
            4: 2855,
            8: 10250,
            16: 2785886,
            32: 10815761,
            64: 42607512,
        }
        for d, length in expected.items():
            with self.subTest(states=d):
                cosines = rational_cosines(d)
                delta = min(2 * (1 - value) for value in cosines[1:])
                self.assertEqual(delta_squared(d)[0], delta)
                coefficient = 4 * d * (d + 1) / delta
                self.assertEqual(constants(d), (delta / (2 * d * (d + 1)), coefficient))
                self.assertGreaterEqual(
                    F(3, 14) - (coefficient + F(8, 7)) / length, F(1, 10)
                )
                self.assertLess(
                    F(3, 14) - (coefficient + F(8, 7)) / (length - 1), F(1, 10)
                )
                row = depth_row(d)
                self.assertEqual(row["depth_values_for_error_at_least_1_10"], length)
                self.assertEqual(row["maximum_depth"], length - 1)
                self.assertEqual(row["short_exact_witness_depth_values"], d + 2)

    def test_two_state_three_depth_control_is_sharper(self) -> None:
        p0, p1, p2 = independent_target(2)
        error = F(1, 10)
        self.assertGreaterEqual(p0 - error, p1 + error)
        self.assertEqual((p1 - error) ** 2 - (p2 + error), F(31, 1600))

    def test_arbitrarily_large_clock_fits_then_absorbs(self) -> None:
        for horizon in (1, 4, 12):
            with self.subTest(horizon=horizon):
                values = independent_target(horizon)
                d = horizon + 1
                clock = tuple(
                    tuple(F(j == min(i + 1, horizon)) for j in range(d))
                    for i in range(d)
                )
                mu = (F(1),) + (F(0),) * horizon
                fitted = predict(clock, mu, values, horizon + 2)
                self.assertEqual(fitted[:d], values)
                self.assertEqual(fitted[d:], (values[-1], values[-1]))
                self.assertNotEqual(fitted[d], independent_target(horizon + 1)[-1])

    def test_two_state_depth_dependent_reset_escapes_contract(self) -> None:
        values = independent_target(12)
        state = (1 - values[0], values[0])
        observed = [state[1]]
        kernels = []
        for value in values[1:]:
            reset = ((1 - value, value),) * 2
            kernels.append(reset)
            observed.append(predict(reset, state, (F(0), F(1)), 1)[-1])
            state = (1 - value, value)
        self.assertEqual(tuple(observed), values)
        self.assertGreater(len(set(kernels)), 1)

    def test_no_state_cap_is_not_a_valid_design_parameter(self) -> None:
        for d in (0, -1):
            with self.assertRaises(ValueError):
                delta_squared(d)


if __name__ == "__main__":
    unittest.main()
