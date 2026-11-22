"""Explicit finite-memory/depth tradeoffs for a supplied centered native ray.

CONTRACT. One homogeneous d-state real row-stochastic P, one probability row
mu and one fixed response r in [0,1]^d predict q_t=mu P^t r. Depth t counts
repetitions of D=T12 T01, NOT successive experimental shots. The preparation,
transition and response do not change with requested depth. Intermediate
measurement, unmodeled clocks, selection, time-dependent controls and hidden
apparatus registers are outside this fixed complete-state contract.

The supplied centered ray (1,-1,0)/sqrt(2) has the Gaussian-dyadic representative
s=(1,-1,0)/(1+i), with the SAME projector. Its calibrated return probability
is p_t=|s* D^t s|^2=(4+3 cos(t omega))/7, cos(omega)=1/8. The exact native
Gaussian-dyadic gate walk and rational recurrence are independently checked.
The phase
alpha=exp(i omega) has infinite order: alpha+alpha^-1=1/4, whereas a rational
algebraic integer is an integer. This is an analytical arithmetic argument,
not a finite enumeration proof of irrationality or a Born/preparation derivation.

UNIFORM RESOLVENT BOUND (analytical proof, not Lean). Put
  Delta_d^2 = min_{1<=j<=d} |1-alpha^j|^2 > 0,
  c_d = Delta_d^2 / (2*d*(d+1)).
For any complex v with ||v||_infinity=1, select i with |v_i|=1 and let
epsilon=||(P-alpha I)v||_infinity. Sup-norm contraction gives
||(P^t-alpha^t I)v||_infinity <= t*epsilon. Starting X_0=i,
E|v(X_t)-alpha^t v_i|^2 <= 2*t*epsilon, since E|v(X_t)|^2<=1.
Every path X_0,...,X_d repeats some state X_a=X_b. Thus
Delta_d^2 <= 2*sum_{t=0}^d |v(X_t)-alpha^t v_i|^2 pointwise. Taking
expectations yields epsilon>=c_d, including reducible/nonreversible chains.
Consequently ||(P-alpha I)^-1||_infinity<=1/c_d. Telescoping now gives
  |L^-1 sum_{t=0}^{L-1} alpha^-t q_t| <= 2/(L*c_d)
                                           =4*d*(d+1)/(L*Delta_d^2).
There is no unknown transition-dependent mixing rate in this bound.
Models with fewer than d states may be padded by unused absorbing states.

For the target the same Fourier score is 3/14 plus two geometric tails, so
its magnitude is at least 3/14-20/(7*sqrt(7)*L). We use the conservative
RATIONAL tail bound 8/(7L). Hence the maximum prefix error is at least
  3/14 - (4*d*(d+1)/Delta_d^2 + 8/7)/L.
The printed depth table chooses L by exact rational arithmetic for a guaranteed
error >=1/10. L is the number of depth values 0,...,L-1, not shots or elapsed
time. These sufficient depths are loose, not optimized complexity estimates;
the default benchmark does NOT simulate millions of depths or collect data.

SHORT EXACT PREFIX. Let chi be P's degree-d characteristic polynomial. Since
chi(1)=0, chi(S)p_t=(3/7)Re(alpha^t chi(alpha)). Exact agreement at t=0,...,d+1
would make this zero at t=0,1. Nonreal alpha then forces chi(alpha)=0, forbidden
by the residual bound. An optional very loose quantitative version follows:
all eigenvalues lambda obey |lambda-alpha|>=c_d, so |chi(alpha)|>=c_d^d, and
the coefficient l1 norm is <=2^d because |lambda|<=1. If prefix error is eta,
the two real equations give |chi(alpha)| <= (4*sqrt(7)/3)*2^d*eta.
Therefore eta >= (3/(4*sqrt(7)))*(c_d/2)^d >= (1/4)*(c_d/2)^d.
The last bound is exact rational but becomes extremely small. It does not
replace the much sharper targeted probe_two_state_readout_barrier.py, whose
different target is the bare e0/port0 triple (1,1/2,1/8).
Indeed, its necessary inequality q2>=q1^2 when q0>=q1 already excludes error
<=1/10 on THIS centered target's first three depths: the interval gap is
31/1600. Thus even the table's d=2 length 130 is far from minimal.

ASYMPTOTIC SHARP ERROR. Every finite stochastic chain has a positive stride K
such that P^(Kn) converges (finite closed-class periods and decaying transient
parts). The target on that stride has limit points 1/7 and 1. Thus every fixed
finite homogeneous model has all-time sup error >=3/7, attained by the constant
response 4/7. This is not inferred from the weaker Fourier coefficient 3/14.
FiniteStochasticPeripheral/TwistedReadout already formalize the qualitative
peripheral/twisted obstruction; FiniteStochasticCompact supplies a non-effective
finite window, and FiniteStochasticPrefix supplies the horizon-dependent clock.
The effective residual constant here is an analytical/executable addition, not
a new Lean theorem or an upgrade of those different native-sequence results.

NEGATIVE CONTROLS. Every prefix t=0,...,M is exactly fitted by an M+1-state
absorbing clock storing the supplied table in its response. Two states with
depth-dependent reset transitions also fit it; depth-dependent preparations or
responses evade the fixed-model contract too. Thus no one finite trace rules out
ALL finite d. Three quantum ports do not bound complete classical memory. No
experimental rates, physical state-count bounds, independence of trials,
calibrated source/return detector, probability origin or full QM are derived.
"""

from __future__ import annotations

import argparse
import json
import sys
import unittest
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from math import log10
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from scripts.gaussian_dyadic_words import ZERO, Matrix, g, run

RealMatrix = tuple[tuple[F, ...], ...]


def need(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


@dataclass(frozen=True)
class PhaseNumber:
    """Exact x + y*i*sqrt(7); norms squared and real parts are rational."""

    x: F = F(0)
    y: F = F(0)

    def __add__(self, other: PhaseNumber) -> PhaseNumber:
        return PhaseNumber(self.x + other.x, self.y + other.y)

    def __sub__(self, other: PhaseNumber) -> PhaseNumber:
        return PhaseNumber(self.x - other.x, self.y - other.y)

    def __mul__(self, other: PhaseNumber) -> PhaseNumber:
        return PhaseNumber(
            self.x * other.x - 7 * self.y * other.y, self.x * other.y + self.y * other.x
        )

    def scale(self, scalar: F) -> PhaseNumber:
        return PhaseNumber(scalar * self.x, scalar * self.y)

    def star(self) -> PhaseNumber:
        return PhaseNumber(self.x, -self.y)

    def norm2(self) -> F:
        return self.x * self.x + 7 * self.y * self.y


Z, U = PhaseNumber(), PhaseNumber(F(1))
ALPHA = PhaseNumber(F(1, 8), F(3, 8))


def phase_powers(horizon: int) -> tuple[PhaseNumber, ...]:
    if horizon < 0:
        raise ValueError("nonnegative horizon required")
    values = [U]
    for _ in range(horizon):
        values.append(values[-1] * ALPHA)
    need(all(value.norm2() == 1 for value in values), "unit phase powers")
    return tuple(values)


def target(horizon: int) -> tuple[F, ...]:
    return tuple((4 + 3 * value.x) / 7 for value in phase_powers(horizon))


def native_returns(horizon: int) -> tuple[F, ...]:
    inv_pi = g(F(1, 2), F(-1, 2))
    source: Matrix = ((inv_pi,), (g(-1) * inv_pi,), (ZERO,))
    current = source
    values: list[F] = []
    for _ in range(horizon + 1):
        need(
            sum((row[0].norm2() for row in current), F(0)) == 1,
            "native norm conservation",
        )
        amplitude = sum((source[i][0].star() * current[i][0] for i in range(3)), ZERO)
        values.append(amplitude.norm2())
        current = run(current, (("T", 0, 1), ("T", 1, 2)))
    return tuple(values)


def delta_squared(d: int) -> tuple[F, int]:
    if d < 1:
        raise ValueError("positive state count required")
    phases = phase_powers(d)
    index = min(range(1, d + 1), key=lambda j: (U - phases[j]).norm2())
    value = (U - phases[index]).norm2()
    need(value > 0, "finite positive resonance separation")
    return value, index


def constants(d: int) -> tuple[F, F]:
    delta, _ = delta_squared(d)
    residual = delta / (2 * d * (d + 1))
    return residual, 2 / residual


def depth_row(d: int) -> dict[str, object]:
    delta, index = delta_squared(d)
    residual, coefficient = constants(d)
    required = (coefficient + F(8, 7)) / (F(3, 14) - F(1, 10))
    length = -(-required.numerator // required.denominator)
    need(
        F(3, 14) - (coefficient + F(8, 7)) / length >= F(1, 10), "exact depth guarantee"
    )
    short_gap = F(1, 4) * (residual / 2) ** d
    return {
        "states_at_most": d,
        "nearest_period_up_to_d": index,
        "delta_squared_exact": str(delta),
        "delta_squared_display": float(delta),
        "depth_values_for_error_at_least_1_10": length,
        "maximum_depth": length - 1,
        "short_exact_witness_depth_values": d + 2,
        "very_loose_short_gap_log10_display": log10(short_gap.numerator)
        - log10(short_gap.denominator),
    }


def validate_model(p: RealMatrix, mu: tuple[F, ...], response: tuple[F, ...]) -> None:
    d = len(p)
    need(
        d > 0 and len(mu) == len(response) == d and all(len(row) == d for row in p),
        "model dimensions",
    )
    need(
        all(value >= 0 for row in p for value in row)
        and all(sum(row, F(0)) == 1 for row in p),
        "stochastic kernel",
    )
    need(
        min(mu) >= 0
        and sum(mu, F(0)) == 1
        and all(0 <= value <= 1 for value in response),
        "probability endpoints",
    )


def predict(
    p: RealMatrix, mu: tuple[F, ...], response: tuple[F, ...], horizon: int
) -> tuple[F, ...]:
    validate_model(p, mu, response)
    values = []
    state = mu
    for _ in range(horizon + 1):
        values.append(sum((a * b for a, b in zip(state, response, strict=True)), F(0)))
        state = tuple(
            sum((state[i] * p[i][j] for i in range(len(p))), F(0))
            for j in range(len(p))
        )
    return tuple(values)


def matrix_product(a: RealMatrix, b: RealMatrix) -> RealMatrix:
    return tuple(
        tuple(
            sum((a[i][k] * b[k][j] for k in range(len(b))), F(0)) for j in range(len(b))
        )
        for i in range(len(a))
    )


def characteristic(p: RealMatrix) -> tuple[F, ...]:
    """Faddeev-LeVerrier, ascending coefficients, checked by Cayley-Hamilton."""
    d = len(p)
    identity = tuple(tuple(F(i == j) for j in range(d)) for i in range(d))
    b = identity
    descending = [F(1)]
    for k in range(1, d + 1):
        a = matrix_product(p, b)
        coefficient = -sum((a[i][i] for i in range(d)), F(0)) / k
        descending.append(coefficient)
        b = tuple(
            tuple(a[i][j] + coefficient * identity[i][j] for j in range(d))
            for i in range(d)
        )
    need(all(value == 0 for row in b for value in row), "Cayley-Hamilton exact control")
    need(
        sum(descending, F(0)) == 0 and sum(map(abs, descending), F(0)) <= 2**d,
        "stochastic characteristic controls",
    )
    return tuple(reversed(descending))


def check_characteristic(p: RealMatrix) -> None:
    d = len(p)
    coefficients = characteristic(p)
    powers = phase_powers(d + 1)
    at_alpha = sum((powers[j].scale(value) for j, value in enumerate(coefficients)), Z)
    residual, _ = constants(d)
    need(at_alpha.norm2() >= residual ** (2 * d), "determinant lower control")
    values = target(d + 1)
    for shift in (0, 1):
        left = sum(
            (value * values[j + shift] for j, value in enumerate(coefficients)), F(0)
        )
        right = F(3, 7) * (powers[shift] * at_alpha).x
        need(left == right, "target characteristic residual")
    need(at_alpha.norm2() > 0, "two consecutive residuals cannot both vanish")


def check_paths(p: RealMatrix, vector: tuple[PhaseNumber, ...]) -> None:
    d = len(p)
    need(
        len(vector) == d
        and vector[0].norm2() == 1
        and all(z.norm2() <= 1 for z in vector),
        "normalized maximum-modulus start",
    )
    powers = phase_powers(d)
    pv = tuple(sum((vector[j].scale(p[i][j]) for j in range(d)), Z) for i in range(d))
    epsilon2 = max((pv[i] - ALPHA * vector[i]).norm2() for i in range(d))
    delta, _ = delta_squared(d)
    expectations = [F(0)] * (d + 1)
    total_weight = F(0)
    for tail in product(range(d), repeat=d):
        path = (0, *tail)
        weight = F(1)
        for t in range(d):
            weight *= p[path[t]][path[t + 1]]
        errors = tuple(
            (vector[path[t]] - powers[t] * vector[0]).norm2() for t in range(d + 1)
        )
        need(delta <= 2 * sum(errors, F(0)), "pointwise repeated-state inequality")
        total_weight += weight
        expectations = [
            old + weight * error
            for old, error in zip(expectations, errors, strict=True)
        ]
    need(total_weight == 1, "complete Markov path law")
    need(
        all(
            value * value <= 4 * t * t * epsilon2
            for t, value in enumerate(expectations)
        ),
        "mean squared-error bound without floating roots",
    )
    residual, _ = constants(d)
    need(epsilon2 >= residual * residual, "uniform residual lower bound")


def score(values: tuple[F, ...]) -> PhaseNumber:
    powers = phase_powers(len(values) - 1)
    return sum(
        (
            z.star().scale(value / len(values))
            for z, value in zip(powers, values, strict=True)
        ),
        Z,
    )


def model_controls() -> int:
    models: list[RealMatrix] = []
    for d in range(1, 5):
        cycle = tuple(tuple(F(j == (i + 1) % d) for j in range(d)) for i in range(d))
        uniform = tuple((F(1, d),) * d for _ in range(d))
        lazy = tuple(
            tuple((cycle[i][j] + F(i == j)) / 2 for j in range(d)) for i in range(d)
        )
        models.extend((cycle, uniform, lazy))
    for a, b in product((F(0), F(1, 4), F(1, 2), F(3, 4), F(1)), repeat=2):
        models.append(((a, 1 - a), (b, 1 - b)))
    for p in models:
        d = len(p)
        mu = tuple(F(i + 1, d * (d + 1) // 2) for i in range(d))
        response = tuple(F(i, max(d - 1, 1)) for i in range(d))
        validate_model(p, mu, response)
        check_paths(p, phase_powers(d - 1))
        check_paths(p, (U,) + (PhaseNumber(F(1, 2)),) * (d - 1))
        check_characteristic(p)
        predictions = predict(p, mu, response, 31)
        _, coefficient = constants(d)
        for length in (1, 7, 32):
            need(
                score(predictions[:length]).norm2()
                <= min(F(1), coefficient / length) ** 2,
                "finite Fourier bound control",
            )
        native = target(d + 1)
        error = max(
            abs(a - b) for a, b in zip(predictions[: d + 2], native, strict=True)
        )
        residual, _ = constants(d)
        need(error >= F(1, 4) * (residual / 2) ** d, "loose short-prefix bound control")
    return len(models)


def escape_controls(horizon: int = 12) -> dict[str, object]:
    values = target(horizon)
    d = horizon + 1
    clock = tuple(
        tuple(F(j == min(i + 1, horizon)) for j in range(d)) for i in range(d)
    )
    mu = (F(1),) + (F(0),) * horizon
    fitted = predict(clock, mu, values, horizon + 2)
    need(
        fitted[:d] == values and fitted[-2:] == (values[-1],) * 2,
        "horizon-dependent finite clock fits and then absorbs",
    )
    state: tuple[F, ...] = (1 - values[0], values[0])
    reset_values = [state[1]]
    for value in values[1:]:
        reset = ((1 - value, value),) * 2
        state = tuple(
            sum((state[i] * reset[i][j] for i in range(2)), F(0)) for j in range(2)
        )
        reset_values.append(state[1])
    need(tuple(reset_values) == values, "two-state depth-dependent reset escape")
    need(
        tuple((1 - value, value)[1] for value in values) == values,
        "depth-dependent preparation escape",
    )
    need(
        max(abs(value - F(4, 7)) for value in target(128)) == F(3, 7),
        "constant sharp comparator on sampled prefix including t0",
    )
    return {
        "exact_prefix_last_depth": horizon,
        "absorbing_clock_states": d,
        "depth_dependent_reset_states": 2,
        "all_time_sharp_error_analytical": "3/7",
        "constant_comparator": "4/7",
    }


def audit() -> dict[str, object]:
    values = target(128)
    need(
        native_returns(128) == values,
        "independent native and spectral return sequences",
    )
    need(
        values[:3] == (F(1), F(5, 8), F(5, 32)),
        "centered target differs from existing bare-port target",
    )
    tolerance = F(1, 10)
    two_state_gap = (values[1] - tolerance) ** 2 - (values[2] + tolerance)
    need(
        values[0] - tolerance >= values[1] + tolerance and two_state_gap == F(31, 1600),
        "existing two-state inequality is much sharper than the coarse depth table",
    )
    for length in (1, 7, 32, 129):
        lower = max(F(0), F(3, 14) - F(8, 7 * length))
        need(
            score(values[:length]).norm2() >= lower * lower, "native Fourier tail bound"
        )
    return {
        "ok": True,
        "target_first_three": [str(value) for value in values[:3]],
        "native_depths_crosschecked": 129,
        "exact_small_markov_controls": model_controls(),
        "two_state_three_depth_interval_gap_at_error_1_10": str(two_state_gap),
        "dimension_depth_table": [depth_row(d) for d in (1, 2, 3, 4, 8, 16, 32, 64)],
        "escapes_and_comparator": escape_controls(),
        "boundary": "conditional homogeneous finite-state bounds; no experiment, no Lean proof, no universal finite-data exclusion",
    }


class MarkovSpectrumTests(unittest.TestCase):
    def test_native_return_formula(self) -> None:
        self.assertEqual(native_returns(40), target(40))

    def test_residual_and_model_controls(self) -> None:
        self.assertEqual(model_controls(), 37)

    def test_depth_table(self) -> None:
        self.assertEqual(
            [
                depth_row(d)["depth_values_for_error_at_least_1_10"]
                for d in (1, 2, 3, 4, 8, 16, 32, 64)
            ],
            [50, 130, 250, 2855, 10250, 2785886, 10815761, 42607512],
        )

    def test_escape_models(self) -> None:
        self.assertEqual(escape_controls()["absorbing_clock_states"], 13)

    def test_invalid_state_count(self) -> None:
        with self.assertRaises(ValueError):
            delta_squared(0)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    result = audit()
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(
            "PASS: centered native return formula and 37 exact finite Markov controls."
        )
        print("State cap d | sufficient depth values L for max error >= 1/10")
        for d in (1, 2, 3, 4, 8, 16, 32, 64):
            row = depth_row(d)
            print(f"{d:11d} | {row['depth_values_for_error_at_least_1_10']}")
        print(
            "L counts depths 0..L-1, not experimental shots; bounds are conservative."
        )
        print(result["boundary"])


if __name__ == "__main__":
    main()
