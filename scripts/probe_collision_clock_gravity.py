"""A clock-only weak-field wall, conditional on an explicit metric bridge.

This is NOT a derivation of gravity from a lattice. Supply static isotropic
coordinates, universal clock/rod interpretation and geometric-optics readout:
 ds^2=-N(x)^2 c^2 dt^2+A(x)^2 dx^2, N=exp(phi), A=exp(psi).
For phi approximately -GM/(r*c^2), write psi=-gamma*phi to first order.
Identical static clocks give nu_received/nu_emitted=N_emitted/N_received.
Null coordinate speed is c*N/A and optical index is A/N. Consequently
 n=1-(1+gamma)*phi+O(phi^2).
The leading bending and Shapiro coefficient, relative to gamma=1, is
(1+gamma)/2. Merely slowing collision ticks at fixed coordinate steps
identifies N with the clock rate and A=1: gamma=0, half that coefficient.
A=N is conformal scaling, gamma=-1, with unchanged coordinate optical
geometry. A=1/N has gamma=1 at leading order. This exponential ansatz is
not asserted to be an exact Schwarzschild metric beyond first order.

ISOTROPY DOES NOT SELECT A(N). If a coordinate tick has duration T=1/N and
a coordinate step has length L=1/A in fixed reference units, every positive
isotropic L gives a spherical local cone, with speed L/T=N/A. Local proper
light speed A*(N/A)/N is one for every choice. A common cone fixes a ratio,
not an independent rod response to the clock field. This is a new finite
countermodel at the collision-to-metric bridge, not a new discovery that
PPN gamma is independent: section 127 and ppn_no_slip_validation_I already
supply gamma conditionally. probe_universal_clock_rescaling tests homogeneous
dispersion rescaling and explicitly excludes inhomogeneous propagation.
SIGN WARNING: the legacy PPN potential Psi has Psi/Phi=gamma; here the
logarithmic spatial psi=-Psi/c^2 and phi=Phi/c^2. They are not the same psi.

CONFORMAL/COORDINATE CONTROLS. Multiplying both N,A by any Omega(x)>0
preserves optical index and unparametrized null paths. Clocks and rods can
break that degeneracy only after their matter interpretation is fixed.
Omega=1 at both endpoint clocks still leaves interior conformal freedom.
A coordinate change is different: lengths and metric components must both
transform, preserving proper round-trip time. A spatially varying N dt is
not a global time-coordinate differential: its integral around a time-space
rectangle is nonzero. The exact slab sums below are prescribed one-dimensional
optical quadratures, not a smooth sourced spacetime or wave-scattering model.

FREE FALL / STOCK / ACTION. If the universal point-particle action
 -m*c^2 integral N*sqrt(1-A^2*v^2/(N^2*c^2)) dt
is supplied, mass cancels and initial rest acceleration is
 -c^2*N^2/A^2*grad(phi), whose leading term is -c^2*grad(phi) for EVERY
gamma. Thus leading universal free fall plus clock redshift does not select
gamma. The common geodesic action, source equation and physical mass coupling
are additional premises, not consequences of first-order cone isotropy.
A coordinate-cell constraint T*L^d=constant would give gamma=1/d, not
automatically one. Choosing a one-space-dimension area gives gamma=1;
choosing a three-space-dimension cell gives 1/3. Neither conservation law
has been derived, and coordinate cell volume alone is not an invariant
physical stock. Conserved proper cell count instead needs a density and
transport law; it does not by itself relate N and A. Fixed E*T and p*L
action units likewise do not couple clock and rod response without a new law.

PRIMARY COMPARATOR. Bertotti, Iess and Tortora, Nature 425, 374-376 (2003),
DOI 10.1038/nature01997. The public author abstract at the source URL below
was retrieved on 2026-11-22 and explicitly reports
 gamma=1+(2.1 +/- 2.3)*10^-5,
from radio frequency-shift measurements near the Sun. It also states the
(1+gamma) propagation dependence. Full subscription text was not inspected.
The default probe is network-free; the HTML digest records that retrieval,
not a claim that a dynamic publisher page will retain the same byte hash.
We compare exact model numbers to the quoted interval only: no new p-value,
confidence level, raw-data analysis, fit, or recalibrated G is manufactured.
Clock-only and conformal examples lie outside that quoted interval under
the SAME static metric/PPN/matter bridge. This is not an exclusion of every
varying-clock theory, nonmetric readout, or alternative physical embedding.

No source-to-clock law, gamma=1 selector, G, metric actualization or GR
closure follows. Existing manifest/Lean statuses and legacy gates are untouched.
Run: python3 -B -O -m scripts.probe_collision_clock_gravity
"""

from __future__ import annotations

import unittest
from dataclasses import dataclass
from fractions import Fraction as F

PRIMARY_URL = "https://www.nature.com/articles/nature01997"
PRIMARY_DOI = "10.1038/nature01997"
PRIMARY_ABSTRACT_RETRIEVED = "2026-11-22"
PRIMARY_HTML_SHA256 = "89ad82f6c2c1dae0e16b326e23c3afc02cb8f97051314f7bd35a23212aed3094"
CASSINI_DELTA = F(21, 1_000_000)
CASSINI_QUOTED_ERROR = F(23, 1_000_000)


def positive(value: F, name: str) -> None:
    if not isinstance(value, F) or value <= 0:
        raise ValueError(f"{name} must be a positive exact Fraction")


@dataclass(frozen=True)
class Cell:
    lapse: F
    rod_scale: F
    coordinate_length: F

    def __post_init__(self) -> None:
        positive(self.lapse, "lapse")
        positive(self.rod_scale, "rod_scale")
        positive(self.coordinate_length, "coordinate_length")

    @property
    def optical_index(self) -> F:
        return self.rod_scale / self.lapse

    @property
    def coordinate_speed(self) -> F:
        return self.lapse / self.rod_scale

    @property
    def proper_length(self) -> F:
        return self.rod_scale * self.coordinate_length

    def conformal(self, factor: F) -> Cell:
        positive(factor, "conformal factor")
        return Cell(factor * self.lapse, factor * self.rod_scale, self.coordinate_length)

    def coordinate_change(self, time_scale: F, length_scale: F) -> Cell:
        positive(time_scale, "time coordinate scale")
        positive(length_scale, "spatial coordinate scale")
        return Cell(self.lapse / time_scale, self.rod_scale / length_scale,
                    self.coordinate_length * length_scale)


def coordinate_round_trip(cells: tuple[Cell, ...]) -> F:
    if not cells:
        raise ValueError("a nonempty prescribed optical path is required")
    return 2 * sum((cell.coordinate_length * cell.optical_index for cell in cells), F(0))


def proper_round_trip(cells: tuple[Cell, ...], emitter_lapse: F) -> F:
    positive(emitter_lapse, "emitter lapse")
    return emitter_lapse * coordinate_round_trip(cells)


def static_frequency_ratio(emitter_lapse: F, receiver_lapse: F) -> F:
    positive(emitter_lapse, "emitter lapse")
    positive(receiver_lapse, "receiver lapse")
    return emitter_lapse / receiver_lapse


def exponential_family(lapse: F, gamma: int) -> Cell:
    positive(lapse, "lapse")
    if type(gamma) is not int or gamma not in (-1, 0, 1):
        raise ValueError("exact example family uses gamma=-1,0,1")
    return Cell(lapse, lapse ** (-gamma), F(1))


@dataclass(frozen=True)
class Jet:
    """Formal first-order a+b*epsilon, epsilon^2=0; not a finite-error bound."""

    constant: F
    linear: F

    def __add__(self, other: Jet) -> Jet:
        return Jet(self.constant + other.constant, self.linear + other.linear)

    def __sub__(self, other: Jet) -> Jet:
        return Jet(self.constant - other.constant, self.linear - other.linear)

    def __mul__(self, other: Jet) -> Jet:
        return Jet(self.constant * other.constant,
                   self.constant * other.linear + self.linear * other.constant)

    def inverse(self) -> Jet:
        if not self.constant:
            raise ValueError("jet is not invertible")
        return Jet(1 / self.constant, -self.linear / self.constant ** 2)


def weak_optical_index(gamma: F) -> Jet:
    return Jet(F(1), -gamma) * Jet(F(1), F(1)).inverse()


def leading_optical_ratio_to_gr(gamma: F) -> F:
    return (1 + gamma) / 2


def initial_geodesic_acceleration(lapse: F, rod_scale: F, grad_phi: F, mass: F) -> F:
    """One component, c=1; force/inertia from the SUPPLIED universal action."""
    positive(lapse, "lapse")
    positive(rod_scale, "rod scale")
    positive(mass, "mass")
    force = -mass * lapse * grad_phi
    inertial_coefficient = mass * rod_scale ** 2 / lapse
    return force / inertial_coefficient


def stock_gamma(time_exponent: F, space_exponent: F) -> F:
    """A proposed T^a L^b=constant in a fixed chart, not a derived stock law."""
    positive(space_exponent, "spatial stock exponent")
    return time_exponent / space_exponent


def cassini_quoted_interval() -> tuple[F, F]:
    return 1 + CASSINI_DELTA - CASSINI_QUOTED_ERROR, 1 + CASSINI_DELTA + CASSINI_QUOTED_ERROR


def compare_quoted_interval(gamma: F) -> str:
    low, high = cassini_quoted_interval()
    return "inside_quoted_interval" if low <= gamma <= high else "outside_quoted_interval"


class CollisionClockGravityControls(unittest.TestCase):
    def test_same_clock_redshift_different_optical_round_trip(self) -> None:
        near = F(9, 10)
        trips = {}
        for gamma in (-1, 0, 1):
            cells = (exponential_family(F(1), gamma), exponential_family(near, gamma))
            self.assertEqual(static_frequency_ratio(near, F(1)), near)
            self.assertEqual(static_frequency_ratio(F(1), near), F(10, 9))
            trips[gamma] = proper_round_trip(cells, F(1))
        self.assertEqual(trips, {-1: F(4), 0: F(38, 9), 1: F(362, 81)})
        self.assertEqual((trips[0] - 4) / (trips[1] - 4), F(9, 19))
        # Exact exponential examples approach, but are not asserted equal to,
        # the half-GR leading-order ratio at a finite potential.
        for q in (F(1, 2), F(9, 10), F(99, 100)):
            self.assertEqual((1 / q - 1) / (1 / q ** 2 - 1), q / (1 + q))

    def test_isotropic_cones_and_local_light_speed_do_not_select_gamma(self) -> None:
        for gamma in (-1, 0, 1):
            cell = exponential_family(F(9, 10), gamma)
            diagonal_gram = (cell.coordinate_speed ** 2,) * 3
            self.assertEqual(len(set(diagonal_gram)), 1)
            self.assertEqual(cell.rod_scale * cell.coordinate_speed / cell.lapse, 1)
        self.assertEqual([weak_optical_index(F(k)) for k in (-1, 0, 1)],
                         [Jet(F(1), F(0)), Jet(F(1), F(-1)), Jet(F(1), F(-2))])
        self.assertEqual([leading_optical_ratio_to_gr(F(k)) for k in (-1, 0, 1)], [F(0), F(1, 2), F(1)])

    def test_conformal_null_degeneracy_is_not_clock_or_rod_equality(self) -> None:
        cells = (Cell(F(1), F(1), F(1)), Cell(F(4, 5), F(5, 4), F(2)), Cell(F(9, 10), F(1), F(1)))
        changed = tuple(cell.conformal(factor) for cell, factor in zip(cells, (F(1), F(3, 2), F(1)), strict=True))
        self.assertEqual([c.optical_index for c in cells], [c.optical_index for c in changed])
        self.assertEqual(proper_round_trip(cells, cells[0].lapse), proper_round_trip(changed, changed[0].lapse))
        self.assertEqual(static_frequency_ratio(cells[0].lapse, cells[-1].lapse),
                         static_frequency_ratio(changed[0].lapse, changed[-1].lapse))
        self.assertNotEqual(sum(c.proper_length for c in cells), sum(c.proper_length for c in changed))
        self.assertNotEqual(cells[1].lapse, changed[1].lapse)

    def test_coordinate_and_unit_changes_preserve_proper_observables(self) -> None:
        cells = (Cell(F(1), F(1), F(2)), Cell(F(9, 10), F(10, 9), F(3)))
        for time_scale, length_scale in ((F(2), F(3)), (F(1, 7), F(5, 2))):
            changed = tuple(c.coordinate_change(time_scale, length_scale) for c in cells)
            self.assertEqual(coordinate_round_trip(changed), time_scale * coordinate_round_trip(cells))
            self.assertEqual(proper_round_trip(changed, F(1) / time_scale), proper_round_trip(cells, F(1)))
            self.assertEqual([c.proper_length for c in changed], [c.proper_length for c in cells])
            self.assertEqual(static_frequency_ratio(changed[0].lapse, changed[1].lapse),
                             static_frequency_ratio(cells[0].lapse, cells[1].lapse))
        # Also an arbitrary monotone piecewise 1D spatial chart, not a new
        # three-dimensional isotropic gauge choice or a physical rod change.
        changed = tuple(c.coordinate_change(F(1), s) for c, s in zip(cells, (F(3), F(1, 5)), strict=True))
        self.assertEqual(coordinate_round_trip(changed), coordinate_round_trip(cells))
        self.assertEqual(sum(c.proper_length for c in changed), sum(c.proper_length for c in cells))

    def test_local_clock_rate_is_not_a_global_time_coordinate(self) -> None:
        n_left, n_right, duration = F(1), F(9, 10), F(3)
        integral_around_rectangle = (n_right - n_left) * duration
        self.assertEqual(integral_around_rectangle, F(-3, 10))
        self.assertNotEqual(integral_around_rectangle, 0)

    def test_universal_geodesic_action_is_an_extra_premise_not_a_gamma_selector(self) -> None:
        for gamma in (F(-1), F(0), F(1, 3), F(1), F(2)):
            n, a, gradient = Jet(F(1), F(1)), Jet(F(1), -gamma), Jet(F(0), F(3))
            acceleration = Jet(F(-1), F(0)) * n * n * a.inverse() * a.inverse() * gradient
            self.assertEqual(acceleration, Jet(F(0), F(-3)))
        for exact_gamma in (-1, 0, 1):
            cell = exponential_family(F(9, 10), exact_gamma)
            values = {initial_geodesic_acceleration(cell.lapse, cell.rod_scale, F(1, 100), m)
                      for m in (F(1), F(7), F(3, 5))}
            self.assertEqual(len(values), 1)

    def test_stock_or_action_constraints_do_not_silently_supply_the_missing_response(self) -> None:
        self.assertEqual(stock_gamma(F(1), F(1)), 1)
        self.assertEqual(stock_gamma(F(1), F(3)), F(1, 3))
        self.assertEqual(stock_gamma(F(0), F(3)), 0)
        # Three-dimensional coordinate-cell volume conservation, an explicitly
        # imposed alternative, differs from conserving each tick-step area.
        step = F(3, 4)
        tick = 1 / step ** 3
        n, a = 1 / tick, 1 / step
        self.assertEqual(tick * step ** 3, 1)
        self.assertEqual(n * a ** 3, 1)
        self.assertNotEqual(a, 1 / n)
        for gamma in (-1, 0, 1):
            cell = exponential_family(F(9, 10), gamma)
            self.assertEqual(cell.lapse * (1 / cell.lapse), 1)  # E*T
            self.assertEqual(cell.rod_scale * (1 / cell.rod_scale), 1)  # p*L

    def test_potential_rescaling_cannot_match_both_fixed_clock_and_optical_anchors(self) -> None:
        gamma = F(0)
        clock_fitted_scale = F(1)
        light_fitted_scale = F(2) / (1 + gamma)
        self.assertNotEqual(clock_fitted_scale, light_fitted_scale)
        self.assertEqual(light_fitted_scale * (1 + gamma), 2)
        self.assertNotEqual(light_fitted_scale, 1)
        # With the clock normalization fixed, the required second response is one.
        self.assertEqual(2 / clock_fitted_scale - 1, 1)

    def test_primary_quoted_cassini_comparison_is_exact_not_a_new_statistical_test(self) -> None:
        self.assertEqual(cassini_quoted_interval(), (F(499999, 500000), F(250011, 250000)))
        self.assertEqual(tuple(leading_optical_ratio_to_gr(x) for x in cassini_quoted_interval()),
                         (F(999999, 1_000_000), F(500011, 500000)))
        self.assertEqual(compare_quoted_interval(F(1)), "inside_quoted_interval")
        self.assertEqual(compare_quoted_interval(F(0)), "outside_quoted_interval")
        self.assertEqual(compare_quoted_interval(F(-1)), "outside_quoted_interval")
        self.assertEqual(PRIMARY_DOI, "10.1038/nature01997")

    def test_invalid_positive_geometry_is_not_silently_accepted(self) -> None:
        for value in (F(0), F(-1)):
            with self.assertRaises(ValueError):
                Cell(value, F(1), F(1))
        with self.assertRaises(ValueError):
            exponential_family(F(1), True)
        with self.assertRaises(ValueError):
            coordinate_round_trip(())


def main() -> None:
    result = unittest.TextTestRunner(verbosity=1).run(
        unittest.defaultTestLoader.loadTestsFromTestCase(CollisionClockGravityControls)
    )
    if not result.wasSuccessful():
        raise SystemExit(1)
    print("Fixed clock profile: gamma=0 clock-only gives half the leading GR optical response; gamma=-1 conformal gives zero; gamma=1 needs the independent rod response A=1/N.")
    print("Same 9/10 clock ratio: exact prescribed round-trip times are 38/9, 4, and 362/81 for clock-only, conformal, and inverse-lapse rods.")
    print("Isotropy and leading universal geodesic free fall do not select gamma. Coordinate-cell conservation and action-unit products require additional physical laws.")
    print(f"Primary public abstract: {PRIMARY_URL}; gamma-1=(2.1+/-2.3)*10^-5. Models 0 and -1 are outside the quoted interval, conditional on the same PPN/matter bridge; no p-value assigned.")
    print("No G, sourced metric, primitive clock-gravity identification, universal varying-clock exclusion, or GR status upgrade.")


if __name__ == "__main__":
    main()
