"""Exploratory hemisphere hidden-variable model; no IDT or QM status upgrade.

Supplied geometry: unit sphere, rotational area, unit preparation n, and sign
detector sign(m dot lambda). Supplied endpoint law on S^2: density
max(n dot lambda, 0)/pi with respect to area. It is the known hemisphere
QSD candidate for isotropic generator D*Delta (D>0), killed at the equator,
conditioned on survival at long time. This script DOES NOT prove convergence,
the principal-eigenfunction theorem, or derive that diffusion/conditioning.

Fixed deterministic quadratures check finitely many orientations. Tolerances
are empirical acceptance thresholds, not certified integration error bounds.
No parameters are fitted. Calibration and held-out lists are fixed in source.
The angular dimension reduction assumes rotational geometry in every dimension;
it is not an independent full-dimensional d=4 simulation or a universal proof.
"""

from fractions import Fraction
from math import acos, cos, pi, sin, sqrt

Vector = tuple[float, float, float]
SPHERE_SAMPLES = 131_072
ANGULAR_SAMPLES = 65_536
TOLERANCE = 0.002
X: Vector = (1.0, 0.0, 0.0)
Y: Vector = (0.0, 1.0, 0.0)
Z: Vector = (0.0, 0.0, 1.0)


def check(condition: bool, message: str) -> None:
    """Remain effective under python -O."""
    if not condition:
        raise RuntimeError(message)


def dot(a: Vector, b: Vector) -> float:
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def unit(a: Vector) -> Vector:
    size = sqrt(dot(a, a))
    check(size > 0.0, "zero direction")
    return a[0] / size, a[1] / size, a[2] / size


def neg(a: Vector) -> Vector:
    return -a[0], -a[1], -a[2]


def close(actual: float, expected: float, label: str) -> float:
    error = abs(actual - expected)
    check(error <= TOLERANCE, f"{label}: {actual} != {expected}, error={error}")
    return error


def sphere_points() -> list[Vector]:
    """Equal-weight Fibonacci quadrature; independent of all tested axes."""
    points: list[Vector] = []
    golden_angle = pi * (3.0 - sqrt(5.0))
    for i in range(SPHERE_SAMPLES):
        z = 1.0 - 2.0 * (i + 0.5) / SPHERE_SAMPLES
        radius = sqrt(1.0 - z * z)
        angle = golden_angle * i
        points.append((radius * cos(angle), radius * sin(angle), z))
    return points


def sphere_readout(points: list[Vector], n: Vector, m: Vector) -> tuple[float, float]:
    """Direct weighted count, with no target-probability formula in the loop."""
    total = positive = 0.0
    hemisphere = positive_hemisphere = 0
    for point in points:
        projection = dot(n, point)
        if projection <= 0.0:
            continue
        total += projection
        hemisphere += 1
        if dot(m, point) > 0.0:
            positive += projection
            positive_hemisphere += 1
    # On S^2, E_uniform[(n dot lambda)+] = 1/4, so area integral is pi.
    close(total / len(points), 0.25, "S2 endpoint normalization")
    check(total > 0.0 and hemisphere > 0, "empty preparation")
    return positive / total, positive_hemisphere / hemisphere


def check_single_readouts(points: list[Vector]) -> None:
    calibration = (
        ("aligned", Z, Z),
        ("orthogonal", Z, X),
        ("rational-dot-3/5", Z, (0.8, 0.0, 0.6)),
    )
    held_out = (
        ("generic-A", unit((2.0, -3.0, 6.0)), unit((-4.0, 7.0, 1.0))),
        ("generic-B", unit((-5.0, 2.0, 4.0)), unit((3.0, 1.0, -7.0))),
        ("generic-C", unit((1.0, 4.0, -2.0)), unit((6.0, -3.0, 5.0))),
        ("generic-D", unit((7.0, -1.0, 3.0)), unit((2.0, 5.0, 4.0))),
    )
    max_weighted_error = max_uniform_error = 0.0
    for stage, cases in (("calibration", calibration), ("held-out", held_out)):
        for label, n, m in cases:
            scalar = max(-1.0, min(1.0, dot(n, m)))
            expected = (1.0 + scalar) / 2.0
            uniform_expected = 1.0 - acos(scalar) / pi
            weighted, uniform = sphere_readout(points, n, m)
            max_weighted_error = max(
                max_weighted_error, close(weighted, expected, label)
            )
            max_uniform_error = max(
                max_uniform_error, close(uniform, uniform_expected, label + " uniform")
            )
            opposite, _ = sphere_readout(points, neg(n), m)
            close(weighted + opposite, 1.0, label + " antipodal mixture")
            detector_opposite, _ = sphere_readout(points, n, neg(m))
            close(weighted + detector_opposite, 1.0, label + " detector complement")
            same, _ = sphere_readout(points, n, n)
            antipodal, _ = sphere_readout(points, n, neg(n))
            close(same, 1.0, label + " repeatability")
            close(antipodal, 0.0, label + " antipodal detector")
            print(
                f"{stage} {label}: weighted={weighted:.8f} target={expected:.8f}; "
                f"uniform_Hn={uniform:.8f} target={uniform_expected:.8f}"
            )
    print(
        f"S2 maximum empirical errors: weighted={max_weighted_error:.8g}; "
        f"uniform={max_uniform_error:.8g}; tolerance={TOLERANCE}"
    )
    # Rational control conditional on the supplied integral identity, not a proof.
    rational_control = (1 + Fraction(3, 5)) / 2
    check(rational_control == Fraction(4, 5), "rational arithmetic control")
    print(f"conditional rational control: dot=3/5 gives P(+)={rational_control}")


def planar_integrals(alpha: float) -> tuple[float, float]:
    """Integrate the two-dimensional plane angle; no S2 samples are reused."""
    total = positive = 0.0
    for i in range(ANGULAR_SAMPLES):
        theta = 2.0 * pi * (i + 0.5) / ANGULAR_SAMPLES
        weight = max(cos(theta), 0.0)
        total += weight
        if cos(theta - alpha) > 0.0:
            positive += weight
    return positive / ANGULAR_SAMPLES, total / ANGULAR_SAMPLES


def check_dimension_reduction() -> None:
    # In the span of n,m write (lambda_1,lambda_2)=r(cos theta,sin theta).
    # Rotational area makes theta uniform and independent of r. Thus the factor
    # E[r] cancels from the weighted probability in every d>=2. For d=2, r=1;
    # on S^3 (d=4), r^2 is uniform on [0,1], so E[r]=integral_0^1 sqrt(u)du=2/3.
    radial_d4 = sum(sqrt((i + 0.5) / 256) for i in range(256)) / 256
    close(radial_d4, 2.0 / 3.0, "d4 reduced radial integral")
    max_error = 0.0
    for scalar in (-1.0, -0.83, -0.27, 0.0, 0.37, 0.6, 0.91, 1.0):
        numerator, denominator = planar_integrals(acos(scalar))
        close(denominator, 1.0 / pi, "planar normalization")
        for dimension, radial in ((2, 1.0), (4, radial_d4)):
            probability = radial * numerator / (radial * denominator)
            max_error = max(
                max_error,
                close(probability, (1.0 + scalar) / 2.0, f"d={dimension} planar"),
            )
    print(
        "d=2,d=4 reduced planar angular integration: "
        f"8 angles each, max empirical error={max_error:.8g}; "
        f"d4 radial integral={radial_d4:.8f} (target 2/3)"
    )
    print(
        "Dimension scope: supplied rotational geometry; NOT full-dimensional d4 sampling."
    )


def mixture_diagnostics(points: list[Vector], n: Vector) -> tuple[float, float, float]:
    """Mixture 1/2(mu_n+mu_-n), proportional to |n dot lambda|.

    Passive sequential ++ means reading x then y on the SAME unchanged lambda.
    The hidden z^2 moment is a latent diagnostic, not an allowed sign observable.
    """
    total = z_squared = first_plus = both_plus = 0.0
    for point in points:
        weight = abs(dot(n, point))
        total += weight
        z_squared += weight * point[2] ** 2
        if point[0] > 0.0:
            first_plus += weight
            if point[1] > 0.0:
                both_plus += weight
    close(total / len(points), 0.5, "antipodal mixture normalization")
    return z_squared / total, first_plus / total, both_plus / total


def check_mixtures_and_instruments(points: list[Vector]) -> None:
    z_hidden, z_single, _ = mixture_diagnostics(points, Z)
    x_hidden, x_single, _ = mixture_diagnostics(points, X)
    close(z_hidden, 0.5, "q_z hidden E[z^2]")
    close(x_hidden, 0.25, "q_x hidden E[z^2]")
    close(z_single, 0.5, "q_z operational x+")
    close(x_single, 0.5, "q_x operational x+")
    print(
        f"q_z vs q_x hidden E[z^2]: {z_hidden:.8f} vs {x_hidden:.8f} "
        "(targets 1/2 vs 1/4); single sign readouts remain 1/2"
    )
    for label, n, target in (
        ("positive slope", (0.6, 0.8, 0.0), Fraction(7, 20)),
        ("mirrored slope", (0.6, -0.8, 0.0), Fraction(3, 20)),
    ):
        _, first, passive = mixture_diagnostics(points, n)
        close(first, 0.5, label + " first marginal")
        close(passive, float(target), label + " passive sequential ++")
        # A DISTINCT supplied instrument: after x+, independently draw mu_x.
        # Its joint ++ rate is P_initial(x+) * P_mu_x(y+), not passive filtering.
        reset_second, _ = sphere_readout(points, X, Y)
        reset = first * reset_second
        close(reset, 0.25, label + " independent reset ++")
        print(
            f"{label} mixture: passive x-then-y ++={passive:.8f} "
            f"(target {target}); independent reset ++={reset:.8f} (target 1/4)"
        )
    print(
        "Operational boundary: antipodal mixtures agree on one sign readout, "
        "but passive sequences can distinguish decompositions; reset is extra dynamics."
    )


def main() -> None:
    print(
        "Exploratory known hemisphere model; finite numerical checks, NOT a QM derivation."
    )
    print(
        "ASSUMED: rotational sphere geometry; supplied isotropic killed diffusion; "
        "long-time survival conditioning/QSD endpoint; cosine-weighted preparation; "
        "sign detector. No diffusion convergence or physical primitive is established."
    )
    print(
        f"Fixed quadrature: S2={SPHERE_SAMPLES}, plane={ANGULAR_SAMPLES}; "
        f"empirical tolerance={TOLERANCE}; no tuning/fitting."
    )
    points = sphere_points()
    check_single_readouts(points)
    check_dimension_reduction()
    check_mixtures_and_instruments(points)
    print(
        "PASS: listed empirical checks only; no universal proof, novelty, or status upgrade."
    )


if __name__ == "__main__":
    main()
