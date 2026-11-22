"""Retrospective two-null benchmark; the input is published aggregates, not a dataset.

V. Jacques et al., Science 315, 966–968 (2007), doi:10.1126/science.1136303.
Publisher: https://doi.org/10.1126/science.1136303
Authors' paper: https://arxiv.org/abs/quant-ph/0610241
Full text: https://arxiv.org/pdf/quant-ph/0610241
Equation (1) and following paragraphs: open-configuration anticoincidence;
Fig. 3 and its caption: closed phase scan and open control. The paper used
a pulsed single NV center, a 48 m polarization interferometer and 45-degree
input. Applying the EOM half-wave voltage recombined the arms; zero voltage
left distinguishable outputs. The optical phase was scanned with an arbitrary
origin. The authors report residual luminescence and Raman background for
the nonzero anticoincidence, and imperfect beam overlap for the visibility.

The figures below are transcribed reported aggregates, NOT inferred integer
counts, raw click records, likelihoods or per-injected-photon efficiencies.
The Fig. 3 data used 1.9 s per point, about 2600 detections per point, with
detector dark rates 59/s and 70/s subtracted. That figure processing must
not be silently attributed to the Eq. (1) measurement. The authors do not
quote a visibility uncertainty in the passages used here. No uncertainty
distribution is assumed and no significance or model fit is calculated.

Null 1: an incoherent path label with fixed path probabilities, fixed
throughputs, and a fixed, phase-blind detector has a constant expected rate
during a phase-only scan: V=0, regardless of unequal constant losses. The
ideal lossless balanced coherent squared-norm rule instead has V=1. Neither
ideal predicts the apparatus's exact V=0.94. A conventional coherent field
also has fringes, so visibility alone does not establish path indivisibility.

Null 2: a *common* random nonnegative intensity I is split into two fixed
proportions. Conditional on I, calibrated detector clicks are independent
and their response probabilities f(I),g(I) are nondecreasing. For an
independent copy I', (f(I)-f(I'))(g(I)-g(I')) >= 0, hence E[fg]>=E[f]E[g].
With nonzero marginal click rates this gives population α>=1. It is not a
deterministic inequality for every finite stochastic sample; equality need
not hold with a fluctuating source. Exclusive one-click events instead give
ideal α=0, even with independent thinning of the surviving single clicks
and arbitrary no-click trials (no backgrounds). Neither ideal predicts
the published α=0.12 exactly. Positivity alone is insufficient for the
bound, as the nonproportional two-port countercontrol demonstrates.

These are separate comparisons at separate settings, not a joint event
inequality or a test of a particular native gate, source yield, C4 phase,
or microscopic detector. No new experiment, calibrated prediction, raw-data
reanalysis or advantage over ordinary quantum optics is claimed.

Run: python3 -O -m scripts.probe_interferometer_benchmark
"""

from dataclasses import dataclass
from fractions import Fraction as F
from math import lcm


def need(ok: bool, reason: str) -> None:
    if not ok:
        raise ValueError(reason)


@dataclass(frozen=True)
class Counts:
    """Inclusive singles: each double-click contributes to BOTH singles counts."""

    triggers: int
    n1: int
    n2: int
    both: int

    def alpha(self) -> F:
        need(0 < self.n1 <= self.triggers and 0 < self.n2 <= self.triggers, "singles")
        need(
            max(0, self.n1 + self.n2 - self.triggers)
            <= self.both
            <= min(self.n1, self.n2),
            "impossible joint count",
        )
        return F(self.both * self.triggers, self.n1 * self.n2)


def independent_mixture(rows: tuple[tuple[F, F, F], ...]) -> Counts:
    """Synthetic exact frequencies, not random data. Rows: weight, click1, click2."""
    need(sum((w for w, _, _ in rows), F(0)) == 1, "mixture weights")
    need(all(0 <= x <= 1 for row in rows for x in row), "conditional probabilities")
    p1 = sum((w * x for w, x, _ in rows), F(0))
    p2 = sum((w * y for w, _, y in rows), F(0))
    both = sum((w * x * y for w, x, y in rows), F(0))
    n = lcm(p1.denominator, p2.denominator, both.denominator)
    return Counts(n, int(n * p1), int(n * p2), int(n * both))


def synthetic_controls() -> None:
    fixed = independent_mixture(((F(1), F(1, 2), F(1, 2)),))
    fluctuating = independent_mixture(
        (
            (F(1, 2), F(1, 4), F(1, 4)),
            (F(1, 2), F(3, 4), F(3, 4)),
        )
    )
    exclusive = Counts(triggers=100, n1=23, n2=31, both=0)
    # Both channels have nonnegative intensity. Conditional detection is
    # independent, but the two incident intensities move in opposite directions.
    # Neither channel is now a fixed proportion of one common intensity.
    alternating = independent_mixture(
        (
            (F(1, 2), F(0), F(1, 2)),
            (F(1, 2), F(1, 2), F(0)),
        )
    )
    need(
        fixed.alpha() == 1 and fluctuating.alpha() == F(5, 4),
        "common-intensity controls",
    )
    need(
        exclusive.alpha() == alternating.alpha() == 0, "suppressed coincidence controls"
    )
    print("Synthetic exact frequency tables only: N_trigger, N_1, N_2, N_both -> alpha")
    for label, t in (
        ("constant intensity", fixed),
        ("fluctuating common intensity", fluctuating),
        ("exclusive lossy events", exclusive),
        ("alternating positive port intensities", alternating),
    ):
        print(f"  {label}: {t.triggers}, {t.n1}, {t.n2}, {t.both} -> {t.alpha()}")


def phase_blind_rate(weight: F, left_response: F, right_response: F) -> F:
    return weight * left_response + (1 - weight) * right_response


def phase_comparison() -> None:
    # Exact ideal controls ONLY, not claimed calibrated optical scan points.
    # A terminal orthogonal label adds squared norms over its two components;
    # erasing the label before recombination adds amplitudes instead.
    quarter_turns = ((1, 0), (0, 1), (-1, 0), (0, -1))
    tagged = tuple(F(1 + x * x + y * y, 4) for x, y in quarter_turns)
    coherent = tuple(F((1 + x) ** 2 + y * y, 4) for x, y in quarter_turns)
    need(tagged == (F(1, 2),) * 4, "orthogonal labels remove cross term")
    need(coherent == (F(1), F(1, 2), F(0), F(1, 2)), "balanced coherent control")
    # A positive phase-blind rate can be asymmetric and lossy. It is still
    # constant: phase shifts neither change the alternative nor its weights.
    null_rate = phase_blind_rate(F(1, 3), F(2, 7), F(4, 5))
    need(
        null_rate > 0 and (null_rate - null_rate) / (2 * null_rate) == 0,
        "strict flat control",
    )
    visibility = F("0.94")  # Published rounded value; NOT an uncertainty interval.
    # Express endpoint rates in units of their midpoint, NOT in units of
    # per-injection probability. No raw extrema or phase origin is needed.
    low, high = 1 - visibility, 1 + visibility
    need((high - low) / (high + low) == visibility, "endpoint normalization")
    # For ANY constant c, max(|high-c|,|low-c|) >= (high-low)/2 by triangle
    # inequality. Equality at the midpoint shows that this bound is tight.
    need(max(high - 1, 1 - low) == visibility, "best possible constant")
    print(
        "Closed: reported V=0.94; fixed phase-blind V=0; ideal balanced coherent V=1."
    )
    print(
        "From that contrast, any constant misses one implied fringe extremum by at least ~94% of their midpoint;"
    )
    print(
        "  this is rate contrast, not 94 percentage points of per-injection probability."
    )
    print(
        "Open: no modulation; authors report port detection probabilities 0.50 ± 0.01."
    )


def run() -> None:
    print(
        "Jacques et al. (2007), doi:10.1126/science.1136303; reported aggregates only."
    )
    phase_comparison()
    print("Open α = N_both N_trigger / (N_1 N_2): reported 0.12 ± 0.01.")
    print(
        "  Common split-intensity population bound ≥1; exclusive ideal 0; neither equals 0.12."
    )
    synthetic_controls()


if __name__ == "__main__":
    run()
