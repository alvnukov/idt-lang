"""What two reactor oscillation scales and one invisible width can count.

Assume coherent, relativistic, fixed mass eigenstates, a single vacuum
generator in the independently calibrated coordinate L/E, and stationary
source/detector projectors. P_ee=|sum_i w_i exp(-i m_i² L/(2E))|²,
w_i=|U_ei|². In any two-eigenvalue system only one nonzero gap can
appear. Even a general fixed preparation and measurement then gives a
constant plus a single sine/cosine, with possibly zero contrast. Distinct
gaps on the same ruler require >=3 participating eigenvalues *under these
assumptions*, not exactly three species, independent fundamental clocks,
weak doublets or complete charged families. Mass ordering and the common
additive mass-squared offset are not determined by counting frequencies.

Source facts (external fitted summaries, no common likelihood replay):
* KamLAND 2013, https://arxiv.org/html/1303.4667, oscillation analysis,
  KamLAND-only three-flavor fit with no external oscillation pull:
  Delta m21²=7.54 (+0.19/-0.18) x10^-5 eV². Do not use the combined
  7.53 +/- 0.18 value from its abstract as KamLAND-only. Reactor inverse
  beta decay (IBD); a flux-weighted baseline of about 180 km stands for
  many cores, not a single path. The fit includes matter corrections,
  geoneutrinos, time-dependent sources, energy response and backgrounds.
  Overlapping 2008 KamLAND sample, https://arxiv.org/html/0801.4589,
  measured 7.58 (+0.14/-0.13 stat) +/- 0.15 syst x10^-5 eV². This is
  NOT an additional independent measurement.
* Final Daya Bay, https://arxiv.org/html/2211.14988, Eqs. (1)-(3),
  3158 days, 5.55 million IBD candidates; flux-averaged near/near/far
  baselines about 500/500/1650 m. The short-baseline Eq. (2) gives
  |Delta m_ee²|=(2.519 +/- 0.060)x10^-3 eV². This is the effective fast
  wavelength: in the exact three-flavor expression it is a weighted
  combination of two fast sin² terms, not an independent fourth mass
  or necessarily m3²-m2². Eq. (2) retains the small slow term; the
  analysis supplies sin²(theta12)=0.307 +/- 0.013 and Delta m21²=
  (7.53 +/- 0.18)x10^-5 eV². Independent events and detectors do NOT
  make these model-dependent summaries independent likelihoods. Reactor
  spectra and IBD physics are common, while each experiment calibrates
  its own energies, geometry and response. No rejection significance,
  bin-by-bin unfolding, exact one-gap fit, or global refit is performed.
* A check on independence, NOT a third independent fast gap: in JUNO's
  207.2-day analysis, https://arxiv.org/html/2609.37895, the JUNO-only
  fast profile has several local minima. Daya Bay information selects a
  minimum under each ordering; precision at that minimum is driven by
  JUNO. The earlier https://arxiv.org/html/2511.14593 highlights a slow
  gap AND an angle, not two distinct masses measured in that early sample.
* The width comparator is a distinct experiment and dictionary. The
  reanalysis of LEP lineshapes, https://arxiv.org/html/1912.02067,
  gives 2.9963 +/- 0.0074 effective standard light-neutrino widths.
  This needs a visible-width normalization and SM unit invisible width.
  For a standard unit left projector P under those assumptions the
  invisible width is at most Tr(P²)=rank(P)<=number of states; masses
  cannot increase it. Thus a two-state projector cannot provide three
  massless-width units. The reported number is not an event count or a
  measured rank; no integer rounding or combined confidence. See the
  separate massive left-current probe for thresholds, detector visibility
  and recoil data.

Everything in the synthetic section is an exact rational finite witness,
NOT a claimed test on published reactor bins. Sampling several true L/E
values in one reconstructed bin need not preserve a one-gap recurrence.
"""

from __future__ import annotations

import json
from fractions import Fraction as F
from math import pi, sin

from scripts.probe_massive_invisible_channels import factor, identity, width


def need(ok, detail):
    if not ok:
        raise ArithmeticError(detail)


def cmul(a, b):
    return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]


def cpow(z, n):
    out = (1, 0)
    for _ in range(n):
        out = cmul(out, z)
    return out


def survival(weights, phases, n):
    need(min(weights) >= 0 and sum(weights) == 1 and all(a*a+b*b == 1 for a, b in phases), "normalization")
    terms = [(w*a, w*b) for w, z in zip(weights, phases, strict=True) for a, b in (cpow(z, n),)]
    re, im = map(sum, zip(*terms, strict=True))
    result = re*re+im*im
    need(0 <= result <= 1, "invalid survival probability")
    return result


def hankel_minor(samples):
    # A fixed two-eigenvalue U has eigenvalues 1,z,z* in the density
    # evolution (1 is repeated). Differencing removes the constant.
    # First differences obey D[n+2]=2Re(z)*D[n+1]-D[n], so this
    # three-by-three determinant must vanish for six equispaced samples.
    a, b, c, d, e = (samples[i+1]-samples[i] for i in range(5))
    return a*(c*e-d*d)-b*(b*e-c*d)+c*(b*d-c*c)


def deficit_test(samples):
    # More specialized survival-only check. If P0=1 and Dn=1-Pn=
    # A sin²(n phi), D2=4 cos²(phi) D1 and D3=(4 cos²(phi)-1)² D1.
    need(samples[0] == 1, "known pure survival preparation required")
    d1, d2, d3 = (1-p for p in samples[1:4])
    return d1*d3-(d2-d1)**2


def synthetic():
    one, i = (1, 0), (0, 1)
    for phase in (one, i, (-1, 0), (F(3, 5), F(4, 5))):
        for w in (F(0), F(1, 3), F(1, 2)):
            row = [survival((w, 1-w), (one, phase), n) for n in range(6)]
            need(hankel_minor(row) == deficit_test(row) == 0, "one-gap control")
        # An arbitrary offset and quadrature do not rescue the one-gap
        # generator. This positive sequence need not have P(0)=1.
        row = [F(1, 2)+F(1, 4)*r+F(1, 8)*s for n in range(6) for r, s in [cpow(phase, n)]]
        need(hankel_minor(row) == 0, "phase-offset measurement")

    phases, weights = (one, i, (-1, 0)), (F(2, 3), F(1, 6), F(1, 6))
    need(all(cpow(z, 4) == one for z in phases), "period-four alias check must cover all ticks")
    p = tuple(survival(weights, phases, n) for n in range(16))
    need(p[:4] == (1, F(5, 18), F(4, 9), F(5, 18)) and min(p) > 0, "positive three-level witness")
    d, h = deficit_test(p), hankel_minor(p)
    need((d, h) == (F(40, 81), F(200, 729)), "spectral witness")
    # If |delta P|<=eps, each matrix entry changes by <=2eps. There
    # are 6 triple products; telescope each, using |entry|<=1.
    eps = F(1, 200)
    determinant_error = 36*eps*(1+2*eps)**2
    need(h > determinant_error, "synthetic witness lacks promised perturbation margin")

    for n in range(16):
        # Exact countermodel to applying the test to an unresolved bin.
        # Two equal-mixing levels give S(n)=(1+cos(n*pi/2))/2.
        # 5/9 at L plus 4/9 at 2L gives precisely the same three-level
        # series, including all n, by direct cosine expansion. This is
        # not a proposed description of either experiment's baseline map.
        s1 = survival((F(1, 2),)*2, (one, i), n)
        s2 = survival((F(1, 2),)*2, (one, i), 2*n)
        need(F(5, 9)*s1+F(4, 9)*s2 == p[n], "baseline alias countermodel")
        # A decoupled extra level leaves the survival measure unchanged.
        need(survival((*weights, 0), (*phases, (F(3, 5), F(4, 5))), n) == p[n], "spectator")
    return {"true_equispaced_survival_first_six": p[:6], "four_sample_deficit_witness": d,
            "six_sample_difference_Hankel_minor": h, "synthetic_uniform_sample_error": eps,
            "absolute_determinant_error_bound": determinant_error,
            "indistinguishable_if_true_baseline_unresolved": {"weight_at_L": "5/9", "weight_at_2L": "4/9"},
            "scope": "two resolved gaps can be harmonics; no independent fundamental time standards inferred"}


def observed_scales():
    # Daya Bay Eq. (1): sin²[1.267 Delta m²(eV²) L(m)/E(MeV)].
    # Same numeric L/E in km/GeV. Comparisons below are translations of
    # fitted scales into common units, not measured periods in one bin.
    slow, slow_dn, slow_up = map(F, ("0.0000754", "0.0000018", "0.0000019"))
    fast, fast_err = F("0.002519"), F("0.000060")
    lo, hi = (fast-fast_err)/(slow+slow_up), (fast+fast_err)/(slow-slow_dn)
    need(30 < lo < fast/slow < hi < 36, "separation of reported scales on the supplied units")

    def first_minimum(gap):
        return pi/(2*1.267*float(gap))   # meters/MeV

    # A concrete common-ruler discriminator, NOT an observed single bin:
    # maximal mixing and |sin(x)|<=|x| give an upper bound if one uses
    # only the slow gap (within its printed error box). Compare the *fast
    # component* of the published Daya Bay effective curve at the identical
    # point, before folding actual reactor distances, energy and backgrounds.
    ruler = F(1650, 4)
    slow_only_upper = (F("1.267")*(slow+slow_up)*ruler)**2
    fast_central = 0.0852*sin(float(F("1.267")*fast*ruler))**2
    need(slow_only_upper < F(17, 10000) and 0.079 < fast_central < 0.081, "far-hall scale discriminator")
    return {"KamLAND_only_2013_Dm21_eV2_central_minus_plus": ["0.0000754", "0.0000018", "0.0000019"],
            "Daya_Bay_final_abs_Dmee_eV2_central_error": ["0.002519", "0.000060"],
            "central_fast_over_slow": round(float(fast/slow), 4),
            "ratio_extrema_of_separate_printed_error_boxes_not_a_CI": [round(float(x), 3) for x in (lo, hi)],
            "illustrative_first_minimum_L_at_4MeV_km_slow_fast": [round(first_minimum(x)*4/1000, 4)
                                                                    for x in (slow, fast)],
            "illustrative_1650m_4MeV_unfolded_theory_point_not_observed_bin": {
                "one_slow_gap_any_mixing_deficit_strictly_less_than": "0.0017",
                "unrounded_slow_upper_bound": slow_only_upper,
                "DayaBay_central_fast_term_deficit": round(fast_central, 8)},
            "baseline_meters_KamLAND_flux_average__DayaBay_three_halls_approx": [180000, [500, 500, 1650]],
            "distinction": "Dmee is an effective fast wavelength, not an additional independent mass pair"}


def width_countermodel():
    # Illustrative *nonzero* masses, not fitted. A massless width can only
    # be a limit if the active states really have nonzero mass splittings.
    # Use a deliberately round external parent mass for the scale example.
    masses_ev = (F(0), F(1, 100), F(1, 20))
    m_z_ev = 90*10**9
    light = tuple(m/m_z_ev for m in masses_ev)
    i3 = identity(3)
    four = tuple(tuple(F(i == j and i < 3) for j in range(4)) for i in range(4))
    massive_extra = (*light, F(3, 5))
    w3, c3 = width(i3, light)
    w4, c4 = width(four, massive_extra)
    need(w3 == w4 and all(c4[i, j] == row for (i, j), row in c3.items()) and
         all(row[0] == 0 for (i, j), row in c4.items() if 3 in (i, j)), "new channels must vanish termwise")
    # Deficit from rank 3 is positive but <=sum 5x_i because
    # (1-x)sqrt(1-4x)>=(1-x)(1-4x)>=1-5x on this open branch.
    lower = 0
    for r in light:
        x = r*r
        lam, s = factor(r, r)
        need(lam == 1-4*x and s == 1-x and 1 >= lam >= 0, "equal light masses")
        lower += s*lam
    bound = 5*sum(r*r for r in light)
    need(0 < 3-lower <= bound < F(1, 10**22) and any(r > 0 for r in light), "finite mass error")
    # These light masses have distinct gaps and can all appear in the
    # electron row. The heavy fourth state is neither produced nor coupled,
    # not a relativistic MeV reactor state to which we apply a phase fit.
    msq = tuple(m*m for m in masses_ev)
    gaps = sorted({msq[j]-msq[i] for j in range(3) for i in range(j)})
    need(len(gaps) == 3, "hierarchy example")
    # Without standard unit couplings even 'three width units implies at
    # least three states' fails: this positive Hermitian 2x2 current has
    # diagonal 1, off-diagonals (1+i)/2 and conjugate, Frobenius norm²=3.
    # It is NOT a projector and does not fake two oscillation gaps.
    offdiag_squared = F(1, 2)**2+F(1, 2)**2
    need(1-offdiag_squared > 0 and 2+2*offdiag_squared == 3, "noncanonical width countercontrol")
    return {"LEP_updated_effective_standard_widths": ["2.9963", "0.0074"],
            "example_active_masses_eV_not_fit": masses_ev, "example_gaps_eV2_not_fit": gaps,
            "rank_three_width_deficit_strictly_positive_at_most": bound,
            "add_fully_sterile_heavy_state": "all old oscillation terms unchanged, all extra width terms zero",
            "two_state_nonprojector_massless_width_control_only": 3}


def probe():
    return {"published_scales_no_refit": observed_scales(), "synthetic_readout": synthetic(),
            "width_and_species": width_countermodel(),
            "scope": "shared two-eigenvalue vacuum generator has only one gap; complete family count not determined"}


if __name__ == "__main__":
    print(json.dumps(probe(), default=str, indent=2, sort_keys=True))
