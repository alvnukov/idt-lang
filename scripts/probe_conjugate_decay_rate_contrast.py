"""Direct CP comparison independent of a global CKM-magnitude table.

There are TWO different observables below. NA48 and KTeV compared K_L
and K_S decays into two CP-even pion channels. They did NOT count two
initial flavor-tagged samples to measure Gamma(K0->f)-Gamma(K0bar->f).
We replay a corrected published double ratio; a separate rational toy
illustrates a partial-rate asymmetry. No free phases fitted to kaon data.

Let eta_f=A(K_L->f)/A(K_S->f). Writing eta_+-=eps+eps', eta_00=eps-2eps'
defines effective amplitude parameters. In the NA48 orientation, with
x=eps'/eps, R=|eta_00/eta_+-|²=|1-2x|²/|1+x|²=1-6 Re(x)+O(|x|²).
A common indirect impurity may give sizable nonzero eta in BOTH channels
but cannot by itself give R!=1. R probes a channel-dependent effect,
not the overall neutral-kaon CP impurity or a separately identified
value of a fundamental weak phase. R=1 need not imply complete CP symmetry.

Primary corrected summaries:
* NA48, Phys. Lett. B 544 (2002) 97, https://arxiv.org/html/hep-ex/0208009,
  sections on analysis principles and results. 2001 corrected
  R=0.99181 +/- 0.00147(stat) +/- 0.00110(syst), with finite statistics
  of control samples included in the latter. All four modes collected
  simultaneously; proton time tagging, kaon proper-time weighting to
  match acceptances, 20 energy bins, backgrounds, triggers and accidental
  losses matter. The reported new sample gives (13.7 +/- 3.1)x10^-4;
  all NA48 data together give (14.7 +/- 2.2)x10^-4. These overlap.
* KTeV, Phys. Rev. D 83 (2011) 092001, https://arxiv.org/html/1011.0127,
  Eqs. (3), (10)-(13): independent Fermilab samples in 1996, 1997 and
  1999. Two beams, one with coherent regeneration K_L+rho K_S; it is
  NOT a pure K_S beam. The reciprocal double ratio is used in Eq. (3).
  Fit to background-subtracted yields in twelve momentum bins, accounting
  for regeneration/interference, attenuation and simulated acceptance.
  The quoted fit sets both eta phases to the superweak phase under its
  stated CPT assumption. Result: (19.2 +/- 1.1 stat +/- 1.8 syst)x10^-4,
  or (19.2 +/- 2.1)x10^-4. We do not treat the translated partial-rate
  asymmetry as another measurement: arXiv Eq. (14) even prints identical
  differences in numerator and denominator (also in its source TeX).
  No combined significance or independent-likelihood claim.

Model boundary: CP is unitary, NOT global complex conjugation. In the
specified conjugate-amplitude convention weak couplings are conjugated,
but the same CP-even final-state rescattering acts in both channels.
Stating which beams, states, interactions, acceptances and rates are CP
conjugates is extra physics; arbitrary unequal probabilities with new
labels prove nothing. The synthetic kaon algebra is not a full decay,
mixing, regeneration or detector calculation. Only within a specified
weak charged-current model does a mixing matrix have a family-count
interpretation. No quark masses, independent family count, microscopic
phase source, or necessity of fundamentally complex numbers is inferred.
"""

from __future__ import annotations

import json
from fractions import Fraction as F
from itertools import product


def need(ok, reason):
    if not ok:
        raise ArithmeticError(reason)


def z(re=0, im=0):
    return F(re), F(im)


def plus(x, y):
    return x[0]+y[0], x[1]+y[1]


def scale(r, x):
    return r*x[0], r*x[1]


def times(x, y):
    return x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0]


def conj(x):
    return x[0], -x[1]


def norm(x):
    return x[0]**2+x[1]**2


def div(x, y):
    return scale(1/norm(y), times(x, conj(y)))


def double_ratio(widths):
    # Order: L00, S00, L+-, S+-.
    ln, sn, lc, sc = widths
    return F(ln*sc, sn*lc)


def source_replay():
    r, stat, syst = map(F, ("0.99181", "0.00147", "0.00110"))
    re_in_units = (1-r)*10000/6
    # The published single-decimal 13.7 is consistent with linearizing
    # the rounded central value (13.65 before last-place rounding).
    need(re_in_units == F("13.65") and abs(re_in_units-F("13.7")) == F("0.05"), "NA48 2001 central")
    var = (stat**2+syst**2)*(F(10000, 6)**2)
    need(F("3.05")**2 < var < F("3.15")**2, "rounded NA48 2001 total error")
    naive = double_ratio((1546, 2159, 7136, 9605))  # rounded totals in thousands
    need(F("0.9638") < naive < F("0.9639") < r, "selected totals are not corrected rates")
    # A beam factor times a mode factor cancels. An efficiency depending
    # jointly on beam and mode can mimic a deviation if not calibrated.
    beam, mode = (7, 5), (11, 13)
    pure_indirect = (beam[0]*mode[0], beam[1]*mode[0], beam[0]*mode[1], beam[1]*mode[1])
    need(double_ratio(pure_indirect) == 1 and double_ratio((r*pure_indirect[0], *pure_indirect[1:])) == r,
         "acceptance control, not an explanation of NA48")
    kte = F("0.00192")
    need(1+6*kte == F("1.01152") and 1-6*kte == F("0.98848"), "double-ratio convention")
    return {"NA48_2001_corrected_R_stat_syst": ["0.99181", "0.00147", "0.00110"],
            "NA48_2001_linearized_Re_times_10000": "13.65",
            "NA48_2001_rounded_count_ratio_NOT_the_observable": round(float(naive), 7),
            "full_Re_times_10000_value_total_error": {"NA48": ["14.7", "2.2"], "KTeV": ["19.2", "2.1"]},
            "KTeV_first_order_translation_to_NA48_R_not_reported_yields": "0.98848"}


def eta(pair, f):
    # K_S=p K0+q K0bar, K_L=p K0-q K0bar; common state phases omitted.
    p, q = pair
    a, abar = f
    u, v = times(p, a), times(q, abar)
    return div(plus(u, scale(-1, v)), plus(u, v))


def ratio_from_x(x):
    return norm(plus(z(1), scale(-2, x)))/norm(plus(z(1), x))


def kaon_controls():
    mixing = (z(F(4, 5)), z(F(3, 5)))
    charged = (z(1), z(1))
    neutral = (z(2, 1), z(2, 1))
    ec = eta(mixing, charged)
    need(ec == eta(mixing, neutral) == z(F(1, 7)), "common indirect impurity")
    # All strong phases zero; in the neutral channel a second weak path
    # has phase +pi/2 in one decay and -pi/2 in its conjugate. Both
    # tagged rates are identical in BOTH channels. The common mixing is
    # held fixed, exposing different rephasing-invariant relative phases.
    # This is NOT the small-eta, phase-constrained KTeV fit or its physics.
    neutral = (z(1, F(1, 7)), z(1, F(-1, 7)))
    en = eta(mixing, neutral)
    r = norm(en)/norm(ec)
    need(all(norm(a) == norm(b) for a, b in (charged, neutral)) and r == F(2401, 1201),
         "double ratio and tagged partial-rate asymmetry conflated")
    eps = scale(F(1, 3), plus(scale(2, ec), en))
    eps_prime = scale(F(1, 3), plus(ec, scale(-1, en)))
    need(ratio_from_x(div(eps_prime, eps)) == r, "exact eta convention")
    # Flavor rephasing and independent common final-state phases do not
    # alter this effect when p,q and decay amplitudes transform together.
    t = z(F(3, 5), F(4, 5))
    mix2 = (times(mixing[0], conj(t)), times(mixing[1], t))
    for f, final_phase in ((charged, t), (neutral, z(0, 1))):
        a2 = times(final_phase, times(t, f[0]))
        b2 = times(final_phase, times(conj(t), f[1]))
        need(eta(mix2, (a2, b2)) == eta(mixing, f), "rephasing changed observable")
    # A ratio of moduli is blind to Im(x)'s sign and even can equal 1
    # for finite nonzero x: |x|²=2 Re(x). It is not tomography.
    x = z(F(2, 10001), F(200, 10001))
    need(ratio_from_x(x) == ratio_from_x(conj(x)) == 1 and x != z(0), "rate-only blindness")
    return {"common_indirect_eta_each": "1/7", "common_indirect_R": 1,
            "toy_R_with_all_flavor_tagged_partial_rates_equal": r, "toy_not_a_kaon_fit": True}


def vector_out(matrix, initial):
    return tuple(plus(times(row[0], initial[0]), times(row[1], initial[1])) for row in matrix)


def realify(matrix):
    # Interleaved real/imag parts. Each complex coefficient a+ib acts
    # via a*I+b*J, J(x,y)=(-y,x). Not a scalar real CKM matrix.
    out = []
    for row in matrix:
        out.append(tuple(v for a, b in row for v in (a, -b)))
        out.append(tuple(v for a, b in row for v in (b, a)))
    return tuple(out)


def apply_r(matrix, vector):
    return tuple(sum(a*b for a, b in zip(row, vector, strict=True)) for row in matrix)


def two_paths():
    units = (z(1), z(-1), z(0, 1), z(F(3, 5), F(4, 5)), z(F(-5, 13), F(12, 13)))
    for a, b, strong, weak in product((F(0), F(3, 5)), (F(0), F(4, 5)), units, units):
        # Strong and weak angles are each relative to the first path.
        rates = tuple(norm(plus(z(a), scale(b, times(strong, w)))) for w in (weak, conj(weak)))
        need(rates[0]-rates[1] == -4*a*b*strong[1]*weak[1], "two-path sine product")
        need(a*b*strong[1]*weak[1] != 0 or rates[0] == rates[1], "one path/global phase/null weak or strong")
    # A two-channel unitary CP-even rescatterer demonstrates partial rate
    # asymmetries with equal total rates. This is a control, not fitted.
    c, s = F(3, 5), F(4, 5)
    st = ((z(c), z(0, s)), (z(0, s), z(c)))
    w = (z(c), scale(s, z(c, s)))
    wbar = tuple(map(conj, w))  # conjugate the weak inputs, NOT the final-state propagation
    rate, bar = (tuple(map(norm, vector_out(st, v))) for v in (w, wbar))
    need(sum(rate) == sum(bar) == 1 and rate[0]-bar[0] == F(-2304, 3125) == bar[1]-rate[1],
         "opposing partial asymmetries")
    common = z(F(5, 13), F(12, 13))
    need(tuple(map(norm, vector_out(st, tuple(times(common, v) for v in w)))) == rate and
         tuple(map(norm, vector_out(st, tuple(times(conj(common), v) for v in wbar)))) == bar,
         "a global weak phase changed a tagged rate")
    fully_conjugated = tuple(tuple(map(conj, row)) for row in st)
    need(tuple(map(norm, vector_out(fully_conjugated, wbar))) == rate, "conjugating everything hides asymmetry")
    real_only = ((z(c), z(-s)), (z(s), z(c)))
    need(tuple(map(norm, vector_out(real_only, w))) == tuple(map(norm, vector_out(real_only, wbar))),
         "real-only common dynamics with conjugate input")
    # Explicit real orthogonal realization for BOTH tagged preparations.
    # It retains two real coordinates per complex component, J, a weak
    # CP dictionary, and squared norms per final channel.
    r = realify(st)
    jmat = realify(((z(0, 1), z(0)), (z(0), z(0, 1))))
    for i in range(4):
        e = tuple(F(k == i) for k in range(4))
        need(apply_r(tuple(zip(*r, strict=True)), apply_r(r, e)) == e, "not orthogonal")
        need(apply_r(jmat, apply_r(jmat, e)) == tuple(-x for x in e), "J² != -I")
        need(apply_r(jmat, apply_r(r, e)) == apply_r(r, apply_r(jmat, e)), "lost complex structure")
    for u, target in ((w, rate), (wbar, bar)):
        out = apply_r(r, tuple(value for pair in u for value in pair))
        need((out[0]**2+out[1]**2, out[2]**2+out[3]**2) == target, "realification rates")
    return {"toy_tagged_rates_two_finals": rate, "toy_conjugate_rates": bar,
            "partial_rate_differences": [rate[i]-bar[i] for i in range(2)],
            "totals_equal": True, "same_rates_real_orthogonal_dimension": 4}


def two_family_control():
    # ONLY if a unitary charged-current mixing matrix is the relevant
    # weak-phase source: for a 2x2 unitary V=[[a,b],[c,d]], row
    # orthogonality gives a c* = -b d*, so a d b* c* = -|b d|²
    # and its rephasing-invariant imaginary part vanishes identically.
    # No count follows if weak couplings or sources beyond this are allowed.
    v = ((z(F(3, 5)), z(F(4, 5))), (z(F(-4, 5)), z(F(3, 5))))
    u = (z(F(3, 5), F(4, 5)), z(F(5, 13), F(-12, 13)))
    h = (z(0, 1), z(F(-5, 13), F(12, 13)))
    (a, b), (c, d) = tuple(tuple(times(times(u[i], v[i][j]), h[j]) for j in range(2)) for i in range(2))
    need(plus(times(a, conj(c)), times(b, conj(d))) == z(0), "row orthogonality")
    quartet = times(times(a, d), conj(times(b, c)))
    need(quartet == z(-norm(times(b, d))), "charged-current quartet")
    return {"two_by_two_unitary_charged_current_quartet_imaginary_part": quartet[1],
            "qualification": "not a test of every two-family effective Hamiltonian"}


def probe():
    return {"published_no_refit": source_replay(), "kaon_double_ratio": kaon_controls(),
            "separate_two_path_model": two_paths(), "restricted_weak_mixing": two_family_control(),
            "scope": "direct CP comparator, not a global CKM fit, quark-family count or fundamental-complexity test"}


if __name__ == "__main__":
    print(json.dumps(probe(), default=str, indent=2, sort_keys=True))
