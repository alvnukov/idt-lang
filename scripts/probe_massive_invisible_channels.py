"""What changes if one of four Dirac mass eigenstates is not massless?

Supplied external physics: a narrow on-shell unpolarized Z of mass M,
standard two-body phase space, purely left vector-fermion vertex in the
mass basis and unit reference width Gamma0 for one massless Dirac species
at unit current. Orthogonal ordered i anti-j channels add incoherently.
Examples are real rational projectors. For a complex Hermitian current
the channel weight is |P_ij|^2. This is not a Majorana, mixed-chirality,
finite parent-width or off-shell formula. No masses, current, particle
dictionary or detector selection are inferred from graph or family counts.

Derivation (set M=1): the symmetric part of the left spin trace is
proportional to p^mu k^nu+p^nu k^mu-g^mu nu (p.k). The antisymmetric
part drops out against the polarization sum; there is no m_i m_j term
for a purely left current. Contract with -g_mu nu+Q_mu Q_nu/M^2 and
divide by the massless value. This gives S=p.k+2(Q.p)(Q.k) =
1-(x+y)/2-(x-y)^2/2, with x=(m_i/M)^2 and y=(m_j/M)^2. The spatial
polarization sum in the parent rest frame instead gives 3E_i E_j+|p|^2.
The relative two-body phase space is 2|p|=sqrt(lambda); total weight
is S sqrt(lambda), only on the physical m_i+m_j<M branch, zero otherwise.
Two distinct orders i anti-j and j anti-i are counted separately when i!=j.
On the open branch lambda=(1-(r+s)^2)(1-(r-s)^2)<=1 and S<=1,
strict if either mass ratio r or s is positive. Thus attaining the full
massless trace requires every COUPLED channel to have massless daughters;
a massive *uncoupled* spectator does not lower the width.

This separate experiment does not change neutral_current_width.py or its
explicit rejection of unmapped masses. A produced heavy neutral particle
may decay visibly, be displaced, or change recoil detection efficiency.
A produced two-body partial width is not automatically a measured invisible
width. No realistic detector response, fit, confidence or mass bound here.

Primary measurements (rounded published summaries, distinct samples; not
combined, and none is a count of microscopic species):
* CMS, https://arxiv.org/html/2206.07110, Eqs. (1),(2) and fit discussion:
  36.3 fb^-1 at 13 TeV, invisible and ee/mumu plus jets and background
  controls. A ratio fit normalized by simulation (Gamma_inv^MC=498.7 MeV;
  charged width per flavor 84.2 MeV, input total Z width 2.4988 GeV)
  gives 523 +/- 3 stat +/- 16 syst MeV. Not the same MeV anchor as ATLAS.
* ATLAS, https://arxiv.org/html/2312.02789, 37 fb^-1, ratio of invisible
  to charged-dilepton recoil times the external charged-lepton partial
  width: 506 +/- 2 stat +/- 12 syst MeV. Both hadron-collider analyses
  rely on production, visible normalization, background and acceptances.
* Janot & Jadach, https://arxiv.org/html/1912.02067, reanalysis of the LEP
  lineshapes: 2.9963 +/- 0.0074 effective SM-light-neutrino widths, using
  the updated Bhabha luminosity and SM neutrino/lepton width ratio. Not
  independent of the original https://arxiv.org/abs/hep-ex/0509008 data.
  These are descriptive reference values, not likelihoods for our examples.
  Optional common MeV illustration follows the older adapter's hybrid
  central scale, original LEP Gamma_ll=83.985 +/- 0.086 MeV times updated
  SM Gamma_nu/Gamma_ll=1.99060 +/- 0.00021. This transfers a massless
  radiatively calibrated unit, not a calculation of finite-mass loop
  corrections, data acceptance or propagated normalization uncertainty.
"""

from __future__ import annotations

import json
from fractions import Fraction as F
from itertools import product
from math import isqrt


def need(ok, why):
    if not ok:
        raise ArithmeticError(why)


def sqrt_bounds(z, scale=10**12):
    """Exact rational root when possible; else adjacent outward grid points."""
    if z < 0 or not isinstance(scale, int) or scale < 1:
        raise ValueError("nonnegative radicand and positive integer grid required")
    n, d = z.numerator, z.denominator
    a, b = isqrt(n), isqrt(d)
    if a*a == n and b*b == d:
        return F(a, b), F(a, b)
    k = isqrt((n*scale*scale)//d)
    lo, hi = F(k, scale), F(k+1, scale)
    need(lo*lo < z < hi*hi, "bad directed root enclosure")
    return lo, hi


def rest_frame(r, s):
    # Independent start from E_i+E_j=1 and E_i²-E_j²=r²-s².
    a = (1+r*r-s*s)/2
    b = 1-a
    p2 = a*a-r*r
    need(a > 0 and b > 0 and p2 == b*b-s*s > 0, "rest-frame mass shell")
    return 4*p2, 3*a*b+p2


def factor(r, s):
    """Returns lambda and normalized spin contraction, both exact rationals."""
    if r < 0 or s < 0:
        raise ValueError("mass ratios must be nonnegative")
    r, s = F(r), F(s)
    if r+s >= 1:  # includes vanishing phase space and the unphysical pseudothreshold
        return F(0), F(0)
    x, y = r*r, s*s
    lam = (1-(r+s)**2)*(1-(r-s)**2)
    spin = 1-(x+y+(x-y)**2)/2
    need((lam, spin) == rest_frame(r, s), "covariant contraction/phase space disagrees with rest frame")
    need(0 < lam <= 1 and 0 < spin <= 1, "suppression or threshold")
    return lam, spin


def width_factor(r, s):
    lam, spin = factor(r, s)
    lo, hi = sqrt_bounds(lam)
    return spin*lo, spin*hi


def transpose(a):
    return tuple(zip(*a, strict=True))


def matmul(a, b):
    return tuple(tuple(sum(x*y for x, y in zip(row, col, strict=True)) for col in transpose(b)) for row in a)


def identity(n):
    return tuple(tuple(F(i == j) for j in range(n)) for i in range(n))


def rotate(i, j, c=F(4, 5), s=F(3, 5)):
    u = [list(row) for row in identity(4)]
    u[i][i], u[i][j], u[j][i], u[j][j] = c, s, -s, c
    u = tuple(map(tuple, u))
    need(matmul(transpose(u), u) == identity(4), "mixing matrix is not orthogonal")
    return u


def projector(u):
    active = ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 0))
    p = matmul(transpose(u), matmul(active, u))
    need(transpose(p) == matmul(p, p) == p and sum(p[i][i] for i in range(4)) == 3,
         "not a rank-three orthogonal projector")
    return p


def width(p, masses, invisible=None):
    # Optional ideal binary per-leg tag, NOT a real detector. The default
    # sums produced widths; calling it invisible requires external assumptions.
    n = len(masses)
    if invisible is None:
        invisible = (True,)*n
    need(len(invisible) == len(p) == n and all(len(row) == n for row in p), "dimension mismatch")
    lo = hi = F(0)
    channels = {}
    for i, j in product(range(n), repeat=2):
        cut = masses[i]+masses[j] >= 1
        a, b = width_factor(masses[i], masses[j])
        w = p[i][j]**2
        if invisible[i] and invisible[j]:
            lo, hi = lo+w*a, hi+w*b
        channels[i, j] = (w, cut, a, b)
    return (lo, hi), channels


def kinematics_checks():
    exact = 0
    for i, j in product(range(15), repeat=2):
        r, s = F(i, 10), F(j, 10)
        lam, spin = factor(r, s)
        lo, hi = width_factor(r, s)
        need((lam, spin) == factor(s, r) and 0 <= lo <= hi <= 1, "exchange symmetry/bounds")
        need(lo*lo <= lam*spin*spin <= hi*hi and hi-lo <= F(1, 10**12), "outward width bound")
        if r == s and 2*r < 1:
            need(lam*spin**2 == (1-4*r*r)*(1-r*r)**2, "equal-mass limit")
        if s == 0 and r < 1:
            target = (1-r*r)**2*(1+r*r/2)
            need(lo == hi == target, "one-heavy limit")
        exact += lo == hi
    need(factor(F(1, 4), F(3, 4)) == (0, 0) and factor(F(3, 2), F(1, 10)) == (0, 0),
         "threshold and pseudothreshold controls")
    need(sqrt_bounds(F(1, 9)) == (F(1, 3),)*2, "exact root off decimal grid")
    return {"mass_pairs": 225, "exact_rational_width_factors": exact, "others": 225-exact}


def examples():
    base, mixed = projector(identity(4)), projector(rotate(2, 3))
    aligned_heavy = projector(rotate(2, 3, F(0), F(1)))
    light = (F(0),)*4
    split = (*light[:3], F(3, 5))
    all_open = (*light[:3], F(1, 5))
    need(all(width(p, light)[0] == (3, 3) for p in (base, mixed, aligned_heavy)), "massless trace")
    unrotated, _ = width(base, split)
    purely_heavy, _ = width(aligned_heavy, split)
    result, channels = width(mixed, split)
    ll = 2+F(16, 25)**2
    hl = (1-F(9, 25))**2*(1+F(9, 50))
    need(channels[2, 3] == channels[3, 2] == (F(12, 25)**2, False, hl, hl), "ordered heavy-light terms")
    need(channels[3, 3] == (F(9, 25)**2, True, 0, 0), "heavy-heavy channel must close")
    total_cross = 2*F(12, 25)**2*hl
    need(result == (ll+total_cross,)*2 and unrotated == (3, 3) and purely_heavy == (2, 2),
         "same masses and rank, different current alignment")
    need(2 < ll < result[0] < 3, "diagonal-only/open-channel count control")
    # Basis-free grouping for a single massive eigenstate h. P²=P gives
    # sum_j |P_hj|² = P_hh = u, not u². Subtract the hh term; two distinct
    # off-diagonal orders each have total weight u-u². The rest is light.
    for p in (base, mixed, aligned_heavy):
        u = p[3][3]
        need(sum(p[3][i]**2 for i in range(3)) == u*(1-u), "off-diagonal sum rule")
        need(sum(p[i][j]**2 for i, j in product(range(3), repeat=2)) == 3-2*u+u*u, "light block")
        predicted = 3-2*u+u*u+2*u*(1-u)*hl  # heavy-heavy forbidden at this mass
        need(width(p, split)[0] == (predicted, predicted), "grouped width")
    tagged, _ = width(mixed, split, (True, True, True, False))
    need(tagged == (ll, ll), "ideal observable with visible heavy leg")
    open_width, open_channels = width(mixed, all_open)
    need(not any(row[1] for row in open_channels.values()) and result[1] < open_width[0] < open_width[1] < 3,
         "all channels may be open without the massless trace")
    forbidden, _ = width(mixed, (*light[:3], F(1)))
    need(forbidden == (ll, ll), "heavy-light threshold")
    # Rotating a degenerate light subspace is not a new physical model.
    rot = rotate(0, 2)
    rebased = matmul(transpose(rot), matmul(mixed, rot))
    need(width(rebased, split)[0] == result, "degenerate light-basis change")
    # Jointly relabel masses and current, even across unequal mass labels.
    order = (3, 1, 2, 0)
    perm = tuple(tuple(mixed[i][j] for j in order) for i in order)
    need(width(perm, tuple(split[i] for i in order))[0] == result, "mass-eigenstate relabeling")
    return {"unit": "one supplied massless Dirac left-current width", "rotation_cos_sin": ["4/5", "3/5"],
            "all_massless": 3, "same_three_zero_and_one_3_over_5_masses": {
                "heavy_uncoupled": unrotated[0], "heavy_fully_active": purely_heavy[0],
                "mixed_light_light": ll, "two_mixed_heavy_light_terms": total_cross, "mixed_total": result[0],
                "mixed_heavy_heavy": 0, "mixed_if_visible_heavy_ideal_veto": tagged[0]},
            "mixed_mh_over_M_one_fifth_all_pairs_open_enclosure": open_width,
            "mixed_mh_over_M_one": forbidden[0]}


def probe():
    ex = examples()
    gamma0 = F("83.985")*F("1.99060")
    mixed = ex["same_three_zero_and_one_3_over_5_masses"]["mixed_total"]
    return {"kinematics": kinematics_checks(), "examples": ex,
            "external_central_MeV_illustration_no_propagated_errors": {
                "Gamma0": str(gamma0), "massless_three": f"{float(3*gamma0):.2f}",
                "example_mixed_if_fully_invisible": f"{float(gamma0*mixed):.2f}"},
            "published_no_fit": {"CMS_MeV_value_stat_syst": [523, 3, 16], "ATLAS_MeV_value_stat_syst": [506, 2, 12],
                                 "LEP_updated_effective_width_units_value_error": ["2.9963", "0.0074"]},
            "scope": "conditional produced widths, not detector-level mass bounds or a species count"}


if __name__ == "__main__":
    print(json.dumps(probe(), indent=2, sort_keys=True, default=str))
