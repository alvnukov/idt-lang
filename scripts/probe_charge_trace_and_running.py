"""A trace normalization is not a measurement of running gauge couplings.

The raw pair ballot gives q on sixteen folded-carrier sites. We assign
Y=q/6 (Q_em=T3+Y convention) and T3=(bit_a-bit_b)/2 for the *two marked
ports*. An unweighted trace over sites is not an outcome distribution.
It normalizes one generator relative to another; it supplies no gauge
fields, gauge kinetic metric, coupling equality, RG scale, particle
identification, thresholds or electroweak radiative corrections.
The standard SU(5)-style normalization and common coupling are one
way to enforce the relation. An accidentally equal coupling ratio would
not establish SU(5); the carrier supplies neither the embedding nor a
unified gauge group.

External comparison 1 (deliberately naive, and fails): impose equal
canonically normalized couplings, then equate the resulting tree mixing
angle *directly* to the charged-lepton effective Z-pole angle. Only this
additional dictionary is tested by the empirical counterexamples. No
exclusion of a high-scale equality; no parameter fit or quantified
extrapolation into the extreme tail of a quoted experimental error.

External comparison 2: adopt SM nonabelian representations, Weyl
fermions, a single complex scalar doublet, standard gauge bosons and
mass-independent one-loop RG in a common active-particle interval. The
normalized beta coefficients and pairwise differences are calculated
with rational arithmetic. No effective pole angle is used as a running
MSbar input, and no numerical unification-scale determination is made.
If D_ij = alpha_i^-1-alpha_j^-1 at a reference scale distinct from a
postulated common meeting, a necessary one-loop consistency test is
218 D_23 = 115 D_12. It holds under that postulate, not for arbitrary
measured inputs. An extra complete family shifts absolute running but
not this test; thresholds, split multiplets, scalars and higher loops
can change it. UV location and positive coupling require extra checks.

Checked primary sources (offline published summaries, not raw fits):
* SLD, Phys. Rev. Lett. 84 (2000) 5945, https://arxiv.org/html/hep-ex/0004026,
  Eq. (1), discussion after Eq. (4). The full 1992-98 corrected polarized
  left-right pole asymmetry is +0.15138 +/- 0.00216. Its equivalent
  effective angle 0.23097 +/- 0.00027 uses the same data, not a replication.
  Polarimetry, beam/acceptance asymmetries, pole corrections and the
  effective electron coupling identification matter; see the earlier
  independent count replay in probe_polarized_z_electron.py.
* CMS, Phys. Lett. B 866 (2025) 139526, doi:10.1016/j.physletb.2025.139526,
  https://arxiv.org/html/2408.07622, abstract and results: 138 fb^-1 at
  13 TeV, 2016-18, dielectron/dimuon forward-backward asymmetry as a
  function of mass and rapidity; effective leptonic angle 0.23152 +/-
  0.00031 (CT18Z; combined uncertainty including correlations and PDFs).
  Separate pp data/method, not polarized A_e or a direct MSbar angle;
  13 TeV is the collider energy, not the scale of this pole parameter.
* L. N. Mihaila, J. Salomon, M. Steinhauser, Phys. Rev. Lett. 108
  (2012) 151602, https://arxiv.org/html/1201.5868. Keep ONLY the leading
  terms of their SM gauge equations, with GUT-normalized alpha_1.
  Their beta convention is d(alpha_i/pi)/d ln(mu^2); the respective
  leading coefficients are 1/40+n_G/3, -43/24+n_G/3, -11/4+n_G/3.
  Multiply by four for b_i in d alpha_i^-1 / d ln(mu)=-b_i/(2*pi).

Run: python3 -B [-O] -m scripts.probe_charge_trace_and_running
"""

from __future__ import annotations

import json
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations

from scripts.probe_two_turn_germ_ballots import forced_completion, record, votes


def need(ok, why):
    if not ok:
        raise ArithmeticError(why)


def trace(a, b):
    return sum(x*y for x, y in zip(a, b, strict=True))


def germ_traces():
    g = forced_completion()
    frames = 0
    spectrum = None
    for r in range(len(g)):
        read = record(g, r)
        for t in set(range(len(g))) - {r} - g[r]:
            first, second = sorted(p for p in read if read[p][t])
            others = set(read) - {first, second}
            ys = tuple(F(votes(read, t, v)[0], 6) for v in range(len(g)))
            weak = tuple(F(read[first][v]-read[second][v], 2) for v in range(len(g)))
            yy, tt, yt = trace(ys, ys), trace(weak, weak), trace(ys, weak)
            need((yy, tt, yt) == (F(10, 3), 2, 0), "measured trace table")
            need(sum(ys) == sum(weak) == 0 and ys[t] == 1 and weak[t] == 0, "readout convention")
            # A different signed port order gives the opposite T3. A
            # difference between two large ports has the same squared norm,
            # without supplying any nonabelian representation or coupling.
            for i, j in combinations(others, 2):
                color = tuple(F(read[i][v]-read[j][v], 2) for v in range(len(g)))
                need((trace(color, color), trace(color, ys), trace(color, weak)) == (2, 0, 0),
                     "large-port trace control")
            # Positive nonuniform metric: double only the marked site's
            # weight, respecting all permutations inside the two blocks.
            weighted_ratio = (tt + weak[t]**2) / (yy + ys[t]**2)
            need(weighted_ratio == F(6, 13), "weighted trace did not discriminate")
            if spectrum is None:
                spectrum = Counter(ys)
            need(Counter(ys) == spectrum, "frame-dependent spectrum")
            frames += 1
    need(frames == 160, "not all two-turn frames")
    return yy, tt, yt, spectrum, frames


def ae(s):
    # External electron handedness and effective neutral-current assignment.
    # Overall factors cancel; real effective couplings in the pole adapter.
    left, right = s-F(1, 2), s
    return (left*left-right*right)/(left*left+right*right)


def pole_check(yy, tt):
    k2 = tt / yy   # normalized generator is sqrt(k2) Y, g' = sqrt(k2) g1

    def angle(ratio):
        # ratio is g1^2/g2^2 at a common specified scale, not estimated here.
        return k2*ratio/(1+k2*ratio)

    common = angle(1)
    need(k2 == F(3, 5) and common == F(3, 8) and ae(common) == F(-4, 5), "equality bridge")
    need(angle(F(1, 3)) == F(1, 6) and ae(angle(F(1, 3))) > 0, "independent-coupling countercontrol")
    # Compare *published* summaries; do not compute an unsupported many-
    # sigma tail, combine correlated SLD observables, or turn CMS into A_e.
    sld_a, sld_da = F("0.15138"), F("0.00216")
    sld_s, sld_ds = F("0.23097"), F("0.00027")
    cms_s, cms_ds = F("0.23152"), F("0.00031")
    need(sld_a-sld_da > 0 > ae(common) and cms_s+cms_ds < common, "direct pole comparison")
    need(abs(ae(sld_s)-sld_a) < F("0.0001"), "SLD effective/polarization conventions")
    return {"k_squared": k2, "common_couplings_sin2": common, "naive_pole_Ae": ae(common),
            "same_traces_g1_squared_over_g2_squared_one_third": angle(F(1, 3)),
            "SLD_pole_Ae_value_error": [f"{float(x):.5f}" for x in (sld_a, sld_da)],
            "SLD_equivalent_angle_same_data": [f"{float(x):.5f}" for x in (sld_s, sld_ds)],
            "CMS_effective_angle_value_error": [f"{float(x):.5f}" for x in (cms_s, cms_ds)]}


@dataclass(frozen=True)
class Rep:
    # Explicit external representation choices, not inferred from dimensions
    # of charge level sets. "bar3" is not an additional color dimension.
    color: str
    weak: int
    y: F

    def dimensions(self):
        return {"1": 1, "3": 3, "bar3": 3}[self.color], self.weak

    def indices(self):
        c, w = self.dimensions()
        need(w in (1, 2), "only weak singlet/fundamental in this dictionary")
        return (F(3, 5)*self.y**2*c*w, F(c, 2) if w == 2 else F(0),
                F(w, 2) if c == 3 else F(0))

    def conjugate(self):
        return Rep({"1": "1", "3": "bar3", "bar3": "3"}[self.color], self.weak, -self.y)


def vector_sum(*rows):
    return tuple(map(sum, zip(*rows, strict=True)))


def scale(c, row):
    return tuple(c*x for x in row)


def running(spectrum):
    # Q, u^c, d^c, L, e^c, N^c, all written as left-handed Weyl fields.
    fam = (Rep("3", 2, F(1, 6)), Rep("bar3", 1, F(-2, 3)), Rep("bar3", 1, F(1, 3)),
           Rep("1", 2, F(-1, 2)), Rep("1", 1, F(1)), Rep("1", 1, F(0)))
    external_spectrum = Counter()
    for rep in fam:
        c, w = rep.dimensions()
        external_spectrum[rep.y] += c*w
    need(spectrum == external_spectrum, "representation dictionary does not count the actual germ sites")
    indices = vector_sum(*(rep.indices() for rep in fam))
    need(indices == (2, 2, 2) and all(rep.indices() == rep.conjugate().indices() for rep in fam),
         "index sum or complex-conjugate test")
    family = scale(F(2, 3), indices)   # per two-component Weyl
    scalar = scale(F(1, 3), Rep("1", 2, F(1, 2)).indices())   # one complex scalar doublet
    gauge = scale(F(-11, 3), (0, 2, 3))
    b0 = vector_sum(gauge, scalar)
    need(family == (F(4, 3),)*3 and scalar == (F(1, 10), F(1, 6), 0), "matter normalization")
    published_b0 = scale(4, (F(1, 40), F(-43, 24), F(-11, 4)))
    need(b0 == published_b0 and family == scale(4, (F(1, 3),)*3), "published one-loop coefficients")
    b3 = vector_sum(b0, scale(3, family))
    need(b3 == (F(41, 10), F(-19, 6), -7), "SM signs and field counting")

    def differences(row):
        return row[0]-row[1], row[1]-row[2]

    d12, d23 = differences(b0)
    need(differences(family) == (0, 0) and differences(b3) == (d12, d23), "family cancellation")
    need((d12, d23, d23/d12) == (F(109, 15), F(23, 6), F(115, 218)), "common-meeting test")
    # A single multiplet threshold and a second scalar are NOT complete
    # families. Their relative slopes differ; not candidates fitted to data.
    partial = scale(F(2, 3), fam[4].indices())
    need(differences(partial) == (F(2, 5), 0) and differences(scalar) == (F(-1, 15), F(1, 6)),
         "incomplete multiplet/scalar slope controls")
    return {"Weyl_family_index_sums": indices, "one_complete_family_delta_b": family,
            "one_complex_scalar_doublet_delta_b": scalar, "gauge_delta_b": gauge, "b_at_zero_families": b0,
            "b_at_three_families": b3, "b1_minus_b2__b2_minus_b3": [d12, d23],
            "crossing_necessary_ratio_D23_over_D12": d23/d12,
            "one_extra_charged_singlet_Weyl_delta_b": partial}


def probe():
    yy, tt, yt, spectrum, frames = germ_traces()
    return {"germ": {"frames": frames, "vertex_readings": frames*16, "Tr_T3_squared": tt, "Tr_Y_squared": yy,
                     "Tr_Y_T3": yt, "mark_double_weight_T3_to_Y_norm_squared_ratio": F(6, 13)},
            "pole": pole_check(yy, tt), "one_loop": running(spectrum),
            "scope": "trace identity plus external conditional bridges; no IDT gauge coupling, scale or family count"}


if __name__ == "__main__":
    print(json.dumps(probe(), indent=2, sort_keys=True, default=str))
