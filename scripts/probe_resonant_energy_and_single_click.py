"""Where positive viscous absorbers take resonant ENERGY, versus one indivisible click.

On the supplied equal-spring/equal-mass clamped graph, prepare the pure driven
top spatial mode x_v(t)=u(t) q_v/20. With identical positive local viscous
drag c, instantaneous power is c*x'_v(t)^2: over ANY common time interval
with positive dissipation the local ENERGY fraction is q_v^2/sum q^2.
Uniform drag preserves a freely prepared single mode even if not weak. To
select this shape by a harmonic drive at a single site, other modes have to
be removed: measure steady response at the top frequency and take weak drag,
or prepare the mode itself. At nonzero drag the full driven fractions need
not equal the pure limit. A clamped zero has no moving absorber power.
Drive/clamp order, scalar motion, preparation, common positive calibration,
suitable observation window and gain are supplied. This is NOT a probability
law for one whole event. Detecting local energy can give several responses.

For the splitter null let H be a valid upstream herald, declared without
looking at either output. Given H and a SINGLE shared scalar integrated
input I, a stable fixed splitter and two independent local click channels
have E[X|I,H]=f(I), E[Y|I,H]=g(I), both nondecreasing. Then
 Cov(X,Y|H)=E[(f(I)-f(J))*(g(I)-g(J))|H]/2 >= 0
for an independent conditional copy J. This includes saturating response,
thresholds and independent constant dark backgrounds. The *population*
alpha=P11/(P1*P2) is >=1 when both marginals are positive. It is undefined
otherwise. The null does not include unrecorded correlated readiness, jointly
vetoing double counts, a second coherent input, or a randomly switching split.
Conditioning on an output, or dropping the valid no-click heralds, changes
the estimand. Report such changes; never use them to repair a trial. Finite
samples can fluctuate below one without violating the population result.

A single allocated packet can suppress coincidences by construction. A
phase-blind packet with no other influence at a phase-independent recombiner
has no phase fringe. More generally, after an independent choice of which
arm is occupied, if only its own phase can affect a packet and no signal,
memory or second excitation carries the other arm's setting, the unconditional
one-port probability is p*f(a)+(1-p)*g(b). Two independently varied late
arm phases have zero mixed contrast. This is a proposed restricted-model
control, NOT the 1986 phase scan. A one-knob fringe need not violate this
broader model, and no universal exclusion of corpuscles or classical physics
is claimed. The two 1986 configurations are not simultaneous per-shot tests.
"""

import json
from collections import Counter
from fractions import Fraction as F
from itertools import combinations_with_replacement, product
from math import lcm

from scripts.probe_marked_carrier_charge import anonymous_fixture
from scripts.probe_passive_carrier_resonance import (
    eye,
    mix,
    modal,
    mul,
    mv,
    solve,
    stiffness,
)


def need(test, why):
    if not test:
        raise AssertionError(why)


def energy():
    g = anonymous_fixture()
    summary = None
    finite = None
    frames = 0
    for root in sorted(g):
        sites, d = stiffness(g,root)
        _,p8 = modal(d)
        for target in sorted(set(sites)-g[root]):
            t = sites.index(target)
            residue = [F(row[t],40) for row in p8]
            unit = lcm(*(x.denominator for x in residue))
            q = [int(x*unit) for x in residue]
            q_all = [*q,0]  # the missing pinned site
            norm = sum(x*x for x in q_all)
            classes = Counter(q_all)
            report = {k:(count,F(k*k,norm),F(count*k*k,norm)) for k,count in classes.items()}
            need(unit == 20 and norm == 120 and sum(x[2] for x in report.values()) == 1,
                 "mode norm and energy accounting")
            if summary is None:
                summary = report
            need(report == summary, "equivariant source frames have different energy histograms")
            frames += 1
            if finite is None:
                # Exact equal-drag steady-state response in the two real
                # quadratures of i*delta*(D-8I+i*delta*I)^-1 e_target.
                h = mix((1,d),(-8,eye(len(d))))
                delta = F(1,32)
                y = solve(mix((1,mul(h,h)),(delta**2,eye(len(d)))),eye(len(d))[t])
                re, im = [delta**2*a for a in y], [delta*a for a in mv(h,y)]
                power = [a*a+b*b for a,b in zip(re,im,strict=True)]
                total = sum(power)
                tv = sum(abs(a/total-F(b*b,norm)) for a,b in zip(power,q,strict=True))/2
                # Orthogonal error e has ||e||²<=7/16010, ||residue||²=3/10.
                # For normalized complex vectors, TV of squared magnitudes
                # <=sqrt(1-|overlap|²), by Cauchy-Schwarz on (|a|+|b|)(|a|-|b|).
                bound2 = F(7,4810)
                need(0 < tv*tv <= bound2, "finite drag should perturb the shares within the bound")
                finite = {"dimensionless_drag":str(delta),"actual_total_variation":str(tv),
                          "certified_upper_bound_on_TV_squared":str(bound2)}
    # Equal mean share, deliberately different single-shot support. The two
    # externally grouped banks contain the negative and positive mode sites.
    # Choosing a unit with these probabilities is a countermodel, not a mechanism.
    left = sum(total for q,(_,_,total) in summary.items() if q<0)
    right = sum(total for q,(_,_,total) in summary.items() if q>0)
    need((left,right) == (F(11,20),F(9,20)), "two-bank power balance")
    return {"frames":frames,"sum_of_q_squared":120,
            "sectors":[{"q":q,"sites":n,"fraction_per_site":str(one),"fraction_of_total_sector":str(total)}
                       for q,(n,one,total) in sorted(summary.items())],
            "same_mean_two_bank_controls":{
                "mean_energy_both_models":[str(left),str(right)],
                "fixed_wave_energy_covariance":"0","whole_unit_allocation_energy_covariance":str(-left*right),
                "ideal_positive_energy_detectors":{
                    "divided_wave":describe((F(0),F(0),F(0),F(1))),
                    "externally_sampled_whole_unit":describe((F(0),right,left,F(0)))}},
            "finite_drag_steady_state_example":finite}


def mixture(rows):
    """Independent armed detectors at given latent conditions, in 00,01,10,11 order."""
    need(sum(w for w,_,_ in rows) == 1 and all(w>=0 and 0<=a<=1 and 0<=b<=1 for w,a,b in rows),
         "not a probability mixture")
    return tuple(sum(w*(a if x else 1-a)*(b if y else 1-b) for w,a,b in rows)
                 for x,y in product((0,1),repeat=2))


def alpha(t):
    _none,right,left,both = t
    need(sum(t) == 1 and min(t) >= 0, "joint herald ledger did not sum to one")
    p,q = left+both,right+both
    return None if not p*q else both/(p*q)


def describe(t):
    a = alpha(t)
    return {"probabilities_00_01_10_11":[str(p) for p in t],"alpha":None if a is None else str(a)}


def clicks():
    levels = (F(0),F(1,2),F(1))
    weights = (F(1,6),F(1,3),F(1,2))  # arbitrary herald-conditional input law
    maps = list(combinations_with_replacement(levels,3))
    checked = undefined = 0
    for f,g in product(maps, repeat=2):
        t = mixture(list(zip(weights,f,g,strict=True)))
        p,q = t[2]+t[3],t[1]+t[3]
        sym = sum(weights[i]*weights[j]*(f[i]-f[j])*(g[i]-g[j]) for i,j in product(range(3),repeat=2))/2
        need(t[3]-p*q == sym >= 0 and (alpha(t) is None or alpha(t) >= 1), "monotone common-drive null")
        checked += 1
        undefined += alpha(t) is None
    half, quarter = F(1,2),F(1,4)
    fixed = mixture([(F(1),quarter,F(3,4))])
    threshold = mixture(list(zip(weights,(F(1,8),F(1,8),F(1)),(F(1,4),F(1,2),F(1,2)),strict=True)))
    # Varying the splitter routes all light to one arm, despite one source;
    # equivalently an external readiness flag can enable only one detector.
    # The second explicit model retains independent darks when an arm is disabled.
    split = mixture([(half,1,0),(half,0,1)])
    readiness_dark = mixture([(half,1,quarter),(half,quarter,1)])
    # With two equal-probability relative phases 0/pi on inputs (1,+/-1/2)
    # of a fixed balanced splitter, both outputs are illuminated, but their
    # intensities are in ratios 9:1 or 1:9. Model linear click means at this gain.
    two_inputs = mixture([(half,F(9,10),F(1,10)),(half,F(1,10),F(9,10))])
    raw = mixture([(F(1),half,half)])
    # Shared first-click-only electronics misreports genuine raw doubles;
    # explicitly retain the raw table and the fraction modified.
    veto = (raw[0],raw[1]+raw[3]/2,raw[2]+raw[3]/2,F(0))
    conditioned = (F(0),*(x/(1-raw[0]) for x in raw[1:]))
    # One indivisible route with 1/2 detection efficiency and independent
    # dark probability 1/4 PER ARM. Keep all heralds, including no detections.
    hit_if_allocated = 1-(1-half)*(1-quarter)
    lossy_exclusive = mixture([(half,hit_if_allocated,quarter),(half,quarter,hit_if_allocated)])
    checks = {"fixed_unequal_split":fixed,"threshold_saturation_independent_dark_floors":threshold,
              "random_exclusive_split_or_ideal_whole_packet":split,
              "shared_complementary_readiness_with_darks":readiness_dark,"two_coherent_inputs":two_inputs,
              "raw_independent_before_electronic_veto":raw,"shared_first_click_only_veto":veto,
              "incorrectly_drop_valid_no_click_heralds":conditioned,"lossy_whole_packet_plus_darks":lossy_exclusive}
    need(alpha(fixed)==alpha(raw)==1 and alpha(threshold)>1 and alpha(split)==alpha(veto)==0 and
         alpha(readiness_dark)==F(16,25) and alpha(two_inputs)==F(9,25) and
         alpha(conditioned)==F(3,4) and 0<alpha(lossy_exclusive)<1, "joint-table controls")
    return {"ordered_response_pairs_checked":checked,"undefined_zero_marginal_cases":undefined,
            "joint_controls":{key:describe(t) for key,t in checks.items()},
            "raw_fraction_vetoed":str(raw[3]),"raw_no_click_fraction_wrongly_discarded":str(raw[0]),
            "rule":"count every predeclared valid upstream herald; unavailable gate/readout is flagged, "
                   "not inferred to be a no-click or discarded based on its output"}


def fringe():
    vals = (F(0),F(1,2),F(1))
    target = (1,0,0,1)  # cos^2((a-b)/2), a,b each chosen as 0 or pi
    scores = []
    for p,f0,f1,g0,g1 in product(vals,repeat=5):
        table = [p*f+(1-p)*g for f,g in product((f0,f1),(g0,g1))]
        contrast = table[0]-table[1]-table[2]+table[3]
        err = max(abs(x-y) for x,y in zip(table,target,strict=True))
        need(contrast == 0 and err >= F(1,2), "restricted path-only late-phase countercontrol")
        scores.append(err)
    need(min(scores) == F(1,2), "flat fair splitter should attain the restricted bound")
    return {"independently_chosen_arm_phases":["0","pi"],"ideal_balanced_MZ_one_port":target,
            "restricted_path_mixed_contrast":0,"target_mixed_contrast":2,
            "supnorm_error_lower_bound_from_contrast":"1/2","exact_grid_models":len(scores),
            "status":"proposed comparison under no unoccupied-arm influence; not an analysis of four measured settings"}


def evidence():
    # Verified transcriptions only. No raw gates, fit, invented error bars,
    # cross-experiment pooling, or inference of one four-cell ledger from rounded rates.
    return {"grangier_roger_aspect_1986":{
        "doi":"10.1209/0295-5075/1/4/004",
        "primary_pdf":"https://courses.physics.illinois.edu/phys513/sp2016/reading/week1/GrangierSinglePhoton1986.pdf",
        "primary_pdf_sha256":"e3365f01f784a9b01181c62d00ae7b4600853b73d931c5faa1af4cfcab7225d7",
        "locator":"pp. 174-178, Figs. 1-5; conditional PM singles and coincidences per upstream cascade trigger",
        "gate_width_ns":9,"alpha":"0.18","alpha_one_standard_deviation":"0.06",
        "wall_counting_duration_approx_hours":5,"observed_coincidences":9,"classical_expected_coincidences_at_least":50,
        "approx_trigger_rate_per_second":8800,"included_trigger_dark_rate_per_second":300,
        "full_raw_joint_herald_table_available_here":False,
        "separate_Mach_Zehnder_configuration":{"gated_visibility":"greater than 98 percent",
            "gated_visibility_dark_correction":"smaller than 0.3 percent as reported, Fig. 5",
            "ungated_alignment_visibility_percent":"98.7 +/- 0.5; not a gated sample"},
        "experimental_control":"pulsed diode at matched trigger and singles probabilities obeyed classical bound"},
        "chou_polyakov_kuzmich_kimble_2004":{
        "doi":"10.1103/PhysRevLett.92.213601","author_source":"https://arxiv.org/abs/quant-ph/0401147",
        "author_tex_sha256":"d469a0456709df6322951fabe363bcf804ad666d76396bfbcb7e5529f6774928",
        "locator":"atomic ensemble, Fig. 4(b); same-trial herald field 1, conditional field 2",
        "reported_w":"p^(1)(1) * p^(3)(1,2,2) / p^(2)(1,2)^2 using their pooled detector estimators",
        "points":[{"storage_delay_ns":0,"w":"0.24","reported_statistical_uncertainty":"0.05"},
                  {"storage_delay_ns":150,"w":"0.34","reported_statistical_uncertainty":"0.06"}],
        "background":"no dark-count or other background correction in Fig. 4; different-trial control in panel (a)",
        "raw_time_tags_reanalysed":False,"same_estimator_as_literal_2x2_ledger_asserted":False}}


def probe():
    return {"scope":"energy transfer, single-event null and primary published comparisons are distinct",
            "resonant_energy":energy(),"heralded_clicks":clicks(),"late_fringe_control":fringe(),
            "published_summaries_not_raw_data":evidence()}


if __name__ == "__main__":
    print(json.dumps(probe(),separators=(",",":")))
