"""Exchange topology, two-source partition noise and a distinguishability intervention.

Two hard-core occupations on a Y admit a path swapping their ordered lift.
Both trivial and negative characters are possible. The graph alone does
not choose a particle, a character, a coherent splitter, an internal state
or a detector law. The lab below is NOT an implementation of the Y paths.

Conditional comparator: precisely one same-charge particle per input,
reciprocal lossless energy-independent splitter, independent incoming
internal/temporal states, coherent addition of the two assignments with
supplied character eta, Born readout, no two-body forces. For product tags
v=|<a|b>|² in [0,1]. Compared to independent random partition at the same
splitter, output number variance has ratio 1+eta*v. One particle at a
time gives no exchange term; being unable to double-load a SOURCE, or
observing one source's shot noise, is not this two-input comparison.
Perfectly distinguishable tags erase the difference, even at equal input
energies. Spin-entangled inputs can change the sign of the tag-swap
expectation; do not read out intrinsic statistics from an arbitrary input.

Primary empirical comparators, reporting summary numbers rather than raw
coincidence data. None is a model-independent measurement of a graph
character or a direct fit of an unrestricted exchange phase:

1. Bocquillon et al., Science 339 (2013) 1054, doi:10.1126/science.1232572,
   https://arxiv.org/html/1301.7093, Eqs. (2)-(3), Fig. 3 and discussion.
   Independent mesoscopic capacitors emit an electron then a hole per
   drive period (2.1 GHz) on outer quantum Hall edge channels. The output
   QPC has transmission 1/2. It measures low-frequency single-output
   excess current noise (on minus both-off baseline), not a histogram of
   individual electron pairs. A hole here is a Fermi-sea excitation.
   Independently switched one-source partition noises sum to the delayed
   two-source plateau. The normalized exponential dip fit has depth
   0.45 +/- 0.05, width parameter 62 +/- 10 ps and center 13 +/- 6 ps.
   Hence 0.55 +/- 0.05 is the INFERRED ratio at the fitted center, not a
   separately measured count or zero-delay bin. The dot transmission,
   also quoted as 0.45 +/- 0.05, is a different parameter. At ~240 ps a
   hole meets an electron and the noise is consistent with random partition.
   This disfavors a simple like-charge repulsion/unlike-charge attraction
   explanation of the low-noise feature; it does not exclude all correlated
   routing or Coulomb-induced decoherence. Fermi sea, finite temperature,
   normalization, nonidentical source energies and coherence limit matter.

2. Preiss et al., Phys. Rev. Lett. 122 (2019) 143602,
   https://arxiv.org/html/1811.12939, Fig. 2; Supplemental Methods.
   Separate apparatus/species/estimand: same-spin 6Li atoms released from
   two tweezers 1.7 micrometers apart, joint momenta from time of flight.
   Each well is prepared with one of each of two spin states; spin images
   are separated and analyzed as two realizations, not as an entangled
   singlet/triplet comparison. Interspin scattering tuned to its zero;
   the authors checked that the two spin manifolds were uncorrelated. Number postselection
   is used. Spin-resolved exchange fringes in relative momentum have a
   damped-cosine fit contrast 79(2)%. Below 30 micrometers separation
   coincident images are unreliable and were excluded, so the node at
   zero is NOT a measured zero. This is not a second electron dip or a
   directly measured exchange angle. Do not pool the two contrasts.

3. Fletcher et al., Nat. Nanotechnol. (2023), doi:10.1038/s41565-023-01369-4,
   https://arxiv.org/html/2210.03473, Figs. 3-4. In a different high-energy
   electron collider the peak partition noise is suppressed by up to about
   30% near synchrony (no uncertainty quoted on that approximate maximum
   in the corresponding text). Barrier dependence, mean currents and
   reconstructed partition statistics favor a Coulomb-dominated account.
   A genuine control against interpreting any electronic noise dip as
   exchange; not a contradictory replication at the same source energies.

Only the idealized models below are replayed; no raw-event reconstruction,
confidence calculation, experimental likelihood, graph selection, or new
measurement. Run: python3 -B [-O] -m scripts.probe_fermion_exchange_intervention
"""

from __future__ import annotations

import json
from fractions import Fraction as F
from itertools import product

from scripts import probe_collision_free_exchange_paths as graph_exchange


def need(ok, why):
    if not ok:
        raise ArithmeticError(why)


def topology():
    g = graph_exchange.check_graphs()
    x, swapped = graph_exchange.trace(graph_exchange.EXCHANGE, g)
    r, returned = graph_exchange.trace(graph_exchange.REFERENCE, g)
    need(swapped == returned[::-1] and returned == graph_exchange.RING[0], "wrong lift")
    need(graph_exchange.key_for(graph_exchange.EXCHANGE, x) ==
         graph_exchange.key_for(graph_exchange.REFERENCE, r), "unmatched path nuisance")
    # On the two ordered sheets the permutation exchanges components, so
    # both vectors (1,eta) are eigenvectors. Neither is selected by the lift.
    for eta in (-1, 1):
        state = (1, eta)
        need(state[::-1] == tuple(eta*z for z in state), "not a transposition character")
    return {"moves_each": len(x), "ordered_reversal": True, "possible_real_characters": [-1, 1]}


def moments(prob):
    """Number at output 1, given exactly two incident particles."""
    need(len(prob) == 3 and sum(prob) == 1 and min(prob) >= 0, "invalid count distribution")
    mean = sum(n*p for n, p in enumerate(prob))
    return mean, sum((n-mean)**2*p for n, p in enumerate(prob))


def count_law(t, eta, swap_expectation):
    """Use only with an independently calibrated splitter and specified tags."""
    if not 0 <= t <= 1 or eta not in (-1, 1) or not -1 <= swap_expectation <= 1:
        raise ValueError("invalid two-input model")
    w = t*(1-t)*(1+eta*swap_expectation)
    return w, 1-2*w, w    # n=0,1,2.


def amplitudes(matrix, norm, eta, tag):
    # Each integer column divided by sqrt(norm) is a normalized port
    # amplitude. Two-port amplitude products have rational denominator
    # norm. Explicitly trace the two unobserved tags on each output.
    need(all(sum(matrix[k][i]*matrix[k][j] for k in range(2)) == norm*(i == j)
             for i, j in product(range(2), repeat=2)), "not a unitary splitter")
    a, b = (1, 0), tag
    need(sum(x*x for x in b) == 1, "uncalibrated tag")
    probs = [F(0)]*3
    for i, j, s, u in product(range(2), repeat=4):
        direct = matrix[i][0]*matrix[j][1]*a[s]*b[u]
        exchanged = matrix[i][1]*matrix[j][0]*b[s]*a[u]
        # Orthogonal input ports give squared symmetrizer norm exactly 2.
        probs[(i == 0)+(j == 0)] += F((direct+eta*exchanged)**2, 2*norm**2)
    return tuple(probs)


def quantum_controls():
    cases = 0
    for matrix, norm in ((((1, 1), (1, -1)), 2), (((3, 4), (4, -3)), 25)):
        t = F(matrix[0][0]**2, norm)
        for eta, tag in product((-1, 1), ((1, 0), (0, 1), (F(3, 5), F(4, 5)))):
            v = tag[0]**2
            p = amplitudes(matrix, norm, eta, tag)
            need(p == count_law(t, eta, v), "explicit path amplitudes")
            mean, var = moments(p)
            need(mean == 1 and var/(2*t*(1-t)) == 1+eta*v, "normalized variance")
            cases += 1
    balanced = F(1, 2)
    far = count_law(balanced, -1, 0)
    need(far == count_law(balanced, 1, 0) == (F(1, 4), F(1, 2), F(1, 4)),
         "distinguishable arrivals")
    # An antisymmetric two-spin tag has swap expectation -1; product
    # tag assumptions matter even with a known fermionic transposition.
    spin = {(0, 1): 1, (1, 0): -1}
    expectation = F(sum(v*spin[j, i] for (i, j), v in spin.items()), sum(v*v for v in spin.values()))
    need(count_law(balanced, -1, expectation) == count_law(balanced, 1, 1), "spin singlet control")
    # A pair of perfect antibunched single-particle SOURCES alone is
    # compatible with all three laws: distinguishable, even, and odd.
    return {"squared_amplitude_checks": cases, "balanced_delayed_n0_n1_n2": far,
            "perfect_product_tags_even": count_law(balanced, 1, 1),
            "perfect_product_tags_odd": count_law(balanced, -1, 1)}


def classical_routes(mode, strength):
    """Two fair output marginals; choose independent, correlated or anticorrelated routes."""
    if mode not in ("split", "group", "independent") or not 0 <= strength <= 1:
        raise ValueError("invalid classical routing")
    joint = {}
    for i, j in product(range(2), repeat=2):
        correlated = F(1, 4) if mode == "independent" else F((i != j) == (mode == "split"), 2)
        joint[i, j] = (1-strength)*F(1, 4)+strength*correlated
    need(all(sum(p for key, p in joint.items() if key[n] == 1) == F(1, 2) for n in (0, 1)), "marginal")
    return joint


def normalized_noise(joint, q1, q2):
    # Toy per-collision output charge, not a reanalysis of AC Fermi-sea
    # noise. Baseline = variance of two independently fair charges.
    obs = {(i, j): q1*i+q2*j for i, j in joint}
    mean = sum(obs[z]*p for z, p in joint.items())
    return sum((obs[z]-mean)**2*p for z, p in joint.items()) / F(q1*q1+q2*q2, 4)


def noise_controls():
    # A legitimate correlated classical mechanism mimics an entire
    # fermionic curve if its strength follows the delay-dependent overlap.
    # This is an explicit ambiguity, not a fitted cause in the apparatus.
    for v in (F(0), F(1, 4), F(1, 2), F(1)):
        routings = classical_routes("split", v)
        count = tuple(sum(p for (i, j), p in routings.items() if i+j == n) for n in range(3))
        need(count == count_law(F(1, 2), -1, v) and normalized_noise(routings, 1, 1) == 1-v,
             "classical correlated routing")
        # Toy symmetric-Coulomb picture: like charges split, unlike group;
        # either gives low net output-charge noise at its synchronized time.
        need(normalized_noise(classical_routes("group", v), 1, -1) == 1-v, "unlike attraction")
        # A charge-selective device that leaves unlike arrivals independent
        # also reproduces the half-period control; not all alternatives die.
        need(normalized_noise(classical_routes("independent", v), 1, -1) == 1, "unlike independent")
    # A positive dip depth is a signed contrast against a delayed baseline.
    # For product tags the even/uncorrelated models give depth <=0/zero;
    # electronics causing delay-dependent correlated routes are not in them.
    gamma, err = F("0.45"), F("0.05")
    need(0 < gamma-err < gamma+err < 1, "descriptive reported error interval")
    # Even a coherent two-route *intensity* at one phase setting generally
    # fixes only v*cos(phi). Allow a continuous uncalibrated route phase:
    # phi=pi and phi=2*pi/3 give exactly the same fitted center for
    # different admissible v. This is an identifiability counterexample
    # for one scalar, NOT a new unitary anyon scattering theory.
    alternatives = ((gamma, F(-1)), (2*gamma, F(-1, 2)))
    need(all(0 <= v <= 1 and 1+v*cosine == 1-gamma for v, cosine in alternatives), "phase visibility tradeoff")
    return {"electron_reported_fit_depth_error": ["0.45", "0.05"],
            "normalized_noise_at_fitted_center_derived_error": [f"{float(1-gamma):.2f}", f"{float(err):.2f}"],
            "fitted_time_parameter_ps": [62, 10], "fitted_center_ps": [13, 6],
            "opposite_charge_half_period_ps_approx": 240,
            "same_noise_two_route_visibility_cosine_examples": alternatives,
            "ambiguity": "even and independent product-tag splitter not a dip; correlated classical routing can be"}


def correlation_controls():
    # Equal-amplitude direct and exchange paths in far-field detection
    # from two fixed wells: relative phase a*(k1-k2), arbitrary common
    # baseline divided out. At d=k_lat and 2*k_lat the cosines are -1
    # and +1. This ideal two-bin identity uses NO unresolved d=0 bin.
    # These numbers ARE NOT extracted counts, fitted bins or a replay of
    # the paper's finite envelope, resolution and momentum calibration.
    for eta, v in product((-1, 1), (F(0), F(1, 2), F(1))):
        odd, even = 1-eta*v, 1+eta*v
        need((odd-even)/(odd+even) == -eta*v, "relative-momentum sign")
    # For a fixed number of two same-charge particles, mean plus variance
    # recovers all three count probabilities; the noise alone need not.
    for row in ((F(1, 8), F(3, 4), F(1, 8)), (F(0), F(1, 4), F(3, 4)),
                (F(3, 4), F(1, 4), F(0))):
        mu, var = moments(row)
        p2 = (var+mu*mu-mu)/2
        recovered = (1-mu+p2, mu-2*p2, p2)
        need(recovered == row, "charge-partition reconstruction")
    a, b = (F(0), F(1, 4), F(3, 4)), (F(3, 4), F(1, 4), F(0))
    need(moments(a)[1] == moments(b)[1] and moments(a)[0] != moments(b)[0], "noise-only ambiguity")
    return {"Li6_fitted_contrast_percent_and_error": [79, 2], "Li6_unresolved_below_um": 30,
            "hot_electron_peak_noise_suppression_up_to_approx_percent": 30,
            "different_regime": "Coulomb-dominated; no error stated on approximate maximum, no pooled contrast"}


def probe():
    return {"topology": topology(), "conditional_quantum": quantum_controls(), "two_source_noise": noise_controls(),
            "independent_comparators": correlation_controls(),
            "scope": "finite comparator plus external published summaries, not a Pauli derivation or a phase measurement"}


if __name__ == "__main__":
    print(json.dumps(probe(), default=str, indent=2, sort_keys=True))
