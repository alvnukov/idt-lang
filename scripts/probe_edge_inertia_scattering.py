"""Reciprocal scalar spring dynamics on a star: current, dispersion, and inertia.

Each lead is a semi-infinite chain of identical masses m and springs K. The
hub has mass mu*m; all arms share its displacement. Each edge accelerates
its endpoints with equal opposite forces proportional to their displacement
difference. Displacement from rest, inertia, a clock, common scalar motion,
coherent excitation, lossless bonds and the graph are supplied. No assigned
input/output subtraction, complex state in the local update, or spatial
embedding is needed. This is a classical model, not an IDT/QM derivation.

In units K=m=1 use the real part of z_n*exp(-i omega t) and positive n
outward. Write z_n=a*exp(-iqn)+b*exp(iqn) on a lead, 0<q<pi. The interior
equation gives omega^2=2-2*cos(q); continuity gives b_i=z_0-a_i. Inserting
the first-site values in -mu*omega^2*z_0=sum(z_i1-z_0) then gives
z_0=2*sum(a_i)/[d+i*(d-2*mu)*tan(q/2)]. Relative phase refers to the same
hub plane on all leads. No power coefficient is claimed at zero group speed.

One inertia unit per site gives mu=1. One half of an inertia unit charged to
each end of each bond gives mu=degree/2 at the hub and unit mass on the
leads. Both conventions are anonymous; choosing the second by *fitting*
the desired star would not derive it. Matched response is exact across the
propagating band, not dispersionless flight. The d=3 site rule also has a
localized alternating mode ABOVE the whole lead band, accessible via a
local hub kick/displacement, not incoming on-band monochromatic scattering.

Primary comparison: Avdonin et al., arXiv:2210.09274, section 3, formula
labeled mass_cond: add (degree-2)/2 to a unit vertex mass in a DISCRETE-TIME
wave-equation discretization, aiming to reproduce metric-graph scattering.
That variational construction is not an empirical selection of mass here.
"""

from __future__ import annotations

import json
from fractions import Fraction as F
from itertools import pairwise


def need(ok, message):
    if not ok:
        raise ArithmeticError(message)


# Rational pairs are only a calculator for two real quadratures.
def add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def scale(k, z):
    return (k * z[0], k * z[1])


def mul(x, y):
    return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def bar(x):
    return (x[0], -x[1])


def norm2(x):
    return x[0] ** 2 + x[1] ** 2


def total(items):
    x = (0, 0)
    for y in items:
        x = add(x, y)
    return x


def solve(incoming, mu, t):
    """t=tan(q/2)>0; verify the answer against actual forces and energy flow."""
    d = len(incoming)
    need(d >= 2 and mu > 0 and t > 0, "only propagating leads and positive masses")
    step = ((1 - t*t) / (1 + t*t), 2*t / (1 + t*t))
    omega2 = 2 * (1 - step[0])
    denom = (d, (d - 2*mu)*t)
    coefficient = scale(F(2) / norm2(denom), bar(denom))
    hub = mul(coefficient, total(incoming))
    outgoing = [add(hub, scale(-1, a)) for a in incoming]
    force, powers = [], []
    for a, b in zip(incoming, outgoing, strict=True):
        first = add(mul(a, bar(step)), mul(b, step))
        second = add(mul(a, bar(mul(step, step))), mul(b, mul(step, step)))
        need(add(a, b) == hub, "discontinuous junction displacement")
        need(add(add(hub, second), scale(-2, first)) == scale(-omega2, first),
             "lead acceleration disagrees with bond forces")
        force.append(add(first, scale(-1, hub)))
        # Mean outward mechanical current / (K*omega/2) directly at the bond.
        current = mul(bar(hub), first)[1]
        need(current == mul(bar(first), second)[1]
             == step[1] * (norm2(b) - norm2(a)), "mechanical energy current")
        powers.append(current)
    need(total(force) == scale(-mu*omega2, hub), "hub force balance")
    need(sum(powers) == 0, "hub creates average power")
    return outgoing


def scattering_checks():
    checked = 0
    for d in range(2, 7):
        for mu in {F(1, 2), F(1), F(d, 2), F(d), F(d+1)}:
            for t in map(F, ("1/5", "1/2", "1", "2", "7")):
                for a in [[(F(i == j), F(0)) for i in range(d)] for j in range(d)] + [
                    [(F(2*i-3), F(i*i-1)) for i in range(d)]
                ]:
                    b = solve(a, mu, t)
                    ideal = [add(scale(F(2, d), total(a)), scale(-1, x)) for x in a]
                    need((b == ideal) == (2*mu == d or total(a) == (0, 0)),
                         "an off-match escaped outside the incident-zero-sum sector")
                    checked += 1
    a = [(F(1), F(0)), (F(0), F(0)), (F(0), F(0))]
    result = {}
    for name, mu in (("site", F(1)), ("half_edge", F(3, 2))):
        b = solve(a, mu, F(1))
        power = [norm2(z) for z in b]
        expected = [F(1, 5), F(2, 5), F(2, 5)] if mu == 1 else [F(1, 9), F(4, 9), F(4, 9)]
        need(power == expected and sum(power) == 1, "quarter-cycle probe")
        result[name] = {
            "displacement_quadratures": [[str(x) for x in z] for z in b],
            "outgoing_energy_fractions": list(map(str, power)),
        }
    return {"verified_inputs": checked, "d3_single_incident_q_pi_over_two": result}


def localized_mode():
    # Above-band decay requires r<0, |r|<1 on every semi-infinite lead.
    # Continuity fixes its prefactor to the hub value; a zero hub implies
    # an identically zero decaying solution. Eliminate omega^2 from the
    # two force equations: mu*(1-1/r)=d, so only 0<mu<d/2 can bind.
    d, mu, r = 3, F(1), F(-1, 2)
    omega2 = 2 - r - 1/r
    need(omega2 == F(9, 2) and mu*omega2 == d*(1-r), "localized hub acceleration")
    for n in range(1, 18):
        need(-omega2*r**n == r**(n-1) - 2*r**n + r**(n+1), "localized lead")
    mode_mass = mu + d*r*r / (1-r*r)
    projection = mu / mode_mass
    need(projection == F(1, 2), "hub-only initial displacement projection")
    # Independent finite Dirichlet trial: K quadratic form / M quadratic form.
    # For half-edge masses, (u-v)^2 <= 2(u^2+v^2) gives <=4 for ALL trials.
    profile = [r**n for n in range(6)] + [F(0)]
    stiffness = d * sum((a-b)**2 for a, b in pairwise(profile))
    arm_mass = d * sum(v*v for v in profile[1:-1])
    quotients = [stiffness / (m0+arm_mass) for m0 in (mu, F(d, 2))]
    need(quotients[0] > 4 >= quotients[1], "finite-domain above-band control")
    return {
        "d3_site_mode_neighbor_to_parent_displacement": str(r),
        "squared_frequency_in_K_over_m": str(omega2),
        "lead_band_upper_squared_frequency": 4,
        "unit_hub_displacement_bound_component_at_hub": str(projection),
        "five_live_sites_per_arm_dirichlet_rayleigh_site_then_half_edge": list(map(str, quotients)),
        "half_edge_above_band_mode": False,
    }


def vacancy_control():
    # Same topology, no springs: each bond just swaps two occupancy bits at
    # rate gamma. The net transfer rate for a given state is gamma*(eta_u-eta_v)
    # even when occupancies are correlated. Thus the mean generator is -gamma L.
    # The spring model on equal sites has second derivative -(K/m)L instead.
    decay, ratio, bias = F(9, 2), F(-1, 2), F(1, 4)
    for u in (0, 1):
        for v in (0, 1):
            need(u*(1-v) - v*(1-u) == u-v, "vacancy transfer closure")
    for n in range(17):
        delta = bias * ratio**n
        rho = F(1, 2) + delta
        neighbors = (delta*ratio,) * 3 if n == 0 else (delta/ratio, delta*ratio)
        need(0 <= rho <= 1 and sum(x-delta for x in neighbors) == -decay*delta,
             "same staggered mode must solve the unsigned density generator")
    return {
        "preparation": "mean occupancy 1/2+(1/4)*(-1/2)^n on unfed equal-rate star; spring comparator initially at rest with same displacement contrast",
        "hub_contrast_factor_vacancy": "exp[-(9/2)*gamma*t]",
        "hub_contrast_factor_site_inertia": "cos[sqrt((9/2)*K/m)*t]",
        "discriminator": "spatial staggering alone fits both; after release only the spring contrast changes sign in this prepared free mode",
        "not_excluded": "forced or delayed vacancy hardware; short/damped data need not resolve sign reversal",
    }


def probe():
    return {
        "reciprocal_vacancy_control": vacancy_control(),
        "scattering": scattering_checks(),
        "local_excitation": localized_mode(),
        "scope": "lossless classical scalar dynamics on supplied equal chains; energy is not an event probability",
        "controls": "use a hub excitation to see the bound mode; zero-sum incoming drives hide hub inertia; identical long leads and equal low-q limits alone do not identify the mass assignment",
    }


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True))
