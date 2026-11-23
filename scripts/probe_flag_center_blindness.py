"""Which global center choices can the marked five-flag readout distinguish?

Input from the finite carrier: even occupations of five slots split 3+2,
counts C,W and the calibrated integer ballot q=-2C+3W. SUPPLY, for this
comparison, a compact product SU(3) x SU(2) x U(1) with a 2*pi-periodic
angle, fundamental center convention exp(2*pi*i*C/3), (-1)^W, and U(1)
character q. The graph does not produce those continuous groups, their
actions, a gauge connection, or genuine electric or magnetic line probes.

The common central kernel K=<xi> of order six, xi=(omega_3,-1,exp(2*pi*i/6)),
already occurs with a supplied block action in probe_five_slot_charge.
Here we ask what ALL products of the local labels cannot see. Put
delta=2*t3+3*t2+q mod 6 for any external electric center label. A quotient
by the subgroup of order d in K admits it exactly when d divides delta.
Local labels have delta zero; their additive combinations span EXACTLY
the zero-defect labels at the center-character level, not necessarily all
full representations or realizable compounds. Exact integer conservation
of q in a selected reaction is a distinct condition from delta=0 on its
input and output labels.

For the external comparison see David Tong, "Line Operators in the
Standard Model", https://doi.org/10.1007/JHEP07(2017)104, section 3
(author paper: https://arxiv.org/abs/1705.01853). We check the electric
and purely magnetic CENTER classes at vanishing theta with Tong's minus
sign for q*g in the Dirac pairing. This is not a classification of dyons,
noncentral weights, confinement, global anomalies or bundle sums. Wilson
lines describe external probes, not a promise of finite-mass particles.
The distinct neutron-charge test in probe_neutron_charge_anchor imports
additional representations and an electromagnetic readout; it does not
measure the four global forms. No empirical global-form choice is made.
"""

import json
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import gcd


def need(ok, why):
    if not ok:
        raise ArithmeticError(why)


def occupation(mask):
    return (mask & 7).bit_count(), (mask >> 3).bit_count()


MASKS = tuple(i for i in range(32) if i.bit_count() % 2 == 0)
RESIDUES = tuple(product(range(3), range(2), range(6)))
DIVISORS = (1, 2, 3, 6)


def character(mask, a=-2, b=3):
    c, w = occupation(mask)
    return c % 3, w % 2, a * c + b * w


def defect(e):
    t3, t2, q = e
    return (2 * t3 + 3 * t2 + q) % 6


def add(e, f):
    return (e[0] + f[0]) % 3, (e[1] + f[1]) % 2, e[2] + f[2]


def turns(h, e):
    a, b, z = h
    return (F(a * e[0], 3) + F(b * e[1], 2) + z * e[2]) % 1


def kernel(labels):
    # A local (t3,t2,q)=(1,1,1) forces the U(1) phase for each of the six
    # possible non-Abelian centers; no continuous angles are skipped.
    need((1, 1, 1) in labels, "missing primitive character anchor")
    candidates = {
        (a, b, (-F(a, 3) - F(b, 2)) % 1) for a, b in product(range(3), range(2))
    }
    return {h for h in candidates if all(turns(h, e) == 0 for e in labels)}


def local_center():
    es = tuple(character(i) for i in MASKS)
    k = kernel(es)
    diagonal = {(j % 3, j % 2, F(j, 6)) for j in range(6)}
    need(
        len(es) == 16 and k == diagonal and all(defect(e) == 0 for e in es),
        "central kernel",
    )
    need(
        gcd(*(e[2] for e in es)) == 1 and sum(a == b == 0 for a, b, _ in k) == 1,
        "pure compact U(1) should act faithfully in this normalization",
    )
    # Even without formally adjoining antiparticles, +1 and -3 can
    # synthesize any integer q as an abstract additive center label.
    # Negative n=-3k+r, k=ceil(-n/3), 0<=r<=2.
    unit, negthree = (1, 1, 1), (0, 1, -3)
    need(unit in es and negthree in es, "additive generators")
    for n in range(-24, 25):
        l = 0 if n >= 0 else (-n + 2) // 3
        r = n + 3 * l
        value = (0, 0, 0)
        for e in (unit,) * r + (negthree,) * l:
            value = add(value, e)
        need(
            value == (n % 3, n % 2, n) and all(turns(h, value) == 0 for h in k),
            "compound not at predicted label",
        )
    two = {add(e, f) for e, f in product(es, repeat=2)}
    need(
        {q % 6 for _, _, q in two} == set(range(6))
        and all(defect(e) == 0 for e in two),
        "some two-packet center residue missing or spuriously charged",
    )
    return {
        "sixteen_mask_character_multiplicities": sorted(
            (list(e), n) for e, n in Counter(es).items()
        ),
        "central_kernel_order": len(k),
        "independent_pure_U1_kernel_order": 1,
        "additive_local_center_label_lattice": "(q mod 3,q mod 2,q), all integer q formally",
        "distinct_mod_six_abelian_residues_on_two_packet_labels": 6,
    }


def dirac(e, m):
    # h=6*g mod 6, not g in integer units. This convention is important:
    # endpoint xi^k corresponds to (m3,m2,6g)=(k mod 3,k mod 2,-k mod 6)
    # in Tong's electric-minus-Abelian-magnetic pairing.
    t3, t2, q = e
    m3, m2, h = m
    return (2 * t3 * m3 + 3 * t2 * m2 - q * h) % 6


def quotient_rows():
    rows = {}
    for d in DIVISORS:
        # xi^(6/d) generates the subgroup of order d. Electric labels
        # repeat under q -> q+6. In particular the pure singlet q=d is a
        # genuine representation, forcing d*g integral for a mutually
        # local magnetic line. Hence the h=6*g residue grid is exhaustive.
        powers = tuple(range(0, 6, 6 // d))
        groups = {(k % 3, k % 2, F(k, 6)) for k in powers}
        electric = {e for e in RESIDUES if all(turns(h, e) == 0 for h in groups)}
        need(
            electric == {e for e in RESIDUES if defect(e) % d == 0}
            and len(electric) == 36 // d,
            "electric descent condition",
        )
        magnetic = {m for m in RESIDUES if all(dirac(e, m) == 0 for e in electric)}
        need(
            magnetic == {(k % 3, k % 2, -k % 6) for k in powers} and len(magnetic) == d,
            "magnetic annihilator or orientation",
        )
        need(
            {e for e in RESIDUES if all(dirac(e, m) == 0 for m in magnetic)}
            == electric,
            "magnetic labels lost the electric lattice",
        )
        expected_defects = set(range(0, 6, d))
        need(
            {defect(e) for e in electric} == expected_defects
            and all(
                sum(defect(e) == v for e in electric) == 6 for v in expected_defects
            ),
            "classes modulo local compound labels",
        )
        singlets = [q for q in range(1, 7) if (0, 0, q % 6) in electric]
        hmin = 6 // d
        at_min = sorted((m3, m2) for m3, m2, h in magnetic if h == hmin % 6)
        need(
            min(singlets) == d and len(at_min) == 1,
            "least fractional flux or singlet generator",
        )
        # If a hypothetical connection has central holonomy xi K_d, its
        # phase on the genuine singlet q=d is d/6 turns. This does not
        # supply that connection, its preparation or the probe line.
        xi = (1, 1, F(1, 6))
        phase = turns(xi, (0, 0, d))
        need(
            all(turns(xi, character(i)) == 0 for i in MASKS)
            and phase == F(d, 6) % 1
            and phase.denominator == 6 // d,
            "conditional holonomy discriminator",
        )
        rows[d] = {
            "subgroup_generator_xi_power": 6 // d,
            "electric_residue_classes": len(electric),
            "classes_after_ignoring_all_local_center_labels": 6 // d,
            "magnetic_residue_classes_m3_m2_6g": sorted(magnetic),
            "minimum_positive_pure_singlet_integer_q": min(singlets),
            "minimum_positive_g_with_admitted_center_flux": str(F(hmin, 6)),
            "m3_m2_at_minimum_g": at_min[0],
            "xi_holonomy_phase_turns_on_genuine_singlet_q_equals_d": str(phase),
            "hypothetical_genuine_singlet_q2_q3": (2 in singlets, 3 in singlets),
        }
    need(
        [rows[d]["hypothetical_genuine_singlet_q2_q3"] for d in DIVISORS]
        == [(True, True), (True, False), (False, True), (False, False)],
        "two-probe discriminator",
    )
    return rows


def inverse_controls():
    # From occupations (2,0),(0,2),(1,1), diagonal blindness requires
    # 3|(a+2), 3|b, and 6|(a+b+5). Conversely C+W is always even, so
    # adding (3,3) to the two slopes changes no retained q modulo six.
    compatible = [
        (a, b)
        for a, b in product(range(6), repeat=2)
        if all(defect(character(i, a, b)) == 0 for i in MASKS)
    ]
    need(compatible == [(1, 0), (4, 3)], "even-mask inverse arithmetic")
    old, alt = [tuple(character(i, a, b) for i in MASKS) for a, b in ((-2, 3), (-5, 6))]

    def sgn(x):
        return (x > 0) - (x < 0)

    need(
        all(
            x[:2] == y[:2] and (x[2] - y[2]) % 6 == 0 and sgn(x[2]) == sgn(y[2])
            for x, y in zip(old, alt, strict=True)
        )
        and kernel(old) == kernel(alt)
        and len({e[2] for e in alt}) == 6,
        "different faithful ballot with the same characters mod six",
    )
    # Explicit synchronized ternary channel: 2 blanks and a mixed seed,
    # held at the occupied color port. Other four bits flip on every
    # packet (in the even-state description). NO central selection in it.
    before = (0, 0, 9)
    after = tuple(x ^ 30 for x in before)
    dc, dw = [
        sum(occupation(x)[j] for x in after) - sum(occupation(x)[j] for x in before)
        for j in (0, 1)
    ]
    need(
        (dc, dw) == (6, 4) and -2 * dc + 3 * dw == 0 and -5 * dc + 6 * dw == -6,
        "center-only alternative should fail exact native conservation",
    )
    need(
        defect(character(1, -5, 6)) == 3 and defect(character(1, -2, 3)) == 0,
        "odd-mask algebraic control should reveal parity degeneracy",
    )
    # Keep the compact angle fixed but multiply all local U(1) characters
    # by m. This is a NEW action, not merely a change of notation. The
    # primitive mixed row now implies z^m=omega^(-a)*(-1)^b, so z is a
    # (6m)-th root, and all roots are covered by the cyclic diagonal.
    scaled = {}
    for m in (1, 2, 3, 6, 7):
        labels = [(t, u, m * q) for t, u, q in old]
        ker = {
            (a, b, F(j, 6 * m))
            for a, b in product(range(3), range(2))
            for j in range(6 * m)
            if all(turns((a, b, F(j, 6 * m)), e) == 0 for e in labels)
        }
        need(
            ker == {(j % 3, j % 2, F(j, 6 * m)) for j in range(6 * m)}
            and sum(a == b == 0 for a, b, _ in ker) == m,
            "scaled charge lattice and pure Abelian kernel",
        )
        scaled[m] = (len(ker), m)
    return {
        "compatible_slopes_mod_six": compatible,
        "alternate_slopes": (-5, 6),
        "calibrated_integer_totals_change_in_matching_collision": {
            "ballot": 0,
            "alternative": -6,
        },
        "outside_even_carrier_single_flag_alternative_defect": 3,
        "rescaled_charges_at_fixed_angle_total_and_pure_U1_kernel_orders": scaled,
    }


def probe():
    return {
        "scope": "supplied compact group, center characters and line semantics; conditional arithmetic only",
        "local": local_center(),
        "global_options_by_quotient_order": quotient_rows(),
        "inverse_controls": inverse_controls(),
        "boundary": "No retained local compound detects K. Allowing an external line is not producing it. "
        "Failure to observe a particle/line does not show its representation is inadmissible. "
        "No global gauge group, monopole, SM physics or empirical status is derived.",
    }


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True))
