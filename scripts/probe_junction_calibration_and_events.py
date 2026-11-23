"""Exact wave-star calibration controls, not a derivation of event counting.

At a common reciprocal junction the voltage/displacement is continuous
and flux is balanced. Write incoming/outgoing voltages a_i,b_i and real
admittances Y_i. Then a_i+b_i=V and sum_i Y_i(a_i-b_i)=Y_L V for a
passive shunt Y_L. In power-normalized amplitudes, u_i=sqrt(Y_i),
the matrix is 2*u*u^T/(sum_i Y_i+Y_L)-I. The lossless equal-line
case gives the real three-port reflection I/O law 2*J/3-I.

Coherent classical fields obey the amplitude comparison too. Squared
wave amplitudes are energy ratios in this model, not automatically
probabilities of exclusive, individually registered events. The
prospective event trial fixes its herald/attempt before the junction
and records no-click and multiclick bins without survivor normalization.

Primary comparisons inspected: Osawa et al. 2018 arXiv:1810.02033,
Eqs. (4),(5),(8),(9); Kim et al. 2021 arXiv:2106.13473, Eqs. (13)
through (20); and Schwarze et al. 2024 arXiv:2409.04303, a *four*-port
Grover interferometer. None of these directly reports this complete
three-port Grover wave and raw single-event calibration as one dataset.
"""

from __future__ import annotations

import json
from fractions import Fraction as F

Matrix = tuple[tuple[F, ...], ...]
OMEGA = ((1, 0), (0, 1), (-1, -1))


def need(condition, why):
    if not condition:
        raise ArithmeticError(why)


def identity(n: int) -> Matrix:
    return tuple(tuple(F(int(i == j)) for j in range(n)) for i in range(n))


def mul(a: Matrix, b: Matrix) -> Matrix:
    return tuple(tuple(sum((x*y for x, y in zip(row, col, strict=True)), F(0)) for col in zip(*b, strict=True))
                 for row in a)


def transpose(a):
    return tuple(zip(*a, strict=True))


def apply(a, x):
    return tuple(sum(t*v for t, v in zip(row, x, strict=True)) for row in a)


def scale(a, ratio):
    return tuple(tuple(F(x)*ratio for x in row) for row in a)


def energy(a):
    return tuple(tuple(F(x)*x for x in row) for row in a)


def shunt_star(admittance_roots: tuple[int, ...], load: int = 0) -> Matrix:
    admittances = tuple(u*u for u in admittance_roots)
    den = sum(admittances)+load
    need(all(a > 0 for a in admittance_roots) and load >= 0, "passive positive-load model only")
    power = tuple(tuple(F(2*u*v, den)-int(i == j) for j, v in enumerate(admittance_roots))
                  for i, u in enumerate(admittance_roots))
    need(power == transpose(power), "power-normalized reciprocity")
    # Check voltage continuity, flux balance and energy accounting
    # directly for every input basis state and a coherent mixed input.
    for incoming in (*identity(len(admittances)), tuple(F((-1)**i*(i+1)) for i in range(len(admittances)))):
        a = tuple(v*u for v, u in zip(incoming, admittance_roots, strict=True))
        b = apply(power, a)
        voltage_out = tuple(v/u for v, u in zip(b, admittance_roots, strict=True))
        voltage = {x+y for x, y in zip(incoming, voltage_out, strict=True)}
        need(len(voltage) == 1, "not a common endpoint")
        v, = voltage
        need(sum(y*(x-z) for x, y, z in zip(incoming, admittances, voltage_out, strict=True)) == load*v,
             "endpoint does not balance admitted flux")
        need(sum(x*x-y*y for x, y in zip(a, b, strict=True)) == load*v*v, "failed wave-energy accounting")
    return power


def text_matrix(m):
    return [[str(x) for x in row] for row in m]


def admitted_attempts(probabilities, attempts: int):
    columns = []
    for col in transpose(probabilities):
        loss = 1-sum(col)
        need(loss >= 0, "recorded ports exceed incoming trial weight")
        columns.append({"each_recorded_port": [str(p*attempts) for p in col],
                        "unrecorded_attempts": str(loss*attempts),
                        "multiple_clicks_in_ideal_single_event_model": "0"})
    return columns


def omega_product(a, b):
    x, y = a
    z, w = b
    return x*z-y*w, x*w+y*z-y*w


def omega_norm(a) -> int:
    x, y = a
    return x*x-x*y+y*y


def f3_square(insert_flip_at: int | None):
    """Use F3 entries omega^(ij)/sqrt(3), so F3 D F3 has denominator 3."""
    result = []
    for i in range(3):
        row = []
        for j in range(3):
            amp = [0, 0]
            for k in range(3):
                z = omega_product(OMEGA[i*k % 3], OMEGA[k*j % 3])
                sign = -1 if k == insert_flip_at else 1
                amp[0] += sign*z[0]
                amp[1] += sign*z[1]
            row.append(F(omega_norm(amp), 9))
        result.append(tuple(row))
    return tuple(result)


def phase_flip(n: int, port: int) -> Matrix:
    return tuple(tuple(F((-1 if i == port else 1)*int(i == j)) for j in range(n)) for i in range(n))


def phase_and_pass_audit(s: Matrix) -> dict[str, object]:
    ideal = energy(s)
    f = ((F(1, 3),)*3,)*3
    identity3 = identity(3)
    inverse_ports = tuple(tuple(F(int((i+j) % 3 == 0)) for j in range(3)) for i in range(3))
    twice = energy(mul(s, s))
    classical_event_chain = mul(ideal, ideal)
    need(twice == identity3 and f3_square(None) == inverse_ports
         and classical_event_chain[0] == (F(11, 27), F(8, 27), F(8, 27)),
         "coherent and incoherent two-pass controls changed")
    on = energy(mul(mul(s, phase_flip(3, 0)), s))
    off = energy(mul(mul(s, phase_flip(3, 1)), s))
    need(transpose(on)[0] == (F(49, 81), F(16, 81), F(16, 81))
         and transpose(off)[0] == (F(1, 81), F(16, 81), F(64, 81)), "phase flip predictions")
    out = {
        "S3_same_orientation_zero_phase": admitted_attempts(twice, 810),
        "S3_flip_intermediate_port_0": admitted_attempts(on, 810),
        "S3_flip_intermediate_port_1": admitted_attempts(off, 810),
        "F3_same_orientation_zero_phase": admitted_attempts(inverse_ports, 810),
        "F3_flip_intermediate_port_0": admitted_attempts(f3_square(0), 810),
        "phase_insensitive_S3_event_chain_or_fully_dephased_fields": admitted_attempts(classical_event_chain, 810),
        "bare_identity_with_or_without_intermediate_phase": admitted_attempts(identity3, 810),
        "S3_uniform_half_amplitude_zero_phase_two_pass": admitted_attempts(scale(twice, F(1, 16)), 810),
        "F3_followed_by_its_inverse_uninformative_identity_echo": admitted_attempts(identity3, 810),
    }
    for data in (twice, on, off, inverse_ports, f3_square(0), classical_event_chain, f):
        need(all(sum(col) == 1 for col in transpose(data)), "lossless probability column sums")
    return out


def balanced_two_arm_controls(s):
    def star(sign):
        return tuple((s[i][0]+sign*s[i][1])**2/2 for i in range(3))

    def fourier(sign):
        return tuple(F(omega_norm((1+sign*a, sign*b)), 6) for a, b in OMEGA)

    plus, minus = star(1), star(-1)
    need(plus == (F(1, 18), F(1, 18), F(8, 9)) and minus == (F(1, 2), F(1, 2), 0),
         "coherent pair source control")
    incoherent = tuple((a+b)/2 for a, b in zip(transpose(energy(s))[0], transpose(energy(s))[1], strict=True))
    return {name: list(map(str, rate)) for name, rate in (
        ("S3_plus", plus), ("S3_minus", minus), ("F3_plus", fourier(1)), ("F3_minus", fourier(-1)),
        ("S3_incoherent_equal_source_mixture", incoherent),
    )}


def phase_gauge_control(s):
    d = phase_flip(3, 1)
    moved = mul(mul(d, s), d)
    need(moved != s and energy(moved) == energy(s), "reciprocal reference-plane rephasing did not preserve intensities")

    def rectangle(m):
        # Invariant even under independently rephased input/output
        # modes, when the second two entries are complex conjugated.
        return m[0][0]*m[1][2]*m[0][2]*m[1][0]

    need(rectangle(moved) == rectangle(s) == F(-8, 81), "phase closure sign")
    return {"reference_plane_rephasing_leaves_energies_same": True,
            "phase_sensitive_rectangle_S00_S12_conjS02_conjS10": str(rectangle(s)),
            "absolute_reflection_sign_requires_declared_reference_planes": True}


def terminate_one_port_of_g4(z: F) -> Matrix:
    g4 = shunt_star((1, 1, 1, 1))
    # a_3=z*b_3; solve the terminated mode before forming the open block.
    return tuple(tuple(g4[i][j]+g4[i][3]*z*g4[3][j]/(1-z*g4[3][3]) for j in range(3)) for i in range(3))


def mirror_phase_energy(cosine: int) -> tuple[F, F, F]:
    # With |z|=1, diag(S_eff)=-1/(2+z), offdiag=(1+z)/(2+z).
    denominator = 5+4*cosine
    return F(1, denominator), F(2*(1+cosine), denominator), F(2*(1+cosine), denominator)


def literature() -> dict[str, object]:
    return {
        "Spagnolo_et_al_2013_comparator": {
            "doi": "10.1038/ncomms2616",
            "setting": "integrated tritter, three-photon coalescence with a fourth trigger photon and delay scans",
            "limits": "reported output probabilities reconstructed from coincidences; not this raw S3 junction test",
        },
        "Osawa_et_al_2018": {
            "doi": "10.1364/OE.26.027201", "author_full_text": "https://ar5iv.labs.arxiv.org/html/1810.02033",
            "setting": "three-port directionally unbiased, target 1/3 all entries at selected phases",
            "reported_transition_matrix_eq9_diagonal": ["0.332 +/- 0.007", "0.339 +/- 0.006", "0.338 +/- 0.007"],
            "reported_average_visibility": "0.97 +/- 0.01",
            "limits": "attenuated coherent 633 nm light, per-contour normalization, return isolation at 50%, lost trials not counted",
            "does_this_measure_target_S3": False,
        },
        "Kim_et_al_2021": {
            "doi": "10.1364/OE.436075", "author_full_text": "https://ar5iv.labs.arxiv.org/html/2106.13473",
            "setting": "SPDC singles distribution and two-photon HOM, transfer matrix reconstructed in two ways",
            "reported_count_ratio_eq13_diagonal": ["0.220 +/- 0.001", "0.610 +/- 0.002", "0.131 +/- 0.001"],
            "reported_fidelity_between_their_two_reconstructions": "0.971 +/- 0.005",
            "does_this_measure_target_S3": False,
        },
        "Schwarze_et_al_2024": {
            "doi": "10.1364/OE.532364", "author_full_text": "https://ar5iv.labs.arxiv.org/html/2409.04303",
            "setting": "four-port Grover implementation with classical power readout, also two terminated ports in Michelson",
            "reported_normalized_eq9_diagonal": ["0.2715 +/- 0.0008", "0.2353 +/- 0.0009",
                                                 "0.2542 +/- 0.0030", "0.2350 +/- 0.0016"],
            "uncertainty_scope": "three repeated port probing/alignment estimates, not an all-event error bar",
            "does_this_measure_the_proposed_one_termination_three_port_variant": False,
        },
        "search_status": "no directly matched all-port complex S3 and raw exclusive-event dataset verified in these originals",
    }


def probe() -> dict[str, object]:
    s = shunt_star((1, 1, 1))
    unequal = shunt_star((1, 2, 3))
    loaded = shunt_star((1, 1, 1), load=1)
    ideal = energy(s)
    balanced = ((F(1, 3),)*3,)*3
    need(mul(s, s) == mul(unequal, unequal) == identity(3)
         and ideal[0] == (F(1, 9), F(4, 9), F(4, 9)), "undamped reflection law")
    need(loaded[0] == (F(-1, 2), F(1, 2), F(1, 2))
         and energy(loaded) == scale(balanced, F(3, 4)), "loaded-star postselection alias")
    need(terminate_one_port_of_g4(F(1)) == s
         and terminate_one_port_of_g4(F(-1)) == scale(identity(3), -1)
         and terminate_one_port_of_g4(F(0)) == loaded, "four-port terminated control")
    need(mirror_phase_energy(1) == ideal[0] and mirror_phase_energy(-1) == identity(3)[0]
         and mirror_phase_energy(0) == (F(1, 5), F(2, 5), F(2, 5)), "mirror-phase calibration")
    return {
        "scope": "conditional wave calibration and prospective finite event tests; not an event-law derivation",
        "primary_source_audit": literature(),
        "wave_power_normalized_S3": text_matrix(s),
        "unequal_admittance_1_4_9_reciprocal_scattering": text_matrix(unequal),
        "calibrated_g4_one_port_termination_control": {
            "S_effective": "-I+((1+z)/(2+z))*J at specified coherent return amplitude z",
            "mirror_return_plus_1": "S3", "mirror_return_minus_1": "-I", "matched_termination_0": "loaded equal star",
            "mirror_return_phase_pi_over_2_power_distribution_for_input_port_0": list(map(str, mirror_phase_energy(0))),
            "status": "prospective narrowband control; neither mirror setting is inferred from graph degree",
        },
        "ideal_one_pass_900_attempts_per_input_before_any_survivor_conditioning": {
            "S3_squared_amplitude_event_prediction": admitted_attempts(ideal, 900),
            "balanced_F3": admitted_attempts(balanced, 900),
            "bare_event_identity": admitted_attempts(identity(3), 900),
            "bare_permutation": admitted_attempts(tuple(identity(3)[i] for i in (2, 0, 1)), 900),
            "S3_uniform_half_amplitude": admitted_attempts(scale(ideal, F(1, 4)), 900),
            "equal_star_extra_shunt_one_line": admitted_attempts(energy(loaded), 900),
        },
        "two_pass_expected_counts_810_attempts_each_input": phase_and_pass_audit(s),
        "one_pass_two_precalibrated_coherent_inputs_or_incoherent_null": balanced_two_arm_controls(s),
        "phase_reference_control": phase_gauge_control(s),
        "three_independent_calibration_stages": {
            "1_complex_wave": "drive each matched port separately with the other ports matched; measure all complex"
                              " reflections and transmissions versus frequency, de-embed to common reference planes",
            "2_raw_events": "predeclare a herald at the input and every output category; characterize detector"
                            " efficiencies and dark counts independently and retain no-click and multiclick bins",
            "3_phase_intervention": "use two matched copies in the same forward orientation; independently calibrate"
                                    " relative delays/phases, then switch one intermediate arm to pi without"
                                    " registering its path and compare an explicitly dephased run",
        },
        "needed_for_an_event_test": [
            "separate measured complex wave transfer and independently calibrated routing/detector efficiencies",
            "herald or attempt flag fixed before choosing the setting; retain no-click and multi-click records",
            "arrange equal delays to make mode histories unresolved; verify phase settings and off-coherence null",
            "same forward orientation of both copies; a reverse-inverse echo is not this test",
            "energy or a dark fringe also occurs in coherent classical wave optics, not proof of discrete outcomes",
            "reported counts are ideal expected values, not measurements or confidence statements",
        ],
    }


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, separators=(",", ":")))
