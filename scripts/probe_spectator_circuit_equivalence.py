"""Exact local circuit rewrites for the six-mode spectator comparison.

Matrix products act rightmost first. Let A=S3[012] and B=S4[1345].
S_n=2J/n-I on its listed support and identity elsewhere. In all five
odd-spectator branches, a word V_j avoiding j obeys the exact full
operator identity V_j B A = U_j T_j. U_j uses just three modes and
every elementary operation in T_j avoids source port 0. T_j fixes
e0 with positive sign, not just as a ray. This is more information
than matching one prepared output vector.

Transferring an EVENT prediction still requires calibrated circuit
equivalence, the absence of consequential records from applying T_j
to initially empty modes, and spectator nondisturbance of the raw j
marginal under V_j. Equal wave matrices alone do not supply any of
these three operational premises. In particular, a dephased stochastic
implementation obeys the spectator condition but not these full wave
word identities. A normalized one-event comparator is not a proof of
the Born rule or a claim about an implemented detector.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from math import gcd, lcm

N = 6
PORTS = tuple(range(N))
ODD = (0, 1, 3, 4, 5)
Matrix = tuple[tuple[F, ...], ...]
Vector = tuple[F, ...]
I = tuple(tuple(F(i == j) for j in PORTS) for i in PORTS)
E0 = I[0]


def need(ok, why):
    if not ok:
        raise ArithmeticError(why)


@dataclass(frozen=True)
class Gate:
    kind: str
    ports: tuple[int, ...]

    def matrix(self) -> Matrix:
        p = self.ports
        need(len(p) == len(set(p)) and set(p) <= set(PORTS), "gate support not exact")
        if self.kind == "star":
            need(len(p) in (3, 4), "expected one of the calibrated stars")
            return tuple(tuple(F(2, len(p))-int(i == j) if i in p and j in p else F(i == j)
                               for j in PORTS) for i in PORTS)
        need(len(p) == 2 and self.kind in ("swap", "sign_pair"), "unknown supported elementary control")
        if self.kind == "swap":
            a, b = p
            return tuple(I[b] if i == a else I[a] if i == b else I[i] for i in PORTS)
        return tuple(tuple(x*(-1 if i in p else 1) for x in I[i]) for i in PORTS)

    def specification(self):
        return {"gate": self.kind, "ports": self.ports}


def star(*ports):
    return Gate("star", ports)


def swap(a, b):
    return Gate("swap", tuple(sorted((a, b))))


def flip(a, b):
    return Gate("sign_pair", tuple(sorted((a, b))))


A = star(0, 1, 2)
B = star(1, 3, 4, 5)


def transpose(w: Matrix) -> Matrix:
    return tuple(zip(*w, strict=True))


def mul(w: Matrix, v: Matrix) -> Matrix:
    cols = transpose(v)
    return tuple(tuple(sum(a*b for a, b in zip(row, col, strict=True)) for col in cols) for row in w)


def wave(word: tuple[Gate, ...]) -> Matrix:
    result = I
    for gate in word:
        result = mul(result, gate.matrix())
    return result


def column(w: Matrix, j: int = 0) -> Vector:
    return tuple(row[j] for row in w)


def vector(w: Matrix, x: Vector) -> Vector:
    return tuple(sum(a*b for a, b in zip(row, x, strict=True)) for row in w)


def energy(w: Matrix) -> Matrix:
    return tuple(tuple(x*x for x in row) for row in w)


def dephased(word: tuple[Gate, ...]) -> Matrix:
    """Distinct physical null: compose observed stagewise populations."""
    result = I
    for gate in word:
        result = mul(result, energy(gate.matrix()))
    return result


def isometry(w: Matrix) -> bool:
    return mul(w, transpose(w)) == I


def masks(word: tuple[Gate, ...]) -> set[int]:
    return {p for gate in word for p in gate.ports}


def primitive_ray(x: Vector) -> tuple[int, ...]:
    denominator = lcm(*(a.denominator for a in x))
    numerator = tuple(int(a*denominator) for a in x)
    common = gcd(*numerator)
    need(common > 0, "zero ray")
    return tuple(a//common for a in numerator)


def reduced_odd_weights(x: Vector) -> tuple[F, ...]:
    ray = primitive_ray(x)
    odds = tuple(x % 2 for x in ray)
    return tuple(F(x, sum(odds)) for x in odds)


def words(j: int) -> tuple[tuple[Gate, ...], tuple[Gate, ...], tuple[Gate, ...]]:
    """Return the V_j, U_j, T_j written words."""
    if j == 0:
        return (B,), (A,), ()
    if j == 1:
        return (star(0, 3, 4, 5),), (swap(0, 1), A), (B, swap(1, 2), B)
    need(j in (3, 4, 5), "not an odd spectator in BA")
    return (
        (star(*(v for v in ODD if v != j)), flip(1, 2)),
        (flip(2, j), swap(0, j), star(0, 2, j)),
        (B, swap(2, j), flip(1, j), B),
    )


def certify_branches() -> tuple[dict[int, object], dict[int, object]]:
    initial = wave((B, A))
    x = column(initial)
    need(tuple(3*a for a in x) == (-1, -1, 2, 1, 1, 1), "central prepared vector")
    p = column(energy(initial))
    classical = column(dephased((B, A)))
    need(classical == p == (F(1, 9), F(1, 9), F(4, 9), F(1, 9), F(1, 9), F(1, 9)),
         "common central wave/Markov starting control")
    audits, nulls = {}, {}
    for j in ODD:
        v, u, t = words(j)
        lhs = (*v, B, A)
        rhs = (*u, *t)
        need(j not in masks(v) and 0 not in masks(t) and len(masks(u)) == 3, "gate support violated")
        need(all(isometry(g.matrix()) for g in (*lhs, *rhs)), "nonorthogonal elementary gate")
        need(wave(lhs) == wave(rhs) and column(wave(t)) == E0, "full operator factorization failed")
        need(wave(v)[j] == I[j], "spectator row changed")
        # All paths of T avoid mode 0, hence the factorization does not
        # rely on cancelling arbitrary relative source phases.
        compressed = column(wave(u))
        weights = reduced_odd_weights(compressed)
        need(weights == column(I, j) and sum(p) == 1 and compressed[j] == x[j],
             "spectator residue witness or coherent marginal changed")
        need(len({i for i, a in enumerate(compressed) if a}) == 3
             and abs(primitive_ray(compressed)[j]) == 1, "not a three-mode single-odd ray")
        null_lhs = column(dephased(lhs))
        null_rhs = column(dephased(rhs))
        tv = sum(abs(a-b) for a, b in zip(null_lhs, null_rhs, strict=True))/2
        need(tv == F(1, 3) and null_lhs[j] == null_rhs[j] == p[j] == F(1, 9),
             "dephased complement null lost its exact discriminator")
        audits[j] = {
            "V_j": [g.specification() for g in v], "U_j": [g.specification() for g in u],
            "T_j": [g.specification() for g in t], "all_36_matrix_entries_match": True,
            "V_avoids_j": True, "T_avoids_source_0": True, "T_source_sign": 1,
            "compressed_vector_times_3": tuple(int(3*a) for a in compressed),
            "compressed_residue_rule_event_at_j": str(weights[j]),
            "compressed_Born_model_prediction_at_j": str(compressed[j]**2),
        }
        nulls[j] = {"long_word_output": list(map(str, null_lhs)), "factorized_word_output": list(map(str, null_rhs)),
                    "same_spectator_marginal": str(p[j]), "full_output_total_variation": str(tv)}
    return audits, nulls


def robust_event_bound(observed_small_raw: tuple[F, ...],
                       spectator_error: tuple[F, ...], circuit_error: tuple[F, ...],
                       empty_operation_error: tuple[F, ...]) -> F:
    """Lower bound on sum of mutually exclusive raw central-j bins."""
    need(all(len(a) == len(ODD) for a in (observed_small_raw, spectator_error, circuit_error, empty_operation_error)),
         "each spectator needs an independently bounded transfer")
    return sum((max(F(0), p-s-c-e) for p, s, c, e in zip(
        observed_small_raw, spectator_error, circuit_error, empty_operation_error, strict=True)), F(0))


def sideband_controls() -> dict[str, object]:
    # Reversible bit update at a B gate or at any P_2j used in a T word.
    # Every elementary pair (wave gate, xor on bit) is an involution.
    # Remarkably the full five word equalities survive this augmentation.
    side_gates = {B, *(swap(2, j) for j in ODD if j != 0)}

    def augmented(word, source, bit):
        return vector(wave(word), source), (bit+sum(g in side_gates for g in word)) % 2

    def readout(state):
        x, h = state
        return E0 if h and x[0] else reduced_odd_weights(x)

    central = readout(augmented((B, A), E0, 0))
    memory = {}
    for j in ODD:
        v, u, t = words(j)
        lhs, rhs = (*v, B, A), (*u, *t)
        need(all(augmented(lhs, initial, bit) == augmented(rhs, initial, bit)
                 for initial, bit in product(I, (0, 1))), "rewrites do not preserve augmented transformations")
        need(all(augmented((g, g), initial, bit) == (initial, bit)
                 for g, initial, bit in product(set(lhs+rhs), I, (0, 1))), "not an involutive augmented gate")
        t_input = augmented(t, E0, 0)
        long, factorized, direct = (readout(augmented(w, E0, 0)) for w in (lhs, rhs, u))
        need(t_input == (E0, int(j != 0)) and long == factorized == E0
             and long[j] == central[j] and direct == I[j], "toy model did not isolate empty-operation premise")
        memory[j] = {"bit_after_empty_T_at_source_0": t_input[1],
                     "events_long_then_factorized_then_direct_small": [long.index(1), factorized.index(1), direct.index(1)]}
    return {
        "sideband": "one reversible bit toggled by B or the swaps on the listed (2,j) pairs",
        "tested_five_augmented_operator_equalities_hold": True,
        "tested_central_spectator_nondisturbance_holds": True,
        "branches": memory,
        "fails": "empty-operation invariance; nominally empty modes can write a consequential sideband bit",
    }


def operational_controls() -> dict[str, object]:
    upper = F(1)  # exclusive six-port bins on the same central preparation
    ideal = robust_event_bound((F(1),)*5, (F(0),)*5, (F(0),)*5, (F(0),)*5)
    example = robust_event_bound((F(3, 5),)*5, (F(1, 10),)*5, (F(1, 10),)*5, (F(1, 10),)*5)
    need(ideal == 5 and example == F(3, 2) > upper, "wrong operational gap")
    # A registered conditional certainty can be manufactured by
    # retaining only outcomes already at the selected spectator.
    unfiltered = tuple(F(int(j in ODD), 5) for j in PORTS)
    survivors = [{i: p if i == j else F(0) for i, p in enumerate(unfiltered)} for j in ODD]
    need(all(row[j] / sum(row.values()) == 1 for row, j in zip(survivors, ODD, strict=True))
         and sum(row[j] for row, j in zip(survivors, ODD, strict=True)) == 1,
         "postselection control does not preserve raw spectator marginals")
    return {
        "sum_raw_exclusive_central_spectator_probabilities_at_most": str(upper),
        "ideal_transferred_lower_bound_from_five_small_controls": str(ideal),
        "example_lower_bound_raw_small_3_over_5_and_three_errors_1_over_10": str(example),
        "uncertain_test_formula": "sum_j max(0,u_j - spectator_j - circuit_j - empty_operation_j) > 1",
        "loss_boundary": "a conditional probability of one does not bound u_j; 1/5 raw per branch can postselect to 1",
        "loss_alias_total_survival_by_spectator": ["1/5"]*5,
        "which_circuit_flag_control": sideband_controls(),
    }


def probe() -> dict[str, object]:
    branches, nulls = certify_branches()
    return {
        "scope": "six-mode finite wave/circuit identities and conditional raw event comparator only",
        "rightmost_factor_runs_first": True,
        "central_vector_times_3": (-1, -1, 2, 1, 1, 1),
        "odd_spectators": ODD,
        "branches": branches,
        "incoherent_stagewise_markov_null": nulls,
        "event_controls": operational_controls(),
        "measurement_contract": [
            "use the same pre-setting attempt flag and disjoint raw click bins including loss and coincidences",
            "count the selected output j and its actual complement in one instrument; no survivor renormalization",
            "verify complement-only operation and directly record j before any later recombination mixing it",
            "calibrate external phase references, delays, ports, detector efficiencies and side records across words",
            "equal coherent transfer matrices are not by themselves equal trial instruments",
            "phase-insensitive propagation can preserve a spectator while failing the wave circuit identity on other outputs",
            "a compatible six-port outcome law in general is not fixed by this one comparator",
        ],
    }


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, separators=(",", ":")))
