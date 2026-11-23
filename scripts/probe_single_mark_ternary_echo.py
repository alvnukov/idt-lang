"""A reversible, anonymous one-mark counterfeit of one ternary wave column.

Prepare the localized input port and two hidden, ordered port labels,
uniform over nine pairs; keep the updated labels for an echo. The raw
permutation fixes three equal labels, interchanges the two names if
exactly two occur, and swaps the first two slots if all occur. It emits
one port mark, and its visible one-shot fractions are (1,4,4)/9.

One-shot compatibility and a full-state echo do not give compositional
wave behavior. For the two addressed overlapping junctions below,
all couplings with uniform individual pair stocks can be optimized by
an exact bipartite assignment/transport argument. The bound rests on
the submitted routing rule, not on general hidden-state possibilities.
Label invention and a different nonuniform seed stock are controls.

Supplied resources: persistent ordered seed labels, a calibrated
equiprobable stock, complete readout of one output per preparation,
fixed gates and timing, and (for the comparator only) signed coherent
wave addition and square-norm readout. No experimental claim.
"""

from __future__ import annotations

import json
from collections import Counter
from fractions import Fraction as F
from functools import cache
from itertools import permutations, product

PORTS = range(3)
H = (0, 1, 2)
G = (1, 2, 3)
SEEDS = tuple(product(PORTS, repeat=2))
Triplet = tuple[int, int, int]
Pair = tuple[int, int]


def need(test, message):
    if not test:
        raise ArithmeticError(message)


def turn(state: Triplet) -> Triplet:
    i, a, b = state
    if i == a == b:
        return state
    if len(set(state)) == 2:
        u, v = sorted(set(state))
        return tuple(v if k == u else u for k in state)
    return (a, i, b)


def permute(p, state):
    return tuple(p[x] for x in state)


def inverse(p):
    return tuple(p.index(i) for i in range(len(p)))


def local_controls():
    all_states = tuple(product(PORTS, repeat=3))
    for s in all_states:
        after = turn(s)
        need(
            turn(after) == s and set(after) == set(s),
            "local echo or support preservation",
        )
        need(
            all(turn(permute(p, s)) == permute(p, after) for p in permutations(PORTS)),
            "hidden port-name preference",
        )
    counts = tuple(
        tuple(sum(turn((i, *seed))[0] == j for seed in SEEDS) for j in PORTS)
        for i in PORTS
    )
    need(
        counts == ((1, 4, 4), (4, 1, 4), (4, 4, 1)) and turn((0, 1, 1)) == (1, 0, 0),
        "calibrated visible counts or singleton-input two-name swap",
    )
    independent_echoes = sum(
        turn((turn((0, *a))[0], *b))[0] == 0 for a, b in product(SEEDS, repeat=2)
    )
    need(
        independent_echoes == 33, "fresh second seed should destroy the completed echo"
    )

    # An unchanged seed is a mixture of port permutations. Every
    # involution of an odd set has a fixed point, hence trace >= 1.
    involutions = tuple(p for p in permutations(PORTS) if inverse(p) == p)
    traces = tuple(sum(p[i] == i for i in PORTS) for p in involutions)
    need(min(traces) == 1 > F(1, 3), "frozen seed trace obstruction")

    # Nine is only a lower bound for EQUIPROBABLE raw seeds. A nonuniform
    # stock uses one idle and two opposed cyclic orientations instead.
    weights = {-1: F(4, 9), 0: F(1, 9), 1: F(4, 9)}

    def oriented(i, d):
        return (i + d) % 3, -d

    for i, d in product(PORTS, weights):
        j, e = oriented(i, d)
        need(oriented(j, e) == (i, d), "orientation coin must update its hidden state")
        for p in permutations(PORTS):
            winding = 1 if (p[1] - p[0]) % 3 == 1 else -1
            need(
                oriented(p[i], winding * d) == (p[j], winding * e),
                "orientation coin needs the orientation action",
            )
    need(
        all(
            tuple(
                sum(w for d, w in weights.items() if oriented(i, d)[0] == j)
                for j in PORTS
            )
            == tuple(F(n, 9) for n in counts[i])
            for i in PORTS
        ),
        "nonuniform stock rates",
    )

    return {
        "raw_states_checked": len(all_states),
        "visible_counts_per_nine": counts,
        "singleton_input_when_both_hidden_labels_equal_other": turn((0, 1, 1)),
        "two_firings_return_probability_retained_vs_fresh": (
            "1",
            str(F(independent_echoes, 81)),
        ),
        "minimum_equiprobable_raw_seeds_per_input": 9,
        "frozen_seed_port_involution_traces_vs_target": {
            "available": traces,
            "target": "1/3",
        },
        "three_nonuniform_orientation_seeds_escape": {
            "weights": tuple(map(str, weights.values())),
            "resource": "orientation register changes sign under a port reflection and on every firing",
        },
    }


def trial(s, gate, which, rule):
    port, a, b = s
    if port not in gate:
        return s
    local = a if which == 0 else b
    new_port, x, y = permute(gate, rule((gate.index(port), *local)))
    encoded = (gate.index(x), gate.index(y))
    return (new_port, encoded, b) if which == 0 else (new_port, a, encoded)


def overlap_matrix(rule):
    return tuple(
        tuple(
            int(trial(trial((0, a, b), H, 0, rule), G, 1, rule)[0] == 3) for b in SEEDS
        )
        for a in SEEDS
    )


def assignment(matrix, maximize):
    @cache
    def solve(used):
        row = used.bit_count()
        if row == len(matrix):
            return 0, ()
        choices = []
        for column in range(len(matrix)):
            if not ((used >> column) & 1):
                rest, match = solve(used | (1 << column))
                choices.append((matrix[row][column] + rest, (column, *match)))
        return (max if maximize else min)(choices)

    count, match = solve(0)
    need(
        sorted(match) == list(range(len(matrix)))
        and count == sum(matrix[i][j] for i, j in enumerate(match)),
        "assignment sampled a nonuniform marginal",
    )
    return count, match


def bound_by_pattern(rule, matrix):
    mid = tuple(rule((0, *a))[0] for a in SEEDS)
    need(Counter(mid) == {0: 1, 1: 4, 2: 4}, "expected calibrated H output marginal")
    first, second = (
        {j for j, valid in enumerate(matrix[mid.index(i)]) if valid} for i in (1, 2)
    )
    need(len(first) == len(second) == 4, "expected single-G calibration")
    need(
        all(
            {j for j, valid in enumerate(row) if valid}
            == ({1: first, 2: second}.get(mid[i], set()))
            for i, row in enumerate(matrix)
        ),
        "unexpected dependency on unobserved H memory at G",
    )
    # Arbitrary nonnegative joint masses with row/column sums 1/9:
    # all upper mass lies on the union, all lower mass on shared columns
    # except what the lone bypass row can absorb. Matchings attain them.
    shared = len(first & second)
    lo, hi = assignment(matrix, False), assignment(matrix, True)
    need(
        (lo[0], hi[0]) == (max(0, shared - 1), len(first | second)),
        "matching and analytic coupling bounds disagree",
    )
    return shared, lo, hi


def reflection(x, gate):
    c = F(2 * sum(x[i] for i in gate), len(gate))
    return tuple(c - a if i in gate else a for i, a in enumerate(x))


def network_control():
    for port, a, b in product(range(4), SEEDS, SEEDS):
        s = (port, a, b)
        final = trial(trial(s, H, 0, turn), G, 1, turn)
        need(
            trial(trial(final, G, 1, turn), H, 0, turn) == s,
            "two contacts did not undo on full hidden state",
        )
    matrix = overlap_matrix(turn)
    shared, lo, hi = bound_by_pattern(turn, matrix)
    independent = F(sum(map(sum, matrix)), 81)
    intermediate = reflection((1, 0, 0, 0), H)
    bright = reflection(intermediate, G)
    dark = reflection(tuple(-a if i == 1 else a for i, a in enumerate(intermediate)), G)
    for v in (intermediate, bright, dark):
        need(sum(a * a for a in v) == 1, "rational comparator changed norm")
    need(
        independent == F(32, 81)
        and bright[3] ** 2 == F(64, 81)
        and dark[3] == 0
        and (shared, lo[0], hi[0]) == (3, 2, 5),
        "network comparison",
    )
    return {
        "independent_local_seeds_port3": str(independent),
        "full_joint_states_checked_for_reverse_network": 4 * len(SEEDS) ** 2,
        "arbitrary_coupled_uniform_local_marginals_port3": (
            str(F(lo[0], 9)),
            str(F(hi[0], 9)),
        ),
        "extremal_second_seed_indices_for_each_first_seed": {
            "min": lo[1],
            "max": hi[1],
        },
        "coherent_wave_port3_bright_vs_one_path_minus": (
            str(bright[3] ** 2),
            str(dark[3] ** 2),
        ),
        "bright_gap_beyond_all_correlations_for_submitted_rule": str(
            bright[3] ** 2 - F(hi[0], 9)
        ),
        "conditional_vs_marginal_stock": "conditional uniformity of the G stock given actual entry is sufficient for 32/81; the interval assumes only unconditional uniform stocks",
        "phase_operation_scope": "a sign in one shared interior wave path produces exact darkness. An operation fixing the packet position and the relevant hidden stock leaves its prediction unchanged; an actual hidden phase update changes the model.",
    }


def involutive_parameters(index_map, renamings):
    """For each paired orbit choose one relabeling; inverse is then forced."""
    slots = [None] * len(index_map)

    def visit(i):
        if i == len(index_map):
            yield tuple(slots)
        elif slots[i] is not None:
            yield from visit(i + 1)
        else:
            j = index_map[i]
            for p in renamings:
                inv = inverse(p)
                if i == j and p != inv:
                    continue
                slots[i] = p
                slots[j] = inv
                yield from visit(i + 1)
                slots[i] = slots[j] = None

    return visit(0)


def anonymous_census():
    # Equal-label orbit has size three and is forced to be fixed by
    # equivariance. The other four are free S3 orbits (three positions
    # for the singleton of a two-name triple, then the all-distinct orbit).
    reps = ((1, 0, 0), (0, 1, 0), (0, 0, 1), (0, 1, 2))
    relabels = tuple(permutations(PORTS))
    orbit = {permute(p, r): (i, p) for i, r in enumerate(reps) for p in relabels}
    need(len(orbit) == 24, "regular orbit classification")
    by_shared = Counter()
    preserving = Counter()
    repeated_seed_calibration = Counter()
    visible_preserving = set()
    all_rules = 0
    escape = None
    repeated_witness = None
    for index_map in permutations(range(4)):
        if inverse(index_map) != index_map:
            continue
        for ps in involutive_parameters(index_map, relabels):
            table = {
                s: permute(p, permute(ps[i], reps[index_map[i]]))
                for s, (i, p) in orbit.items()
            }
            table.update({(i, i, i): (i, i, i) for i in PORTS})
            need(
                all(table[row] == s for s, row in table.items()),
                "equivariant parameterization produced a noninvolution",
            )
            all_rules += 1
            if any(table[(0, *ab)][0] == 0 for ab in SEEDS if ab != (0, 0)):
                continue
            need(
                all(
                    Counter(table[(i, *ab)][0] for ab in SEEDS)
                    == {j: (1 if i == j else 4) for j in PORTS}
                    for i in PORTS
                ),
                "no-extra-stay criterion did not imply calibration",
            )
            shared = sum(
                table[(0, *ab)][0] == 2 and table[(1, *ab)][0] == 2 for ab in SEEDS
            )
            by_shared[shared] += 1
            if all(set(z) == set(out) for z, out in table.items()):
                preserving[shared] += 1
                visible_preserving.add(tuple(table[s][0] for s in sorted(table)))
            if table[(0, 1, 1)][0] == 1:
                # Equivariance forces G's repeated (target,target) stock
                # to succeed from *both* active inputs. It supplies one
                # shared success column, so the union has at most seven.
                need(
                    table[(0, 2, 2)][0] == table[(1, 2, 2)][0] == 2 and shared >= 1,
                    "repeated-target calibration did not generate a shared success column",
                )
                repeated_seed_calibration[shared] += 1
                if shared == 1 and repeated_witness is None:
                    repeated_witness = table
            if shared == 0 and escape is None:
                escape = (index_map, ps, table)
    states = tuple(product(PORTS, repeat=3))
    visible_unflipped = tuple(turn(s)[0] for s in states)
    visible_flipped = tuple(turn((i, b, a))[0] for i, a, b in states)
    need(
        all_rules == 940
        and by_shared == {0: 20, 1: 20, 2: 60, 3: 60}
        and preserving == {3: 8}
        and visible_preserving == {visible_unflipped, visible_flipped},
        "anonymous involution census",
    )
    need(
        repeated_seed_calibration == {1: 20, 3: 60} and repeated_witness is not None,
        "single calibration cohort",
    )
    repeat_matrix = overlap_matrix(repeated_witness.__getitem__)
    _, _, repeat_max = bound_by_pattern(repeated_witness.__getitem__, repeat_matrix)
    need(repeat_max[0] == 7, "single-calibration bound was not sharp")
    need(escape is not None, "inventive routing countercontrol lost")
    index, parameters, table = escape
    matrix = overlap_matrix(table.__getitem__)
    shared, lo, hi = bound_by_pattern(table.__getitem__, matrix)
    # Mix two matchings at the preparation, never condition on an exit.
    # Row and column marginals stay uniform over the *ordered pairs*.
    p = tuple(
        tuple(F(int(j == lo[1][i]) + 8 * int(j == hi[1][i]), 81) for j in range(9))
        for i in range(9)
    )
    need(
        all(sum(row) == F(1, 9) for row in p)
        and all(sum(col) == F(1, 9) for col in zip(*p, strict=True)),
        "counterfeit coupling violated local prepared stocks",
    )
    score = sum(p[i][j] * matrix[i][j] for i, j in product(range(9), repeat=2))
    need(
        (shared, lo[0], hi[0], score) == (0, 0, 8, F(64, 81)),
        "broader anonymous countermodel did not match bright comparator",
    )
    return {
        "anonymous_involutions_on_three_slots": all_rules,
        "calibrated_involutions": sum(by_shared.values()),
        "calibrated_counts_by_overlap_of_success_seed_sets": dict(
            sorted(by_shared.items())
        ),
        "calibrated_support_preserving_rules": sum(preserving.values()),
        "support_preserving_visible_tables": len(visible_preserving),
        "support_preserving_visible_classes_modulo_hidden_slot_exchange": 1,
        "one_extra_repeated_seed_control": {
            "prepare_input_and_seed": (0, 1, 1),
            "required_output": 1,
            "surviving_rules_by_shared_columns": dict(
                sorted(repeated_seed_calibration.items())
            ),
            "sharp_maximum_port3_under_all_uniform_marginal_couplings": str(
                F(repeat_max[0], 9)
            ),
            "bright_gap": str(F(64, 81) - F(repeat_max[0], 9)),
            "resource": "known repeated hidden-pair preparation, not implied by visible calibration or echo",
        },
        "inventive_label_escape": {
            "orbit_permutation": index,
            "representatives": reps,
            "representative_relabels": parameters,
            "extremal_matching_indices": {"min": lo[1], "max": hi[1]},
            "uniform_marginal_mixture_probability_port3": str(score),
            "mixture_min_max_weights": ("1/9", "8/9"),
        },
    }


def probe():
    return {
        "scope": "submitted finite one-mark transducer with persistent local stock, not a physical detector law or complete wave model",
        "local_rule": local_controls(),
        "overlap": network_control(),
        "support_preserving_vs_label_inventing": anonymous_census(),
        "assumptions": [
            "two distinguishable storage slots holding port species, a specified hidden-stock preparation, and exactly one port mark reported per prepared trial",
            "local stocks used persistently for echoes; preparing fresh marks between firings is a different instrument",
            "two addressed contacts use distinct local stores and cannot query each other's hidden state; the allowed initial correlations do not change this causal rule",
            "wave signs, coherence and squared-norm comparison are separate calibration assumptions; allowance for a hidden phase update or broader gate rules requires new tests",
        ],
    }


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, separators=(",", ":")))
