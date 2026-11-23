"""Equal wavefronts need not define one propagation metric on a record cover.

The folded fixture supplies adjacency, not spatial axes. A root and an
actual two-hop mark select three reciprocal root edges; signed crossings
are the rooted loop record. A second declared set of omitted square
relations gives the diffuse rank-three cover. Its charts below are for
analysis, not physical positions or extra observable coordinates.

On the same graph and a common tick, set nine equally weighted dispatch
tickets per vertex. In A every edge has one ticket; in B the three
recognizable root edges have two each. Both fill the remaining tickets
with holds, and every hold/edge remains possible, so *all* timed supports
and shortest fronts agree. Ticket weighting changes dispersion, not time
cost per traversal. Uniform ticket branches can be exhaustively prepared;
using them as random outcomes is an additional physical premise.

For a first return to the same root, read elapsed ticks and the signed
closed record. The covariance per mean return time equals the long-time
diffusion tensor for these stated dispatch laws. Check it by both a
harmonic correction and an independent killed-chain moment solve. An
early finite counter needs neither an asymptotic limit nor an unbounded
record. This does not establish a physical position, wave equation,
Euclidean geometry or universal physical clock.
"""

from __future__ import annotations

import json
from collections import Counter, deque
from fractions import Fraction as F
from itertools import combinations, pairwise, product
from math import gcd, lcm

ZERO = (0, 0, 0)
TICKETS = 9


def need(test, message):
    if not test:
        raise ArithmeticError(message)


def add(a, b):
    return tuple(x + y for x, y in zip(a, b, strict=True))


def neg(a):
    return tuple(-x for x in a)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def det(a):
    x, y, z = a
    return sum(
        x[i] * (y[(i + 1) % 3] * z[(i + 2) % 3] - y[(i + 2) % 3] * z[(i + 1) % 3])
        for i in range(3)
    )


def add_periods(word, gains):
    return tuple(sum(gains[u, v][i] for u, v in pairwise(word)) for i in range(3))


def fixture():
    return {
        v: frozenset(min(v ^ (1 << i), v ^ (1 << i) ^ 31) for i in range(5))
        for v in range(16)
    }


def edge(u, v):
    return (u, v) if u < v else (v, u)


def tree(graph, root):
    parent = {root: None}
    todo = deque([root])
    while todo:
        u = todo.popleft()
        for v in sorted(graph[u]):
            if v not in parent:
                parent[v] = u
                todo.append(v)
    need(len(parent) == len(graph), "disconnected carrier")
    return parent


def squares(graph):
    faces = sorted(
        {
            (u, v, w, z)
            for u in graph
            for v in graph[u]
            if v > u
            for w in graph[v]
            if w > u
            for z in graph[u] & graph[w]
            if z > v
        }
    )
    need(len(faces) == 40, "wrong adjacency-discovered face inventory")
    return tuple((*face, face[0]) for face in faces)


def echelon(rows, width):
    """Return normalized pivot rows; augmented columns may be wider."""
    pivots = {}
    for row in rows:
        work = list(map(F, row))
        for j in range(width):
            a = work[j]
            if a:
                if j not in pivots:
                    pivots[j] = [t / a for t in work]
                    break
                work = [x - a * y for x, y in zip(work, pivots[j], strict=True)]
    return pivots


def solve(left, right):
    n = len(left)
    rows = echelon([(*a, *b) for a, b in zip(left, right, strict=True)], n)
    need(len(rows) == n, "singular killed-chain/grounded Laplacian")
    values = [None] * n
    for i in reversed(range(n)):
        values[i] = tuple(
            rows[i][n + k] - sum(rows[i][j] * values[j][k] for j in range(i + 1, n))
            for k in range(len(right[0]))
        )
    need(
        all(
            tuple(dot(row, col) for col in zip(*values, strict=True)) == rhs
            for row, rhs in zip(left, right, strict=True)
        ),
        "linear-system residual",
    )
    return values


def primitive_chart(graph, faces, omitted, parent):
    edges = sorted({edge(u, v) for u in graph for v in graph[u]})
    tree_edges = {edge(v, u) for v, u in parent.items() if u is not None}
    chords = [a for a in edges if a not in tree_edges]
    need(len(chords) == 25, "base cycle rank")
    rows = []
    for j, word in enumerate(faces):
        if j not in omitted:
            path = set(pairwise(word))
            rows.append(tuple(int(a in path) - int(a[::-1] in path) for a in chords))
    pivots = echelon(rows, len(chords))
    columns = []
    for k in sorted(set(range(len(chords))) - pivots.keys()):
        v = [F(int(i == k)) for i in range(len(chords))]
        for j in sorted(pivots, reverse=True):
            v[j] = -sum(pivots[j][i] * v[i] for i in range(j + 1, len(chords)))
        scale = lcm(*(a.denominator for a in v))
        columns.append(tuple(int(a * scale) for a in v))
    need(len(columns) == 3, "expected rank three")
    images = tuple(zip(*columns, strict=True))
    minors = [(abs(det(c)), c) for c in combinations(sorted(set(images)), 3)]
    index = gcd(*(d for d, _ in minors))
    frame = next(c for d, c in minors if d == index)
    determinant = det(frame)
    result = dict.fromkeys(edges, ZERO)
    for chord, w in zip(chords, images, strict=True):
        v = tuple(
            F(det((*frame[:i], w, *frame[i + 1 :])), determinant) for i in range(3)
        )
        need(all(a.denominator == 1 for a in v), "non-integral primitive chart")
        result[chord] = tuple(map(int, v))
    result |= {(v, u): neg(w) for (u, v), w in result.items()}
    need(
        all(
            add_periods(word, result) == ZERO
            for i, word in enumerate(faces)
            if i not in omitted
        ),
        "retained face broke",
    )
    return result


def records(graph, faces, root):
    mark = min(graph.keys() - graph[root] - {root})
    common = graph[root] & graph[mark]
    # Observers can use a nominated gated two-turn word and square
    # comparison: the second mark and the two common root ports are local.
    word = (root, min(common), mark)
    marked = tuple(sorted(graph[root] - common))
    gains = {
        (u, v): tuple(
            int(u == root and v == p) - int(v == root and u == p) for p in marked
        )
        for u in graph
        for v in graph[u]
    }
    omitted = {
        i
        for i, face in enumerate(faces)
        if any(
            v == root and u in marked or u == root and v in marked
            for u, v in pairwise(face)
        )
    }
    need(
        len(omitted) == 9
        and all(
            add_periods(face, gains) == ZERO
            for i, face in enumerate(faces)
            if i not in omitted
        ),
        "wrong rooted release",
    )
    root_ports = next(p for p in graph[root] if p not in marked)
    loop_basis = [
        (root, p, next(iter((graph[p] & graph[root_ports]) - {root})), root_ports, root)
        for p in marked
    ]
    need(
        [add_periods(path, gains) for path in loop_basis]
        == [tuple(int(i == j) for i in range(3)) for j in range(3)],
        "root-local edge crossings not primitive",
    )
    diffuse_omitted = {0, 4, 5, 6, 10, 11, 12, 28, 30}
    need(
        not set.intersection(*(set(faces[i]) for i in diffuse_omitted)),
        "diffuse release has a common root",
    )
    parent = tree(graph, root)
    diffuse = primitive_chart(graph, faces, diffuse_omitted, parent)
    return gains, diffuse, marked, word


def weights(graph, root, marked, boosted):
    counts = {}
    for u in graph:
        outgoing = {
            v: 1
            + int(boosted and (u == root and v in marked or v == root and u in marked))
            for v in graph[u]
        }
        outgoing[u] = TICKETS - sum(outgoing.values())
        need(min(outgoing.values()) > 0, "timed support lost an edge or hold")
        counts[u] = outgoing
    need(
        all(row[v] == counts[v][u] for u, row in counts.items() for v in row),
        "not a reciprocal protocol",
    )
    return counts


def gain(gains, u, v):
    return ZERO if u == v else gains[u, v]


def killed_laplacian(counts, root, tickets=TICKETS):
    live = sorted(counts.keys() - {root})
    return live, [
        tuple(tickets * int(u == v) - counts[u].get(v, 0) for v in live) for u in live
    ]


def harmonic_tensor(counts, gains, root):
    live, left = killed_laplacian(counts, root)
    currents = {
        u: tuple(
            sum(c * gain(gains, u, v)[i] for v, c in row.items()) for i in range(3)
        )
        for u, row in counts.items()
    }
    psi = {
        root: ZERO,
        **dict(zip(live, solve(left, [currents[u] for u in live]), strict=True)),
    }
    corrected = {
        (u, v): add(add(gain(gains, u, v), psi[v]), neg(psi[u]))
        for u, row in counts.items()
        for v in row
    }
    need(
        all(
            sum(c * corrected[u, v][i] for v, c in row.items()) == 0
            for u, row in counts.items()
            for i in range(3)
        ),
        "harmonic correction is not a martingale increment",
    )
    tensor = tuple(
        tuple(
            F(
                sum(
                    c * corrected[u, v][i] * corrected[u, v][j]
                    for u, row in counts.items()
                    for v, c in row.items()
                ),
                TICKETS * len(counts),
            )
            for j in range(3)
        )
        for i in range(3)
    )
    return tensor, corrected


def first_return_tensor(counts, gains, root, tickets=TICKETS):
    """No harmonic function supplied: absorb on arrival at root and solve."""
    live, left = killed_laplacian(counts, root, tickets)
    right = [
        (
            *tuple(
                sum(c * gain(gains, u, v)[i] for v, c in counts[u].items())
                for i in range(3)
            ),
            tickets,
        )
        for u in live
    ]
    means = {root: (0, 0, 0, 0), **dict(zip(live, solve(left, right), strict=True))}
    ij = tuple(product(range(3), repeat=2))

    def increment(u, v):
        p = gain(gains, u, v)
        m = means[v]
        return tuple(p[i] * p[j] + p[i] * m[j] + p[j] * m[i] for i, j in ij)

    rhs = [
        tuple(
            sum(c * increment(u, v)[k] for v, c in counts[u].items())
            for k in range(len(ij))
        )
        for u in live
    ]
    second = {root: (0,) * len(ij), **dict(zip(live, solve(left, rhs), strict=True))}
    elapsed = 1 + F(sum(c * means[v][3] for v, c in counts[root].items()), tickets)
    need(
        elapsed == len(counts),
        "uniform-stationary recurrence time should equal carrier size",
    )
    need(
        all(
            sum(
                c * (gain(gains, root, v)[i] + means[v][i])
                for v, c in counts[root].items()
            )
            == 0
            for i in range(3)
        ),
        "reversible first-return loop has nonzero mean",
    )
    second_return = tuple(
        F(
            sum(
                c * (increment(root, v)[k] + second[v][k])
                for v, c in counts[root].items()
            ),
            tickets,
        )
        for k in range(len(ij))
    )
    return tuple(
        tuple(second_return[i * 3 + j] / elapsed for j in range(3)) for i in range(3)
    ), elapsed


def finite_ballots(counts, gains, root, ticks):
    """Count all TICKETS^ticks issued plans; after first return pad with unused tickets."""
    live = Counter({(root, ZERO): 1})
    returns = Counter()
    for t in range(ticks):
        nxt = Counter()
        for (u, p), multiplicity in live.items():
            for v, n in counts[u].items():
                shifted = add(p, gain(gains, u, v))
                if v == root:
                    returns[t + 1, shifted] += (
                        n * multiplicity * TICKETS ** (ticks - t - 1)
                    )
                else:
                    nxt[v, shifted] += n * multiplicity
        live = nxt
    incomplete = sum(live.values())
    need(
        sum(returns.values()) + incomplete == TICKETS**ticks,
        "wrong exhaustive ballot denominator",
    )
    return returns, incomplete


def quadratic(q, x):
    return sum(a * x[i] * x[j] for i, row in enumerate(q) for j, a in enumerate(row))


def covariance_ratio(q, x, y):
    return F(quadratic(q, x), quadratic(q, y))


def change_basis(gains, matrix):
    def offset(u):
        return (u % 3, -(u % 5), u % 2)

    def transform(w):
        return tuple(dot(row, w) for row in matrix)

    result = {
        (u, v): transform(add(w, add(offset(v), neg(offset(u)))))
        for (u, v), w in gains.items()
    }
    return result, transform


def conjugate_tensor(matrix, q):
    return tuple(
        tuple(
            sum(a * b * q[i][j] for i, a in enumerate(x) for j, b in enumerate(y))
            for y in matrix
        )
        for x in matrix
    )


def covariance_controls(gains, root, same_carrier_protocols):
    rows = {}
    tensors = {}
    memberships = []
    for name, rates in same_carrier_protocols.items():
        analytical, _ = harmonic_tensor(rates, gains, root)
        first, elapsed = first_return_tensor(rates, gains, root)
        need(
            analytical == first and det(first) > 0,
            "independent moment solvers disagree or tensor is not full rank",
        )
        ballots, incomplete = finite_ballots(rates, gains, root, 4)
        rows[name] = {
            "tensor_per_common_tick": tuple(tuple(map(str, row)) for row in first),
            "determinant_in_primitive_return_basis": str(det(first)),
            "mean_first_return_ticks": str(elapsed),
            "four_tick_elapsed_and_return_record_support_size": len(ballots),
            "emissions_without_return_at_four_tick_cutoff": incomplete,
        }
        memberships.append(set(ballots))
        tensors[name] = first
        # Shear the period basis and change the open-path convention.
        # All completed route values shift only by their basis image.
        shear = ((1, 1, 0), (0, 1, 1), (0, 0, 1))
        need(det(shear) == 1, "non-primitive shear control")
        changed, transformed = change_basis(gains, shear)
        changed_tensor, _ = harmonic_tensor(rates, changed, root)
        changed_ballots, changed_incomplete = finite_ballots(rates, changed, root, 4)
        need(
            changed_tensor == conjugate_tensor(shear, first)
            and det(changed_tensor) == det(first),
            "basis/gauge covariance",
        )
        need(
            {(t, transformed(v)): n for (t, v), n in ballots.items()} == changed_ballots
            and incomplete == changed_incomplete,
            "actual observed closed records changed under a gauge",
        )
    need(
        memberships[0] == memberships[1],
        "equal timed branch support lost at internal readout",
    )
    return rows, tensors


def root_discriminator(rates, rooted, root, tensor):
    c = (1, -1, 0)
    s = (1, 1, 1)
    timeline = {}
    for name, plan in rates.items():
        ballots, incomplete = finite_ballots(plan, rooted, root, 4)
        score_c = sum(n * dot(p, c) ** 2 for (_, p), n in ballots.items())
        score_s = sum(n * dot(p, s) ** 2 for (_, p), n in ballots.items())
        need(
            all(t == 4 for t, p in ballots if any(p)),
            "period detected before minimum nonzero excitation",
        )
        timeline[name] = {
            "four_tick_all_preparations": TICKETS**4,
            "four_tick_incomplete": incomplete,
            "square_score_contrast": score_c,
            "square_score_sum": score_s,
            "four_tick_retained_moment_ratio": str(F(score_c, score_s)),
            "long_time_moment_ratio": str(covariance_ratio(tensor[name], c, s)),
        }
    a, b = timeline.values()
    need(
        (
            a["square_score_contrast"],
            a["square_score_sum"],
            b["square_score_contrast"],
            b["square_score_sum"],
        )
        == (20, 12, 64, 24),
        "finite rooted discriminator did not realize the direct square enumeration",
    )
    ref, boosted = tensor.values()
    transverse = covariance_ratio_pair(boosted, ref, c)
    parallel = covariance_ratio_pair(boosted, ref, s)
    need(
        (parallel, transverse) == (F(32, 27), F(64, 39)),
        "unexpected invariant relative diffusion spectrum",
    )
    # Verify these are generalized eigenvalues, not selected Rayleigh
    # quotients (two independent contrasts have the same value).
    for v, ratio in ((s, parallel), (c, transverse), ((0, 1, -1), transverse)):
        need(
            tuple(dot(row, v) for row in boosted)
            == tuple(ratio * dot(row, v) for row in ref),
            "not a generalized eigenvector",
        )
    return {
        "root_records": {
            "signed_two_port_contrast": c,
            "signed_total_of_three_ports": s,
        },
        "protocols": timeline,
        "basis_invariant_generalized_eigenvalues": tuple(
            map(str, (parallel, transverse, transverse))
        ),
        "shape_change_factor_transverse_to_parallel": str(transverse / parallel),
    }


def covariance_ratio_pair(numerator, denominator, v):
    return F(quadratic(numerator, v), quadratic(denominator, v))


def germ_router(graph, gains, root, selected):
    """A second local rule with exactly one-hop ticks and no hold padding."""
    degree = len(graph[root])
    need(
        degree >= 3 and all(len(neighbors) == degree for neighbors in graph.values()),
        "regular carrier required",
    )
    ordinary = {u: {v: 1 for v in graph[u]} for u in graph}
    single = {u: {**ordinary[u], u: TICKETS - degree} for u in graph}
    # Uniform holds only scale the diffusion per tick and do not change
    # the harmonic correction; use those correctors on genuine hops.
    padded, all_corrected = harmonic_tensor(single, gains, root)
    edges = {e: w for e, w in all_corrected.items() if e[0] != e[1]}
    raw = {e: {(e[1], w): 1 for w in graph[e[1]] if w != e[0]} for e in edges}
    ingress = (selected, root)
    need(
        len(tree(raw, ingress)) == len(edges)
        and all(sum(e in row for row in raw.values()) == degree - 1 for e in raw),
        "directed ingress chain is not uniformly recurrent",
    )
    adjusted = {}
    alpha = F(1, degree - 2)
    g = {}
    for e, row in raw.items():
        vectors = []
        for nxt in row:
            # Given e, E[h(nxt)|e]=h(e)/(degree-1), since the reversed
            # ingress is the only term omitted from a zero-sum row.
            h = tuple(
                (1 + alpha) * a - alpha * b
                for a, b in zip(edges[nxt], edges[e], strict=True)
            )
            adjusted[e, nxt] = h
            g[e, nxt] = gains[nxt]
            vectors.append(h)
        need(
            all(not sum(z) for z in zip(*vectors, strict=True)),
            "wrong ingress martingale correction",
        )
    covariance = tuple(
        tuple(
            F(sum(h[i] * h[j] for h in adjusted.values()), len(adjusted))
            for j in range(3)
        )
        for i in range(3)
    )
    ordinary_tensor = tuple(
        tuple(x * F(TICKETS, degree) for x in row) for row in padded
    )
    ordinary_check, _ = first_return_tensor(ordinary, gains, root, degree)
    expected = tuple(
        tuple(x * F(degree, degree - 2) for x in row) for row in ordinary_tensor
    )
    returned, elapsed = first_return_tensor(raw, g, ingress, degree - 1)
    need(
        covariance == returned == expected and ordinary_check == ordinary_tensor,
        "first-return germ moments disagree with the persistent-transport factor",
    )
    # No first path restriction when routing from a released root. A
    # displayed relay can choose its first step before ingress is set.
    # Shortest lifted paths never immediately retrace an edge: the two
    # reciprocal gains cancel, and omitting the steps saves two ticks.
    return {
        "first_return_to_same_arrival_germ_mean_ticks": str(elapsed),
        "first_return_scope": "marked root AND same incoming port; a vertex hit with other ingress does not reset this process",
        "ordinary_to_never_retrace_dispersion_multiplier": str(F(degree, degree - 2)),
        "closed_record_propagation_front": "same earliest positions at free launch; immediate retraces never help a shortest route",
        "two_hop_echo_probability_ordinary_and_no_retrace": [str(F(1, degree)), "0"],
        "never_retrace_tensor_per_one_hop_tick": tuple(
            tuple(map(str, row)) for row in returned
        ),
    }


def probe():
    graph = fixture()
    faces = squares(graph)
    root = 0
    rooted, diffuse, marked, two_turn = records(graph, faces, root)
    rates = {
        "equal_edges": weights(graph, root, marked, False),
        "two_tickets_on_three_marked_edges": weights(graph, root, marked, True),
    }
    unweighted, weighted = rates.values()
    need(
        all(set(unweighted[u]) == set(weighted[u]) for u in graph),
        "not identical timed wavefront supports",
    )
    root_rows, root_tensors = covariance_controls(rooted, root, rates)
    diffuse_rows, diffuse_tensors = covariance_controls(diffuse, root, rates)
    relative_det = F(
        det(diffuse_tensors["equal_edges"]), det(root_tensors["equal_edges"])
    )
    return {
        "scope": "supplied folded record graph, abelianized finite-loop counters and ticket dispatch at one common tick; no physical movement or Euclidean metric",
        "two_turn_frame": two_turn,
        "marked_root_ports": marked,
        "timed_support_identical_before_any_scoring": True,
        "rooted": root_rows,
        "diffuse_free_rank_three": diffuse_rows,
        "diffuse_to_rooted_determinant_ratio_equal_dispatch": str(relative_det),
        "operational_root_readout": root_discriminator(
            rates, rooted, root, root_tensors
        ),
        "operational_ingress_germ_control": germ_router(graph, rooted, root, marked[0]),
        "proof_boundary": {
            "shared_front": "both dispatches allow exactly the same one-tick edge transitions and waits, so all finite attainable route/arrival sets match on a fixed cover",
            "long_time": "vertex potential removes conditional drift, leaving martingale increments; potential difference is bounded and zero on a closed loop. Symmetric ticket P has uniform stationary law, and the return expected visit counts solve mP=m with m_root=1, so E[tau]=16 and first-return covariance/tau equals the long-time tensor.",
            "bounded_actual_observer": "root contact + elapsed count and signed root-germ tallies, score completed paths by tick 4, retain all 9^4 prepared ticket lists in denominator and explicitly count censoring; no endpoint chart or unbounded register for this finite comparison",
            "diffuse_extra_resource": "diffuse primitive chart is recovered from supplied retained square relators and path abelianization; reading its open edge increments needs the corresponding finite route recorder, not the rooted-only detector",
            "not_a_universal_metric": "diffusion is a second moment of a particular dispatch/branch preparation and can change shape while the complete wavefront stays fixed; no result for unmodeled autonomous rules or physical clocks",
        },
    }


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, separators=(",", ":")))
