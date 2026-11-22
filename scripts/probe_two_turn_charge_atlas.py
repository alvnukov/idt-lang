"""Conditional six-charge readouts for ALL two-hop frames of the anonymous folded five.

Follow two observed nonbacktracking edges r->b->m. An ordered record (r,m)
defines a frame for probe_marked_carrier_charge; exactly two b give each
frame. The graph supplies neither a deterministic anonymous choice of the
hops nor a persistent record of their endpoints. This is not a microscopic
construction of a charge meter. Supplied laws: additive occupation on the
double cover, zero vacuum, stabilizer invariance, antipodal oddness, and
primitive normalization with positive weight on the distinguished two
ports. We compare even-sheet charges on the SAME unchanged vertices unless
an explicitly verified graph action also transports the preparation.

Each charge is a function of distances to the ordered anchors, but the
six numerical values are not graph distances or an unassisted physical
measurement. Four globally identified probes can diagnose a retained frame;
this consumes a common set of named targets and calibrated readings. An
unrecorded walk supplies no such dictionary. No gauge charge, particle
spectrum, actual transport law or observer-independent scalar is claimed.
Run: python3 -B -O -m scripts.probe_two_turn_charge_atlas
"""

import json
from collections import Counter, defaultdict
from itertools import combinations, product

from scripts.probe_marked_carrier_charge import (
    all_base_automorphisms,
    anonymous_fixture,
    distances,
    double_cover,
    occupations,
    recover_cover_coordinates,
    validate_base,
)


def need(test, reason):
    if not test:
        raise AssertionError(reason)


def atlas(g):
    cover = double_cover(g)
    vertices = sorted(g)  # arbitrary labels only for tuple alignment
    dist = {v: distances(g, v) for v in vertices}
    paths = [(r, b, m) for r in vertices for b in g[r] for m in g[b] if m != r]
    frames = Counter((r, m) for r, _, m in paths)
    need(len(paths) == 320 and len(frames) == 160 and set(frames.values()) == {2}, "two-path quotient")
    values, dictionary, charts = {}, {}, {}
    for r in vertices:
        ports, coords = recover_cover_coordinates(cover, r)
        charts[r] = {v: coords[v, 0] for v in vertices}
        for m in vertices:
            if (r, m) not in frames:
                continue
            block = sum(1 << k for k, x in enumerate(ports) if x in g[m])
            need(block.bit_count() == 2 and coords[m, 0] == block, "not a two-port mark")
            word = []
            for v in vertices:
                a, b = occupations(coords[v, 0], block)
                q = -2*a + 3*b  # occupation counts weighted by the primitive solution 3*(-2)+2*3=0
                aa, bb = occupations(coords[v, 1], block)
                need(-2*aa + 3*bb == -q, "deck sheet did not reverse the calibrated sign")
                key = dist[r][v], dist[m][v]
                need(dictionary.setdefault(key, q) == q, "calibrated charge is not a distance-pair field")
                word.append(q)
            values[r, m] = tuple(word)
    need(dictionary == {(0,2):0, (2,0):6, (1,1):-3, (1,2):2, (2,1):-4, (2,2):1},
         "six charge classes have changed")
    return vertices, dist, paths, values, dictionary, charts


def comparisons(vertices, dist, values):
    signatures = Counter()
    nontrivial_relabels = affine = 0
    common = set(values[next(iter(values))])
    # A nonzero affine relabel of a fixed finite support swaps or fixes its
    # endpoints. The only candidates are identity and reflection about the midpoint.
    reflection = {min(common)+max(common)-q for q in common}
    need(reflection != common, "this support admits an unexpected negative affine symmetry")
    for (r, m), p in values.items():
        agreement = Counter()
        for (s, n), q in values.items():
            tied = sum(a == b for a, b in zip(p, q, strict=True))
            agreement[tied] += 1
            affine += int(p == q)
            transport = set(zip(p, q, strict=True))
            relabel = len(transport) == len(common)  # both fields have the same six-value support
            need(relabel == ({r, m} == {s, n}), "scalar relabel did not preserve singleton anchor fibers")
            nontrivial_relabels += int(relabel and p != q)
        signatures[tuple(sorted(agreement.items()))] += 1
    need(len(signatures) == 1 and len(set(values.values())) == 160 and affine == 160,
         "frame-distinguishing fields or pair agreement changed")
    agreement, = signatures
    need(dict(agreement) == {0:8, 2:36, 3:24, 4:69, 6:6, 8:16, 16:1} and nontrivial_relabels == 160,
         "alignment comparisons")
    joint_ties = Counter()
    for (i, x), (j, y) in combinations(enumerate(vertices), 2):
        joint_ties[dist[x][y], sum(w[i] == w[j] for w in values.values())] += 1
    need(joint_ties == {(1, 24):40, (2, 32):80}, "common scalar coarsening control")
    # If h(v)=f_frame(q_frame(v)) even for different arbitrary many-to-one
    # relabelings per frame, every tied pair has equal h. EVERY distinct
    # vertex pair ties in some frame, hence h is constant.
    reverse = {}
    for frame, word in values.items():
        other = values[frame[::-1]]
        need(sum(x == y for x, y in zip(word, other, strict=True)) == 8, "anchor reversal agreement")
        for x, y in zip(word, other, strict=True):
            need(reverse.setdefault(x, y) == y, "anchor reversal inconsistent")
    need(len({tuple(abs(x) for x in w) for w in values.values()}) == 160, "unsigned control")
    return {"same_vertex_agreements_per_fixed_frame": dict(agreement),
            "ordered_frame_pairs": len(values)**2, "affine_equivalent_ordered_pairs": affine,
            "additional_ordered_pairs_equivalent_by_arbitrary_bijective_relabel": nontrivial_relabels,
            "anchor_reversal_on_values": reverse, "fields_still_distinct_after_absolute_value": 160,
            "frames_tying_each_adjacent_pair": 24, "frames_tying_each_distinct_nonadjacent_pair": 32,
            "common_frame_dependent_coarsening": "constant only"}


def covariance(g, vertices, values, charts):
    root = vertices[0]  # chart to verify, not a proposed preferred root
    actions = all_base_automorphisms(g, root)
    idx = {v: i for i, v in enumerate(vertices)}
    base = next(iter(values))
    images = Counter()
    for act in actions:
        image = tuple(idx[act[v]] for v in vertices)
        key = act[base[0]], act[base[1]]
        need(all(values[key][image[i]] == q for i, q in enumerate(values[base])),
             "one transported preparation disagrees")
        images[key] += 1
    need(len(images) == 160 and set(images.values()) == {12}, "frames not transitive")
    # All actions from every source frame follow from the group law and the
    # tested transitive base orbit. Also construct the layer-preserving xor
    # translation specifically exchanging each ordered pair, check it is a
    # graph rewire and contrast with the unchanged vertex from that pair.
    coords = charts[root]
    inverse = {q: v for v, q in coords.items()}
    for (r, m), word in values.items():
        shift = coords[r] ^ coords[m]
        image = {v: inverse[coords[v] ^ shift] for v in vertices}
        need(image[r] == m and image[m] == r and
             all({image[w] for w in g[v]} == g[image[v]] for v in vertices) and
             all(values[m, r][idx[image[v]]] == word[idx[v]] for v in vertices),
             "affine carrier translation failed to transport the actual preparations")
    return {"checked_actions_from_one_frame": len(actions), "actions_to_each_target": 12,
            "verified_anchor_swap_translations": len(values),
            "transport_means": "move both anchors AND the tested vertex; not an experimental implementation"}


def memory(g, vertices, paths, values):
    idx = {v: i for i, v in enumerate(vertices)}
    endings, ingresses = defaultdict(set), defaultdict(set)
    for r, b, m in paths:
        endings[m].add((r, m))
        ingresses[b, m].add((r, m))
        need(values[r, m][idx[r]] == 0 and values[r, m][idx[b]] == -3 and values[r, m][idx[m]] == 6,
             "walk-local signed control")
    need({len(fs) for fs in endings.values()} == {10} and {len(fs) for fs in ingresses.values()} == {4},
         "ephemeral path memory")
    trials = 0
    for (b, m), fs in ingresses.items():
        for (r, _), (s, _) in product(fs, repeat=2):
            if r != s:
                need(values[r, m][idx[r]] == 0 and values[s, m][idx[r]] == 1,
                     "same terminal ingress must not reconstruct the prior start")
                trials += 1
    # Does an autonomous unlabelled edge remember a unique next port? Test
    # the actual edge stabilizer. Orbit transitivity then transports to all edges.
    b, m = next(iter(ingresses))
    acts = all_base_automorphisms(g, b)
    fix = [a for a in acts if a[b] == b and a[m] == m]
    choices = g[m] - {b}
    need(len(fix) == 24 and all({a[x] for a in fix} == choices for x in choices),
         "edge stabilizer not transitive on nonbacktracking choices")
    return {"frames_at_terminal": 10, "frames_at_terminal_with_last_ingress": 4,
            "extra_distinguishable_memory_values_at_least_given_terminal": 10,
            "extra_distinguishable_memory_values_at_least_given_last_arc": 4,
            "same_ingress_distinct_start_zero_versus_one_tests": trials,
            "completion": "two possible middles per ordered pair; reversible erasure needs an extra two-way record",
            "next_port": "four equivalent nonbacktracks: no deterministic equivariant choice from an edge alone"}


def diagnostics(g, vertices, values):
    words = list(values.values())
    tested, winners = {}, []
    for k in range(1, 5):
        good = []
        for subset in combinations(range(len(vertices)), k):
            if len({tuple(w[i] for i in subset) for w in words}) == len(words):
                good.append(frozenset(vertices[i] for i in subset))
        tested[k] = len(good)
        if good:
            winners = good
            break
    stars = {frozenset(g[v] - {x}) for v in vertices for x in g[v]}
    need(tested == {1:0, 2:0, 3:0, 4:80} and set(winners) == stars, "named target resource")
    # Even adaptive decision trees with only these six-valued readings need
    # four in worst case: at EVERY root query, 60 remaining frames give 1,
    # and 60 > 6^2. A successful fixed four realizes this bound.
    for i in range(len(vertices)):
        hist = Counter(w[i] for w in words)
        need(hist[1] == 60 > len(hist)**2, "adaptive three-query exclusion")
    return {"distinguishing_fixed_subsets_by_size": tested, "worst_case_optimal_adaptive_queries": 4,
            "all_optimal_fixed_sets": "four of the neighbors of one globally named pivot",
            "prerequisite": "stable target identities, a repeatable frame, exact calibrated readings"}


def probe():
    g = anonymous_fixture()
    validate_base(g)
    vs, dist, paths, values, dictionary, charts = atlas(g)
    # Change the ordering used to name recovered cover walls, not only their
    # numeric names. All 2,560 charge values stay covariant after decoding anew.
    rename = {v: 101 + (7*i+3) % 16 for i, v in enumerate(vs)}
    renamed = {rename[v]: frozenset(rename[w] for w in g[v]) for v in vs}
    others, _, _, tables, recovered, _ = atlas(renamed)
    where = {v:i for i,v in enumerate(others)}
    need(recovered == dictionary and
         all(tables[rename[r], rename[m]][where[rename[v]]] == q
             for (r,m), word in values.items() for v,q in zip(vs, word, strict=True)),
         "one of the six charges depends on arbitrary cover-wall names")
    return {"scope": "supplied signed additive even-sheet convention; no canonical marks or physical measurement",
            "oriented_two_step_paths": len(paths), "ordered_frames": len(values),
            "distance_pair_dictionary": [[*k, x] for k, x in sorted(dictionary.items())],
            "unchanged_vertices": comparisons(vs, dist, values), "transport": covariance(g, vs, values, charts),
            "path_memory": memory(g, vs, paths, values), "named_target_queries": diagnostics(g, vs, values)}


if __name__ == "__main__":
    print(json.dumps(probe(), separators=(",", ":")))
