"""Exhaust raw 24-flag reciprocal updates without a history-endpoint oracle.

S4 acts regularly on flags by left relabeling. The stabilizer S3 of port 0
has four regular torsors; an equivariant T0 is determined by four arbitrary
flag images. Transport T0 to the other three ports, then test actual flag
state returns. No signed-count, coordinate, or word-quotient equality is used.

The exhaustive result is a finite wall for this precise state space and
equivariance contract, not a no-go theorem for richer native dynamics or QM.
"""

from __future__ import annotations

import json
from collections import Counter, deque
from itertools import permutations, product

Perm = tuple[int, ...]
Table = tuple[int, ...]
Ports = tuple[Table, ...]
FLAGS: tuple[Perm, ...] = tuple(permutations(range(4)))
INDEX = {p: i for i, p in enumerate(FLAGS)}
IDENTITY = FLAGS[0]
PORTS = tuple(range(4))
STABILIZER = tuple(p for p in FLAGS if p[0] == 0)


def need(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def compose(a: Perm, b: Perm) -> Perm:
    return tuple(a[x] for x in b)


def port_transposition(port: int) -> Perm:
    result = list(PORTS)
    result[0], result[port] = result[port], result[0]
    return tuple(result)


REPRESENTATIVES = tuple(port_transposition(p) for p in PORTS)
REP_INDICES = tuple(INDEX[p] for p in REPRESENTATIVES)
LEFT = tuple(tuple(INDEX[compose(h, f)] for f in FLAGS) for h in STABILIZER)
TRANSPORT = tuple(tuple(INDEX[compose(p, f)] for f in FLAGS) for p in REPRESENTATIVES)
DECOMPOSITION = tuple(
    (f.index(0), STABILIZER.index(compose(f, REPRESENTATIVES[f.index(0)])))
    for f in FLAGS
)
TRIPLES = tuple(permutations(PORTS, 3))
PAIRS = tuple(permutations(PORTS, 2))


def apply_prototype(state: int, images: Table) -> int:
    orbit, translation = DECOMPOSITION[state]
    return LEFT[translation][images[orbit]]


def prototype(images: Table) -> Table:
    return tuple(apply_prototype(s, images) for s in range(24))


def transported(table: Table) -> Ports:
    # The chosen (0 i) representatives are involutions. S3-equivariance
    # makes the result independent of which representative carries 0 to i.
    return tuple(tuple(p[table[p[s]]] for s in range(24)) for p in TRANSPORT)


def walk(ports: Ports, start: int, word: Perm) -> int:
    state = start
    for port in word:
        state = ports[port][state]
    return state


def check_covariance(ports: Ports) -> None:
    for relabel in FLAGS:
        action = tuple(INDEX[compose(relabel, f)] for f in FLAGS)
        for p in PORTS:
            need(all(action[ports[p][s]] == ports[relabel[p]][action[s]]
                     for s in range(24)), "transported rules are not S4 covariant")


def graph_signature(ports: Ports) -> tuple[tuple[int, ...], bool, int]:
    component_sizes: list[int] = []
    seen: set[int] = set()
    bipartite = True
    girth = 25
    for start in range(24):
        distances = {start: 0}
        parents = {start: -1}
        queue = deque([start])
        while queue:
            current = queue.popleft()
            for table in ports:
                neighbor = table[current]
                if neighbor not in distances:
                    distances[neighbor] = distances[current] + 1
                    parents[neighbor] = current
                    queue.append(neighbor)
                elif parents[current] != neighbor:
                    girth = min(girth, distances[current] + distances[neighbor] + 1)
                if distances[current] % 2 == distances[neighbor] % 2:
                    bipartite = False
        if start not in seen:
            seen.update(distances)
            component_sizes.append(len(distances))
    return tuple(sorted(component_sizes)), bipartite, girth


def nonretracing_returns(ports: Ports, length: int, start: int = 0) -> list[Perm]:
    returns: list[Perm] = []

    def extend(state: int, word: Perm) -> None:
        if len(word) == length:
            if state == start:
                returns.append(word)
            return
        for p in PORTS:
            if not word or p != word[-1]:
                extend(ports[p][state], (*word, p))

    extend(start, ())
    return returns


def chart_orbit(table: Table) -> set[Table]:
    # These and only these flag rechartings commute with the regular left
    # S4 action: right multiplication by one of the 24 group elements.
    orbit = set()
    for right_factor in FLAGS:
        chart = tuple(INDEX[compose(f, right_factor)] for f in FLAGS)
        inverse = tuple(chart.index(s) for s in range(24))
        orbit.add(tuple(chart[table[inverse[s]]] for s in range(24)))
    return orbit


def screen() -> dict[str, object]:
    need(len(FLAGS) == 24 and len(STABILIZER) == 6, "group sizes")
    need(len(set(DECOMPOSITION)) == 24, "four free S3 torsors")
    counts: Counter[str] = Counter()
    signatures: Counter[tuple[tuple[int, ...], bool, int]] = Counter()
    contrast_tables: list[Ports] = []
    contrast_images: list[Table] = []
    # Deliberately enumerate all maps, not just a handpicked involution family.
    for images in product(range(24), repeat=4):
        counts["equivariant_maps"] += 1
        if not all(apply_prototype(apply_prototype(s, images), images) == s
                   for s in REP_INDICES):
            continue
        table = prototype(images)
        need(all(table[table[s]] == s for s in range(24)), "involution extension")
        need(all(table[left[s]] == left[table[s]] for left in LEFT for s in range(24)),
             "S3 equivariance extension")
        counts["involutions"] += 1
        if any(table[s] == s for s in range(24)):
            continue
        counts["fixed_point_free"] += 1
        ports = transported(table)
        need(all(t[t[s]] == s for t in ports for s in range(24)), "reciprocal ports")
        if not all(len({t[s] for t in ports}) == 4 for s in range(24)):
            continue
        counts["four_distinct_neighbors"] += 1
        check_covariance(ports)
        signature = graph_signature(ports)
        signatures[signature] += 1
        counts["bipartite_candidates"] += int(signature[1])
        counts["connected_bipartite_candidates"] += int(signature[1] and len(signature[0]) == 1)
        all_abc_return = all(
            walk(ports, s, (a, b, c, a, b, c)) == s
            for s in range(24) for a, b, c in TRIPLES
        )
        all_ab_nonreturn = all(
            walk(ports, s, (a, b, a, b, a, b)) != s
            for s in range(24) for a, b in PAIRS
        )
        counts["all_distinct_abcabc_returns"] += int(all_abc_return)
        counts["all_distinct_ababab_nonreturns"] += int(all_ab_nonreturn)
        if not (all_abc_return and all_ab_nonreturn):
            continue
        counts["desired_six_tick_contrast"] += 1
        counts["connected_contrast"] += int(len(signature[0]) == 1)
        contrast_tables.append(ports)
        contrast_images.append(images)

    need(counts["equivariant_maps"] == 24 ** 4 == 331776, "complete map count")
    need(counts["involutions"] == 4 ** 4 + 6 * 6 * 4 ** 2 + 3 * 6 ** 2 == 940,
         "independent torsor involution count")
    need(counts["fixed_point_free"] == 3 ** 4 + 6 * 6 * 3 ** 2 + 3 * 6 ** 2 == 513,
         "independent fixed-point-free involution count")
    need(counts["four_distinct_neighbors"] == 264, "degree-four candidates")
    need(counts["bipartite_candidates"] == 132
         and counts["connected_bipartite_candidates"] == 120, "alternating-role candidates")
    need(counts["all_distinct_abcabc_returns"] == counts["desired_six_tick_contrast"] == 12,
         "contrast family count")
    need(counts["connected_contrast"] == 0, "connected raw-flag countercontrol")
    need(signatures == {
        ((24,), False, 3): 96,
        ((6, 6, 6, 6), False, 3): 24,
        ((24,), True, 4): 120,
        ((8, 8, 8), True, 4): 12,
        ((12, 12), False, 3): 12,
    }, "exhaustive graph classifications")

    expected_four = {(a, b, a, b) for a, b in PAIRS} | set(FLAGS)
    for ports in contrast_tables:
        need(graph_signature(ports) == ((8, 8, 8), True, 4), "contrast graph")
        # Four reciprocal neighbors on each side of an eight-vertex
        # bipartite component exhaust its opposite side: each is K4,4.
        for s in range(24):
            need(set(nonretracing_returns(ports, 4, s)) == expected_four,
                 "all origins have the same 36 premature echoes")
        need(all(ports[a][ports[b][s]] == ports[b][ports[a][s]]
                 for a, b in PAIRS for s in range(24)), "contrast maps commute")
        need(all(walk(ports, s, PORTS) == s for s in range(24)),
             "all-four-port parity relation")
    witness = contrast_tables[0]
    return_counts = [len(nonretracing_returns(witness, n)) for n in range(1, 7)]
    need(return_counts == [0, 0, 0, 36, 0, 216], "short-return witness")
    orbit = chart_orbit(witness[0])
    need(len(orbit) == 12 and orbit == {ports[0] for ports in contrast_tables},
         "one regular-S4 recharting class")
    moore_bound = 2 * sum(3 ** i for i in range(3))
    need(moore_bound == 26 > len(FLAGS), "degree-four girth-six vertex lower bound")
    return {
        "scope": "all S3-equivariant prototype maps on the regular 24-flag S4 set",
        "counts": dict(counts),
        "graph_classes": [{"components": sizes, "bipartite": bipartite,
                           "girth": girth, "count": n}
                          for (sizes, bipartite, girth), n in sorted(signatures.items())],
        "contrast_positive": {
            "rules": 12, "equivariant_recharting_classes": 1,
            "graph": "three disjoint K4,4 components",
            "nonretracing_returns_at_ticks_1_through_6": return_counts,
            "uniform_nonretracing_four_tick_return_rate": "1/3",
            "uniform_nonretracing_six_tick_return_rate": "2/9, not the abelian 2/81",
            "four_tick_words": "abab for a!=b, or any permutation of four distinct ports",
            "mechanism": "commuting involutions with T0 T1 T2 T3 = identity",
            "prototype_representative_image_indices": contrast_images[0],
            "witness_port_tables": witness,
            "state_index_flags": FLAGS,
        },
        "girth_six_minimum_vertices": moore_bound,
        "conclusion": "six-tick contrast alone gives false positives; no connected 24-flag hit",
        "boundaries": [
            "Origin return compares actual raw flag states, not a history quotient or displacement.",
            "An observer/origin-marker interaction is not itself derived by this finite screen.",
            "The fixed 24-state carrier, global reciprocal port labels and S4 covariance are assumptions.",
            "This exhausts only single-flag deterministic updates under that exact contract.",
            "Richer carriers, junction memories and weaker symmetry contracts remain outside scope.",
            "No physical space, probability law, metric or QM derivation is claimed.",
        ],
    }


def main() -> None:
    print(json.dumps(screen(), indent=2))


if __name__ == "__main__":
    main()
