"""Finite neutral-pair lift diagnostic. Run: python3 -B -O -m scripts.probe_neutral_pair_lift

Inputs include the anonymous base, ordered root/nonneighbour mark, root
sheet, the inherited collision template and an OPTIONAL pair source. Nothing
here supplies such a source. A packet at chart coordinate 0 is not no packets.
The earlier pairing probe already compared a supplied self-pair constraint
with a conjugate-pair constraint. Here the new information is their location
in the full lifted neutral-pair census and the deck obstruction to an oriented
deterministic source, not the mere availability of those two algebraic choices.
The SM dictionary is checked only AFTER the combinatorics; it is not a
physical identification, a selection principle, or a rate calculation.
"""
from collections import Counter
from itertools import combinations_with_replacement, product
import json

from scripts import probe_blind_collision_charge as collision
from scripts import probe_marked_carrier_charge as carrier
from scripts import probe_packet_charge_pairings as dictionary


def check(condition, why):
    if not condition:
        raise ArithmeticError(why)


def q(x):
    c, w = collision.occ(x)
    return -2*c + 3*w


def X(x):
    return 3 - 2*collision.occ(x)[0]


def deck(packets):
    """Simultaneous deck change, on unordered configurations."""
    return tuple(sorted(x ^ carrier.MASK for x in packets))


def control_step(packets, relation=None, reference=None):
    """A supplied transposition, not an inferred source. reference is a sheet bit.

    For 'same', the *shared* reference is retained across the step, and flips
    under deck change. For 'opposite' no reference is needed. Unmentioned
    configurations are fixed; an unknown law is not a choice of law.
    """
    if relation == "opposite":
        target = (0, carrier.MASK)
    elif relation == "same" and reference in (0, 1):
        target = (reference*carrier.MASK,)*2
    else:
        raise ValueError("supply a relative-sheet law and (for same) an oriented reference")
    if any(type(x) is not int or not 0 <= x <= carrier.MASK for x in packets):
        raise ValueError("not packet coordinates")
    state = tuple(sorted(packets))
    return target if state == () else () if state == target else state


def pair_audit(graph, root, mark):
    carrier.validate_base(graph)
    cover = carrier.double_cover(graph)
    block, coords, _ = carrier.port_block(graph, cover, root, mark)
    if block.bit_count() != 2:
        raise ValueError("the selected 3+2 frame requires a distinct nonneighbour mark")
    # Reindex the recovered large block into collision ports 0..2. Never
    # interpret the anonymous base names as occupations or slot numbers.
    order = sorted(range(5), key=lambda j: (bool(block & (1 << j)), j))
    image = tuple(order.index(j) for j in range(5))
    masks = {v: collision.relabel(x, image) for v, x in coords.items()}
    check(set(masks.values()) == set(carrier.CUBE), "chart not bijective")
    check(all(collision.occ(masks[v]) == carrier.occupations(x, block) for v, x in coords.items()),
          "block transport mismatch")
    pairs = list(combinations_with_replacement(cover, 2))
    neutral = [(a, b) for a, b in pairs if q(masks[a]) + q(masks[b]) == 0]
    exceptions, mixed = [], 0
    for a, b in neutral:
        pair = tuple(sorted((masks[a], masks[b])))
        total = sum(map(X, pair))
        if a[1] != b[1]:
            check(total == 0, "mixed sheet neutral pair has nonzero X")
            mixed += 1
        else:
            exceptions.append((pair, total))
    fiber = {tuple(sorted((masks[a], masks[b]))) for a, b in pairs if a[0] == b[0] == root}
    r, s = masks[root, 0], masks[root, 1]
    same, opposite = (r, r), tuple(sorted((r, s)))
    independent = {tuple(sorted((r ^ i, r ^ j))) for i, j in product((0, carrier.MASK), repeat=2)}
    check(independent == fiber and same != deck(same) and opposite == deck(opposite),
          "root-fiber deck comparison")
    check(len(pairs) == 528 and len(neutral) == 62 and mixed == 60 and
          sorted(exceptions) == [((0, 0), 6), ((31, 31), -6)], "neutral census")
    return {"pairs": len(pairs), "q_neutral": len(neutral), "mixed_x_zero": mixed,
            "same_sheet_exceptions": sorted(exceptions), "projected_root_pair": (root, root),
            "global_deck_orbit_sizes": [len({same, deck(same)}), len({opposite, deck(opposite)})],
            "independent_deck_orbit_size": len(independent)}


def collision_audit():
    counts = []
    for n in (1, 2):
        count = 0
        for s, (i, j) in product(product(collision.STATES, repeat=n), collision.PAIRS):
            t = (collision.shuffle(s[0], i, j),) if n == 1 else collision.exchange(s, i, j)
            for field in (q, X):
                check(sum(map(field, s)) == sum(map(field, t)), "unary/binary field mismatch")
            count += 1
        counts.append(count)
    rule = collision.ternary_library()[1][1, 1, "large", 1]
    deltas = Counter()
    for s, (t, _) in rule.items():
        check(t == tuple(sorted(collision.fire(s, rule))) and rule[t][0] == s, "ternary inverse")
        check(sum(map(q, s)) == sum(map(q, t)), "ternary q")
        deltas[sum(map(X, t))-sum(map(X, s))] += 1
    s = (0, 0, 9)
    t = rule[s][0]
    check(counts == [160, 2560] and deltas == {-12: 6, 12: 6}, "even-menu census")
    return {"even_unary_binary_counts": counts, "even_ternary_unordered_edges": len(rule)//2,
            "even_ternary_directed_deltas": dict(deltas),
            "example_forward": [s, t, sum(map(X, t))-sum(map(X, s))]}


def probe():
    graph = carrier.anonymous_fixture()
    root = min(graph)
    mark = min(graph.keys()-graph[root]-{root})
    pairs = pair_audit(graph, root, mark)
    for x in carrier.CUBE:
        sign = (-1)**x.bit_count()
        check((X(x) - 3*sign + 2*q(x)) % 12 == 0, "single-packet congruence")
        y, = deck((x,))
        check(X(x) == -X(y) and q(x) == -q(y), "complement antisymmetry")
    # External even occupation dictionary Q,u^c,d^c,L,e^c,N^c; no Higgs here.
    blocks = ((1, 1), (2, 0), (2, 2), (3, 1), (0, 2), (0, 0))
    rows = [[x for x in collision.STATES if collision.occ(x) == b] for b in blocks]
    check(tuple(map(len, rows)) == dictionary.DIMS, "external even multiplicities")
    for row, bl, sm in zip(rows, dictionary.BL[:6], dictionary.SM[:6], strict=True):
        check(all(X(x) == bl and q(x) == sm for x in row), "external table mismatch")
    # An equivariant deterministic output at a fixed input has to be fixed.
    # Enumerate ONLY the q-neutral two-packet outputs above (root,root).
    root_pairs = list(combinations_with_replacement((0, carrier.MASK), 2))
    fixed = [pair for pair in root_pairs if deck(pair) == pair]
    check(fixed == [(0, 31)], "invariant true empty cannot select either same root orientation")
    controls = []
    for relation, bit in (("opposite", None), ("same", 0), ("same", 1)):
        out = control_step((), relation, bit)
        check(control_step(out, relation, bit) == () and sum(map(q, out)) == 0, "source inverse/charge")
        check(deck(out) == control_step((), relation, None if bit is None else 1-bit), "source covariance")
        controls.append({"relation": relation, "supplied_reference": bit, "created": out,
                         "delta_q": sum(map(q, out)), "delta_X": sum(map(X, out))})
    return {"pairs": pairs, "collision": collision_audit(),
            "congruence": {"one_packet_checks": len(carrier.CUBE),
                           "additive_identity": "X_total = 3*(N_even-N_odd)-2*q_total (mod 12)",
                           "independent_evidence": False},
            "dictionary": {"even_X": [X(row[0]) for row in rows],
                           "scope": "3(B-L) only in the supplied external one-generation dictionary"},
            "source": {"root_pair_fixed_outputs": fixed, "native_law_selected": False, "controls": controls,
                       "without_a_source": "no creation required; identity also deck-equivariant",
                       "relative_lift": "global deck preserves same/opposite; independent flips erase it",
                       "scope": "two reversible controls, not a native interaction, physical selection or rate"}}


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, indent=2))
