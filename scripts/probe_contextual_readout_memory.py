"""Sequential memory controls for a Peres-Mermin parity target; no native measurement inferred.

Primary source: M. Kleinmann, O. Gühne, J. R. Portillo, J.-A. Larsson and
A. Cabello, Memory cost of quantum contextuality, New J. Phys. 13 (2011)
113011, https://doi.org/10.1088/1367-2630/13/11/113011 ,
author text and Mealy tables: https://arxiv.org/abs/1007.3650 .
A3 and A4 below are THEIR published automata. An entry emits its sign
before updating, with no advance knowledge of the context or next input.
Their optimality theorems concern deterministic finite-state simulation of
certain (probability-one) constraints, not fitting every outcome frequency.
For the nine PM observables: all words lying inside one commuting context
(also after arbitrary prep) require and admit three states; adding YXY-type
repetitions with EVERY intermediate input commuting with Y (not necessarily
with each other) requires and admits four states for the primed contracts.
They also show all certain unrestricted-sequence predictions need more
than four states, and discuss a different 15-observable extension. We
verify the two exhibited machines, NOT the lower-bound proofs or optimal
memory for probabilistic, quantum, context-announced or unbounded models.

The static control assumes deterministic preassigned context-independent
values, or their mixtures independent of setting. This is not every notion
of operational noncontextuality. The announced-context sampler is a
different interface: it can generate one parity-valid fair triple, not
answer unforeseen interleavings. For genuine online inputs we compare the
published tables, then a specific extra persistent, independently prepared
uniform sign mask. Uniform row/column statistics alone can still miss a
within-trial disturbance. No empirical correlation, disturbance-free
instrument, actual detector, or replacement for quantum theory is claimed.
"""

import json
from collections import Counter, deque
from fractions import Fraction as F
from itertools import permutations, product
from math import prod

from scripts.probe_opposition_magic_square import (
    I4,
    SQUARE,
    add,
    mm,
    scale,
    trace,
    transpose,
)

NAMES = ("A", "B", "C", "a", "b", "c", "alpha", "beta", "gamma")
CONTEXT = ((0,1,2), (3,4,5), (6,7,8), (0,3,6), (1,4,7), (2,5,8))
PARITY = (1,1,1,1,1,-1)
SIGNS = (-1,1)
PAULI = sum(SQUARE, ())


def need(test, why):
    if not test:
        raise AssertionError(why)


def table(signs, changes):
    return tuple(tuple((1 if x == "+" else -1, change.get(j, s)) for j,x in enumerate(row))
                 for s,(row,change) in enumerate(zip(signs, changes, strict=True)))


# State numbers and observable indices in code start at 0. Strings are
# row-major A B C / a b c / alpha beta gamma. Omitted changes are self-loops.
A3 = table(("+++++++++", "+++-+---+", "+--+++--+"),
           ({2:1, 5:2}, {1:0, 7:2}, {3:0, 6:1}))
A4 = table(("+++++++++", "+++-+--++", "+--++++-+", "+---+---+"),
           ({2:1, 5:2}, {6:3, 7:0}, {6:0, 7:3}, {2:2, 5:1}))


def run(machine, start, inputs):
    output = []
    for j in inputs:
        result, start = machine[start][j]
        output.append(result)
    return tuple(output), start


def quantum_probability(inputs, outcomes):
    """Separate supplied ideal sharp Pauli comparator, from maximally mixed I/4."""
    k = I4
    for j, outcome in zip(inputs, outcomes, strict=True):
        k = mm(scale(add(I4, scale(PAULI[j], outcome)), F(1,2)), k)
    return trace(mm(transpose(k), k))/4  # zero iff impossible for every input density state


def context_closure(machine):
    """For arbitrary lengths, record prior sign per named observable inside a context."""
    result = []
    for ctx, sign in zip(CONTEXT, PARITY, strict=True):
        queue = deque((s, (0,0,0)) for s in range(len(machine)))
        seen = set(queue)
        while queue:
            s, record = queue.popleft()
            for k,j in enumerate(ctx):
                output, nxt = machine[s][j]
                need(record[k] in (0, output), "repeat disturbed inside one context")
                updated = record[:k]+(output,)+record[k+1:]
                need(0 in updated or prod(updated) == sign, "forbidden context triple")
                pair = nxt, updated
                if pair not in seen:
                    queue.append(pair)
                    seen.add(pair)
        result.append(len(seen))
    return result


def compatible_repeat(machine):
    """Y ... Y: exclude a change under arbitrary intermediates commuting with Y."""
    bad = []
    counts = []
    for y in range(9):
        allowed = sorted({j for ctx in CONTEXT if y in ctx for j in ctx})
        queue = deque()
        seen = set()
        for start in range(len(machine)):
            o,s = machine[start][y]
            if (s,o) not in seen:
                seen.add((s,o))
                queue.append((s,o,start,(y,)))
        while queue:
            s, old, start, path = queue.popleft()
            if machine[s][y][0] != old:
                bad.append((y,start,path+(y,)))
            for j in allowed:
                _, nxt = machine[s][j]
                if (nxt,old) not in seen:
                    seen.add((nxt,old))
                    queue.append((nxt,old,start,path+(j,)))
        counts.append(len(seen))
    return counts,bad


def sign_controls():
    static = Counter()
    masks = []
    for values in product(SIGNS, repeat=9):
        signs = tuple(prod(values[j] for j in ctx) for ctx in CONTEXT)
        static[sum(a != b for a,b in zip(signs,PARITY,strict=True))] += 1
        if signs == (1,)*6:
            masks.append(values)
    need(static == {1:96, 3:320, 5:96} and len(masks) == 16, "global assignment census")
    for ctx,sign in zip(CONTEXT,PARITY,strict=True):
        # Context-known sampler: two new fair bits, third sign from parity.
        triples = {(x,y,sign*x*y) for x,y in product(SIGNS,repeat=2)}
        need(len(triples) == 4 and all(sum(t[k] for t in triples) == 0 for k in range(3)), "context marginals")
        even = Counter(tuple(m[j] for j in ctx) for m in masks)
        need(len(even) == 4 and set(even.values()) == {4} and all(prod(x)==1 for x in even), "mask restriction")
    return static,masks


def uniform_contexts(machine, masks):
    # Gauge signs are fixed for an entire trial; the online table is blind to
    # the next observable. Include the 16-valued seed as a persistent resource.
    checks = 0
    for ctx,sign in zip(CONTEXT,PARITY,strict=True):
        for word in permutations(ctx):
            required = {z:F(1,4) for z in product(SIGNS,repeat=3) if prod(z)==sign}
            need(all(quantum_probability(word,z) == required.get(z,0) for z in product(SIGNS,repeat=3)),
                 "wrong ideal sharp-instrument convention")
            for start in range(len(machine)):
                base,_ = run(machine,start,word)
                counts = Counter(tuple(x*m[j] for x,j in zip(base,word,strict=True)) for m in masks)
                need({z:F(n,16) for z,n in counts.items()} == required, "uniform context law mismatch")
                checks += 1
    # Together with the closure check, this covers all fixed single-context
    # words: repeated values agree; a full word extends one consistent
    # parity triple, and a partial word only retains signs on its seen labels.
    # The uniform masks project to all four even triples with equal multiplicity.
    return checks


def witness(machine, masks, word, selected, expected_product):
    seen = set()
    bare = []
    for start in range(len(machine)):
        out,_ = run(machine,start,word)
        bare.append(out)
        for mask in masks:
            trial = tuple(x*mask[j] for x,j in zip(out,word,strict=True))
            need(prod(trial[k] for k in selected) == -expected_product, "witness depends on prep or gauge")
            seen.add(trial)
    # Compute operator support independently for ALL signs of this intervention.
    mass = F(0)
    for signs in product(SIGNS, repeat=len(word)):
        p = quantum_probability(word,signs)
        if prod(signs[k] for k in selected) != expected_product:
            need(p == 0, "a claimed forbidden branch has positive ideal weight")
        mass += p
    need(mass == 1 and all(quantum_probability(word,z) == 0 for z in seen), "witness comparator")
    return {"inputs":[NAMES[j] for j in word], "tested_output_positions_one_based":[k+1 for k in selected],
            "required_product":expected_product, "bare_outputs_by_initial_state":bare,
            "initial_state_mask_pairs_failing":len(machine)*len(masks),
            "different_impossible_five_sign_records":len(seen), "ideal_failure_probability":"0"}


def probe():
    static,masks = sign_controls()
    fresh_repeat = F(sum(x[0] != y[0] for x,y in product(masks,repeat=2)),len(masks)**2)
    need(fresh_repeat == F(1,2), "per-step fresh masks should destroy an A,A repeat")
    reports = {}
    for label,m in (("published_A3",A3),("published_A4",A4)):
        # All states are reachable using a preparation sequence, so starting
        # the monitors at ALL published states includes every such prep.
        states, todo = {0}, [0]
        for s in todo:
            for _,n in m[s]:
                if n not in states:
                    states.add(n)
                    todo.append(n)
        need(len(states) == len(m), "unreachable prepared state")
        closure = context_closure(m)
        count,bad = compatible_repeat(m)
        need(bool(bad) == (m is A3), "compatibility result changed")
        need(all(row[0][0] == 1 for row in m) and quantum_probability((0,),(1,)) == F(1,2),
             "bare table should not simulate the mixed-state single-observable distribution")
        reports[label] = {"context_monitor_nodes_by_triple":closure, "arbitrary_one_context_words_pass":True,
                          "cross_context_repeat_nodes_by_observable":count, "cross_context_repeats_pass":not bad,
                          "target_labels_with_repeat_failures":sorted({NAMES[y] for y,_,_ in bad}),
                          "signed_gauge_ordered_triple_preparation_checks":uniform_contexts(m,masks),
                          "bare_A_plus_for_all_initial_states":True,
                          "possible_internal_states_in_explicit_seed_augmented_implementation":16*len(m)}
    three = witness(A3,masks,(6,1,2,7,1),(1,4),1)  # prep alpha; B (C beta) B
    four = witness(A4,masks,(7,3,4,2,5),(1,2,4),1)  # prep beta; a b (C) c
    need(run(A3,0,(1,2,7,1))[0] == (1,1,-1,-1), "published A3 witness transcription")
    return {"scope":"classical single-observable Mealy controls; no measurement derived from central signs",
            "primary_source":"https://doi.org/10.1088/1367-2630/13/11/113011",
            "author_version":"https://arxiv.org/abs/1007.3650",
            "static_assignments_by_failed_contexts":dict(sorted(static.items())), "best_static_uniform_score":"5/6",
            "context_given_sampler":"four equiprobable valid triples, identical one-label marginals; "
                                    "no online answer contract when context is not supplied",
            "sequential":reports,
            "online_mask_control":"16 equally likely even-row/even-column sign masks held for the whole trial, "
                                  "independent of settings; adds four persistent bits, no per-step resampling",
            "mismatched_A_A_probability_if_the_mask_is_redrawn_each_setting":str(fresh_repeat),
            "three_state_disturbance":three, "four_state_inferred_value_disturbance":four}


if __name__ == "__main__":
    print(json.dumps(probe(), separators=(",",":")))
