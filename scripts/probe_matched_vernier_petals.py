"""Local clock with no phase synchronization, target-weight memory or stall bus.

Duplicate the *unary* apparatus, including the one moving excitation. On the
reference only, insert two relay vertices in one marked-lane wire. The reader
sits at the common hub and uses only a marked departure on a distinguished
reference rail as its trigger. Its other input is the held signal rail.
Both walkers move on reciprocal physical edges, one edge per same-rate step.
No remote pulse is read, paused or reversed; every reference trigger counts.

Conditional result: for a fixed active packet the reference period is T+2
when the signal period is T. Any initial phases give the signal's square
shares over a complete joint orbit. The clock is packet matched, expensive
and not freely set by an external experimenter. Copies do not create a
second unknown quantum state: supplying the same classical unary installation
twice and preparing an active excitation on each are explicit resources.
"""

from collections import Counter
from itertools import pairwise
from math import gcd, lcm

from scripts.probe_bipartite_triangle_origin import need
from scripts.probe_internal_detector_clocks import advance
from scripts.probe_reversible_excitation_detector import Apparatus


def extend_one_wire(g, home, extra=2):
    need(home in g.order and extra >= 2 and extra % 2 == 0, "need a live home and even detour")
    u = g.starts[home,1,1]
    v, = (v for v in g.adj[u] if v != 0)
    need(len(g.adj[u]) == len(g.adj[v]) == 2 and not {u,v} & g.cells.keys(),
         "splice must be inside a plain wire")
    info = g.arc.pop((u,v))
    need(g.arc.pop((v,u)) == info == (home,1), "wrong lane")
    g.adj[u].remove(v)
    g.adj[v].remove(u)
    path = [u, *(g.new() for _ in range(extra)), v]
    for a,b in pairwise(path):
        g.adj[a].append(b)
        g.adj[b].append(a)
        g.arc[a,b] = g.arc[b,a] = info
    # g.perimeter presumes equal lane lengths: deliberately do not use it
    # to compute time or rate anywhere in this construction.
    g.audit_local()
    return path


def tour(g, first, d, home, split=()):
    start = state = g.launch(first,d,0)
    label, out, triggers, splice_crossings = first, [], [], 0
    while True:
        u,v,_ = state
        if u == 0 and v in (g.starts[home,1,1],g.starts[home,-1,1]):
            triggers.append(len(out))
        if split and {u,v} == {split[0],split[1]}:
            splice_crossings += 1
        out.append(label)
        state,label = advance(g,state,label)
        if (state,label) == (start,first):
            break
        need(len(out) < 100000, "tour exceeds fixture budget")
    need(len(triggers) == 1 and (not split or splice_crossings == 1),
         "reference does not have one local trigger/splice traversal per tour")
    return tuple(out),triggers[0]


def local_joint(signal, ref, first, sdir, rdir, home, offset, period):
    s = signal.launch(first,sdir,0)
    r = ref.launch(first,rdir,0)
    for _ in range(offset):
        r = ref.step(r)
    orig, name, seen = (s,r),first,Counter()
    marked_ports = {ref.starts[home,d,1] for d in (-1,1)}
    for _ in range(period):
        if r[0] == 0 and r[1] in marked_ports:
            seen[name] += 1
        s,name = advance(signal,s,name)
        r = ref.step(r)
    need((s,r) == orig and name == first, "joint physical orbit did not close")
    return seen


def all_offsets(signal_trace, reference_period):
    # Enumerate discrete contact orbit, NOT a random phase distribution.
    # Translating either starting pulse only changes the first signal index.
    n = len(signal_trace)
    return {tuple(sorted(Counter(signal_trace[(phase+k*reference_period) % n]
                         for k in range(n//gcd(n,reference_period))).items()))
            for phase in range(n)}


def main():
    samples, physical = 0,0
    for sizes in ((1,), (2,1,3), (1,2,1,2), (1,0,2,3,2), (1,3,2,1,3)):
        signal = Apparatus(sizes)
        for home in signal.order:
            ref = Apparatus(sizes)
            path = extend_one_wire(ref,home)
            for d in (-1,1):
                trace,_ = tour(signal,home,d,home)
                reft,_ = tour(ref,home,-d,home,path)
                t, p = len(trace), len(reft)
                need(t == sum(4*n*n for n in sizes) and p == t+2, "unmatched reference tour")
                observed = all_offsets(trace,p)
                target = tuple((i,2*sizes[i]**2) for i in signal.order)
                need(observed == {target}, "clock fails for some phase")
                samples += t
                # Physical edge-by-edge evolution at several unknown phases;
                # all offsets are checked independently above.
                for shift in (0,1,p//2,p-1):
                    counts = local_joint(signal,ref,home,d,-d,home,shift,lcm(t,p))
                    need(tuple(sorted(counts.items())) == target, "local hardware/phase mismatch")
                    physical += 1
    target = Apparatus((1,2,1,2))
    target_trace,_ = tour(target,0,1,0)
    plain = Apparatus((1,2,1,2))
    same,_ = tour(plain,0,1,0)
    need(len(all_offsets(target_trace,len(same))) == 4 and
         all(sum(n for _,n in row) == 1 for row in all_offsets(target_trace,len(same))),
         "identical clocks repeat one and the same channel")
    mismatch = Apparatus((1,1))
    path = extend_one_wire(mismatch,0)
    short,_ = tour(mismatch,0,1,0,path)
    bad = all_offsets(target_trace,len(short))
    need(len(short) == 10 and len(bad) == 2 and
         any(len(row) < 4 for row in bad), "wrong unary packet no longer exposes alias")
    trapped = Apparatus((1,2))
    extend_one_wire(trapped,0)
    state = start = (0,trapped.starts[0,1,0],trapped.cellmask[1])
    for _ in range(4):
        need(not (state[0] == 0 and state[1] in {trapped.starts[0,d,1] for d in (-1,1)}),
             "trapped reference spuriously emitted")
        state = trapped.step(state)
    need(state == start, "trapped control did not close")
    # Same geometry but reference steps at half the physical speed. One
    # slow tour = 84 signal steps here; gcd(40,84)=4 still works. At
    # quarter speed it is 168 and gcd=8 no longer divides the short blocks.
    need(len(all_offsets(target_trace,84)) == 1 and len(all_offsets(target_trace,168)) > 1,
         "time-scale mismatch boundary")
    print(f"matched vernier: {samples} first-contact phases; {physical} full edge-by-edge "
          "joint orbits. T=40, reference=42: 20 clicks in 840 hops, (2,8,2,8) for "
          "every phase; undetuned, mismatched, trapped and speed controls retained.")


if __name__ == "__main__":
    main()
