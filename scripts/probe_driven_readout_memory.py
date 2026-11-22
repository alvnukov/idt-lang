"""One deterministic event for a chosen circuit: what must the device remember?

Consider a finite, time-homogeneous, total deterministic transducer. It sees
the present setting c, emits one bit, and updates its joint source/device
state. From a fixed initial state, require for EVERY finite drive prefix
followed by an endlessly repeated nonempty drive word that the limiting
frequency of ones among occurrences of each recurring c be a_c/q_c in
lowest terms. There is no condition on settings visited only finitely often.

Every reachable closed walk can be driven periodically after reaching its
start. If it visits c exactly m times, its ones count equals m*a_c/q_c;
thus m=0 mod q_c, also when c is absent. Choose a reachable bottom strongly
connected component and a state s in it. Two drive words taking s to the
same state can be closed back to s by the SAME suffix. Subtract the two
closed counts: the words have identical per-setting residues mod q_c.
Every residue vector is attainable by spelling an appropriate word from s
(the component is closed under all inputs). Hence there are at least
product(q_c) states, not merely lcm(q_c). A separate periodic emitter with
q_c slots and a_c ones for each c attains the bound as a target-aware control.
No randomness, independence, or uniform initial phase is required or proved.

The native construction below instead enumerates the microscopic tickets
via each setting's own persistent clock; no target odds enter the routing.
It supplies an initialized source, gates, signed cloud, matching, counters
and access to the chosen circuit BEFORE addressing its first gate. Whole
cloud propagation is not a dynamics on a lone click. Clock phases count
as memory, including any counter placed in the source or experimenter.
Unbounded counters or a supplied clock/state stream need not admit a finite
joint-state model. Unknown settings chosen only after an early gate cannot
be used there. Neither finite records nor an incorrect candidate establishes
physical randomness or excludes a class of unrestricted event mechanisms.

Run: python3 -B -O -m scripts.probe_driven_readout_memory
"""

import sys
from collections import Counter
from itertools import product
from math import prod
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_native_recurrence_witness import native_prefix
from scripts.probe_rotor_event_stream import PLATE, H, Stage, embedded, need, prepare


def cycle_masks(dest: tuple[int, ...]) -> set[int]:
    """Edge masks for each nonempty setting on each reachable simple cycle.

    Edges 2*s and 2*s+1 are the two possible settings at state s. All
    outgoing edges are defined. The prescribed initial state is 0.
    """
    n = len(dest) // 2
    reachable = {0}
    for _ in range(n):
        reachable |= {dest[2*s+c] for s in reachable for c in (0, 1)}
    masks = set()

    def visit(start: int, s: int, seen: set[int], edges: tuple[int, ...]) -> None:
        for c in (0, 1):
            e = 2*s+c
            t = dest[e]
            path = edges + (e,)
            if t == start:
                for k in (0, 1):
                    mask = sum(1 << j for j in path if j % 2 == k)
                    if mask:
                        masks.add(mask)
            elif t > start and t not in seen:
                visit(start, t, seen | {t}, path)

    for s in reachable:
        visit(s, s, {s}, ())
    return masks


def small_memory_oracle() -> None:
    """Independent of the residue bound: inspect transitions AND emissions."""
    count = 0
    for n in (1, 2, 3):
        for dest in product(range(n), repeat=2*n):
            masks = cycle_masks(dest)
            for labels in range(1 << (2*n)):
                # Some recurring setting on a reachable simple cycle is
                # completely biased, not merely different from one half.
                need(any((labels & m) in (0, m) for m in masks), "short-cycle witness")
                count += 1
    need(count == 46916, "exhaustive two-setting binary machines")
    dest = tuple(s ^ (1 << c) for s in range(4) for c in (0, 1))
    labels = sum(((s >> c) & 1) << (2*s+c) for s in range(4) for c in (0, 1))
    need(all(2*(labels & m).bit_count() == m.bit_count() for m in cycle_masks(dest)),
         "four-state fair response on every simple cycle")
    print(f"{count} machines of 1..3 states: a reachable cycle of length <=3 gives"
          " one recurring setting only one outcome. Four states attain half/half.")


def tick(stages: list[Stage], phase: int) -> tuple[int, int]:
    """Route exactly one tag, with raw mixed-radix digits, not port weights."""
    p = (0, 0)
    for routing, gain in stages:
        digit, phase = phase % gain, phase // gain
        p = routing[p, digit]
    need(phase == 0, "phase exceeds raw ticket stock")
    return p


def interleaved_native() -> None:
    word = (embedded(0, 2), embedded(2, 2))
    oracle = tuple(native_prefix(2)[1:])
    need(tuple((p.numerator, p.denominator) for p in oracle) == ((1, 2), (1, 8)),
         "independent native port targets")
    for reverse in (False, True):
        circuits = [prepare(word * t, reverse) for t in (1, 2)]
        gains = [prod(g for _, g in stages) for _, stages in circuits]
        need(gains == [16, 256], "raw stock")
        for offsets in ((0, 0), (15, 255), (7, 145)):
            phases = list(offsets)
            quota = [2*g for g in gains]
            outputs = [[], []]
            previous = 0
            for t in range(sum(quota)):
                c = int(previous == 0) ^ int(t % 5 == 0)
                if len(outputs[c]) == quota[c]:
                    c ^= 1  # ensure both settings recur for the finite assay
                cloud, stages = circuits[c]
                p = tick(stages, phases[c])
                previous = cloud[p[0]][0] // 2
                outputs[c].append((p, previous))
                phases[c] = (phases[c] + 1) % gains[c]
            for records, g, target in zip(outputs, gains, oracle, strict=True):
                need(records[:g] == records[g:] and len({p for p, _ in records[:g]}) == g,
                     "every sliding local period emits every microscopic tag once")
                need(sum(port == 0 for _, port in records[:g]) * target.denominator
                     == target.numerator * g, "external native port oracle")
    print("Adaptive drive of native depths 1,2: one tag/shot; 16 and 256 distinct tags"
          " per local period. Port-0 rates 1/2 and 1/8: >=16 joint states;"
          " separate raw-ticket clocks supply 4096 phase states (not port-minimal).")


def shared_clock_control() -> None:
    """Same port observable; changing a terminal plate does not change it."""
    circuits = [prepare((H,), False), prepare((H, PLATE), False)]
    for c, (cloud, stages) in enumerate(circuits):
        need([cloud[tick(stages, k)[0]][0] // 2 for k in range(4)] == [0, 0, 1, 1],
             f"late setting {c} has the same directly counted ports at each phase")
    for offset in range(4):
        for separate in (False, True):
            phase = [offset, offset]
            history = []
            postwarmup = [Counter(), Counter()]
            for t in range(258):
                # A=0 iff port two previous shots ago was 1. No peeking.
                c = int(history[-2] == 0) if t >= 2 else 0
                cloud, stages = circuits[c]
                key = c if separate else 0
                port = cloud[tick(stages, phase[key])[0]][0] // 2
                phase[key] = (phase[key]+1) % 4
                history.append(port)
                if t >= 2:
                    postwarmup[c][port] += 1
            if not separate:
                need(postwarmup == [Counter({0: 128}), Counter({1: 128})],
                     "shared clock pooled fairness masks conditional extremes")
            else:
                need(all(sum(h.values()) >= 4 and abs(h[0]-h[1]) <= 2
                         for h in postwarmup), "persistent per-setting local subsequence")
        cloud, stages = circuits[0]
        reset = [cloud[tick(stages, offset)[0]][0] // 2 for _ in range(8)]
        need(len(set(reset)) == 1, "resetting to identical phase repeats one port")
    print("H vs H then plate, feedback two shots back, all four shared phases:"
          " A=128:0, B=0:128, pooled=128:128. Per-setting phases resist this"
          " split only with setting access; identical per-shot reset repeats one port.")


def omitted_memory_control() -> None:
    """A one-state box is a false counterexample if its clock input is free."""
    unbounded_visits = [0, 0]
    counted_state = 0
    previous = 1
    for t in range(259):
        c = int((previous == 1) ^ (t % 7 < 3))
        external_tick = unbounded_visits[c]  # per-context visit clock, NOT wall time
        port = external_tick % 2   # the box has no internal memory
        need(port == ((counted_state >> c) & 1), "hidden clock parity")
        unbounded_visits[c] += 1
        counted_state ^= 1 << c
        previous = port
    need(min(unbounded_visits) > 32, "both external clocks exercised")
    print("A nominal one-state box driven by external visit counters reproduces"
          " alternating subsequences; counting the two clock parities restores"
          " four effective states. A free global shot index is not a visit clock.")


def main() -> None:
    small_memory_oracle()
    interleaved_native()
    shared_clock_control()
    omitted_memory_control()


if __name__ == "__main__":
    main()
