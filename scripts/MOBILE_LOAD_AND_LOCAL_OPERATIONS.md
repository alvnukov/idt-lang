# Can the marker be matter, and the clock a local event?

The [collision census](LOCAL_CELL_INFERENCE.md) inferred a swap between a
travelling and a parked bit on the prepared one-marker sector. The following
candidate represents that sector using **two indistinguishable conserved
units**, not one independently initialized binary register at every cell.
It still assumes that a moving packet and stock resting at a site are
operationally different, as well as a reciprocal graph and specified ports.

### A local load exchange

If k≥1 units arrive and s≥0 are parked, **send 1+s onward and leave k−1
behind**. This is a conservative involution. With two units the alternatives
are one moving pair, or one moving singleton and one parked singleton. The
same occupied-site dynamics results regardless of which unit one chooses
to name. The [load probe](probe_indistinguishable_mobile_load.py) checks all
192 two-unit states of the example against the earlier bit apparatus,
including 80 trapped states and 112 active ones. One unit alone cannot
produce a returning pair from an empty apparatus. This removes named
per-cell *material* bits, not the information in the parked location.

There is a useful conditional characterization: suppose the outgoing size
depends only on the prior stock, k′=F(s). Positivity and conservation on
(1,0) give F(0)=1. Reversibility on (k,0) then forces F(k−1)=k. Remove
that independence premise and many reversible cold-splitting completions
remain. At total four, one sends (2,2) to (3,1), another leaves (2,2)
unchanged. A threshold test need not distinguish them: when the two extreme
load states are interchanged, a bijection leaves the positive-positive
interior within itself. A load-resolving instrument can distinguish them.

On active lengths (2,1,3) the **occupied-packet** hop counts are 4:1:9,
but the **unit fluxes** are 6:2:12. Which physical quantity is registered
is consequential. At a cold station a packet of any size sends exactly
one unit around a reporting loop. Returning that unit restores both the
packet and station. If the station initially contains s units the loop
carries 1+s instead. Removing or absorbing the reporter prevents the return.

### Can one local observer count visits occurring elsewhere?

The [serial return bus](probe_serial_return_bus.py) has a measured link at
the observer for each rail. A reporting tap and the bus have the same
local exchange rule: a moving excess k−1 and stationary stock s are swapped.
When unequal, the tap crosses the signal and bus ports; equal loads pass
straight. Distinct bypass and return ports distinguish a skipped from a
finished report without erasing its origin.

A shared circuit of taps initially stocked at r sends a fixed packet of
1+r around the bus and parks k−1 at the origin. Other taps are unchanged.
The returning packet meets the one changed tap and restores both the
outgoing signal and its stock. No source address rides the bus. A load
k=r+1 would be invisible. Two stages, r=0 and r=1, handle that precise
case: bound packets use the first bus; singletons fall through to the
second. A reversible meter at the observer sends exactly **one unit**
through the same measured link for either report size. Each distinct rail
still has its own identifiable meter.

On the two-unit example this complete network produces **4,1,9 local
counts after 156 actual edge traversals**. With prescribed unequal
reciprocal travel times, the same path took 625 instead of 156 time
units; the counts did not change. This is an event-order result, not a
new clock law. It costs extra wiring, six baseline units in the example,
clean stores and an in-flight request limit of one. Two concurrent
requests restore both original loads at their respective exits but cause
only **one** common meter crossing. Nothing was silently treated as two.
A passive meter is not the absorption of a quantum, and an external
stream arriving at arbitrary times is a different experiment.

### A four-port operation: what was programmed, and what was not?

Put one binary travelling slot and three stored slots in a short petal.
Use the [word experiment](probe_mobile_cell_complement_mixer.py) with the
cell that reflects on double occupancy and not on transfer. F completes a
normal passage to the hub; B bypasses one stored bit on that passage.
The same word of 16 commands, `FFBFFFBFBFBFBBFB`, acts on all six
two-mark inputs as a fixed four-cycle of the addressed slots followed by
set complement. Direction returns to its initial positive value. This
word was *synthesized against the target*, not inferred from a law of
nature. Physical replay takes 216–320 edge hops depending on the input.
One further bypass passage distinguishes the six outputs from the local
lane and return port, without reading the remote stores; eleven more
such passages restore data and direction. The preparations, switched
bypass, feedback path, readout and timing resources are explicit.

For N prepared packets let m_j count the packets containing slot j.
Then m′=N·1−Pm for the stated port permutation P. This yields the
complementary port-count relation **without finding and pairing all the
occurrences in a global list**. On centered counts at fixed N it is just
−P, not arbitrary interference. The [first-moment check](probe_packet_marginal_automorphisms.py)
classifies all 720 reversible maps of two-of-four subsets: 24 wire
permutations and 24 complemented permutations preserve equal input port
marginals for every ensemble. For every other map two inputs with equal
marginals give different output marginals. With two marks and five or
more slots only permutations survive that same closure requirement: two
intersecting edges of the complete graph cannot be re-paired, and its
stars of size ≥4 distinguish the underlying slots. None of this excludes
detectors sensitive to correlations, ancillas, or coherent amplitudes.

### Can the programmed operation be replaced by static hardware?

The [static search](probe_static_cell_mixer_search.py) gives every site
one of the 40 local reciprocal rules that conserve carried plus parked
marks. It checks all 40³=64,000 ordered triples with **no changing switch**.
The predeclared target was complement **and** one four-cycle on the owned
ports at one common passage count, with restored forward direction for every
two-mark input. No triple reaches it. The search checks the full orbit of
each first-return permutation, not just a few small powers. Even ignoring
direction, none realizes this particular target on all six inputs.

A separate result is positive: **16 assemblies realize bare complement**
with no rotation of the output names. Two symmetric assemblies use only
the earlier timing-selected cell rules. For example, in X–S–X the outside
cells reflect when the carried and stored bits disagree, the middle passes
straight, and every cell swaps the two bits. At the third hub return
all six two-mark inputs have complemented, forward-facing outputs after
exactly **32 physical edge hops**. The same statement does not hold on the
single-mark sector. A three-return counter or a calibrated time is still
a resource: for one input the first and third returns have exactly the
same local side and lane. Reassigning output names on paper would not make
the failed four-cycle target a success.

A [separate timing holdout](probe_static_cell_elapsed_readout.py) allows
different passage counts on the six inputs but demands return to the hub at
the *same positive physical time*. Intersections of congruences over the
actual edge-hop periods check all times, not just a horizon. The four-cycle
target still has no hit. For bare X–S–X complement the local end-of-gate
problem can also be quantified: receiving just side and lane at each return,
no two-state deterministic observer can announce precisely the third return
on all six inputs, even if initialized using their starting lane. A
three-state event counter suffices. This is not a lower bound for observers
with their own time readout or extra contacts.

Reproduce the occupancy, local bus, mixer and population-boundary runs with
`python3 -B -m scripts.replay_primitive_probe_campaign --bundle mobile_load_operations`.
The [retained inventory](../data/primitive_mobile_load_inventory.json)
keeps the proposals, weak readouts and negative controls separately.
