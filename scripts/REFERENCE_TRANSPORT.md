# What can a triangle use as a phase reference?

A single neutral, real three-label current has only two independent
components. The earlier [exchange apparatus](CONTACTS_AND_COMPARATORS.md)
could reproduce three trine tests, but gave no fourth local reading. Here
**one laboratory package now contains two currents**, a data triangle and a
reference triangle. This is a change in the candidate, not a new prediction
of the smaller one.

```sh
python3 -B -m scripts.replay_primitive_probe_campaign --bundle reference_transport_and_carriers
```

## A new reading and a coherent operation

Turn both triangles cyclically together. Add the three possible path
lengths (zero, one, two) in one output, and subtract this sum from three
straight paths in the other. These are integer signed paths, not angles
or probabilities. The [two-output contact](probe_triangle_cycle_phase_axis.py)
has constant ticket gain nine. It prepares two states on which **all three**
old tests are fair but the new test is deterministic and opposite. The
affine dimension of the normalized 8-by-8 table increases from two (old
trines) to three. Flipping just one winding swaps the new bit. An initially
independent product of two neutral currents itself has zero bias on it.

Can this package do more than switch among eight states? [Split, turn the
reference on one undetected path, then coherently undo the split](probe_coherent_triangle_pulses.py).
One pulse gives a new-reading frequency 504/576 = 7/8; reversing the turn
gives 1/8; an empty bypass gives 1/2. The new preparation is **outside the
convex hull** of the original eight: two absolute mean outcomes sum to 5/4
where every old mixture gives at most one. If a distinguishable path record
survives, each branch gives 1/2, despite the same clean output port.
Two distinct trine pulses have rotation-product trace 9/16. The exact
finite matrices and the standard closed-subgroup argument give a dense
set of rotations **conditional** on arbitrarily long coherent programs and
the usual rotation topology. Not every rotation is exactly available;
there is no derived continuous time or Hamiltonian. Literal ticket counts
grow by sixteen per full pulse (four per compressed pulse).

## Before and after two sources meet are different experiments

| Reference contract | What the same laboratory can compare |
| --- | --- |
| One finished real package from each source, independently hidden cyclic frames | On 576 ordered input/frame combinations a premeasurement accepts half, then antiswap exactly matches the complex pure-state benchmark. With zero false positives no one-pair positive binary effect can do better than half efficiency on orthogonal inputs. |
| All those inputs retained; false positives allowed | Exact best maximum frequency error **1/12**, even for any positive real effect on the pair. Two cycle comparisons, a swap and an independent 1-in-3 choice attain it. |
| References meet **before** the independent setting choices and local preparations | Keep both original reference flags, reversing one winding on one flag. Direct whole-package swap now gives all 64 reference comparisons on **each** initial flag without another half-loss. |

The [first two results](probe_triangle_reference_sewing.py) use a finite
certificate: equal-input vectors span 14 dimensions out of 16. Moreover a
weighted mixture of orthogonal inputs minus twice the equal-input mixture
has positive part of trace 1/4. These are bounds for one-copy positive
effects in the stated real model, not for devices that receive the
preparation labels or have a pre-shared extra resource. Retrying with
fresh packets changes the copy budget.

In the [prior-contact control](probe_prior_triangle_reference.py) all 8,192
local joint readout entries factor as products, including 1,920 zeros, but
the real joint current has matrix rank two on each preparation and initial
flag. The prepared **sources do not factor**. The uncorrected positive
flag misses 20 of the 64 comparison targets. A related [reference transfer](probe_native_triangle_reference_fanout.py)
shows that following a contact with a fresh reference one can read **the same**
data through either reference. Reading via a fresh untouched one loses the
pole contrast; this is not cloning a second data packet.

The premise has an experimental counterpart. The [Renou network bound](https://arxiv.org/abs/2101.10873)
assumes real quantum composition with separable source resources; shared
classical randomness alone does not evade it. [Chen et al.](https://arxiv.org/abs/2103.08123)
report 8.09(1), and [Wu et al.](https://arxiv.org/abs/2201.04177) report
7.83(3) on the corresponding score, versus a bound of 7.6605. These are
different platforms with partly overlapping author teams, not observations
of this contact. Wu's photon experiment retains a detection loophole.
[Weilenmann et al.](https://arxiv.org/abs/2502.20102) show why earlier
sharing matters: a real entangled reference can be reused across rounds.
Separation of today's emissions is not certification of yesterday's
initial conditions. Our finite comparison is not a reanalysis of either
experiment's trial stream.

## A three-plus-two split, with its condition exposed

The [sparse five-slot pencil](probe_sparse_chiral_supports.py) asks which
punctures of a fixed 40-edge support can satisfy a *hypothetical* rank
restriction. Keep all ten channels active but allow an isolated state:
the smallest nonempty deletion permitting a weighting without any rank-ten
combination is five edges, a single vertex star. Keep **all sixteen states
active as well**: now twelve deletions are necessary, and precisely twenty
supports at that size admit such a weighting. They choose two of the five
slots and remove all links internal to one of the resulting parity halves.
This is a conditional structural selector, not evidence that nature
minimizes deletions or tests these ranks. A different 14-edge control passes
every one-, two- and three-channel test yet forces rank ten on four channels.
The original nonzero-domain checker rightly leaves zeros unsupported.

From the surviving [anonymous adjacency alone](probe_anonymous_punctured_carrier.py)
one can recover a cube of eight degree-five states, with two degree-two
twins joining each antipodal pair. No Euclidean space is involved. Its
768 automorphisms have just **two vertex orbits**; hence an invariant
scalar on its vertices cannot give six charge values. Given the commuting
five-port completion prescription there are eight addressed completions,
indistinguishable on the current graph. Three extra yes/no transition
probes would distinguish them if such a channel existed. Given **also**
a chosen vacuum, centered additive charges, block symmetry and neutrality
of that vacuum, the conventional ratio and one-family multiplicities
follow up to unit/sign. These assumptions do not pick gauge interactions,
masses, or generations.

## Returning to the same station is not returning with the same frame

In three finite [anonymous station networks](probe_relational_chart_holonomy.py)
the immediately visible neighborhood, all 24 small triangular loops and
the first straight return at six steps agree. Comparing directions around
the long return finds respectively trace/determinant (3,+1), (1,−1) and
(−1,+1): a translation, a glide, and a half-turn screw. Independent
renaming of each station's chart does not erase the distinction. This is
global orientation transport in deliberately constructed locally flat
examples. It is not evidence for local curvature or a derivation of gravity.
