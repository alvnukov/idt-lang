# What the four-label gate can conserve

These are exact controls on finite classical labels and short mathematical
arguments about their extension. They are not a Lean proof, evidence of
physical charges, a Born readout, or a selection of primitives for nature.
Run the two probes together with
`python3 -m unittest tests.test_chain_relational_probes`.

## What is allowed

All gates fix equal inputs and square to exchange of the two ports. The
chain is closed to external inputs; **any one** adjacent pair may be
updated, any number of times. Thus adjacent swaps are available and any
permutation of sites is reachable. This says nothing about the trajectory
of a particular clocked update schedule or the probability of an outcome.
A reference is *faithful* if neither output of a collision of a different
label with that reference equals the reference. This is not yet a detector.

## Faithful relative to every reference: two parity bits

The eight tables from [the fanout probe](probe_reference_fanout.py) all
replace a pair of distinct labels with the complementary pair. The ordered
outputs may differ between tables, but the possible unordered moves agree.
To derive an additive charge, assign one generator to each label and impose
the three complementary-pair sum equalities. Relative to one label, the
remaining generators satisfy `x=y+z, y=x+z, z=x+y`. Thus `2x=2y=0`
and `z=x+y`. Two independent binary labels attain these relations: the
universal abelian group of additive charges is length plus two parity bits, not a
nonconstant real number per cell. One may calculate the bits by labelling
the cells 0 through 3 and taking the bitwise XOR. Another labelling can
rename sectors, but not change which words of the same length share one.

The [chain probe](probe_chain_relational_charge.py) tests actual one-gate
transitions. There is also a constructive explanation for arbitrary length.
Uniform words are isolated. In a nonuniform word, choose a label 0 and
repeatedly replace two distinct nonzero labels by 0 and the other nonzero
label. This increases the number of zeros until only zeros and copies of
one nonzero label remain. For distinct A,B,C one has `AAB ↔ CCB`:
replace AB by CD, then AD by CB, where D is the fourth label. Consequently
`0xxx ↔ 000x`: replace 0x by yz, use `xxy ↔ 00y`, then replace yz
by 0x. This reduces the nonzero count by twos. At the end one nonzero
label equals the charge; two equal nonzero labels can be changed to a
canonical doublet using a zero as spectator. Permutations are allowed
throughout. Thus at fixed length, every nonempty nonuniform charge class
is one component. This is reachability, not a mixing-rate claim.

## Trying a real weight on neighboring cells

An isolated ordered pair has seven independent real conserved readouts
(four fixed pairs and three cycles). That does not make them conserved
when a neighbor can also interact. For an unrestricted directed bond
table with 16 entries the exact constraints leave four dimensions on a
ring of four, but only one independent value for the total at fixed length:
the densities are `c + g(a) - g(b)`, whose differences telescope. On an
open chain of four, without boundary corrections, only the constant bond
table survives. The probe tests all edge updates, including at the ends.

Why longer but fixed-range additive densities cannot repair this model:
let H be a sum of terms on at most r consecutive sites. Choose two sites
which occur in no common term (ring length ≥ 2r, or open length ≥ r+1).
The change of H when changing one of those sites is independent of the
other. Because swaps preserve H, the same holds for **every** pair of
sites, in every background. Changing one site at a time then writes H
as a constant plus a sum of one-site weights; permutation symmetry makes
these weights the same function up to constants. Complementary collisions
force that real function to be constant. Nonlocal sector indicators,
size-dependent interaction ranges, and invariance only after a whole clock
cycle are not excluded. The finite rank checks do not on their own establish
this general argument.

## Keeping alternatives: faithful relative to two prepared references

The [tradeoff probe](probe_reference_weight_tradeoff.py) retains all 120
gate tables. Counting the constant in the dimension of the one-site
real weight space gives:

| Faithful references out of four | Real-weight dimension | Number of tables |
| ---: | ---: | ---: |
| 4 | 1 | 8 |
| 2 | 2 | 48 |
| 1 | 1 | 64 |

For the 48, up to relabelling the weights are L=0, X=Y=1, H=2 (the
origin and unit are conventional). The faithful references are precisely
X and Y. The unordered reactions are LX ↔ LY, HX ↔ HY, and LH ↔ XY.
This is not an equivalence of all **timed, ordered-output** protocols.

At fixed length N≥2 the integer sum separates 2N+1 possible values.
Only the middle sector splits further: X-only and Y-only words are
separate frozen components. To see why there are no other splits, note
that the excess of H over L is fixed by the sum. Cancel LH pairs to XY.
If the excess is nonzero, at least one extreme survives and can
interchange all remaining X/Y labels by acting as a spectator. With zero
excess, stop with one LH pair and use it to interchange the middle labels.
A mixed all-middle word reaches such a pair by XY → LH; a uniform middle
word cannot. Hence there are 2N+3 components for this move set. This is
a candidate mechanism for an integer conserved quantity, not evidence that
the quantity is physical energy or a Standard Model quantum number.

## Does the order of operations matter at the same weight?

The [middle-label order probe](probe_middle_order_echo.py) uses three cells.
Write A for a collision on sites 0,1 and B on 1,2; read words left to right.
Start with (r,m,r), where m is either middle label and r is either extreme.
Run U=AB then V=ABBA, or V then U. All 48 tables give, respectively,
(r,other-middle,r) and (r,m,r). Both side cells return exactly; both words
use the same numbers of gates and give the same wire permutation if every
collision is replaced by a swap. In fact V then U just exchanges the two
outer cells on arbitrary input. Six collisions are minimal **only** in the
tested forward, nearest-neighbor, two-block search with these controls.

The center weight alone is 1 in both cases. To read the bit, collide it with
another middle label s: the output at a fixed port has nonmiddle weight iff
the labels differed. A reference s matching the initial m reveals the flip;
an independent fair s erases this contrast. Readiness is restored before
this analyzer, not claimed afterwards. A reversible map closed on exactly
two classical labels can only fix or exchange them; two such maps commute.
Here the individual blocks are not both closed logical operations, even
though their two complete orderings return the side cells. No superposition,
relative phase, or quantum probability law follows from this order effect.

A separate calibration distinguishes the tables. Start with (m,s,t) where
s,t are independently fair middle labels, run B then A, and ask only whether
site 0 has middle weight. For 24 tables m=X,Y give 1/2 and 1/2. Their gate
commutes with simultaneously exchanging L with H and X with Y. This exchange
also preserves the detector and the auxiliary preparation, so any circuit
using only these gates, wire routing, and independent-of-input auxiliaries
with that symmetry has identical middle-readout laws on X and Y. For the
other 24 tables the same two collisions give 1/4 versus 3/4 (the direction
depends on the table and naming). Reusing a shared fair label s=t instead
gives 1/2 for both inputs on all 48. These are exact classical preparation
weights, not frequencies inferred from the gate or fitted to an experiment.

## What does a native path record change?

The [path-record probe](probe_native_path_record.py) cuts both orders at the
**same time**, after their common first two collisions AB. At that point the
only middle label is on either the left or the right, never in the center.
For each gate and extreme background r there is one middle label k for
which T(r,k) keeps r on the first port. No table-specific choice is needed:
BAAAB on a separate triple (r,L,H) or (r,H,L) supplies k at its center.
The extreme input stocks and port routing are supplied; preparation side
outputs need not be reset. The trial input m is not used to prepare k.

Let c be the right working cell. A single T(c,k) leaves c unchanged on
both reachable inputs. Its detached pointer equals k on the right path and
the other middle label on the left path: in fact it equals the initial m.
The raw pointer weight is always 1, but a collision with another prepared k
reads the path at a fixed port. This copies a classical bit on the specified
code, not arbitrary states. For any single clean contact preserving c and
conserving the sum of weights, the pointer weight alone cannot change.

With the original analyzer comparing the final center to a supplied copy
of m, the exact rates are as follows. Each row applies separately to every
gate and background, averaging both equally weighted inputs, without
conditioning on the pointer.

| Contact on right cell and pointer | Path readable from pointer alone with fixed apparatus? | UV, VU rates |
| --- | --- | --- |
| No contact | No | 1, 0 |
| T with ready k | Yes; all working cells unchanged | 1, 0 |
| T with ready r | No; pointer always r | 1, 1/2 |
| Two T with ready r | Yes; swaps c into the pointer | 1, 1/2 |

Inverting the contact before the suffix restores both the original triple
and the ready state. The two extreme-ready rows give identical detector
outputs even trial by trial, despite disagreeing on whether a record exists.

A second protocol needs **no matched input reference prepared in advance**. Make
two clean records with independently prepared k cells. Compare the final
center with one record; the other remains readable. The rates are (1,0)
with the records retained, and (1/2,1/2) with no write or after undoing the
writes and comparing with k. The 1/2 assumes fair trial inputs; the clean
comparison succeeds on each input separately. This last readout uses a
correlation with a record, not an interference signal on the center alone.
Here each trial follows one deterministic path; neither readout establishes
quantum complementarity, a Born rule, or a physical detector.
