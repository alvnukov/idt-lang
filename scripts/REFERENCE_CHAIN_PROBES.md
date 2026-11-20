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
