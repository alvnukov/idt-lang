# Five binary directions, compatible contexts, and what a recorder can fake

The unsigned carrier has sixteen possible translations and five mutually
equivalent elementary ones whose full product is identity. Now add a binary
register and **assume** that exchanging the order of two words can differ
only by a central flip (one that commutes with everything). The resulting
commutator on the translation space is alternating and bilinear. Full
permutation symmetry of the five directions permits exactly two forms:
all commute, or every pair of distinct elementary directions anticommutes.
Symmetry allows the nontrivial case but does not force it. With only the
marked 3+2 symmetry there are four forms, of ranks 0, 2, 2 and 4.

## The squares matter as well as the commutators

For the nontrivial full-rank commutator the probe checks all sixteen
quadratic refinements, i.e. assignments of the central sign obtained by
squaring a lifted word. They fall into a root, its five neighbors, and its
ten nonneighbors under direction relabelings. In the symmetric root choice
only five nonzero cosets are binary involutions; every two of them are
incompatible. There is **no** three-by-three Peres–Mermin measurement
square in that single lift. All five generator squares agree here, but odd
permutations of the named lifts need sign corrections to preserve their
ordered-product relation.

A refinement associated with a second mark two steps away reverses the
squared signs of its two distinguished directions. This is a *different
microscopic rule*, not the result of attaching a label to an unchanged
device: ordinary sign redefinitions do not change squares. The changed
group has nineteen nonidentity involutions instead of eleven. An Abelian
control even reproduces the five changed generator squares without the
order signal; measuring squares alone is insufficient.

The changed lift has nine noncentral involution cosets, six commuting
triples, and 72 ordered square layouts. A real signed-matrix representation
and a separately supplied ideal projective readout yield five positive
and one negative row/column product. Among the 512 context-independent
assignments, 96 fail one condition, 320 fail three and 96 fail five. The
maximum signed score is 4 versus 6 for the ideal joint model. A sampler
given the entire context can produce uniformly distributed permitted
triples; product identities in a group of permutations do not themselves
define repeatable nondisturbing measurement instruments. Simply taking
two separate copies also does not identify their independent central
flips. A composed parity reference or an extra fourth-root phase is a
separate construction.

## Finite memory survives some apparently strong checks

The separate sequential probe implements the three- and four-state automata
of [Kleinmann et al.](https://doi.org/10.1088/1367-2630/13/11/113011)
under their stated probability-one support contracts. It checks arbitrary
word lengths within each context by finite-state reachability, not just the
six context products in one ordering. Four more supplied, persistent,
uniform sign bits make each individual compatible-context distribution
agree with the ideal maximally mixed target. These are extra preparation
resources; refreshing the bits after every letter breaks repeats.

Two short interventions distinguish the candidate recorders for **every**
initial state, even with that mask. In `α,B,C,β,B` the three-state model
changes its B answer; in `β,a,b,C,c` the four-state model yields
`a b c = −1`. The ideal compatible projective instruments assign zero
probability to the respective violations. This excludes those two proposed
sequential models in the comparison, not all classical memory, and does
not imply that a physical apparatus satisfies ideal compatibility.

The [trapped-ion experiment of Kirchmair et al.](https://doi.org/10.1038/nature08172)
reported square scores from 5.23(5) to 5.46(4) in ten preparations (6,600
trials per score; figure error bars one standard deviation). Compatibility
was imperfect; its separate disturbance-sensitive inequality was not the
entire ideal square. The independent [single-photon experiment of Amselem
et al.](https://doi.org/10.1103/PhysRevLett.103.160405) used path and
polarization rather than these graph operations. The [authors' Table I](https://arxiv.org/abs/0907.4494)
gives 5.4550 ± 0.0006; the body gives a different summary, so this number
is attributed specifically to the table. The experiments are not graph
observations and have not been pooled.

Run `python3 -B scripts/replay_primitive_probe_campaign.py --bundle carrier_sign_contexts`.
All three source records and the weak/negative alternatives remain
unassessed as physical primitives.
