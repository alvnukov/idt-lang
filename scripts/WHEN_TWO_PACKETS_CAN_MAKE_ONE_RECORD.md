# When two packets can make one record

One offered four-place contact can record a property of **two** addresses and
stay reversible. But a network whose distant instruments merely read local
addresses cannot reproduce the published quantum-network score, even with
that new contact at the middle station. These are two different findings.

## Positive addresses before signed contrasts

Use two copies of the [sixteen-address carrier](WHEN_PACKET_ORDER_GENERATES_A_QUARTER_TURN.md)
with three colored matchings, quarter turn `W=ABC` and half turn `Z=W²`. Its
raw states are 256 distinct ordered pairs. Two proposals identify simultaneous
advances: `D=(W,W)` or `H=(W,W⁻¹)`. On the raw addresses these are ordinary
permutations, with no sign, amplitude, probability, or phase origin assigned.

| Moves whose orbits define a record | Number of cells | Which moves leave the record unchanged? (S, H, D, L) |
|---|---:|---|
| None | 256 | 0000 |
| Simultaneous half turn S=(Z,Z) | 128 | 1000 |
| H | 64 | 1100 |
| D | 64 | 1010 |
| Both H and D | 32 | 1110 |
| Independent quarter turns in each copy | 16 | 1111 |

Here L=(W,identity). The tests compare every partition and every start; all
six local context moves descend to each quotient. Coarsening loses the
ability to read both exact input addresses from the cell alone. On products
of signed differences `b_i=e_i−e_Zi`, the two 64-cell proposals instead keep
opposite eigenvalues of the joint turn: −1 for H, +1 for D. Pushing the raw
integer product onto either set of cells gives **twice** the difference of
two cell vectors. That factor is not a normalized outcome probability.
Mirroring one menu interchanges H and D; neither is selected by isolated
carriers. This supplies a positive-address origin for two of the alternatives
in the earlier [algebraic comparison](TWO_SOURCE_PHASE_NETWORK.md).

## What the detector retains

Fix either a straight identification of the context colors or a mirror
exchanging A and B. Propagating the matching edges from a root pair gives
16 alignments for each color permutation. The 48 even alignments preserve W
and the 48 odd ones reverse it. For one fixed color convention the 16 sheets
`j=f(i)` partition the pairs. A sheet and the W-cycle of i jointly identify
one of the 64 cells. This is the wiring prescription, not a choice made by
the raw firing rule.

For each input (i,j) wire its two one-hot source rails to two initially empty
rails: one for that cell, the other for the C-matching edge of i. On raw bits
the only test is “two of the four occupied”; firing complements all four.
Scanning **all** contact masks gives exactly one offer on every input and
exactly its inverse after firing, in both modes. The residual C edge
distinguishes the four members of the cell without attaching a phase origin.

| Output wiring | Extra rails (class + residue) | Offers after the click |
|---|---:|---:|
| Private pair of rails for each input | 256 + 256 | 1 |
| Named cell plus C edge | 64 + 8 | 1 |
| Named cell plus Z edge | 64 + 8 | 2 |
| Both rails name only the cell | 64 + 64 | 4 |

Unobserved spectator copies do not repair an ambiguous inverse because the
guard does not read them. Eight residue labels are minimal only when one rail
must name the class, a separate one-hot tag is an equivariant function of i,
and all four class members must be distinguishable. The color-preserving
group acts regularly with order 16, W is central of order four and Z is a
nontrivial commutator. A four-label tag separating each W-cycle would let
W act as a four-cycle whose centralizer is abelian; its commutator Z could
not then act as W². The eight C edges attain the restricted bound.

A **single** equality sheet is a different instrument. It can fire if the
two addresses agree, but it does not record a negative result when no
contact fires. On any one four-cycle the *same* equality instrument sees
4/16 coincidences for the independent product, 4/4 for a synchronous scan
in the same direction, and 2/4 for a synchronous scan in opposite directions.
All three preparations have identical one-arm histograms. None of their
weights or scan schedules follows from the contact itself.

## The exposed network limit

Give the outer readers arbitrary deterministic outputs A(x,i), C(z,j) for
each setting, and let the middle reader report any four-way coarse label of
(i,j) independently of those settings. Retain every trial. Even granting
these extra readers, each address pair gives one of 2,048 deterministic
tables for the three-CHSH network functional T. Their scores are −6, −2,
+2 and +6 with multiplicities 256, 768, 768 and 256. A normalized mixture
independent of the settings is therefore bounded by **6**, even if the two
source addresses themselves are correlated. A complete native contact with
a specified four-way relabel attains 6. If the middle reader learns the
settings, or if events are selected as a function of them, the checker can
produce 12. Both are outside the stated comparison.

This is below the experimental aggregates 8.09(1) in a superconducting
processor ([Chen et al.](https://arxiv.org/html/2103.08123v3)) and 7.83(3)
in a photonic network ([Wu et al.](https://arxiv.org/html/2201.04177v2)).
The latter used 77,326 four-photon coincidences and explicitly leaves the
detection loophole open. These are the experimenters' estimates, not a
reanalysis of their trial data. The 6 here is **not** the 7.6605 numerical
upper bound for the broader real quantum model under its source assumptions
in [Renou et al.](https://arxiv.org/html/2101.10873v2). A successful local
coincidence does not bridge this gap. Conversely the comparison does not
rule out an uncompleted primitive without the specified local-reader model.

Replay the [raw orbit/network check](probe_raw_packet_phase_quotients.py) and
[microscopic coincidence and inverse](probe_native_phase_coincidence.py) with
`python3 scripts/replay_primitive_probe_campaign.py --bundle bench_positive_phase_records`.
