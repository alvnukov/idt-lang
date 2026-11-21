# One preparation table, different information at the detector

Replay: `python3 -m unittest tests.test_cube_detector_probes`. A source
setting is a word n of three signs. As a comparison with a qubit, assign
it the **supplied** Bloch direction n/√3. The original eight sign tests
use directions of this same form. The comparison below varies the record
retained by the source, while keeping the apparatus independent of n
given the received record. No statistics in this file are experimental
data or a derivation of the qubit measurement rule.

| Record delivered | Eight cube-aligned binary tests | Matching four-outcome tetrahedral apparatus | One new orientation |
| --- | --- | --- | --- |
| Final vertex v of the [preparation](PREPARATION_CANDIDATES.md), law (n·v)₊/6 | All reproduced by majority | Best normalized worst-entry error 1/24 | Face diagonal separates two preparations |
| Uniformly chosen coordinate and its single bit | All reproduced by comparing that bit | All reproduced: pick uniformly one of the two tetrahedron words matching the bit | Cartesian coordinate reveals a strict information limit |
| Uniformly chosen erased coordinate and the two surviving bits (an edge) | All reproduced | Reproduced, including rotated tetrahedra | Enough for each finite-outcome qubit measurement on these eight source settings |

### A genuinely normalized measurement

The four target effects use tetrahedral sign words tⱼ of parity +1, with
p(j|n)=(1+n·tⱼ/3)/4. This is one device returning one of four outcomes,
not four separate yes/no tests with independent denominators. For the
quantum benchmark see [Renes et al.](https://arxiv.org/abs/quant-ph/0310075).

The [endpoint certificate](probe_endpoint_tetra_detector.py) permits *any*
stochastic four-outcome detector on v, not just threshold detectors. Let
D± denote the mean, over j, of its reported P(j|±tⱼ). Normalization at
each hidden vertex gives D+ + 3D− ≥ 2/3, whereas the ideal table gives
1/2. A detector with maximum entry error 1/24 attains the lower bound.
Using only four negative preparations and one positive still separates,
with exact error 1/52. All six ways to merge a pair of outcomes admit
normalized response functions. Reject only the specified unrefined
carrier and target, not all vertex models or all binary tests.

An apparatus with an extra no-click outcome can reproduce the **conditional**
four-outcome table at efficiency 2/3 for *every* preparation. The fixture
checks the raw losses and the ceiling under exact conditional agreement
and common efficiency. In a separate two-outcome test the target contrast
between words (+++) and (--+) along (1,1,0)/√2 is √(2/3), whereas their
endpoint distributions have total variation 2/3. Any source-independent
readout can only reduce that distance.

### What does retaining a little history buy?

In three dimensions a strictly positive circular ballot survives exactly
when its first two increments are positive. Retaining its last-read axis
and its output vertex yields this same joint law: choose an incident edge
of the prepared word uniformly, then choose an endpoint of that edge with
a fair coin. Passing just the vertex, just one bit, and the edge are
different source channels. The [edge fixture](probe_erased_bit_readouts.py)
checks the joint, not only its endpoint marginal.

For **any** normalized affine target pⱼ(n)=aⱼ+gⱼ·n, nonnegative at all
eight corners, the edge can support the whole apparatus precisely when
Σⱼ |gⱼᵢ| ≤ 2/3 for each coordinate i. Necessity follows by comparing
sources differing in that one bit: one third of their output edges are
identical. For sufficiency, distribute each coordinate's absolute slope
over the two kinds of edges which retained it, with capacity 1/3 per
kind. Individual cuts give the stated inequalities; any two coordinates
touch all three kinds and the total demand is ≤Σaⱼ=1 by corner positivity.
Split each outcome's signed slopes by these common fractions, then fill
unused capacities with constants. The result is a normalized response at
**every** edge. The replay constructs it with exact rational arithmetic.

For qubit effects specified by weights aⱼ and vectors rⱼ, the supplied
formula has gⱼ=aⱼrⱼ/√3, Σaⱼ=1, Σaⱼrⱼ=0 and |rⱼ|≤1. Each demand is at
most 1/√3, below 2/3. In contrast, a target that copies one coordinate
with certainty exceeds capacity. The one-bit channel's corresponding
capacity for a single coordinate is just 1/3.

The edge decoder is constructed from the whole requested measurement.
It is not an apparatus-independent representation of each effect, not an
origin for arbitrary physical settings, and not a sequential measurement
or composition law. These models agree on a substantial family of tests
but retain different latent information. Passing the eight preparations
does not establish a model for all qubit states.
