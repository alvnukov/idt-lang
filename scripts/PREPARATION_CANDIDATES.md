# Where can the preparation weights come from?

Replay: `python3 -m unittest tests.test_preparation_candidate_probes`.
These are deterministic comparisons between mechanisms, not a fit to lab
data or a formal derivation. They target the phase settings missing from
the [two-setting hidden-mode tests](HIDDEN_MODE_CANDIDATES.md). None of
the following preparation protocols is synthesized from that native gate.

### Uniform recurrence is not a phase law

In the [phase-return probe](probe_phase_return_walk.py), start uniformly
in a finite bright set S, apply the same reversible permutation P each
time and read whether the state is still in S. The dark fraction after k
steps is the size of the symmetric difference of S and PᵏS, divided by
twice the size of S. The triangle inequality implies dark(2) ≤ 2 dark(1).
For the six-setting target (0,1/4,3/4,1,3/4,1/4) this forces a maximum
probability error of at least 1/12; a six-cycle attains the bound. It is
not a general exclusion of classical return sets: starting the same cycle
with weights (1,2,1) instead of (1,1,1) gives the target exactly.

One origin for these weights uses equal-probability left/right steps from
the odd sites of an interval with absorbing ends 0 and 2d. Check for
absorption at **each** step; observe survivors after an even number of
steps. The phase interface identifies the d surviving odd sites with
consecutive bins of a 2d-cycle. It supplies the shift and the final
threshold; these are not consequences of the preparation walk.

| Preparation from uniform odd sites | Surviving fraction | Dark per start | Dark among survivors |
| --- | ---: | ---: | ---: |
| d=3, one two-step block, shift 1 | 2/3 | 1/6 | 1/4 |
| d=4, two blocks, shift 1 | 5/8 | 3/32 | 3/20 |
| d=6, two blocks, shift 2 | 3/4 | 5/24 | 5/18 |

For d≥2 the symmetric two-step kernel has positive eigenvector
vⱼ=sin((j+1/2)π/d) and eigenvalue cos²(π/(2d)). Its normalized entries
give the long-time **terminal survivor** distribution. The last k bins then
have total mass sin²(kπ/(2d)), for 0≤k≤d. Finite preparation need not
achieve that limit: for d=6, shift 2, dark-per-start minus survival/4
equals 2⁻ᵗ/12 after t blocks. This follows by applying the two-step kernel
to the symmetric profile; the fixture also checks t=0,…,16. Sampling the
interior of a long trajectory conditioned on past *and* future survival
weights by v², not v. Nor is reading a sign twice the same as preparing
an independent state after the first read.

### Same probabilities, different preparations

| Carrier | Supplied rule | What is checked | Distinguishing control |
| --- | --- | --- | --- |
| [Unit sphere](probe_hemisphere_candidate.py) | Cosine-weighted preparation on one hemisphere; sign detector | Numerical quadrature of (1+n·m)/2, including nonaligned directions | Uniform hemisphere gives 1−angle/π; passive sequential ++ distinguishes mixtures that have identical single-sign statistics |
| [Odd-dimensional bit cube](probe_mid_edge_majority_walk.py) | Uniform adjacent edge, stop at the zero-score midpoint, then choose an endpoint; sign detector | Positive eigenvector (n·v)₊; all 64 direction pairs at d=3 and 1,024 at d=5 | Checking only the endpoint changes the d=3 center probability from 1/2 to 1/3; finite d=5 one-block readout is 19/25 rather than 4/5 |
| [Cyclic ballot tape](probe_cyclic_ballot_preparation.py) | Fair word v, independent uniform reading origin, increment ±1 for agreement/disagreement with preparation word n; stop at the first nonpositive prefix | For each word, exactly (n·v)₊ indexed rotations survive. Same endpoint weights without a long-time limit | Fixing the reading origin introduces a coordinate bias even when the total preparation yield is unchanged |

On the sphere the prepared density is proportional to (n·λ)₊. One
candidate mechanism is supplied isotropic diffusion killed at the equator:
n·λ is positive inside its hemisphere, vanishes on the boundary and is a
principal Dirichlet mode. The numerical fixture starts with that density;
it does **not** simulate or prove diffusion convergence. Splitting the
positive part into an absolute value and a linear term and integrating
over the detector hemisphere gives (1+n·m)/2 in every dimension ≥2.
Thus the law alone does not select the Bloch dimension. In three dimensions
this preparation and detector are the known qubit model of Kochen and
Specker, not a new physical proposal; see section “The Kochen-Specker
model” in [Harrigan and Spekkens](https://arxiv.org/abs/0706.2661).
The sphere fixture states its numerical tolerance and which tests reduce
the angular integral rather than sampling the full higher-dimensional sphere.

On an odd-dimensional bit cube, n,v,m have ±1 entries and the benchmark
is (1+n·m/d)/2; only the finite vertex directions are tested. Readout is
by majority of matches. One midpoint block from the uniform bright half
at d=3 has survival 1/2 and conditional masses (3,1,1,1)/6. On the tape
the same endpoint distribution comes from an initially **unrestricted**
cube, with exact herald fraction 1/4 at d=3, 3/16 at d=5, 5/32 at d=7.
Here the herald is determined by preparation before the analyzer is
chosen. It is not permission to discard later detector failures.

All three constructions assume the available settings, source of
unbiased choices, and a way to read a sign. They neither select the
primitive nor derive arbitrary measurements, composite systems, Pauli
statistics or physical scales. An experiment that distinguishes two
preparations must also specify what is retained between measurements.
