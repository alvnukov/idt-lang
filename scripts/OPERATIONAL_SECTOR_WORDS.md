# Native sector words: exact replay and its boundaries

These probes test distinct statements in supplied models. Run them from the
repository root with `python3 -B -O -m scripts.<probe_name>`; the small regression
oracles run with `python3 -B -m unittest discover -s tests -p test_operational_sector_words.py`.
The arithmetic checks are exact; the general arguments named below are not Lean
proofs. None of these results predicts an experiment or derives the quantum
probability law, a gauge group of nature, or full quantum mechanics.

## What the echo does not identify

[`probe_echo_gauge_normal_form`](probe_echo_gauge_normal_form.py) supplies an
orthogonal, balanced mixer, a port-separable squared norm, and scalar shutters.
In its equal-word counterexample the two raw mixers have the same gain, and one is
the other followed by a common internal rotation `R`. This rotation commutes
with the reference mixer and with every shutter. In a word with `n` mixer
passes the difference is therefore a final common `R^n`. Both port populations
agree for every input and every such same-length comparison. This is stronger
than agreement on single-port basis inputs, but weaker than static conjugacy:
the two fourth powers differ even after accounting for the common gain. This
ambiguity is not a physical gate or a new symmetry principle. An extra fixed
reflection or a coherent unequal-pass comparator can separate the models only
with the corresponding extra controls; a reference with the same drift cancels
the comparison.

## Fixed-port closure is not exact finite synthesis

[`probe_native_mixer_sector_density`](probe_native_mixer_sector_density.py) uses
only the addressed native mixer `T`, on complex ports in a common frame. Every
word fixes the uniform vector of each connected component. On a connected graph
with at least three ports the general closure argument gives `SU(N-1)` on the
centered subspace and four determinant cosets of it, not a claim about exact
finite reachability or a direct-product decomposition. The argument uses an
irrational rotation, two nonparallel axes, and a Lie spanning step. The probe
checks exact identities and finite controls for those steps; it does not infer
the general argument from rank sampling. Two ports give only a cyclic group of
order four; disconnected components retain their separate uniform vectors.

[`gaussian_dyadic_words`](gaussian_dyadic_words.py) solves a different problem:
with a supplied antisymmetric paired-rail code and addresses, a logical `T`
uses two physical mixers and a logical slot phase `i` uses one. In these
coordinates the compiler reduces Gaussian-dyadic orthonormal columns by exact
denominator descent and replays the inverse word. It accepts square unitaries
and rectangular isometries specified on the occupied input columns. It does not
prepare the code or supply a measurement. The logical slot phase here is not an
additional gate assumed in the fixed-port closure argument.

## Exact charge conservation and the five-slot separation

[`probe_exact_charge_sector_wall`](probe_exact_charge_sector_wall.py) assumes
coordinate charge blocks. In a finite Gaussian-dyadic word with *zero* charge
leakage, each block is unitary and its determinant belongs to
`mu_4 = {1, i, -1, -i}`. The five-slot example has a `3+2` split and the target
diagonal is `(z^-2, z^-2, z^-2, z^3, z^3)`, with `z = (3+4i)/5`. Its total
determinant is one; the separating quantity is instead
`det(A)^2 conj(det(B))^3 = z^-30`. It is unchanged by any common scalar phase
(the two determinant powers both carry phase exponent six), including the
common sign. Exact block-preserving words have this invariant in `mu_4`, giving
a positive operator-distance lower bound even modulo common phase.

Exact Gaussian-dyadic **unitaries** compiled by the probe approach that target
with nonzero, shrinking off-block weight. One replay goes inside the above
distance bound without satisfying its zero-leakage premise. The probe reports
logical instruction counts and checks that any nonzero total off-block weight
for its replay with `M` mixer uses is at least `2^-M`. The off-block weight sums
over all input axes; it is not one input's measured probability. This is neither
a resource-optimality result nor a physical superselection rule.

## Heralds, retries, and returning a catalyst are different resources

| Probe | What the executable route separates |
| --- | --- |
| [`probe_heralded_sector_phase`](probe_heralded_sector_phase.py) | A 16-path circuit heralds `diag(z,1)` with input-independent `25/64` success, but some failures record charge; a normalized outcome table does not make those failures reversible. A different three-outcome circuit gives `5/8` success and scalar-identity failures of `1/4` and `1/8`. With coherent ancilla-only readout and reset, the retry tail is `(3/8)^N` and the mean is `8/5` attempts, with no finite worst-case bound. Detecting charge and then forgetting the record is not coherent grouping. |
| [`probe_projective_repeat_classification`](probe_projective_repeat_classification.py) | In the supplied ideal instrument model, a nonzero refined terminal leaf forces projective entry ratios in `Q(i)`. Clearing denominators and cancelling the Gaussian gcd gives a primitive integer matrix `B` with `B* B = m I`. A bounded complete native tree requires `m` to be a power of two; for that case a native word suffices. For other Gaussian-rational rays, a compiled isometry with scalar-identity failures gives finite expected attempts below two, not bounded completion. The tests check examples and exact replay, not every tree. |
| [`probe_catalytic_sector_phase`](probe_catalytic_sector_phase.py) | In a same-total-charge interferometer a **supplied** irrational eigenray gives exact phase kickback and is returned exactly. A finite Gaussian-dyadic branch from a Gaussian-rational ray cannot prepare that eigenray. A finite heralded seed approximates it: under the stated controlled powers, reusing this seed has a call-count-independent error bound, whereas refreshing it gives different fringe behavior. The approximate catalyst need not be exactly uncorrelated with the data. |

The code certifies amplitudes, addressed words, branch tables, or the stated
finite controls. Physical use would need the applicable encoded states, coherent
addressing and bypass, stable reference and readout, and (for retries) an ideal
grouped instrument with reset and its stochastic law. A computational branch
table does not supply these prerequisites. Nor do the exact numerical controls
give a noise or hardware-cost guarantee.

Related primary references are [restricted Gaussian-dyadic synthesis](https://arxiv.org/abs/1908.06076),
[repeat-until-success synthesis in a different gate set](https://arxiv.org/abs/1311.1074),
and [beamsplitter universality](https://arxiv.org/abs/1310.6718). The last is
related context, not a theorem being applied here to this native `T`.
