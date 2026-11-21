# Tests that a single detector table does not settle

Replay: `python3 -m unittest tests.test_parity_and_composition`. The
[cube detector probes](CUBE_DETECTOR_CANDIDATES.md) allow different
records to reproduce the same single-system probabilities. Here the
questions are how much information those records retain and whether
separately prepared records compose independently. The analyses below
are conditional; no particle preparation or real detector is inferred.

### A published comparison, not a fit

Give a uniform three-bit word to the source. After preparation, choose
one of its coordinates uniformly and ask the apparatus to return that
bit. The eight cube states and the three ideal Cartesian qubit analyzers
give success (1+1/√3)/2, about 0.788675. An experiment reported
0.786476 ± 0.000017 for this three-bit protocol. The uncertainty quoted
is the authors', not a new error analysis; their paper discusses
tomographic assumptions, vacuum postselection and possible multiphoton
leakage. We did not obtain raw trials or perform a new fit. See
[Spekkens et al., *Preparation contextuality powers parity-oblivious multiplexing*](https://arxiv.org/abs/0805.1463).

The [parity probe](probe_parity_capacity.py) treats a prepared record
as a classical channel, not as a quantum state. For each subset S of
bits let TVₛ be the total variation distance between its two
parity-conditioned **latent record** distributions. These are not
experimentally measured distances. Let R be the sum for the three pairs
and the triple. For any source-independent readout, average success is
bounded by 1/2 + min(1+R,(5+R)/3)/6. The two bounds follow by aligning
the signs of the singleton biases separately for each record and using
positivity on the eight cube words. Revealing one, two or three uniform
coordinates and mixing adjacent strategies attains the two branches.
In particular at R=0 success is at most 2/3. The experimentally allowed
measurements can conceal parity that a hypothetical raw record contains.

To reach the ideal score within these assumptions requires R≥√3−1. A
mixture which reveals two bits with probability s=√3−1, and one otherwise,
attains it and can support each finite qubit measurement on these eight
sources. For any group of k requested coordinates the largest required
total slope is √(k/3). The available capacities for k=1,2,3 are
(1+s)/3, (2+s)/3 and 1. The singleton cut is tight. This is a **calibrated
resource optimum** against a supplied target; the irrational mixing
weight has not been derived as a microscopic law. An alternative
Hamming-ball channel hides all pair parities but leaks triple parity. A
mixture can reach the same retrieval score yet fails the cube-diagonal
projector. Thus the score alone does not pick the record.

### Independent copies versus correlated erasures

Fix two **adjacent** cube preparations. The 12-edge record hides which
of the two was prepared with probability 1/3. Otherwise it reveals that
choice. With N independent records, all are ambiguous on a common
subdistribution of mass 3⁻ᴺ. In a normalized joint measurement label
the outcomes by preparation words x and score an error if it outputs x
on input x. Then the **sum** of those diagonal probabilities is at least
3⁻ᴺ, hence their uniform mean and their maximum are at least 6⁻ᴺ.
It is not a per-row lower bound. A decoder attains the mean and maximum
bounds: choose an excluded word when any input is revealed and a uniform
word otherwise. With losses, the sum of the **raw** diagonal probabilities
plus the smallest input-dependent no-click probability is at least 3⁻ᴺ.

The [composition probe](probe_independent_edge_composition.py) supplies
a separate orthonormal quantum measurement benchmark. The single-state
squared overlap is 2/3; a Walsh-sign basis with chosen phases is checked
against direct complex inner products and Gram matrices. See
[Pusey, Barrett and Rudolph](https://arxiv.org/abs/1111.3328) for the
preparation-independence/state-exclusion strategy. The quantum benchmark
is an input, not an output of the classical candidate.

| Copies | Independent edge minimum mean error | Quantum comparison | Uniform random-output admixture below which the separation persists |
| ---: | ---: | ---: | ---: |
| 2 | 1/36 | (3−2√2)/12 ≈ 0.01430 | 1−2√2/3 ≈ 5.72% |
| 3 | 1/216 | 0 | 1/27 ≈ 3.70% |

The two-copy test has the larger absolute margin and does not require
resolving an ideal zero. The percentages are analytic white-output-noise
thresholds for these models, not detector specifications or observed
laboratory errors.

Correlating the erasure coordinates changes what follows. A cyclic
three-copy schedule can evade the diagonal test but cannot reproduce
the full parity correlation of the supplied table. A different ternary
schedule, K₃=1−K₁−K₂ modulo 3 with K₁,K₂ independent uniform, has the
same one- **and two-source** erasure distributions as independent draws.
It nevertheless reproduces the entire specified three-copy table with
a normalized, source-blind decoder. The two-copy table also has a
correlated (not independent) construction. Finite data on marginals
are not sufficient to assert joint preparation independence. Passing
these particular tables with correlations is not a simulation of
general composite quantum experiments.
