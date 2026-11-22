# When does the native mixer constrain click probabilities?

**Result.** All finite, lossless projective measurements on three *logical*
ports still permit a preassigned yes/no answer on each accessible ray.
Adding even one blank output path changes this test. Allowing arbitrary
finite native isometries and requiring that a reversible change elsewhere
cannot change a named port's click rate yields a conditional probability
law for a fixed preparation. None of these statements explains why an
individual click occurs, supplies a calibrated preparation, or assumes
that the physical world realizes all these circuits.

Here logical probabilities are compared only after specifying the devices.
Bare physical one-particle mixers preserve a uniform vector. The controls
below use the [paired-rail code and compiler](OPERATIONAL_SECTOR_WORDS.md):
two addressed pairs can mix, a pair can supply its own quarter turn, and
every Gaussian-dyadic isometry can be built on the occupied input columns.
The Euclidean norm is used to recognize the **algebraic gate class**. That
alone does not assign the probabilities of physical records.

## Three-port projective measurements: a constructive countermodel

Let R=ℤ[i,1/2] and π=1+i. A ray in this test admits an actual **unit column
in R³**, not merely a vector with integer coordinate ratios. For example,
(1,1,1) is an integer direction, but it cannot be normalized by any
Gaussian-dyadic scalar. Two normalized R representatives of the same ray
differ by one of ±1, ±i: their overlap belongs to R and has unit norm.

Join a ray to each unordered orthonormal basis containing it. The resulting
infinite incidence graph is a tree. The following is an algebraic argument;
the [replay](probe_native_qutrit_frames.py) independently enumerates the
finite shells, not a Lean proof of the infinite statement.

1. Define a ray's level k to be its least denominator exponent π^k.
   A unit column in dimension three can be completed to a unitary of
   level at most k. The compiler's denominator descent needs only one
   two-slot mixer per round: a nonzero even number of the three Gaussian
   numerators are odd. Inversion of one mixer costs only one algebraic
   denominator, even if executed by three forward gates.
2. There are just six rays in a free two-dimensional dyadic complement:
   two coordinate axes and four equal-weight relative phases. Indeed the
   four squared real numerator coordinates sum to 2^k. For k≥3, reduction
   modulo eight forces all four even. At k=2 all possibilities are again
   jointly divisible by π. Thus each three-mode ray lies in exactly three
   distinct projective bases.
3. For a basis of maximum level k>0, reduce π^k times its matrix modulo π.
   Every nonzero column in the residue has even weight, hence weight two.
   Two distinct such vectors in three binary coordinates have odd overlap,
   so column orthogonality forces all nonzero columns to coincide. Row
   orthogonality forces **exactly two** nonzero columns. One ray of the
   basis has lower level, the other two both have level k.
4. Complete a level-k ray as in (1). For k>0 the other two columns of this
   basis have different levels. Every other basis through the chosen ray
   replaces those two by balanced sums or differences with relative phase
   1 or i. Since one summand has strictly lower level, the leading
   denominator cannot cancel: both new rays have level k+1. At k=0 the
   coordinate basis is the unique level-zero basis, with the same two
   higher branches per ray. Thus each ray has one parent basis of its
   own level; each non-root basis has one parent ray of level one lower.
   Every parent chain terminates at the coordinate basis, and no cycles
   are possible.

Choose one true ray in the root basis. At a new basis, assign neither
new ray if its parent ray is true, otherwise assign exactly one. This
gives a global deterministic assignment with one true ray per native
basis. It is not a Born rule: for instance a true coordinate ray can
coexist with a true balanced superposition having only half overlap.
It is also **not** a model of Lüders update, preparations being mixed
affinely, spacelike composition, or settings implemented by retries.

| Maximum level | Accessible rays | Complete bases |
| ---: | ---: | ---: |
| 0 | 3 | 1 |
| 2 | 63 | 31 |
| 4 | 1,023 | 511 |
| 5 | 4,095 | 2,047 |

The tree construction is cross-checked through level four against an
independent six-square enumeration and all its orthogonal triples. Dense
approximability of continuous rotations says nothing by itself about the
existence of this discontinuous assignment. Meyer's [rational-sphere
example](https://arxiv.org/abs/quant-ph/9905080) is relevant context,
not this ring, graph or proof. No mathematical priority is claimed.

## One extra path: same input, different apparatus

On four logical ports the 24 real directions with entries 0,±1 and
squared norm 1,2,4 already contain nine orthonormal bases on 18 rays in
which each used ray occurs twice. Nine basis clicks cannot equal an even
sum of predetermined common ray values. Normalization of a length-√2
column uses a Gaussian phase choice; no irrational physical gate is needed.
This reproduces a known kind of [18-vector parity obstruction](https://arxiv.org/abs/quant-ph/9706009).

A smaller state-specific comparison uses five events in a cycle. The
unnormalized four-mode directions are

    (1,0,0,0), (0,1,0,0), (1,0,1,0), (-1,-1,1,1), (0,1,1,0).

Each neighboring pair is two orthogonal outputs of one explicitly compiled
measurement; the two other outputs are retained too. For the three-mode
preparation (2+i,1+i,1)/π³ with a fourth blank input, the squared-amplitude
benchmark gives 5/8, 1/4, 5/8, 1/4, 5/16: **33/16 in total**. A common
deterministic assignment respecting all neighboring exclusions gives at
most two. This is a proposed comparison, not measured data. In the
three-input description the fourth listed event is an *unsharp* effect.
One must not silently apply outcome determinism to all such effects or
deduce general contextuality from approximately matching marginals.

## Generalized readout: where a probability law comes from

The [native row-rule probe](probe_native_row_probability.py) begins with
normalized probabilities for reported rows of every finite native
rectangular isometry. If the same effective row has the same probability
across such tests for one preparation, two equal-Gram row lists can be
compared without importing Born probabilities. Scale both lists until
their common residual matrix is componentwise diagonally dominant;
decompose its off-diagonals into dyadic sums of coordinate-pair rows and
its positive diagonal remainder into dyadic squares. Pad the two lists
with **identical** residual rows and compile the two complete tests.
Normalization equates the two original total masses. Binary duplication
supplies dyadic scaling; the resulting positive functional is linear on
dyadic Hermitian matrices. Its representation is a positive trace-one
matrix ρ: positivity on dense dyadic vectors extends the **derived**
quadratic polynomial, not a prior continuity postulate on a click law.
Thus f(r)=rρr† on the specified rows. Identifying ρ with a named pure
preparation still needs calibration. [Generalized Gleason results](https://arxiv.org/abs/quant-ph/0306179)
already discuss normalized probability rules on POVMs including rational
domains; our contribution here is a restricted native construction,
specific operational comparisons, and executable countercontrols.

There is a real obstacle to simply declaring all completions equivalent.
The two one-column devices with numerators (1+6i,3,3,3) and (1+6i,5,1,1),
both divided by eight, have the same first row. The ideals of their other
coordinates are respectively 3R and R. No dyadic unitary confined to
those coordinates maps one to the other, even after padding with zeros.

The [coherent-duplication probe](probe_unread_row_duplication.py) avoids
that direct-orbit obstruction. Supply normalized complete records,
permutation covariance, padding with blank outputs, and predictions that
depend on the **full map on the occupied input columns**, not its
unrecorded circuit history. Also require that a reversible operation
confined to other outputs cannot affect a named port. Put two devices
T,S into distinct coherent routes after an equal amplitude split
(one input, not two copies of its unknown state). In a T/T diagram equal
output rows can be swapped without changing the full map. Undoing each
sibling mixer preserves the sibling total by normalization and locality,
so each receives half its standalone mass. In a T/S diagram the left mass
does not change when the right T is replaced by S: completions give a
native unitary on the **whole right arm**. Likewise for the other arm.
If the two named effective rows agree, exchanging them leaves this mixed
diagram unchanged. Their standalone probabilities must agree. The
individual odd-ideal counterexample remains valid; this uses a different,
larger experiment. Accessible hidden path history or a change in detector
response when another port is rewired violates a premise, not mathematics.

Finally, [two short complete tests](probe_finite_detector_identity.py)
give a usable finite check. For r=(3−2i,1−i)/4 and calibrated Z, X, Y
reference endpoints, with two identical unreported-in-the-contrast
but **retained** remainder rows, normalization gives

    16 p(r) = 7 p(Z0) − 4 p(Z1) + 10 p(X+) + 2 p(Y+).

The two tests have only four and eight outputs. Weights 7,10,2 here come
from sums of binary splitting factors. For an ideal Z0 preparation the
squared-amplitude reference is p(r)=13/16. A normalized fourth-power
control in the specified four-output circuit exceeds that by 221/1392.
The diagnostic accepts simultaneous probability intervals and separate
upper bounds on row matching and the two shared remainders. It reports
inconclusive when those bounds can absorb the discrepancy. No finite grid
or data-free check establishes the operational assumptions universally.

## Sharp rational projectors: a retry is not a change of coordinates

The [rational pentagon](probe_native_rational_pentagon.py) uses three
coordinates throughout the input, not the four-mode blank-path example
above. Five rays e₁,e₂,(1,0,1),(−1,−1,1),(0,1,1) are cyclically orthogonal
and give squared-amplitude sum **13/6** for the native (1,1,0)/(1+i)
preparation. The norm-three ray cannot be reached by a projectively
Gaussian-rational *square unitary on three slots*: if B†B=mI then
Norm(det B)=m³, whereas such a column would force an odd valuation at 3.
But sharp rational projectors do not require preparing this normalized
column. Stack the complete context's projectors with a common numerator,
pad with scalar-identity failure branches and compile the resulting
dyadic isometry. All five contexts admit common success probability
**9/16** and an exactly data-preserving reset on failure. Retrying uses
15 logical outcome/data addresses (30 paired rails) and has no finite
worst-case number of steps. It supplies coherent instruments, independent
control of the extra paths and a readout law; it is not a bare lossless
three-port projective measurement or an observed violation.

The unrestricted search over asymmetric pentagons with denominator primes
only 2 and 5 remains open: 10,986,328 candidate pairings through the stated
larger cutoff had no hit, and an analytical exclusion covers the symmetric
subfamily only. Adding 17 gives an explicit countercontrol.

The [residue-graph probe](probe_qutrit_residue_frames.py) tests a tempting
but invalid inference. Reducing normalized Gaussian coordinates modulo 3
gives 63 nonisotropic rays and 63 bases, which cannot be assigned one true
ray per basis. Modulo 7 the corresponding counts are 2,107 and 14,749;
each ray lies in 21 bases, so even a divisibility argument suffices. Yet the
native *dyadic* three-slot circuits already reach all the residue rays and
bases in both examples, despite their actual infinite incidence tree having
a coloring. Distinct rays can collapse after reduction. A coloring constant
on a residue fiber would pull back, but the nonexistence of such a coloring
does **not** reject the original candidate. Modulo 3 also has no
five-distinct-vertex pentagon; a genuine pentagon can collapse to a walk
with repeated vertices. Real-coordinate rays give a separate restricted
positive coloring. The checker must keep these logical directions separate.
