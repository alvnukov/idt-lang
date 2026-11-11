# Mixture continuation selects the Gaussian norm under three supplied contracts

Four real probe functions on the full integer lattice determine the raw response
\(f(m,n)=m^2+n^2\) when their finite ensemble means remain sufficient under
local translations, the first response is globally Gaussian-multiplicative,
and \(f(2,0)=4\). The probe functions are otherwise arbitrary. The conclusion
holds on every integer pair.
[Selection source](../Proofs/QMClosure/MultiplicativeMixtureReadout.lean)

## The supplied contracts

Write \(z=(m,n)\in\mathbb Z^2\), identify it with \(m+in\), and take
\(P\colon\mathbb Z^2\to\mathbb R^4\) with \(f(z)=P_0(z)\).
The theorem takes exactly three contracts as hypotheses.

1. Every finite probability ensemble with arbitrary nonnegative real weights
   summing to one participates in the following congruence. For each
   \(s\in\{1,-1,i,-i\}\), equality of the entire mean probe vectors implies
   equality of the entire mean probe vectors after translating all sources by
   \(s\).
2. For every pair \(z,w\in\mathbb Z[i]\), the first response satisfies
   \(f(zw)=f(z)f(w)\), with the usual Gaussian multiplication including its
   cross terms.
3. The single calibration is \(f(2,0)=4\).

For a finite ensemble \(\mu\), the first contract reads

\[
\overline P(\mu)=\overline P(\nu)
\quad\Longrightarrow\quad
\overline P((\tau_s)_*\mu)=\overline P((\tau_s)_*\nu),
\qquad
\overline P(\mu)=\sum_z\mu(z)P(z).
\]

Its quantifiers cover all finite supports and all real probability weights.
Equality concerns all four coordinates, allowing repeated continuations.
Accessibility of these mixtures and sufficiency of these means are supplied
mathematical assumptions whose physical origins remain open.
[Mixture source](../Proofs/QMClosure/FiniteMixtureContinuationRank.lean)
[Selection source](../Proofs/QMClosure/MultiplicativeMixtureReadout.lean)

Global multiplicativity covers arbitrary Gaussian integer pairs, including
sources represented by coherent sums. Agreement of a serial-word response with
multiplication leaves the extension to this entire carrier as a separate proof
obligation. The real-valued codomain and the calibration also have supplied
status.
[Selection source](../Proofs/QMClosure/MultiplicativeMixtureReadout.lean)

## From mixture means to a small translate span

For \(k\) real probes on any carrier and a source update \(U\), the mixture
artifact proves the equivalence

\[
\operatorname{MixtureCongruent}(P,U)
\quad\Longleftrightarrow\quad
P_j\circ U\in\operatorname{span}_{\mathbb R}\{1,P_0,\ldots,P_{k-1}\}
\quad\text{for every }j.
\]

The forward implication converts arbitrary finite signed affine relations into
relations between two probability ensembles. The reverse implication uses
linearity of finite expectations. Closure under each generator then propagates
to every finite word of continuations. On \(\mathbb Z^2\), the four elementary
translations generate every integer translation, so each probe's full real
translate span has dimension at most \(k+1\). Four probes give a bound of five.
[Mixture source](../Proofs/QMClosure/FiniteMixtureContinuationRank.lean)

Casting the same \(k+1\) augmented probe functions into complex-valued functions
also contains every translate of the cast response. This explicit finite-family
construction gives complex translate dimension at most \(k+1\). It supplies the
complex bound needed for spectral selection directly.
[Complex-span source](../Proofs/QMClosure/MixtureProbeComplexRank.lean)

## Why rank below eight forces the norm shape

The intermediate selection theorem concerns a complex-valued function on all
of \(\mathbb Z^2\) with finite complex translate dimension strictly below eight,
quadratic doubling \(f(2z)=4f(z)\), and quarter-turn invariance
\(f(iz)=f(z)\).

The existing spectral and dilation artifacts give actual supported
polynomial-character components and a common positive odd period for their
characters. The small-rank argument derives zero origin values for these
components. A nontrivial supported character then generates four distinct
rotated character blocks. Each block contains two independent vectors, giving
eight independent vectors in the translate space. The strict dimension bound
forces every supported character to be trivial.
[Support source](../Proofs/QMClosure/FiniteTranslationSmallRankSupport.lean)

Trivial supported characters give a global polynomial representation on the
integer lattice. Doubling selects homogeneous degree two, and quarter-turn
invariance selects the isotropic quadratic. Consequently

\[
f(m,n)=f(1,0)(m^2+n^2).
\]

This intermediate theorem includes the zero response. Rank below eight is a
sufficient condition. Sharpness and the proposed universal rank-four versus
rank-twenty classification remain separate research obligations.
[Polynomial source](../Proofs/QMClosure/QuadraticPolynomialDyadicSelection.lean)
[Norm-shape source](../Proofs/QMClosure/FiniteTranslationNormSelection.lean)
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

For the real first probe, global Gaussian multiplicativity and \(f(2,0)=4\)
derive \(f(1,0)=f(-1,0)=f(0,1)=1\). Real-square identities eliminate the
negative unit alternatives. Multiplication by \(i\) supplies quarter-turn
invariance, and multiplication by \(2\) supplies quadratic doubling. The complex
translate bound is at most five, so the intermediate theorem applies and the
derived unit value fixes the coefficient to one.
[Selection source](../Proofs/QMClosure/MultiplicativeMixtureReadout.lean)

## Consequences and a concrete instance

The selected raw response is nonnegative and conjugation invariant. It is
monotone along nonnegative integer counts and obeys the parallelogram identity
and vanishing third-order inclusion-exclusion

\[
\begin{aligned}
f(x+y)+f(x-y)&=2f(x)+2f(y),\\
f(x+y+z)-f(x+y)-f(x+z)-f(y+z)
 +f(x)+f(y)+f(z)-f(0)&=0.
\end{aligned}
\]

These properties follow from the three contracts. The theorem also derives
rotation and doubling along its proof path. Continuity and a supplied degree
bound play no role in its premises.
[Selection source](../Proofs/QMClosure/MultiplicativeMixtureReadout.lean)

The concrete probes

\[
Q(z)=\bigl(N(z),N(z+1),N(z+i),N(z+1+i)\bigr),
\qquad N(m,n)=m^2+n^2,
\]

satisfy all three contracts. The mixture artifact gives their congruence under
every integer translation, and `normProbes_contract` combines this with global
multiplicativity and the calibration. `exists_four_probe_contract` records a
concrete inhabitant of the complete supplied contract.
[Mixture source](../Proofs/QMClosure/FiniteMixtureContinuationRank.lean)
[Selection source](../Proofs/QMClosure/MultiplicativeMixtureReadout.lean)

## Research boundary

The earlier modulo-five readout is exactly reconstructible from four raw probes
and has real translate rank twenty, while two equal-half ensembles with the
same four means develop different means after translation. Its checked
obstruction locates the force of the mixture-sufficiency premise.
[Tomography and mixture wall](197-finite-readout-tomography-and-mixtures.md)

Rational or dyadic mixture accessibility requires its own selection argument.
An independently reviewed analytic route is now in formalization for fixed
translated-readout corner probes, equal-half two-source continuation congruence,
global Gaussian multiplicativity, the calibration \(f(2,0)=4\), and the diagonal
sign \(f(1,1)\ge0\); its rectangle and integer-recurrence argument awaits a
compiled Lean artifact. Robustness under approximate mean equality, approximate
continuation laws and finite precision also remains open. The next research
stage concerns those mixture contracts, followed by transport to the initial
dyadic history quotient.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

Physical origins of the real probes, global multiplicativity, calibration and
all-real mixture sufficiency remain open. Normalized event probabilities, Born
actualization, Hilbert representation and full QM closure retain their separate
obligations. The integer carrier also requires an extension before a
nondegenerate normalized echo can be realized.
[Physical scope boundary](150-physical-scope-boundary.md)
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Verification

All six registered targets in this mixture-selection cluster compiled
successfully. An exact-origin audit covered 182 declarations, including 23
private declarations, with zero local axioms and zero unsafe declarations.
Its aggregate transitive axiom set was exactly `propext`, `Quot.sound` and
`Classical.choice`. Source hashes remained unchanged through the audit.
The theorem signatures and their supplied hypotheses determine the mathematical
scope. The operational ledger records the parent-accepted research stages.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
