# Finite readout tomography and mixtures

Four exact raw response probes can determine every Gaussian-integer source
while the span of all translated responses has dimension twenty. The same
four averaged probes do not determine the response after one elementary
continuation.

## Four exact probes and a mixture obstruction

On the Gaussian integers, write

\[
N(m,n)=m^2+n^2,\qquad
f(m,n)=N(m,n)\,\mathbf 1_{m-2n\not\equiv0\pmod5}.
\]

Use the four fixed probes

\[
P(z)=\bigl(P_0(z),P_1(z),P_2(z),P_3(z)\bigr)
     =\bigl(f(z),f(z+1),f(z+i),f(z+1+i)\bigr).
\]

The Lean artifacts establish the following exact mathematical facts.

- The response is nonnegative and globally multiplicative. It satisfies
  \(f(1)=1\), \(f(2)=4\), \(f(i)=1\) and \(f(1+i)=2\).
- The response annihilates the nonzero count five, and conjugation invariance
  fails for an explicit pair.
- The real span of all integer translates has dimension exactly twenty. The
  certificate combines twenty explicit features with an invertible fixed
  twenty-by-twenty sample matrix.
- The map \(P\) is injective. Its actual image is equivalent to the source
  carrier, so arbitrary source operations transport to that image and source
  equivalences transport reversibly.

The four corner residues are distinct modulo five, so at most one probe is
masked. Three unmasked squared distances determine the two source coordinates.
This supplies exact source reconstruction using four real observables while
retaining the global linear translate dimension twenty. The induced updates
act on the realized probe image. Noise stability and continuity require further
contracts. [Lean filter source](../Proofs/QMClosure/FiniteRankReadoutFilter.lean)
[Lean tomography source](../Proofs/QMClosure/FiniteReadoutTomographyWall.lean)

Now average probe vectors componentwise with equal weights. The two ensembles

\[
\mu=\tfrac12(\delta_0+\delta_{-1-i}),\qquad
\nu=\tfrac12(\delta_{-1}+\delta_{-i})
\]

both have mean probe vector \((1,1,1,1)\). Translate every source by \(+1\).
The respective mean vectors become

\[
(1,3,1,\tfrac12),\qquad (1,3,1,3).
\]

Consequently any proposed update on four averaged coordinates receives the
same input for these two ensembles and would have to produce two different
outputs. The theorem `no_meanProbe_translation_update` excludes every
such update function for all equal-half pairs. Its arithmetic averaging is
explicit. A physical interpretation as exclusive preparation mixtures remains
an additional premise. [Lean tomography source](../Proofs/QMClosure/FiniteReadoutTomographyWall.lean)

## Checked algebra and remaining spectral work

The checked finite translation spectrum artifact starts with a complex-valued
function on all of \(\mathbb Z^2\) and a finite-dimensional complex span of
all its translates. It gives the actual joint generalized-eigenspace
decomposition, translation-compatible projections and finitely supported
readout components. Independently, two global coordinate forward-difference
annihilators give a unique bivariate complex polynomial on all of
\(\mathbb Z^2\).
[Spectrum source](../Proofs/QMClosure/FiniteTranslationSpectrum.lean)
[Difference source](../Proofs/QMClosure/FiniteDifferencePolynomial.lean)

The extraction bridge identifies every actual
supported component with a nonzero polynomial times its coordinate character
and sums these components to the original function. A second artifact
adds the supplied law \(f(2z)=4f(z)\). It gives an exact permutation of the
actual finite support under character squaring, component dilation, and one
common positive odd exponent \(M\) with \(\chi_j^M=1\) for every supported
character coordinate. This period concerns the characters. Polynomial factors
retain their separate dilation and degree obligations.
[Extraction source](../Proofs/QMClosure/FiniteTranslationExponentialPolynomial.lean)
[Dilation source](../Proofs/QMClosure/FiniteTranslationDilationSupport.lean)

A separate checked algebraic result starts with homogeneous real quadratics
\(Q_r\) indexed by a monoid, calibration \(Q_1(1,0)=1\), and the supplied
identity

\[
Q_{rs}(zt)=Q_r(z)Q_s(t)
\]

for independent indices and arbitrary real Gaussian coordinate pairs. It
derives \(Q_r=c(r)N\), where \(c\) is a real multiplicative coefficient
map, and proves the converse construction. Deriving that universal
real-coordinate identity from multiplicativity on residue cosets remains a
separate obligation.
[Quadratic source](../Proofs/QMClosure/MultiplicativeResidueQuadratics.lean)

The universal rank-gap proposal remains analytic. For a globally multiplicative
real Gaussian-integer readout with \(f(2)=4\) and finite global real translate
rank \(d\), it proposes

\[
f=N,\ d=4,\qquad\text{or}\qquad f\ne N,\ d\ge20,
\]

with exactly the two filters \(N(m,n)\mathbf1_{m\pm2n\not\equiv0\pmod5}\)
at rank twenty. Remaining universal obligations include general rank transfer,
residue-polynomial degree selection and reconstruction, the coset-to-polynomial
identity, exact block rank, support counting and the equality classification.
The small-rank norm-selection theorem now supplies a sufficient bound below
eight for the mixture route. The explicit rank-twenty example and each checked
bridge retain their own bounded contracts.
[Mixture norm selection](198-mixture-continuation-norm-selection.md)
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## A conditional route through mixture sufficiency

For any finite probability ensemble \(\mu\) with arbitrary nonnegative real
weights summing to one, define

\[
\overline P(\mu)=\sum_z\mu(z)P(z).
\]

Supply a local rule for each generator \(s\in\{1,-1,i,-i\}\)

\[
\overline P(\mu)=\overline P(\nu)
\quad\Longrightarrow\quad
\overline P((\tau_s)_*\mu)=\overline P((\tau_s)_*\nu).
\]

Equality concerns the entire four-vector after each generator. The checked
mixture theorem identifies this congruence with affine-coordinate closure.
Iterating the generator actions puts every translated first response in the
real span of \(1,P_0,P_1,P_2,P_3\), so its translate rank is at most five.
Casting that explicit augmented-probe family also bounds complex translate
rank by five. A checked sufficient rank bound below eight now gives norm
selection when global Gaussian multiplicativity and the sole calibration
\(f(2,0)=4\) are supplied. Selection under rational or dyadic weights remains
a separate research obligation.
[Mixture source](../Proofs/QMClosure/FiniteMixtureContinuationRank.lean)
[Complex-span source](../Proofs/QMClosure/MixtureProbeComplexRank.lean)
[Mixture norm selection](198-mixture-continuation-norm-selection.md)

For the squared norm itself, define the separate probe vector

\[
Q(z)=\bigl(Q_0(z),Q_1(z),Q_2(z),Q_3(z)\bigr)
     =\bigl(N(z),N(z+1),N(z+i),N(z+1+i)\bigr).
\]

The checked translation identity is

\[
N(z+a)=(1-a_x-a_y)Q_0(z)+a_xQ_1(z)+a_yQ_2(z)+N(a)-a_x-a_y.
\]

Applying this identity to each shifted corner supplies affine updates of the
norm's probe vector and hence preserves all finite ensemble means. The local
congruence premise expresses finite affine closure operationally. Its origin
from bare microscopic locality remains open.

The modulo-five equal-half ensembles above give a concrete obstruction to
this rule. The remaining primitive-origin question is precise. Why should a
bounded set of probe means remain sufficient for ordinary mixtures under each
local continuation?

## Finite gate tests leave a localization wall

An additional analytic construction takes any finite Gaussian-rational
generator alphabet, finitely many inverse gates if desired, and finitely many
tested inputs. Choose an odd prime avoiding the relevant denominators and
numerator norms. On the corresponding localization, the response

\[
W(z)=N(z)\,\mathbf1_{\overline{N(z)}\ne0\text{ in }\mathbb F_p}
\]

is proposed to be nonnegative, multiplicative and conjugation invariant,
agree with \(N\) on the selected tests and serial products of the generators,
and annihilate the nonzero integer \(p\). Residue indicators times
\(N,\operatorname{Re},\operatorname{Im},1\) give translate rank at most
\(4p^2\). Coherent circuits introducing additional sums require their own
agreement argument. This localization wall awaits formalization.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Verification and scope

The seven-target tomography and spectral cluster summarized here compiled
successfully. Its exact-origin audit covered 390 declarations, including 112
private declarations, with zero local axioms and zero unsafe declarations.
Its aggregate transitive axiom set was the standard `propext`, `Quot.sound` and
`Classical.choice`. The authoritative research stages are recorded in the
operational primitive ledger. Compiling that ledger checks its metadata.
Mathematical authority lies in the cited theorem statements under their actual
hypotheses.
[Operational ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

The subsequent six-target mixture-selection cluster has its own verification
record. [Mixture norm selection](198-mixture-continuation-norm-selection.md)

Physical readout selection, the origin of ordinary mixture averaging and its
local sufficiency, Born actualization and full QM closure remain open.
[Physical scope boundary](150-physical-scope-boundary.md)
