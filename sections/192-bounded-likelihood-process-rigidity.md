# Bounded likelihood rigidity under exact process covariance

A finite one-way domination bound between two probability preparations forces
their measures to coincide under a supplied transparent square-swap process
with one common Markov channel and exact full product covariance. The outcome
carrier may be any measurable space. Each compared pair may use its own bound.
[Main rigidity theorem](../Proofs/QMClosure/BoundedLikelihoodProcessRigidity.lean)

## The sufficient contract

Let `P(x)` be a probability measure on a measurable space `Omega` for each
preparation label `x`. Supply an operation `F` on every pair of labels and one
Markov channel `K` on pairs of outcomes, with

```text
F(F(x,y)) = (y,x),
F(x,x) = (x,x),
K(P(x) product P(y)) = P(F(x,y).1) product P(F(x,y).2).
```

These equations hold for every raw pair, and the same channel supplies every
covariance equation. If, for some labels `x,y`,

```text
P(x) <= C * P(y),       0 < C < infinity,
```

as measures, then `P(x)=P(y)`. Thus bounded domination between preparations is
equivalent to equality of their measures. Distinct labels can still represent
the same preparation measure.
[Process contract and bounded domination](../Proofs/QMClosure/BoundedDominationProcess.lean)
[Equality and its converse](../Proofs/QMClosure/BoundedLikelihoodProcessRigidity.lean)

Finite relative entropy and log integrability are derived inside the proof.
The input contract supplies probability, the raw operation laws, the common
channel, exact covariance and the selected pair's finite domination bound.
The constants may vary with the pair and with members of the closed component.
[Component entropy and log bounds](../Proofs/QMClosure/BoundedDominationProcess.lean)

## From one-way domination to constant log density

Bounded domination is a preorder on probability measures. Products, application
of the common kernel and probability marginals preserve it. The transparent
square-swap order obstruction reverses each comparable pair, so the initial
bound also gives a finite reverse domination bound.

Fix `y` and restrict the labels to the component

```text
{z | there exists C, 0 < C < infinity and P(z) <= C * P(y)}.
```

This component is closed under `F`. Every member has two-sided domination
relative to `P(y)`, yielding positive finite lower and upper density bounds,
bounded real log likelihoods, log integrability and finite relative entropy.
The resulting pointed component instantiates the existing likelihood-transport
interface.
[Domination reversal and closed component](../Proofs/QMClosure/BoundedDominationProcess.lean)

For a log density `g`, its essential width is the difference between its sharp
finite upper and lower almost-everywhere bounds. Sharpness characterizes all
constant bounds. Independent-coordinate sums have additive essential widths
by Fubini. Writing `(a(x),b(x))=F(x,y)`, the transported log relations give

```text
W(x) = W(a(x)) + W(b(x)),
W(a(x)) = W(b(x)) = W(x)/2.
```

Four actual iterations of `a` therefore give `W(a^4(x))=W(x)/16`. The reciprocal
log identity gives `W(a^4(x))=W(x)/4`. Their equality forces `W(x)=0`.
The proof uses finitely many transported almost-everywhere relations and
finite real algebra. Zero width makes the log density almost-everywhere
constant, and probability normalization identifies the two measures.
[Sharp bounds and finite width elimination](../Proofs/QMClosure/BoundedLogProcessRigidity.lean)
[Measure equality from the component](../Proofs/QMClosure/BoundedLikelihoodProcessRigidity.lean)

## Density consequences

The following consequences use the same full process contract. Write
`r=dP(x)/dP(y)` for the Radon-Nikodym density.

| Additional premise | Consequence |
| --- | --- |
| `P(x)` is absolutely continuous with respect to `P(y)`, and `r` has a finite positive upper bound almost everywhere under `P(y)` | `P(x)=P(y)` |
| `r` has a positive finite lower bound almost everywhere under `P(y)` | `P(x)=P(y)`, including when a singular part is initially allowed |
| `P(x)` is absolutely continuous with respect to `P(y)`, and the two measures are distinct | The reference-essential supremum of `r` is infinity and its essential infimum is zero |

Absolute continuity in the upper-bound premise accounts for the entire
preparation measure when passing from density to measure domination. The
positive lower bound directly gives reverse measure domination. Essential
endpoints describe almost-everywhere bounds and allow endpoint values that
are never attained.
[Density bounds and essential endpoints](../Proofs/QMClosure/BoundedLikelihoodReferenceCorollaries.lean)

## Finite atomic internal references

Suppose one preparation `P(y)` is an explicitly finite sum of weighted Dirac
measures,

```text
P(y) = sum_i weight(i) * dirac(atom(i)),
```

with finite positive `NNReal` weights, and every preparation is absolutely
continuous with respect to `P(y)`. Each preparation's reference-relative density
then has a finite essential upper bound. Applying the rigidity theorem to each
preparation gives

```text
for every x, P(x) = P(y),
for every x,z, P(x) = P(z).
```

The theorem applies on an arbitrary measurable outcome space and its signature
requires only that measurable-space structure. Domination of every preparation
by the internal reference remains an explicit premise alongside the finite
atomic representation. Each density bound is constructed for the selected
preparation.
[Finite atomic bound and family constancy](../Proofs/QMClosure/BoundedLikelihoodReferenceCorollaries.lean)

## Omission controls and consistency

The controls reuse the existing finite models and exhibit a preparation
bounded by four times its internal reference while having a distinct measure.

| Omitted premise | Retained process structure and checked obstruction |
| --- | --- |
| Every raw diagonal fixed | Probability preparations, square-swap and one common Markov channel with exact covariance remain. A concrete raw diagonal moves. |
| One common channel | Probability preparations, square-swap and every raw diagonal fixed remain. Pair-dependent channels supply the displayed covariances, and a single channel supplying all of them is impossible. |

These two examples isolate their displayed omissions. Minimality of the full
assumption package remains a separate research question.
[Bounded domination witnesses and omission controls](../Proofs/QMClosure/BoundedLikelihoodProcessControls.lean)
[Retained laws in the original controls](../Proofs/QMClosure/InternalReferenceProcessControls.lean)

The existing `NativeGaussianStatisticalProcess.model` supplies the probability,
operation, common-channel and exact-covariance fields of this contract. Its
preparation family is injective, giving a nonconstant consistency witness for
the supplied process laws. The Gaussian family itself remains supplied.
[Gaussian model and injective preparations](../Proofs/QMClosure/NativeGaussianStatisticalProcess.lean)

## Reproducing the checks

Run the five proof targets and ledger sequentially from the repository root.

```bash
lake build Proofs.QMClosure.BoundedLogProcessRigidity
lake build Proofs.QMClosure.BoundedDominationProcess
lake build Proofs.QMClosure.BoundedLikelihoodProcessRigidity
lake build Proofs.QMClosure.BoundedLikelihoodProcessControls
lake build Proofs.QMClosure.BoundedLikelihoodReferenceCorollaries
lake build Proofs.MetaLang.V8OperationalPrimitiveResearchLedger
```

All seven frozen proof-module builds passed. A shared dependency audit across
the five bounded-likelihood modules and two rational count-order modules
covered all 205 owning-module declarations, including generated declarations
and one private declaration. It found zero local axioms and zero unsafe
declarations. The exact aggregate transitive axiom set was `propext`,
`Quot.sound` and `Classical.choice`.

The audit exited successfully in 47.964 seconds. All seven proof-source hashes
and the target-registration hash matched their approved values before and
after the audit. All 33 declaration citations across the two updated research
tasks matched their audited owning modules.

The bounded-likelihood task cites 21 declarations across its five modules.

## Physical interpretation boundary

Applying this theorem to physical records requires their own laws to satisfy
the supplied exact covariance and full-carrier closure. Its conclusion is
conditional on that mathematical process contract. Physical finite detectors
retain the separate task of identifying which process laws their record
channels satisfy.

Physical identification of `Qraw`, Born readout, detector selection and event
actualization remain open. So do spectral and Hilbert representation, tensor
and composite structure, dynamics, physical scales, full QM and GR. The
research ledger records this result as a conditional kernel theorem.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
