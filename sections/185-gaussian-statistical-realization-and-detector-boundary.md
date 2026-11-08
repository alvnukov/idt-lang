# Gaussian statistical realization and detector boundary

The Gaussian construction supplies a nonconstant statistical model of the
classical-process bridge. Mean coordinates, a Gaussian location family with
unit variance in each real coordinate, and the native linear mixer are supplied.
The result establishes consistency of that mathematical contract. The physical
origin of its inputs remains open.

## Actual preparation measures and a common channel

The Gaussian entropy source defines the preparation at complex mean `z` as
the product of the two real Gaussian laws with means `z.re` and `z.im` and
variance one. For every ordered pair `x,y`, actual relative entropy is
`KL(K(x),K(y)) = normSq(x-y)/2`, is finite, and gives Jeffreys comparison
`normSq(x-y)`. [Gaussian entropy source](../Proofs/QMClosure/GaussianLocationEntropy.lean)

The native Gaussian process source defines one deterministic sample map
`G` and proves that it transports every independent preparation product to
the full product at the native mixed means. Its `model` instantiates every
field of `ClassicalStatisticalProcessBridge.Contract`. Preparation measures
distinguish all means, and the reconstructed feature at mean one is nonzero. [Native Gaussian process source](../Proofs/QMClosure/NativeGaussianStatisticalProcess.lean)

## A chosen detector and its conserved logarithmic weight

The invariant-effect bridge turns any supplied measurable effect in
`[0,1]` into an actual binary Markov detector. Given full-product channel
covariance and dual invariance of the product effect, it derives conservation
of the acceptance product. Positive acceptance gives pair-sum conservation
of `W(x) = -log(q(x)/q(reference))`. A reference of maximal acceptance makes
this weight nonnegative. [Invariant-effect bridge](../Proofs/QMClosure/InvariantEffectReadoutBridge.lean)

The Gaussian detector source supplies the particular effect
`g(u) = exp(-(u1²+u2²)/2)`. Its integrated true-event probability and normalized
logarithmic weight are

```text
q(z) = exp(-normSq(z)/4)/2
q(0) = 1/2
W(z) = -log(q(z)/q(0)) = normSq(z)/4
```

[Gaussian detector source](../Proofs/QMClosure/GaussianSoftDetectorBoundary.lean)

The product effect is invariant under `G`, so the general bridge applies.
The acceptance is an ordinary detector-event probability obtained by
integration. A Gaussian singleton has probability zero, and a chosen density
value at a point does not supply this event.

`W` is a defined normalized negative-log response. Its quadratic formula
supplies no derivation of a quadratic event-probability law or the Born rule.
For this same detector, the true-event probability is `q(z)`, while `q(z)/q(0)`
is its normalized ratio with reference acceptance `q(0)=1/2`.

## The finite detector records lose channel information

For input pairs `(1,1)` and `(1,i)`, the binary detector-product rows coincide.
The native mixer sends these means to `(1,1)` and `(1+i,0)`, whose required
detector-product rows differ. Hence one finite stochastic channel cannot
transport even these two equal input rows to their required output products.
The selected true-event acceptance products are nevertheless equal.

The continuum preparation channel and its invariant effect therefore coexist
with an exact obstruction for this fixed binary record channel. The obstruction
concerns common exact transport of full detector-product rows. Approximate
transport and other finite measurements require separate analysis.

## Remaining boundaries

The native Gaussian independence characterization, general positive-variance
formulas, actual affinity formula and classification of all continuous positive
invariant effects retain their analytic, unformalized status. The checked
detector uses the chosen unit variance and chosen effect above.

The construction supplies no physical selection of coordinates, variance,
mixer or detector. It identifies no independently specified original response
`Qraw` and derives no physical scale or event actualization. Born, composite
and Bell closure, full QM and GR remain open.

The authoritative task entries and exact evidence declarations are recorded
in the operational primitive research ledger. [Research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
