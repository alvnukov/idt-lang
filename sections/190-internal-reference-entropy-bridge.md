# Internal reference entropy bridge

An internal preparation reference and fixed raw diagonals strengthen the
reference-entropy contract from section 188. Under that contract, every
directed pairwise preparation KL divergence is finite. A separate full-product
interface consequently derives the finite-entropy input of the existing
classical-process adapter from one-way finite KL to a chosen preparation.

## Internal reference forces mutual support

A coordinatewise-monotone operation `F` on a preorder, with `F(F(p)) = swap(p)`
and `F(x,x) = (x,x)`, reverses every comparison. Thus `a <= b` entails `b <= a`.
On a partial order, comparable elements are equal. Incomparable distinct
elements remain possible.
[Order obstruction](../Proofs/QMClosure/TransparentSwapRootOrderWall.lean)

One common Markov channel with full independent-product covariance makes
preparation absolute continuity a coordinatewise-preserved preorder. The
order theorem makes that relation symmetric on comparable preparations.
If the reference is `alpha = K(x0)` and every `K(x)` has finite KL to `alpha`,
every preparation is absolutely continuous with respect to every other one.
Every common effect therefore has responses that are all zero, all one, or
pointwise strictly between zero and one. A single uniform positive endpoint
margin remains a separate condition.
[Internal-reference support bridge](../Proofs/QMClosure/InternalReferenceSupportBridge.lean)

## Likelihood transport supplies the missing entropy bound

Retain the section 188 contract on an arbitrary measurable outcome carrier.
It supplies probability preparations, finite reference KL, one common Markov
channel preserving `alpha product alpha`, raw square-swap and both exact
marginal laws. Its factorization theorem gives full product covariance.
Add only an internal reference `alpha = K(x0)` and fixed raw diagonals.

Hellinger-affinity data processing closes the square-swap cycle and becomes
an equality at every raw input. Equality yields exact likelihood transport
on the actual stationary coupling `(alpha product alpha) compProd channel`,
whose input and output marginals are both `alpha product alpha`. The argument
covers arbitrary measurable carriers using the common forward channel.
[Affinity saturation](../Proofs/QMClosure/LikelihoodTransportSaturation.lean)
[Statistical adapter](../Proofs/QMClosure/InternalReferenceEntropyBridge.lean)

Write `g_x = log(dK(x)/dalpha)`, `a(x) = fst(F(x,x0))` and
`b(x) = snd(F(x,x0))`. Finite
almost-everywhere log comparisons first give `g_(a x) + g_(b x) = g_x` and
make `Q_x = g_(a^2 x) - g_(a x) + g_x/2` constant. Combining `Q_(a^2 x)`,
`Q_(a x)` and `Q_x/2` gives an actual fourth raw iterate.

```text
g_(a^4 x) = -g_x/4 + c    almost everywhere.
```

The log-transport helper requires measurable finite log functions and its
transport identity. Log integrability is derived later. Only finitely many
almost-everywhere identities are combined in each comparison.
[Finite log elimination](../Proofs/QMClosure/LogDensityProcessTransport.lean)

Normalization of that actual preparation yields a genuine integrable
reciprocal-quarter density moment. Forward density integrability supplies
the positive side, hence an integrable exponential absolute-log moment.
Young's entropy inequality and the supplied finite reference KL then yield
cross-log integrability and finite `KL(K(x)||K(y))` for every directed pair.
The final adapter derives every helper premise from the original contract,
the internal-reference equality and fixed raw diagonals.
[Moment and entropy transfer](../Proofs/QMClosure/RelativeEntropyMomentTransfer.lean)
[Pairwise entropy bridge](../Proofs/QMClosure/InternalReferenceEntropyBridge.lean)

The new `PointedContract` starts with full product covariance, square-swap,
fixed diagonals, one common Markov channel and one-way finite KL to its chosen
reference preparation. Covariance at the fixed reference diagonal derives
reference-product invariance. The bridge then constructs the existing
classical-process contract with its all-pair finite-entropy field proved.
[Pointed process interface](../Proofs/QMClosure/InternalReferenceEntropyBridge.lean)

The existing native Gaussian model supplies a nonconstant consistency witness
for `PointedContract`. Its ordinary Gaussian-coordinate preparations at means
zero and one are distinct, as established by preparation injectivity. The
Gaussian family, coordinates and channel are supplied mathematical data.
Physical derivation and calibration remain open.
[Gaussian witness](../Proofs/QMClosure/InternalReferenceProcessControls.lean)

## Omission controls preserve the premise boundary

| Omitted condition | Retained structure and consequence |
| --- | --- |
| Fixed raw diagonal | Bool-squared preparations use fair or point laws in each coordinate. The common routing channel `T((a,b),(c,d))=((b,c),(d,a))` has square-swap, full covariance, internal reference invariance and finite reference KL. A raw diagonal moves and directed pairwise KL can be infinite. |
| One common channel | Five raw labels comprise the uniform `Fin 4` reference and its four point preparations. A fixed-diagonal raw square root of swap has full covariance under pair-dependent reference-preserving translation/swap channels. All reference KL values are finite, some pairwise KL values are infinite, and a common channel supplying all these covariances is impossible. |

These controls concern the stronger support and pairwise-entropy conclusions.
These controls make no minimality claim for the earlier factorization theorem.
The external uniform-reference control from section 188 separately distinguishes
an internal reference from a supplied dominating reference outside the family.
[Internal-reference controls](../Proofs/QMClosure/InternalReferenceProcessControls.lean)
[Earlier reference controls](188-reference-entropy-factorization-and-detector-support-boundary.md)

## Unformalized outlook

An independently reviewed analytic route targets individual bounded-likelihood
rigidity on arbitrary measurable carriers. Under probability preparations,
one common channel, full product covariance, square-swap and fixed diagonals,
a finite positive measure bound `P(x) <= C P(y)` should force equality, with
finite KL absent from the standalone premises. Reverse bounded domination and
finite log-transport relations give incompatible oscillation factors `1/16`
and `1/4` for the fourth raw iterate unless the log density is constant.
For a dominated internal-reference family, the proposed consequence gives each
density of a preparation measure distinct from `alpha` essential supremum
infinity and essential infimum zero.
This remains an analytic task with empty checked evidence, separate from the
checked results and audit counts.
[Research task](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

The finite-support consequence overlaps the existing finite-outcome constancy
theorem under all-pair positive affinity. Applying either route to observation
records requires those record laws to satisfy its exact product covariance
and full-carrier closure hypotheses.
[Existing finite-outcome theorem](../Proofs/QMClosure/FiniteOutcomeChannelWall.lean)

## Reproducing the checks

Run the registered targets sequentially from the repository root.

```bash
lake build Proofs.QMClosure.TransparentSwapRootOrderWall
lake build Proofs.QMClosure.InternalReferenceSupportBridge
lake build Proofs.QMClosure.LikelihoodTransportSaturation
lake build Proofs.QMClosure.LogDensityProcessTransport
lake build Proofs.QMClosure.RelativeEntropyMomentTransfer
lake build Proofs.QMClosure.InternalReferenceEntropyBridge
lake build Proofs.QMClosure.InternalReferenceProcessControls
lake build Proofs.MetaLang.V8OperationalPrimitiveResearchLedger
```

All seven registered proof-module builds passed locally. An independent
frozen-source audit covered all 287 owning-module declarations across the nine
proof modules in this cluster, including 41 private declarations and generated
declarations. Counts for the seven modules above were 3, 5, 9, 53, 5, 56 and 113.
One shared axiom traversal found no local axioms, unsafe declarations or
`sorryAx`. The exact transitive axiom set was `propext`, `Quot.sound` and
`Classical.choice`. All nine proof-source hashes and the target registration
hash matched the approved snapshot before and after the audit. The audit exited
successfully in 53.05 seconds. All 58 declarations cited by the three updated
ledger entries matched their audited module origins. The unformalized outlook
retains empty checked evidence and contributes no audited declarations.

## Remaining physical obligations

The preparation family, common channel, raw operation and finite KL to the
chosen reference remain supplied. The proof derives cross-log integrability
and all-pair finite KL. The conditional mathematical Hilbert-distance adapter
remains available under its own hypotheses.

The reference identity `g_x0 = 0` expresses a density ratio of one. Detector
acceptance and the echo algebra's zero input require separate identifications.
An adapter identifying the statistical and echo readouts remains open.
Independent physical identification of `Qraw`, Born readout, detector selection
and event actualization remains required. Tensor structure, dynamics, physical
scales, full QM and GR retain their separate obligations.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
