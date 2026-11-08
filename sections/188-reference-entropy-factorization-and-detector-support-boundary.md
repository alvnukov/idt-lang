# Reference entropy factorization and detector support boundary

One reference-preserving Markov channel and exact marginal laws force independent
outputs under a finite reference-entropy contract. A separate support theorem
restricts exact detector endpoints when preparations are mutually absolutely
continuous. The reference-entropy contract alone does not supply that support
condition.

## Marginal covariance forces full-product covariance

Let `K(x)` be probability preparations on an arbitrary measurable sample space,
and let `alpha` be a supplied probability reference. Each `KL(K(x)||alpha)` is
finite. One actual common Markov kernel `kappa` on sample pairs preserves
`alpha product alpha`. Independently prepared inputs have the two output
marginals prescribed by a raw operation `F` satisfying `F(F(p)) = swap(p)`.

Write `S(p)` for the sum of the two input reference divergences and `MI(p)`
for the output divergence from the product of its own marginals. The checked
entropy decomposition and data processing give

```text
MI(p) + S(F(p)) <= S(p).
```

Applying the inequality at `F(p)` closes the square-swap cycle. The sum `S`
is conserved. Its finiteness then forces `MI(p) = 0`, so the actual joint
output equals the product of the prescribed preparation marginals. Reference
data processing is an equality at every input pair. The proof uses no
channel-inverse premise.
[Factorization theorem and adapter](../Proofs/QMClosure/ReferenceEntropyFactorization.lean)

The helper constructs a Markov disintegration of a joint probability dominated
by a probability product using normalized Radon–Nikodym densities. Its fallback
rows use the second reference measure. Arbitrary measurable spaces are covered,
with no supplied standard-Borel or nonempty instance. The product-reference
decomposition holds in extended nonnegative reals even at infinite divergence.
Finiteness is needed for faithful real conversion and for the factorization
argument's cancellation.
[Dominated disintegration](../Proofs/QMClosure/DominatedProductDisintegration.lean)
[Product-reference decomposition](../Proofs/QMClosure/ProductReferenceEntropyDecomposition.lean)

| Premise | Exact role or boundary |
| --- | --- |
| Supplied probability reference `alpha` | Need not be a member of the preparation family. |
| Reference-product invariance | Makes reference-relative data processing compare the required entropies. |
| Finite reference KL for every preparation | Permits cancellation of the conserved finite entropy sum. |
| Both exact marginal laws and raw square-swap | Close the entropy cycle. A first-marginal law suffices with explicit sample-kernel swap symmetry. |
| One common sample-pair channel | Retained as the physical contract. Mathematical minimality of commonness is unproved. |
| Chosen raw state, fixed raw diagonal and finite directed pairwise KL | Additional inputs to `Contract.classicalProcess`. |

## Controls distinguish the supplied premises

The factorization controls cover five separate boundaries.

| Supplied or omitted condition | Control and conclusion |
| --- | --- |
| Omit reference invariance | A one-element preparation family with fair-bit law and copy-first channel have both prescribed marginals and raw square-swap, with correlated output. |
| Omit finite reference KL | The same preparation and copy-first channel preserve the product of the point reference at `false`, with correlated output. Absolute continuity also fails, so this control does not isolate integrability alone. |
| Omit raw square-swap | A half-identity, half-simultaneous-bitflip channel preserves the fair product reference. Bernoulli `1/4` inputs have fair output marginals and joint masses `5/16` on the diagonal and `3/16` off the diagonal. A constant raw operation fits these marginals but lacks square-swap. |
| Keep finite reference KL, omit pairwise KL | `Fin 5` point preparations admit an external uniform reference and a reference-preserving root-swap permutation. Distinct preparations have infinite directed pairwise KL. |
| Keep the reference contract, omit diagonal transparency | The unit-Gaussian family with raw minus-native operation and sample mixer `-G` satisfies the reference laws while sending diagonal means from `x` to `-x`. |

The first three controls show that the listed omitted conditions can permit
correlated outputs. The final two keep factorization and separate the stronger
process-adapter premises. The last control changes the native mixer from `G`
to `-G`, so it is compatible with the earlier diagonal conclusion under `G`.
[Factorization controls](../Proofs/QMClosure/ReferenceEntropyFactorizationControls.lean)

## Common detectors preserve exact support endpoints

For measures `mu << nu`, a common kernel transfers a null output event from
`nu` to `mu`. A common measurable effect valued in `[0,1]` consequently transfers
zero acceptance in the same direction. Applying that statement to the
complementary effect transfers acceptance one.

For a mutually absolutely continuous probability family, every common effect
has responses that are all zero, all one, or strictly between zero and one
at each preparation. The theorem supplies no uniform positive margin. A target
having both a zero and a nonzero value, or both a one and a non-one value,
cannot exactly equal these responses. Finite directed pairwise KL supplies
the support premise. This specializes to the supplied isotropic native
Gaussian family when its variance is nonzero.
[Endpoint support wall](../Proofs/QMClosure/DetectorEndpointSupportWall.lean)

The finite-KL positive Bool preparations have indicator responses `1/3` and
`2/3`, so strictly interior responses may vary. Distinct point preparations
have indicator responses `1` and `0` and infinite directed KL. Finite reference
KL alone therefore does not extend this wall to every reference-factorization
contract. Zero-variance nonconstant native point families are also outside
the native endpoint theorem's variance premise.
[Endpoint controls](../Proofs/QMClosure/DetectorEndpointSupportControls.lean)

## Reproducing the checks

Run the registered targets sequentially from the repository root.

```bash
lake build Proofs.QMClosure.DominatedProductDisintegration
lake build Proofs.QMClosure.ProductReferenceEntropyDecomposition
lake build Proofs.QMClosure.ReferenceEntropyFactorization
lake build Proofs.QMClosure.ReferenceEntropyFactorizationControls
lake build Proofs.QMClosure.DetectorEndpointSupportWall
lake build Proofs.QMClosure.DetectorEndpointSupportControls
lake build Proofs.MetaLang.V8OperationalPrimitiveResearchLedger
```

The six registered proof-module builds passed locally. An independent
frozen-source audit checked all 173 owning-module declarations using one shared
axiom-traversal state, including 14 private declarations. Counts were 2 for
dominated disintegration, 8 for entropy decomposition, 49 for factorization,
87 for factorization controls, 13 for the endpoint wall and 14 for endpoint
controls. It found no local axioms, unsafe declarations or `sorryAx`. The exact
transitive axiom set was `propext`, `Quot.sound` and `Classical.choice`. All
audited source hashes and the target registration remained stable. The audit
exited successfully in 19.308 seconds. All 51 declarations cited by the two
ledger entries were present among the audited roots.

## Remaining physical obligations

The reference law, reference invariance, finite entropy, raw
square-swap and exact marginal laws remain supplied. A fixed raw diagonal,
chosen raw state and finite directed pairwise KL remain additional inputs
to the process bridge. The general factorization theorem imposes no Gaussian
carrier or raw measurability structure.

Independent physical identification of `Qraw`, detector selection, event
actualization and a Born interpretation remain open. Hilbert representation,
composites, dynamics, physical scales, full QM and GR retain their separate
obligations. Any physical target excluded by the endpoint theorem requires
an explicit identification of that target with the common effect response.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
