# Native noise classification and detector conservation walls

The Gaussian statistical witness made a common-channel reconstruction contract
nontrivial by supplying Gaussian preparation laws. The next question was whether
the same native sample mixer constrains the law itself, and whether detector
conservation can be imposed broadly without collapsing observable distinctions.
This advances the original primitive search by giving a mathematical selector conditional on the supplied real sample carrier, native mixer and exact stationarity contract.

## Gaussian noise from exact native stationarity

For a scalar Borel probability law, the signed-smoothing equation

```text
phi(t) = phi(t/2)^3 * conjugate(phi(t/2))
```

forces a finite second moment and identifies the law as the real Gaussian at
its own mean and variance. The second moment is a conclusion of the equation.
No moment, density or nondegeneracy premise is needed. Zero variance is included.
[Scalar moments](../Proofs/QMClosure/GaussianSignedSmoothingMoments.lean)
[Scalar classification](../Proofs/QMClosure/GaussianSignedSmoothingCharacterization.lean)

For the supplied real two-coordinate sample carrier and native real-linear
mixer, let `S(mu)` be the first-output law of two independent samples with law
`mu`. Exact two-step stationarity `S(S(mu))=mu`, with each step forming fresh independent samples from its input law, forces a product of two real Gaussians with the
law's actual coordinate means and a shared variance. Exact first-output
stationarity is sufficient. Coordinate independence and finite moments follow.
On this same carrier, a stationary law concentrated on a countable set must
be a Dirac law. This corollary uses the native carrier and sample map.
[Native classification](../Proofs/QMClosure/NativeStationaryNoiseCharacterization.lean)

## Detector conservation has closure walls

Supply probability preparations, a raw operation whose square is swap, and one
common transport of full product laws. If every measurable effect in `[0,1]`
conserves its acceptance product at one input pair, the two preparation measures
at that pair are equal. This result needs no finite-KL, Gaussian or diagonal
transparency assumption.
[Universal wall](../Proofs/QMClosure/UniversalDetectorConservationWall.lean)

A separate result retains the existing classical statistical process contract,
including raw square-swap, fixed raw diagonals, finite ordered latent KL and
exact common full-product Markov covariance. If one detector effect and its complement both conserve acceptance
products at all input pairs, the detector acceptance is constant across the
family. Equivalently, one can require conservation for the effect and its fair
randomization with the sure effect.
[Complementary wall](../Proofs/QMClosure/ComplementaryDetectorConservationWall.lean)

Checked five-label controls isolate the premises. Distinct strictly positive
binary preparation laws can conserve every effect product while admitting no
common transport of full product laws. Dirac preparations admit the actual
routing channel and a nonconstant effect whose acceptance and rejection
products are conserved, while distinct latent preparations have infinite KL.
[Omission controls](../Proofs/QMClosure/DetectorConservationOmissionControls.lean)

## Reproducing the module builds

Run these registered targets sequentially from the repository root.

```bash
lake build Proofs.QMClosure.GaussianSignedSmoothingMoments
lake build Proofs.QMClosure.GaussianSignedSmoothingCharacterization
lake build Proofs.QMClosure.NativeStationaryNoiseCharacterization
lake build Proofs.QMClosure.DetectorEffectOperations
lake build Proofs.QMClosure.UniversalDetectorConservationWall
lake build Proofs.QMClosure.ComplementaryDetectorConservationWall
lake build Proofs.QMClosure.DetectorConservationOmissionControls
```

The seven registered module builds passed locally. An independent local audit
checked 232 declarations owned by these modules, with stable source hashes.
It found no `sorry`, local axioms or unsafe declarations. The aggregate axiom
set was exactly `propext`, `Quot.sound` and `Classical.choice`. The audit exited
successfully in 14.917 seconds. The authoritative evidence declarations and
their actual hypotheses reside in the Lean sources above.

## Open neighboring obligations

The weaker raw-family route remains analytic. It proposes to start with only
first-marginal covariance for every ordered pair and raw square-swap, then
derive shared Gaussian variance, full-product covariance and preparation-level
diagonal transparency. Diagonal transparency is obtained for preparation measures, so the generic
bridge uses the observed carrier or quotient by equality of preparations.
Transparency of the original raw labels would require an extra condition such
as preparation-map injectivity. The positive-variance finite-KL bridge and omission controls await
their own formalization.

Detector randomization and the candidate selection route using coordinate
factorization and one supplied 45-degree symmetry also remain analytic.
The seven modules in this milestone provide no physical selection of sample
coordinates, native mixer, stationary preparation process, variance or detector.
They identify no independently supplied `Qraw`, calibrated physical scale or
event actualization. Born, composite and Bell closure, full QM and GR remain
open. The operational ledger records exact proof pointers and separates the
remaining frontiers. [Research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
