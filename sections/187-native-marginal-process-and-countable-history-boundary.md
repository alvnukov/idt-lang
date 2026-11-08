# Native marginal process and countable history boundary

The preceding native-noise result classified one exactly stationary law.
This cluster starts from a family whose first-output marginal obeys the
native law at every ordered pair. Its contract uses one marginal law in
place of the earlier full-product covariance premise. It supplies a mathematical selector conditional
on the chosen real sample carrier and native mixer. The physical origin of
that contract remains open.

## One marginal determines the full family structure

Supply probability preparations on the real two-coordinate sample carrier,
the specified native real-linear mixer, a raw operation whose square is swap,
and exact first-output marginal covariance for every ordered preparation pair.
Each input uses independently prepared samples. The second marginal,
full-product covariance and moments are conclusions. Finite KL has the
separate precise conditions below.

These premises force each preparation to be an isotropic Gaussian with its
own actual mean and one variance shared by the family. The mean map
intertwines the raw operation with the native mean mixer. The second
marginal, independent-output full-product covariance and diagonal
transparency of preparation measures follow. The observed carrier of
preparation measures consequently has a square-swap, diagonally transparent
operation. Original raw-label diagonal transparency would require an extra
condition such as preparation-map injectivity.
[Family bridge](../Proofs/QMClosure/NativeMarginalProcessBridge.lean)

For each ordered pair, actual KL is finite exactly when the shared variance
is positive or the two preparation measures agree. All ordered KL
divergences are finite exactly when the variance is positive or the family
is constant. A non-Dirac preparation is sufficient, and a constant Dirac
family also qualifies. Absolute continuity with respect to one reference
preparation supplies finite entropy through this particular family
classification. This gives the existing classical statistical process bridge
on the observed carrier.
[Gaussian family helper](../Proofs/QMClosure/NativeIsotropicGaussianFamily.lean)
[Entropy bridge](../Proofs/QMClosure/NativeMarginalProcessBridge.lean)

## Controls preserve the missing-premise boundary

A hidden-label family on the sample carrier times `Fin 5` has nonconstant
unit-variance Gaussian preparations, finite KL and full covariance, while
the raw diagonal moves. The preparation measures still have transparent
diagonals.

A varying-variance family has both marginal covariance laws and fixed raw
diagonals. At positive input variances 1 and 3, square-swap fails and the
actual output product covariance fails. A selected joint characteristic
function has value `exp(-3)`, while the required independent target gives
`exp(-2)`. These controls isolate the raw-label and square-swap premises.
[Omission controls](../Proofs/QMClosure/NativeMarginalProcessControls.lean)

## Countable deterministic histories force degenerate stationary output

Let the entire history carrier be countable and carry a probability law.
A deterministic measurable map into the specified native real sample
carrier produces a countably concentrated outcome law. If that pushed law
is exactly two-step native stationary, it must be Dirac. First-output
stationarity is sufficient. Each smoothing step independently re-prepares
two samples from its current law.

An infinite-history space over a finite alphabet can be uncountable.
The theorem requires countability of the whole carrier. Stochastic output
kernels, approximate stationarity and other outcome carriers require
separate analysis.
[Countable history wall](../Proofs/QMClosure/CountableHistoryNativeNoiseWall.lean)

## Nonconstant families have dense actual mean range

Two distinct preparation measures force the actual complex means to be
dense in the supplied ordinary complex plane. Normalize two actual means
to 0 and 1. Mean compatibility then places every existing finite allocated
scalar-program value in the normalized mean image. The proof reuses the
preexisting Gaussian-dyadic program approximation theorem.
[Mean density](../Proofs/QMClosure/NativeMarginalMeanDensity.lean)
[Prior dyadic approximation](../Proofs/QMClosure/NativeGaussianDyadicDensity.lean)

This result needs neither finite KL nor a non-Dirac preparation. It includes
nonconstant zero-variance Dirac families. Exact coverage of the entire
plane additionally requires a closed mean range. Finite approximation at
each requested tolerance supplies no uniform resource ceiling or physical
availability of those preparations.

## Reproducing the checks

Run these registered targets sequentially from the repository root.

```bash
lake build Proofs.QMClosure.NativeIsotropicGaussianFamily
lake build Proofs.QMClosure.NativeMarginalProcessBridge
lake build Proofs.QMClosure.NativeMarginalProcessControls
lake build Proofs.QMClosure.CountableHistoryNativeNoiseWall
lake build Proofs.QMClosure.NativeMarginalMeanDensity
lake build Proofs.MetaLang.V8OperationalPrimitiveResearchLedger
```

The five registered module builds passed locally. An independent frozen-source
audit checked 164 owning-module declarations, including 12 private roots.
The module counts were 30 for the Gaussian family helper, 73 for the family
bridge, 45 for the controls, 2 for the countable-history wall and 14 for mean
density. It found no local axioms, unsafe declarations or `sorryAx`. The
exact transitive axiom set was `propext`, `Quot.sound` and `Classical.choice`.
All approved source hashes remained stable, and the audit exited successfully
in 15.239 seconds.

## Remaining interpretation boundaries

The real sample carrier, native mixer, independent preparations, exact
covariance and ordinary topology remain supplied. General detector
selection, detector randomization, parameterized detector classification
and nonlinear coordinate conjugation retain their separate analytic
frontiers. The independence-only noise characterization is also separate
from the exact stationarity proof.

An independently specified `Qraw`, physical calibration and scale selection,
event actualization, Born interpretation, composites, Bell closure, full QM
and GR remain open. The operational ledger separates the checked statements
from those obligations.
[Research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
