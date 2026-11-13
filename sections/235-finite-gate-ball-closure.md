# A conditional finite-gate ball-closure theorem

`FiniteGateFrameDimension.Frame.exists_ball_closure` is an end-to-end Lean
theorem. From a real finite-gate `Frame` and actual preparation preservation by
at least one average map, it constructs coordinates with a strictly positive
radius and proves that the mathematical spatial preparation-image closure is
the corresponding closed three-ball. The four new kernel entries have passed
the shared dependency audit and independent review.
[FiniteGateBallClosure.lean](../Proofs/QMClosure/FiniteGateBallClosure.lean)

## Exact operational contract

The carrier starts as an arbitrary real vector space `V`. A nonempty set `S`
real-spans `V`, and a supplied real linear normalization `u` has value one on
every preparation. Actual real linear gates `Jx,Jz,H,T` preserve `S` and obey
the following equations on every vector.

```text
Jx² = Jz² = H² = I,
Jx Jz = Jz Jx,
H Jz H = Jx,
T³ = I,   T ≠ I,
T Jz = Jz T.
```

Define `Ex=(I+Jx)/2`, `Ey=(I+Jx Jz)/2` and `Ez=(I+Jz)/2`. For each average,
one pair of available preparation endpoints is selected before choosing the
input `s`. Every output `Ei(s)` lies in their real segment with coefficient in
`[0,1]`. This is a global fixed-output range premise. The endpoints can
initially coincide, and the Frame contract separately records the gate and
range laws. Initial endpoint E-fixedness and availability of every real
segment point are further statements requiring their own justification.
[FiniteGateFrameDimension.lean](../Proofs/QMClosure/FiniteGateFrameDimension.lean)

The ball-closure theorem additionally assumes that at least one of `Ex,Ey,Ez`
actually maps `S` into `S`. A binary range bound places an output in a segment
whose endpoints are available. Actual availability of that output remains a
separate premise. No finite-dimensional instance, metric, coordinate basis,
ball base or physical continuous gate family occurs in this input contract.
Ordered real segment coefficients supply the exact positivity resource used
in the range estimates.
[FiniteGateBallClosure.lean](../Proofs/QMClosure/FiniteGateBallClosure.lean)

## What is derived

The preceding `dimension_forced` theorem first derives real dimension four,
normalization-kernel dimension three, rank two for each average and rank one
for the four character sectors. `exists_axis_coordinates` constructs a real
coordinate equivalence adapted to those sectors and normalization.
[FiniteGateFrameDimension.lean](../Proofs/QMClosure/FiniteGateFrameDimension.lean)
[FiniteGateFrameCoordinates.lean](../Proofs/QMClosure/FiniteGateFrameCoordinates.lean)

The fixed binary endpoints bound every chosen real linear functional on `S`.
Spanning propagates that bound to a fixed preparation-preserving gate orbit.
The quantifier order is

```text
for each fixed A, f and v,
there exists B such that for every natural n, |f(Aⁿv)| ≤ B.
```

The constant may depend on the gate, functional and vector. Two selected
diagonal orbit bounds then give one bound across all even powers of the
reflected transverse matrix.
[FiniteGatePreparationBounds.lean](../Proofs/QMClosure/FiniteGatePreparationBounds.lean)
[FiniteGateInvariantMetric.lean](../Proofs/QMClosure/FiniteGateInvariantMetric.lean)

Bounded reflected powers force the transverse order-three coefficients and a
positive quadratic weight. H fixes the remaining relative scale.
`exists_invariant_metric` packages a spatial quadratic form that is
nonnegative on the whole carrier, strictly positive on nonzero `ker u`, and
invariant under the four actual gates. Its role is real preparation geometry.
Born outcome probabilities and event actualization require separate laws.
[BoundedPlaneTraceRigidity.lean](../Proofs/QMClosure/BoundedPlaneTraceRigidity.lean)
[FiniteGateInvariantMetric.lean](../Proofs/QMClosure/FiniteGateInvariantMetric.lean)

`exists_cubic_coordinates` then constructs nonzero rescalings and matches T to
the standard z-axis cubic rotation. A sign-dependent actual finite word,
either `HTH` or `HT²H`, supplies the matched x-axis cubic rotation. The data
also give exact compatibility of the three averages with coordinate
projections and injectivity of spatial coordinates on each normalization
fibre.
[FiniteGateCubicCoordinates.lean](../Proofs/QMClosure/FiniteGateCubicCoordinates.lean)

## From two finite gates to the closed ball

In real spatial coordinates, the two cubic rotations generate dense rotation
circles about two nonparallel axes. Their inverse actions are finite positive
words because each rotation has order three. Closedness and continuity allow
passage from those finite words to mathematical circle invariance.
The two-circle sphere-transitivity theorem then forces radiality.
[CubicRotationCircleDensity.lean](../Proofs/QMClosure/CubicRotationCircleDensity.lean)
[TwoCircleSphereTransitivity.lean](../Proofs/QMClosure/TwoCircleSphereTransitivity.lean)
[CubicRotationRadiality.lean](../Proofs/QMClosure/CubicRotationRadiality.lean)

Binary preparation bounds make the spatial image closure compact and
nonempty. Spanning supplies a nonzero spatial preparation, giving a strictly
positive attained maximal radius. Radiality supplies its entire maximal
sphere. The one actual average transfers to an actual coordinate projection
on the closure, filling a full diameter. Radiality then fills the ball.
The integration derives the radius bound, its attainment, radiality and
projection preservation before invoking the final radial-ball lemma.
[FiniteGatePreparationClosure.lean](../Proofs/QMClosure/FiniteGatePreparationClosure.lean)
[TwoCircleRadialBall.lean](../Proofs/QMClosure/TwoCircleRadialBall.lean)
[FiniteGateBallClosure.lean](../Proofs/QMClosure/FiniteGateBallClosure.lean)

For the commuting-phase, involutive-H presentation, this checked proof uses
bounded-orbit algebra and two-circle geometry. Earlier finite-order-H and
commutation-derived presentation extensions retain their separate analytic
status. The exact ordered-field characterization involving `√3` also awaits
its own Lean argument.
[Finite presentation and field boundary](234-finite-presentation-field-boundary.md)

## Why the endpoint is preparation closure

`BallClosureData` contains constructed cubic coordinates, a real `R>0` and
the exact equality

```text
closure(spatial preparation image) = {p | sqnorm(p) ≤ R²}.
```

The topology here is the standard real topology on the constructed spatial
coordinate space. The original carrier supplies real-linear semantics, while
the theorem constructs the coordinates used for this closure.
`BallClosureData.image_eq_ball` concludes exact image equality when the
spatial preparation image is separately assumed closed.
[FiniteGateBallClosure.lean](../Proofs/QMClosure/FiniteGateBallClosure.lean)

Mathematical limit-state membership and physically available preparations are
different resource questions. Passage to limiting rotations establishes a
closed-set invariance statement. Physical implementation of a limiting gate
requires an additional process-access principle. Physical preparation completion
and continuous gate-family access remain additional operational resources.
[FiniteGateBallClosure.lean](../Proofs/QMClosure/FiniteGateBallClosure.lean)

## Countercontrols and exact availability

The previously checked `sphereModel` satisfies Frame using the standard
sphere, the same finite gates and all three binary segment bounds.
Its available x-plus pointer maps under `Ez` to a center outside the sphere.
This gives an exact witness for the missing actual-average premise.
[FiniteGateFrameModel.lean](../Proofs/QMClosure/FiniteGateFrameModel.lean)

`FiniteGateCountableModel` starts from six axis pointers and seven actions,
namely the four finite gates and the three averages. Exact preparations are
finite-word evaluations. `generated_countable` proves countability, and
prefixing words establishes actual availability of every alphabet action.
`generatedFrame` satisfies the full Frame contract, and
`generated_all_averages_actual` supplies all three average-preservation laws.
[FiniteGateCountableModel.lean](../Proofs/QMClosure/FiniteGateCountableModel.lean)

`generated_has_ball_closure` directly consumes the end-to-end theorem and
produces `BallClosureData` in the constructed coordinates.
`exact_preparation_control` combines that inhabitant with countability,
all-average availability and the exact preparation set's inequality with the
supplied standard real ball. The standard ball contains an uncountable axis
segment, while the finite-word set is countable. Explicit model gates,
coordinates and unit-ball containment bounds are inputs to this consistency
control. Its exact-state comparison and its constructed coordinate closure
each retain their stated source scope.
[FiniteGateCountableModel.lean](../Proofs/QMClosure/FiniteGateCountableModel.lean)

Further analytic countercontrols isolate other premises. Allowing T to be
identity admits a normalized singleton. Dropping spanning permits unused
extra directions. Choosing a new binary endpoint pair for each input admits
an unbounded normalized hyperplane. Retaining matrix relations while dropping
actual T preservation admits a normalized coordinate cube that a cubic
rotation sends outside itself. These observations retain analytic scope and
their own formalization obligations.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Remaining premises and next obligations

The result is a universal conditional local geometric reduction from the
stated real-linear operational contract. Real representation, normalization
and spanning, globally fixed ordered binary ranges, the exact actual finite
gates and one actual average remain supplied resources. Their independent
origin from the IDT primitive base is the next operational question.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

The spatial form and ball specify local preparation geometry. Allowed effects,
instruments, probability interpretation and actual events require their own
contracts. Complex representation and orientation, tensor/composite and
entanglement structure, Bell and local-tomographic constraints, physical
generators, empirical scales and full QM remain separate continuations.
Sections 225–234 preserve their historical scope, and the new ledger rows
identify the exact checked commuting, involutive-H theorem.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
