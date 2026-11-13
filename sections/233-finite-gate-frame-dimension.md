# Dimension from a finite gate frame

`FiniteGateFrameDimension.Frame.dimension_forced` derives a four-dimensional
real linear carrier and a three-dimensional normalized kernel from a finite
operational gate contract. Finite-dimensionality is a conclusion of the theorem.
The dimension and companion-control kernel tasks carry `parentAccepted` after
independent review and the shared dependency audit.
[FiniteGateFrameDimension.lean](../Proofs/QMClosure/FiniteGateFrameDimension.lean)

## Exact checked input

The carrier is an initially arbitrary real vector space `V`. A nonempty
preparation set `S` spans `V` and has value one under a supplied real linear
normalization `u`. Four real linear gates `Jx,Jz,H,T` preserve `S` and satisfy

```text
Jx² = Jz² = H² = I,
Jx Jz = Jz Jx,
H Jz H = Jx,
T³ = I,   T ≠ I,
T Jz = Jz T.
```

Define the three averages

```text
Ex = (I+Jx)/2,
Ey = (I+Jx Jz)/2,
Ez = (I+Jz)/2.
```

For each average, the `BinarySegment` premise supplies two fixed available
preparations whose real closed convex segment contains every average output
on `S`. The same two endpoints apply to the entire preparation set. The input
allows a pair to coincide. Finite-dimensionality, a metric and designated
T-fixed endpoints are absent from `Frame`'s input fields.
[FiniteGateFrameDimension.lean](../Proofs/QMClosure/FiniteGateFrameDimension.lean)

The average range bounds are stated separately from actual operation access.
`Frame` requires the four gates to preserve `S`. It places the outputs of the
three averages in their specified endpoint segments. Actual preservation of
`S` by an average is an additional resource in the preparation-closure route.
[FiniteGateFrameDimension.lean](../Proofs/QMClosure/FiniteGateFrameDimension.lean)

## Derived dimensions and ranks

The end-to-end theorem gives all of the following.

- `FiniteDimensional ℝ V` and `finrank ℝ V=4`.
- `finrank ℝ (ker u)=3`.
- Each of `Ex,Ey,Ez` has image rank two.
- The common average `R=(I+Jx+Jz+Jx Jz)/4` has rank one.
- Each transverse character projector `Qx=Ex−R`, `Qy=Ey−R` and `Qz=Ez−R`
  has rank one.

The proof derives the mutually annihilating character-projector decomposition
from the two commuting involutions. Spanning and the fixed binary ranges give
rank at most two for each average. These ranges and the character-sum identity
first supply finite-dimensionality.
[FiniteGateFrameDimension.lean](../Proofs/QMClosure/FiniteGateFrameDimension.lean)

Available gates preserve normalization throughout `V` because they preserve
the normalized spanning set. A real order-three map on a space of dimension
at most two that preserves a nonzero normalization functional is identity.
Applying this fact to the T-invariant `Ez` image yields `T_fixes_Ez`.
Nonidentity `T` needs a two-dimensional complementary real action. Conjugation
by `H` equates the `Ez` and `Ex` image ranks. The resulting rank constraints
force all four character ranks to one and the carrier dimension to four.
[FiniteGateFrameDimension.lean](../Proofs/QMClosure/FiniteGateFrameDimension.lean)

These are universally quantified real-linear statements for every `Frame`
satisfying the source contract. The proof derives its rank and dimension
conclusions from those hypotheses.
[FiniteGateFrameDimension.lean](../Proofs/QMClosure/FiniteGateFrameDimension.lean)

## Concrete ball and sphere frames

`FiniteGateFrameModel.model` supplies the normalized spatial closed unit ball
on `Fin 4 → ℝ`. Its coordinate half-turn phases, axis exchange and real
120-degree z-rotation matrix instantiate the complete finite `Frame` contract.
`model_dimension_forced` directly consumes the general theorem and obtains
its full dimension and rank conclusions. Coordinates, ball geometry and gate
matrices are explicit inputs to this control, establishing nonvacuity of the
conditional contract.
[FiniteGateFrameModel.lean](../Proofs/QMClosure/FiniteGateFrameModel.lean)

The concrete spatial H action is `(x,y,z)↦(z,y,x)`, an axis-exchange reflection.
The symbol H in section 231 has its own proposed coordinate action and
positivity boundary. The present model supplies a generic finite gate meeting
its local conjugation law. Complex orientation remains separately specified.
[FiniteGateFrameModel.lean](../Proofs/QMClosure/FiniteGateFrameModel.lean)

`average_x_available`, `average_y_available` and `average_z_available` prove
that all three coordinate averages preserve the supplied ball preparation set.
The companion `sphereModel` uses the same carrier and gates with spatial
square norm exactly one. It also inhabits `Frame`, including all three fixed
binary segment range bounds and normalized spanning.
[FiniteGateFrameModel.lean](../Proofs/QMClosure/FiniteGateFrameModel.lean)

`sphere_Ez_xPointer` gives `Ez(xPointer 1)=center`.
`center_not_sphere` places that center outside the sphere preparation set, and
`sphere_Ez_unavailable` packages the available-input/unavailable-output witness.
The center lies in the sphere's linear span through `sphere_spanning`.
`sphere_preparations_ne_ball` records the distinct preparation sets. These
checked controls retain the difference between a binary range bound and
actual destructive-map availability, even with the same finite gate frame.
[FiniteGateFrameModel.lean](../Proofs/QMClosure/FiniteGateFrameModel.lean)

## Continuing geometry and origins

The metric, endpoint-radius, rotation-density and preparation-closure bridges
remain analytic obligations. The compact presentation adds actual
availability of at least one average before deriving the strongest ball-closure
endpoint. The checked dimension result supplies its algebraic stage.
[Finite presentation and field boundary](234-finite-presentation-field-boundary.md)

The actual gates, exact finite relations, fixed-output range laws and real
normalized-state semantics remain supplied resources. Independent primitive
origins, event actualization, composite structure and completed QM
reconstruction retain their separate continuations. Sections 225–232 preserve
their historical contracts.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
