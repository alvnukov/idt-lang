# Finite presentation and exact field boundary

Two independently reviewed analytic packages reduce the finite presentation
for local ball closure and characterize an exact ordered-field coordinate
boundary. Their ledger tasks have stage `analyticAwaitingFormalization`, review
state `notYetKernelChecked` and empty checked evidence. The new checked
dimension theorem supplies one algebraic stage under its own `Frame` contract.
The metric, endpoint, rotation-density, closure and field conclusions remain
pending Lean formalization.
[Finite gate frame dimension](233-finite-gate-frame-dimension.md)
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Compact sufficient presentation

Take a real normalized spanning preparation set and actual commuting
involutions `Jx,Jz`. Define `Jy=Jx Jz` and the three averages `Ei=(I+Ji)/2`.
For each average supply one fixed closed real segment between two available
preparations containing its whole preparation image. Supply actual `H,T` with
`H²=I`, `H Jz H=Jx`, `T³=I`, `T≠I` and `T Jz=Jz T`.

For the preparation-closure endpoint, require at least one average `Ek` to
preserve the preparation set `S`. Requiring all three averages to be actual
destructive maps is a sufficient stronger version. The checked `Frame`
dimension theorem uses the range premises and finite gate relations, while
this additional actual-map premise is used in filling the preparation closure.
[FiniteGateFrameDimension.lean](../Proofs/QMClosure/FiniteGateFrameDimension.lean)

The analytic presentation derives the destructive multiplication table and
projector totality from the phases. Its dimension and rank step is now checked
for the commuting involutive-H specialization. It targets a derived center,
positive real inner product and `r>0` with `closure(S)=c+closedBall(0,r)`.
Exact availability of every ball point additionally requires closedness or a
state-completion convention. Mathematical limiting rotations leave physical
process-limit access separately specified.
[Earlier analytic ball-closure route](232-finite-gate-ball-closure-route.md)

## Pending geometry after the dimension theorem

Rank-one common average and normalization determine a center. The binary
output lines and totality bound the preparation set. Its closed convex hull is
a compact full-dimensional normalized affine body. This is a mathematical
envelope, with physical mixing resources kept explicit.

Centroid and covariance invariance under the actual reversible gates give a
common fixed center and a positive metric. Character axes become orthogonal.
The order-three action is a rotation by either sign of `120°` around z, and
its H-conjugate rotates about x. Their product has trace `−3/4` and hence
infinite order through the algebraic-integer trace criterion.

The narrower density route uses the product's full rotation circle and its
conjugate under the z rotation. The two circle axes are nonparallel. Their
infinitesimal generators and bracket span `so(3)`, giving the mathematical
rotation closure `SO(3)`. This two-circle generation bridge requires a genuine
formalization. It avoids making classification of every closed subgroup the
only possible proof route.

Rotation invariance makes the convex envelope a ball. Each average is the
orthogonal projection onto its pointer axis. Its range bound and available
endpoints force the pointer endpoints to be antipodal with the common ball
radius. The closure of `S` contains the pointer sphere. One actual `Ek` projects
that sphere onto its full diameter, and rotation fills the ball.
Formalization of these geometric and closure steps remains pending.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

The y-plus mixture coordinate after `T` on the x-plus pointer is
`(2±√3)/4`. Under the one-destructor minimum, actual `Ey` availability is an
additional condition for physically performing that particular binary readout.
The coefficient's geometric derivation leaves event actualization and the
orientation sign separately specified.

## Separately labeled presentation extensions

The reviewed analytic argument allows positive finite order `H^m=I` together
with conjugation by `H⁻¹`. Finite order makes inverse action available on `S`.
The checked source retains the exact specialization `H²=I`.

A stronger analytic extension removes the phase-commutation premise while
retaining all three binary range bounds and the other operational assumptions.
Expansion still gives `I=Ex+Ey+Ez−2ExEz`. The endpoint bounds constrain `ExEz(S)`
as well as each `Ei(S)`, yielding boundedness and finite dimension. Compact
envelope covariance gives an invariant metric. Each centered average has rank
at most one, forcing normalized dimension at most three.

A two-dimensional normalized carrier would make nonidentity `T³=I` a
`120°` rotation. Its commuting orthogonal involution `Jz` would be scalar.
H-conjugacy would equate `Jx` and `Jz`, making `Jy=I` and violating the y-average
binary rank bound. The normalized dimension is therefore three. The rank bound
for `I+Jx Jz` then makes the two phase axes perpendicular and derives their
commutation. This extension has its own pending proof obligations.

Defining `Jx=H Jz H⁻¹` also transfers its involution and operational access.
The corresponding identity `Ex=H Ez H⁻¹` transfers the z binary range and
actual availability to x using transported endpoints. The product-average
`Ey` range bound remains substantive. These reductions are analytic extensions
with explicit contracts. Global minimality of the primitives remains open.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Exact relation controls

The following controls delimit the analytic presentation. The sphere control
has a checked companion Frame and an explicit unavailable projection. The
remaining relation-deletion controls retain analytic status and planned Lean
artifacts. The table keeps their exact changed premises explicit.

| Changed premise | Concrete analytic control | Remaining boundary |
| --- | --- | --- |
| Actual average availability omitted | Unit sphere in normalized real four-coordinate space, standard coordinate half-turn phases, axis exchange H and a z rotation by 120°. | All three projection ranges lie in pointer segments, while a coordinate projection can leave the sphere. |
| T nonidentity omitted | Classical tetrahedron with vertices `(1,1,1)`, `(1,−1,−1)`, `(−1,1,−1)`, `(−1,−1,1)`, with `T=I`. | Coordinate projections are actual and the axis pointers are available edge midpoints. |
| H conjugation omitted | Hexagonal prism `|x|≤1`, `|x±√3y|≤2`, `|z|≤1`, with `H=I` and T a 120° z rotation. | Named gate transport is a substantive constraint. |
| Product-average binary range omitted | The same prism with `Jx=Jz` the z half-turn, so `Jy=I` and `Ey=I`. | The x and z averages retain binary ranges, while the identity y average has a higher-dimensional image. |
| T commutation with Jz omitted | The tetrahedron with `T(x,y,z)=(z,x,y)`. | This nonidentity order-three symmetry preserves the other stated finite data. |
| Exact order three replaced by unspecified finite order | The unit octahedron with `T(x,y,z)=(−y,x,z)`. | The nonidentity quarter-turn has order four and preserves the octahedron. |
| Finite-order H weakened to invertible forward action, retaining `H Jz H⁻¹=Jx` | The prism with `H(x,y,z)=(z,y/4,x/4)`. | This gate is not an involution and has no positive finite order; its inverse sends `(0,0,1)` to `(4,0,0)`, outside the preparation set. |
| Real carrier semantics reinterpreted as complex ambient dimension | `V=ℂ⁴` with the same real gate matrices and the ordinary real ball as preparations in its real normalized slice. | Complex spanning and real-segment bounds leave a real three-ball inside a real six-dimensional complex normalization kernel. |

These controls preserve the relevance of exact torsion, nonidentity, pointer
phase commutation, H transport, the transverse binary bound and operational
inverse access. Independent origins for those supplied resources remain open.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Ordered-field characterization

Let `F` be an ordered subfield of the reals. Fix one exact F-linear normalized
spanning carrier, F-valued available endpoints and F-linear gates satisfying
the full selector contract. Binary outputs use coefficients in `F∩[0,1]`.
Real-segment wording between distinct F-valued endpoints gives the same
coefficient, recovered as a ratio of F-coordinate differences.

Conditional on the pending real geometric selector, an exact realization of
this full contract exists precisely when `√3∈F`. The necessity uses the
selector's equal-radius orthogonal endpoint frame. The sufficiency uses the
explicit finite-word construction below. The entire field task retains
`analyticAwaitingFormalization/notYetKernelChecked` and empty checked evidence.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

Choose an F-basis and extend scalars to a real vector space. The embedded
preparation set real-spans the extended carrier. Gate relations, actual
availability, nonidentity, endpoint membership and segment bounds survive the
extension. After the real selector, the center and three pointer displacements
`v_x,v_y,v_z` are F-valued. Their equal lengths and real orthogonality make
them both an F-basis and an orthogonal equal-length real basis of the
normalization kernel.

The actual nonidentity order-three gate therefore has transverse action

```text
T(v_x) = −v_x/2 + b v_y,
T(v_y) = −b v_x − v_y/2,
4b² = 3.
```

F-linearity in the endpoint basis gives `b∈F`, and real ordering gives `√3∈F`.
The derived metric may have irrational coefficients in an earlier coordinate
system. The equal-radius endpoint basis fixes the coefficients relevant to
this field argument. The finite-operation image of the available x pointer
already contains the coefficient `b`, so nonclosed preparation sets retain
the exact field constraint.

For the y-plus mixture coordinate `p=(1+b)/2`,

```text
16p² − 16p + 1 = 0,
p = (2±√3)/4.
```

The rational exclusions for `4t²=3` and `16p²−16p+1=0` are planned algebraic
kernels. A separate planned polynomial bridge derives `a=−1/2` and `4b²=3`
from orthogonal-plane coefficients, their cube identities and nonidentity.
These algebraic kernels require their own checked declarations and leave the
preceding geometric bridges separately quantified.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Countable exact model over Q(√3)

Take `F=ℚ(√3)` and coordinates `(t,x,y,z)` in `F⁴`, with `u=t` and the six
normalized coordinate pointers. Let each `Ei` retain t and only coordinate i.
The phases are `Ji=2Ei−I`. Use

```text
T(t,x,y,z) = (t, −x/2−√3y/2, √3x/2−y/2, z),
H(t,x,y,z) = (t,z,y,x).
```

Start from the six pointers and take all finite words in the three averages,
three phases, `T` and `H`, including the empty word. Each gate preserves the
resulting preparation set by construction. The inverse words `T²` and `H`
also preserve it. Projections contract the ordinary spatial norm and the
reversible gates preserve it, so every output lies in the unit ball. Each
binary coefficient `(1+s_i)/2` belongs to `F∩[0,1]`. The pointers span `F⁴`.

The model's coordinates lie in the countable ring `ℤ[1/2,√3]`. There are
countably many finite words, so exact available preparations are countable.
The pending analytic selector gives real unit-ball closure. Exact preparation
access to all F-valued or real ball points remains a separate resource.
The construction works over every real subfield containing `√3`.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Rational forward-only control and encoding scope

A rational prism control uses coordinates `(x,Y,z)` with `|x|≤1`,
`|x±Y|≤2` and `|z|≤1`. Its x and z pointer radii are one and its Y radius is
two. Coordinate projections and half-turn phases preserve the set. The gates

```text
T(x,Y,z) = ((−x−Y)/2,(3x−Y)/2,z),
H(x,Y,z) = (z,Y/4,x/4)
```

are rational. T has order three, fixes the z pointers and preserves the prism.
H is invertible, preserves the prism forward and carries the z pointers to x.
Its inverse sends `(0,0,1)` to `(4,0,0)`, outside the prism. This control retains
an explicit two-sided operational-access failure under rational coordinates.
Its Lean formalization remains planned.

The field boundary concerns one exact finite-dimensional linear carrier whose
gates and endpoint frame are all over `F`. Rational symbolic syntax can
describe algebraic field extensions. Rational approximations require their
own relaxed equations and error bounds. Other rational encodings require
their own rank, endpoint and operational-meaning checks.

The analytic field result leaves real state completion, continuous physical
gate families, complex scalars, tensor products, event actualization, physical
constants and independent gate origins as separate questions. The scalar
mixture coordinate alone supplies no event-actualization rule.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
