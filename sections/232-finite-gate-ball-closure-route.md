# Finite-gate ball-closure route

This independently reviewed analytic argument has ledger stage
`analyticAwaitingFormalization` and review state `notYetKernelChecked`.
Its checked-evidence list is empty. The proposed endpoint is a local
preparation-closure theorem under the exact supplied contract below. Kernel
formalization of the rank, metric, rotation-density and closure steps remains
pending.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Supplied contract

1. A real vector space `V` carries a linear normalization `u` and a nonempty
   preparation set `S`. Every `s∈S` has `u(s)=1`, and `spanℝ(S)=V`.
2. Three actual linear destructive maps `E_x,E_y,E_z` preserve `S`. Each
   `E_i(S)` lies in a fixed closed segment between two available preparations
   `p_i⁻,p_i⁺`. The binary premise fixes these output preparations. Two outcome
   labels with arbitrary retained output information require a stronger range
   argument before this contract applies.
3. The complete destructive multiplication table holds with a common map `R`.
   Projector totality is supplied as `I=E_x+E_y+E_z−2R`.
4. Each phase `J_i=2E_i−I` is an actual transformation preserving `S`. The
   multiplication table derives `J_i²=I`, giving two-sided preservation.
5. An actual linear transformation `T` preserves `S`, obeys `T³=I`, fixes the
   two distinct designated z endpoints, and moves an observable preparation.
   The named fixed axis is part of this premise.
6. A linear equivalence `X` preserves `S` in both operational directions and
   transports the designated z endpoint pair to the designated x endpoint
   pair. Thus `X(S)=S`. A supplied finite involution implementing that exchange
   is one sufficient specialization.

The gate contract specifies operational actions and algebraic laws. Numerical
matrices for `T` and `X`, a selected orientation sign and a physical continuous
transformation family remain additional resources. Earlier projector and
reference kernels provide conditional input routes for item 3 under their own
append, discard, defect and intertwining hypotheses.
[SharpPhaseTomography.lean](../Proofs/QMClosure/SharpPhaseTomography.lean)
[CnotPhaseDefectTransfer.lean](../Proofs/QMClosure/CnotPhaseDefectTransfer.lean)

## Proposed strongest endpoint

The analytic argument gives `dimℝ(V)=4` and `dimℝ(ker u)=3`. It derives a
center `c`, an inner product on `ker u` and a radius `r>0` such that

```text
closure(S) = c + closedBall(0,r)
```

in the normalized affine hyperplane. Exact equality between `S` and this
ball additionally requires closedness of `S` or an explicit preparation
completion convention. The derived metric determines the radius convention.
Mathematical limits of finite gate words concern state closure. Physical access
to limiting transformations requires a separate process-resource assumption.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Rank and center argument

Because `S` spans `V` and each destructive image lies in the span of two fixed
output preparations, `rank(E_i)≤2`. Set `Q_i=E_i−R`. The multiplication table
gives mutually annihilating idempotents `R,Q_x,Q_y,Q_z` whose sum is identity.
Their images therefore decompose `V` as a direct sum. In particular, `V` is
finite-dimensional and

```text
dim(V) = Σ_i rank(E_i) − 2 rank(R) ≤ 4.
```

For each `i`, preservation of normalized preparations and their spanning imply
`uE_i=u`. The common-product identity gives `uR=u`, so `rank(R)≥1`.

The two distinct normalized T-fixed endpoints are linearly independent fixed
vectors. A nonidentity real operator with `T³=I` has a nonzero two-dimensional
component for the factor `t²+t+1`. Consequently `dim(V)≥4`. Equality in the
upper bound forces `rank(R)=1`, `rank(E_i)=2` and `rank(Q_i)=1` for every axis.

Rank one and `uR=u` make `R(s)` independent of `s∈S`. This defines the center
`c`, which is available since `R=E_iE_j` for distinct axes and the destructive
maps are actual preparation maps. The image `E_i(S)` spans `im(E_i)` and its
affine line is the designated endpoint line. The available endpoints therefore
belong to that image subspace and are fixed by `E_i`.

These steps require new rank and finite-order representation lemmas. The
existing algebraic projector theorem supplies its own conditional operator
identity, while the binary-range and named-pole dimension bridges remain
formalization obligations.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Bounded envelope and derived metric

Projector totality writes every preparation as
`s=E_x(s)+E_y(s)+E_z(s)−2c`. The three fixed output segments thus bound `S`.
Its closed convex hull `K` is a compact full-dimensional body in `u=1`.
This hull is a mathematical envelope. Physical availability of arbitrary
preparation mixtures remains an independent issue.

Affine automorphisms of `K` preserve its centroid and covariance metric.
The phase symmetries identify the centroid with `c` and make the three
one-dimensional `Q_i` axes orthogonal in that derived metric. Opposite phases
reflect each endpoint line about `c`. Availability of the endpoints and the
segment range bounds force each pointer pair to be antipodal. The supplied
reversible gates consequently fix `c` and preserve the metric.

Formalization must construct the centroid and positive covariance form, justify
their invariance under the actual affine automorphisms, and prove the endpoint
and orthogonality steps under the stated preparation assumptions.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Two finite rotations and their mathematical closure

On `ker u`, `T` becomes an orthogonal nonidentity order-three transformation
fixing the z axis. It is a rotation by either `120°` or `−120°`.
The conjugate `XTX⁻¹` rotates about the orthogonal x axis. The product of these
two rotations has cosine `−7/8` and trace `−3/4`, independently of their two
orientation signs. Finite-order matrix traces are algebraic integers. This
rational noninteger trace therefore gives an infinite-order product.

Let `Γ` be the subgroup generated by the two rotations. Its closure in
`SO(3)` is infinite. A proper infinite closed subgroup of `SO(3)` preserves
a common unoriented axis, and its order-three elements rotate about that
axis. The orthogonal axes of the two generators exclude that case. The
mathematical subgroup closure is consequently `SO(3)`.

The rotation product calculation, algebraic-integer argument, proper-closed-
subgroup axis theorem and density conclusion each require machine-checkable
artifacts before this selector can acquire a kernel-theorem status. The
finite phase representation supplies a classical realization of its own finite
algebra, with additional selector gates requiring independent assumptions.
[Classical finite phase boundary](231-classical-finite-phase-boundary.md)

## Filling the preparation closure

Rotation invariance makes `K` a ball. The destructive maps become orthogonal
projections onto pointer diameters through `E_i=(I+J_i)/2`. Their segment range
bounds and available endpoints fix the ball radius at the pointer norm. Pointer
purity emerges within this geometric argument.

Write `C=closure(S)` without a convexity premise on `S`. Invariance under
actual finite gate words extends to the mathematical rotation closure, so `C`
contains the full pointer sphere. Continuity of the actual map `E_z` gives
`E_z(C)⊆C`. Projecting the sphere supplies the whole z diameter. Rotation of
that diameter supplies the whole ball. Since `C⊆K`, the endpoint is `C=K`.

Actual destructive-map availability is used in this last diameter step. A
contract supplying only abstract algebraic maps retains the convex-envelope
endpoint unless a separate preparation-mixing premise fills the interior.
The closure transfer and the actual-map distinction remain explicit
formalization obligations.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Derived binary coefficient

In normalized pointer coordinates the displacement of `T(p_x⁺)` is
`(−1/2, ±√3/2, 0)`. Its y-plus coefficient in the actual binary output segment
is `(2±√3)/4`. The numerical coefficients and the pair of orientation choices
are conclusions of the analytic geometry under the supplied gate contract.
Event actualization and selection of one physical orientation remain separate
questions.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Exact preparation and forward-only controls

Exact preparation availability can remain smaller than its closure. In a ball
model, start with finitely many pointers and close them under finite words in
the actual destructive maps and reversible gates, including the inverse words.
The resulting preparation set is countable. The proposed density and
projection argument gives ball closure, while the ball has uncountably many
points. Taking the convex hull of a countable pointer orbit gives another
control with only countably many orbit points on the boundary sphere. These
controls await Lean artifacts.

Two-sided operational preservation by `X` has a concrete analytic control.
Use normalized affine coordinates and the hexagonal prism

```text
|x| ≤ 1,
|x+√3y| ≤ 2,   |x−√3y| ≤ 2,
|z| ≤ 1.
```

Coordinate destructive projections, the common center and coordinate half-turn
phases preserve this preparation set. The pointer radii are one on x and z
and `2/√3` on y. A `120°` z rotation has order three and fixes the named
z endpoints. The invertible map

```text
X(x,y,z) = (z,y/4,x/4)
```

preserves the prism forward and sends z endpoints to x endpoints. Indeed,
`|y|≤2/√3` bounds each transformed slanted expression by `3/2`, and the other
two coordinate bounds also hold. Its inverse sends the available point
`(0,0,1)` to `(4,0,0)`, violating the prism's x bound. This prism satisfies the
forward-only version of the contract and retains its polygonal geometry.
The ledger records it as `analyticAwaitingFormalization/notYetKernelChecked`
with empty checked evidence.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

The classical four-point simplex and the stabilizer octahedron have no
nonidentity order-three automorphism fixing a designated opposite pointer
pair. In the octahedral case the remaining four vertices form a square, whose
stabilizer has no three-torsion. The named-pole requirement therefore matters
even when an example has other order-three symmetries. This observation is
part of the pending analytic control agenda.

## Independent origins and continuing scope

The real-linear normalized preparation semantics, actual binary destructive
maps, actual phases, projector-totality route, pole-fixing `T` and two-sided
axis exchange `X` remain supplied. Independent operational origins for `T`
and `X` join the previous phase and reference-origin tasks. Finite phase and
CNOT identities provide their checked algebraic scope, with the additional
geometric selector requiring its full explicit contract.

The proposed result concerns local preparation closure under a derived real
metric. Composite geometry, complex orientation, event actualization,
physical scales and completed QM reconstruction remain open. Historical
sections 225–230 retain their recorded contracts.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
