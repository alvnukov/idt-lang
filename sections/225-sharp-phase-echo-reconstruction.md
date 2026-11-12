# Sharp-phase echo reconstruction checkpoint

This checkpoint contains five Lean-checked kernel clusters. Their theorems expose
the structural, cone, effect, phase and extension assumptions they use. The
primitive-origin research goal remains active, with the analytic and physical
bridges recorded in the operational research ledger. Its task stages describe
research metadata, and its evidence records point to the actual theorem sources.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Checked scope

| Kernel cluster | Checked conclusion | Remaining premises and formalization work |
| --- | --- | --- |
| Sharp-phase echo | Identity-channel extremality and original-branch `AB = BA = s² I` on the supplied cone/base and visible/hidden split. | Operational origin of the split, canonical local branches, positive phase and cone/effect contract. |
| Finite record phase/projector | Operator phase identities, separate commutative-group defect cancellation, and projector totality under explicit fresh-reference laws. | Operational destructive-process construction, phase origin, extension laws, rank and dimension arguments. |
| Finite XOR orientation | Four surviving choices among sixteen supplied signed tables, plus a generated canonical mirror circuit with readout `-1/2`. | Derivation of general GPT XOR maps, `mirrorZ` gauge/elimination, and general pair-cone classification. |
| Atomicity spectral boundary | Scalar/matrix three-weight and two-weight results, exact calibration, power-envelope exclusion and a real quotient bound. | Graph-preserver Lie group, real-kernel/Levi dichotomy, Zariski reductivity, weight classification and atomicity. |
| Central-inversion witness | A normalized product input positive on all unit local directions, valid selected directions, and a negative readout of the supplied output table. | The geometric and operational bridges producing that table, including the dimension-three twirl argument. |

The five checked kernel entries carry the review state `parentAccepted` after
independent source review and kernel checks. The analytic and physical-origin
tasks retain their unformalized and open stages in the ledger.

## Identity extremality and original-branch echo

`IDT.QMClosure.identity_channel_extreme` takes a compact convex normalized state
base spanning a finite-dimensional real normed vector space. Two linear maps
preserve the base and have identity as their average. Extreme-point fixedness,
Krein–Milman and the closed fixed-point kernel give equality of both maps with
identity. The extreme-point spanning step is proved from the compact convex
contract. [IdentityChannelExtremality.lean](../Proofs/QMClosure/IdentityChannelExtremality.lean)

The echo proof distinguishes the visible transverse sector `T` from the
product-invisible sector `H`, with `T + H` equal to the complement of the two
pointer projections. Local canonicality supplies `AT = TA = sT` and
`BT = TB = sT`. The phase commutes with `T` and acts as negative identity on `H`.
The hidden unread comparison supplies `AH + BH = 2sH`.
[SharpPhaseEchoTransfer.lean](../Proofs/QMClosure/SharpPhaseEchoTransfer.lean)

`IDT.QMClosure.EchoPointerSplit.phase_average_visible_hidden` derives the
canonical averages

```text
C = (A + JBJ)/2 = pP + qQ + s(T+H)
D = (B + JAJ)/2 = qP + pQ + s(T+H)
pq = s², s > 0
```

Orthogonal pointer projections give `CD = DC = s² I`. Positive `A`, `B` and `J`
make the averages positive on the supplied cone. Nonnegative scaling and
composition then make the computed residual maps `N = s⁻² DA` and `M = s⁻² CB`
positive. The exact effect identity `uP + uQ = u` and pointer equations give
`uN = uM = u`. Thus both residual maps preserve the normalized base. Their
average is identity, and identity extremality removes the residual noise.
[SharpPhaseEchoTransfer.lean](../Proofs/QMClosure/SharpPhaseEchoTransfer.lean)

`IDT.QMClosure.sharp_phase_echo_transfer_with_involution` combines these steps and
derives the echo for the original `A` and `B`. Its premises include the explicit
cone, effect, phase, pointer, local-canonicality and hidden-comparison contract.
Residual positivity and normalized-base preservation are derived inside the
theorem. The separately named `negative_complement_phase_average` records an
algebraic control with a whole-complement negative phase assumption.
[SharpPhaseEchoTransfer.lean](../Proofs/QMClosure/SharpPhaseEchoTransfer.lean)

## Finite phase and fresh-reference identities

`IDT.QMClosure.SharpPhaseTomography.complete_phase_package` proves involutions,
pairwise commutation, a three-phase product formula and projector idempotence
from the supplied destructive operator algebra. The separate theorem
`cnot_defect_cancellation` works in a commutative group with an explicitly
supplied homomorphism and phase identities.
[SharpPhaseTomography.lean](../Proofs/QMClosure/SharpPhaseTomography.lean)

`fresh_reference_projector_total` requires append/discard retraction, equality of
old and fresh defects, a fixed fresh reference, old-action intertwining and the
local defect formula. It then forces the projector to be identity. The operator
package and group package retain their own contracts. The module supplies no
formal rank, dimension or operational phase-origin argument.
[SharpPhaseTomography.lean](../Proofs/QMClosure/SharpPhaseTomography.lean)

## Explicit negative witnesses

`IDT.QMClosure.PauliOrientationObstruction.tested_positive_iff_four_choices`
classifies the stated tests across exactly sixteen signed tables. The two circuit
coefficient identities are `circuit_one_coefficients` and
`circuit_two_coefficients`. The four surviving tables are `ordinary`, `ordinaryZ`,
`mirror` and `mirrorZ`.
[PauliOrientationObstruction.lean](../Proofs/QMClosure/PauliOrientationObstruction.lean)

For the canonical `mirror` table, `mirror_triangle_generated` proves that the
specified three-wire circuit belongs to the generated grammar, and
`mirror_triangle_negative` gives its readout `-1/2`.
`generated_product_nonnegativity_impossible` exports the resulting obstruction.
`mirrorZ` remains an enumerated choice, with gauge equivalence and elimination
awaiting formalization. General GPT XOR maps and pair cones require further
arguments. [PauliOrientationObstruction.lean](../Proofs/QMClosure/PauliOrientationObstruction.lean)

`IDT.QMClosure.CentralInversionWitness.input_product_positive` establishes input
positivity for every pair of unit three-dimensional local effect directions.
`alpha_unit` and `beta_unit` validate the selected output directions. For the
supplied four-by-four table `visibleBranch κ`, `visible_branch_readout` gives
`(5 - 3√3)/64`, independently of `κ`, and `witness_value_negative` proves its
strict negativity. The conditional output theorem requires the actual output
table to equal `visibleBranch κ`.
[CentralInversionWitness.lean](../Proofs/QMClosure/CentralInversionWitness.lean)

The full central-inversion exclusion in local dimension three has an
independently reviewed informal argument through faces, rotation lifts, readout
geometry and twirling. Those geometric bridges remain unformalized. The checked
coefficient witness supplies the final readout calculation.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Analytic route and machine-visible agenda

The `optimal_unread_atomicity_origin` task assumes local balls of dimension
`d ≥ 2`, proper finite causal composition, separating effects with steering,
actual reversible `SO(d)` lifts, canonical local branches at `p=3/4`, `q=1/4`, and
complete unread comparison. Its direct pure-marginal-factorization route uses a
graph-preserver Lie group, a real-kernel/Levi dichotomy, Zariski reductivity and
weight classification. These named analytic bridges remain unformalized. The
dimension-three argument has independent expert review. Generalized dimension
has one expert review and retains its own scope.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

`IDT.QMClosure.AtomicitySpectralBoundary` provides `three_boost_weights`,
`matrix_three_boost_weights`, `reciprocal_boost_weights`,
`matrix_reciprocal_boost_weights`, `spinor_calibration`,
`power_envelope_impossible` and `trivial_quotient_scalar_bound`. Their exact
equations and scalar bounds support the analytic route. A representation-theory
bridge and the atomicity theorem remain on the formalization agenda.
[AtomicitySpectralBoundary.lean](../Proofs/QMClosure/AtomicitySpectralBoundary.lean)

These scalar and matrix kernels are over `ℝ`. The informal quotient argument
uses complex irreducible quotients and potentially complex eigenvalues. A checked
realification or complex-norm specialization remains an open bridge.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

The `controlled_phase_origin_route` starts with supplied all-reference atomicity
and a normalized `controlled(Id,N)` process. Its noncentral projector-construction
branch uses a pure fixed target program obtained after the noncentral reduction
to seek the complete projector `E=(I+J)/2`. That reduction requires compact-group
closure and explicit treatment of dimension four. The central `N=-I`
dimension-three exclusion has no pure fixed target program premise. The central
case in general dimension remains open.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

The `bounded_pair_cone_reconstruction_route` requires local dimension `d ≥ 3`,
canonical complete filters, rich `SO(d)` controls, exact pointer XOR and an
exhaustive primitive grammar. The dimension bound supports metric irreducibility
and complex selection. Deriving it from a nontrivial pole-fixing order-three local
state action remains an operational bridge. The real rank-four rebit
countercontrol satisfies the other listed premises, and its exclusion uses this
dimension bound. The long bridges include canonical boosts, tangent transitivity, a self-dual metric
with Laplace arguments, and the Koecher–Vinberg mathematical input. The proposed
fixed pair result is a rank-four complex homogeneous self-dual cone. Ancilla
equality requires a separate `S_N` induction, generated adjoints and dual
saturation. All these reconstruction bridges remain unformalized. The grammar
supplies no arbitrary free joint ancilla or additional unverified two-body
instrument. [Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

The `complete_unread_countermodel_boundary` records manual spinor-parity and
integer-spin analyses. The spinor-parity minimal cone has atomicity and complete
unread/local echo while failing complete echo. The integer-spin variant realizes
actual `SO(3)`. Both lack XOR, with the relevant face dimensions four and two, and
therefore leave the full core contract untested. The analyzed full-PSD gauge,
spectral-cap and equal-gauge-trace XOR extensions fail optimal-unread positivity.
These manual findings await checked artifacts.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

`primitive_phase_echo_origin_continuation` keeps the overarching goal active.
Independent origins of local regularity, optimal unread comparison, reversible
controls, complete process comparisons and exhaustive generation remain open.
The `T_x` cyclic simple-quotient/composition-factor issue also remains unresolved.
Its proposed nilpotent repair has not been accepted, and CNOT closure is
unproved. Next formal steps include atomicity Lie bridges, controlled-phase
construction, central dimension-three twirling, full pair-cone reconstruction
and ancilla orientation. This checkpoint supplies no completed derivation of QM,
Born actualization, Hilbert origin or physical scales.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
