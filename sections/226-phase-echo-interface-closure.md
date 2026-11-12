# Phase-echo interface closure

Three further Lean modules close finite orientation, operator phase-defect and
complex spectral interfaces in the conditional reconstruction route. The earlier
checkpoint retains its historical scope. The operational research ledger records
the new kernels and the continuing origin obligations.
[Earlier checkpoint](225-sharp-phase-echo-reconstruction.md)
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

| Interface | Checked result | Supplied contract and remaining work |
| --- | --- | --- |
| Finite orientation completion | The prior two circuit test families plus the triangle select `ordinary` or `ordinaryZ` among sixteen tables. Both mirror triangles are generated and have a specified readout `-1/2`. | The finite tables, circuits and grammar are supplied. Global generated-state positivity and arbitrary GPT XOR classification remain open. |
| Operator CNOT defect transfer | Explicit finite commutations and homomorphism laws derive equal defects, and the supplied reference laws then force `p = I`. | Operational conjugation, complete destructive construction and natural extension remain supplied. Rank and dimension selection require further arguments. |
| Complex spectral boundary | Field and complex matrix identities, complex modulus bounds and complementary-operator scalar bounds. The finite-dimensional nontrivial complex corollary derives eigenvector existence. | Fixed uniform all-power norm bounds remain supplied. Invariant-fibre bounds, real-complexification, quotient norm transfer and full atomicity remain open. |

The three kernel entries carry `parentAccepted` after kernel compilation,
independent source review and a transitive dependency audit. The continuation task remains an open
physical bridge. Compilation of ledger metadata checks its structure, while the
cited theorem declarations carry the mathematical proof authority.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Both finite mirror orientations

`IDT.QMClosure.PauliOrientationCompletion.tested_positive_and_triangle_positive_iff`
combines the two supplied two-wire circuit test families with the four binary
product events on the specified three-wire triangle. Among the sixteen signed
tables, those finite tests hold exactly for `ordinary` or `ordinaryZ`.
[PauliOrientationCompletion.lean](../Proofs/QMClosure/PauliOrientationCompletion.lean)

The parameterized `triangle` uses one fixed table throughout the supplied local
gate sequence. `triangle_generated` proves reachability in that table's grammar.
`mirror_triangle_negative` and `mirrorZ_triangle_negative` both give the specified
product readout `-1/2`. Thus each mirror violates nonnegativity on its generated
triangle. `tested_and_generated_nonnegativity_forces_ordinary` gives the necessary
ordinary orientation when the prior tests and all-generated specified-event
nonnegativity are imposed.
[PauliOrientationCompletion.lean](../Proofs/QMClosure/PauliOrientationCompletion.lean)

The finite equivalence establishes sufficiency for its stated tests. Positivity
for all generated states of a surviving table requires further proof. Deriving
the table family from arbitrary GPT XOR operations also remains an external
interface. [PauliOrientationCompletion.lean](../Proofs/QMClosure/PauliOrientationCompletion.lean)

## Noncommutative operator phase transfer

`IDT.QMClosure.CnotPhaseDefectTransfer.cnot_defect_cancellation` works in a monoid,
so it applies to a noncommutative operator ring. Six stated commutations suffice
for the finite rearrangement. For two supplied destructive tables,
`destructive_defects_equal` obtains the local involutions and commutations from
`SharpPhaseTomography.complete_phase_package`. Four cross-phase commutations
remain explicit, together with three equations for a supplied monoid
homomorphism `φ`.
[CnotPhaseDefectTransfer.lean](../Proofs/QMClosure/CnotPhaseDefectTransfer.lean)

```text
φ(xOld) = xOld xFresh
φ(zFresh) = zOld zFresh
φ(xOld zFresh) = yOld yFresh
```

The calculation gives `KOld KFresh = I`. Local involutions and commutations give
`KFresh² = I`, hence `KOld = KFresh`.
`cnot_fresh_reference_projector_total` uses this derived equality with the supplied
append/discard retraction, fresh fixation, old-action intertwining and local
formula `localDefect = 2p-I`, concluding `p = I`.
[CnotPhaseDefectTransfer.lean](../Proofs/QMClosure/CnotPhaseDefectTransfer.lean)

Realizing `φ` as an actual operational conjugation, constructing complete
destructive maps and deriving the reference-extension laws remain research
obligations. Rank and dimension arguments also remain outside this interface.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Complex spectral and norm interfaces

`IDT.QMClosure.ComplexAtomicitySpectralBoundary.three_boost_weights` and
`matrix_three_boost_weights` provide the three-weight exclusion over a supplied
field. `complex_matrix_reciprocal_boost_weights` gives the reciprocal matrix
identity over `ℂ`. `complex_triangle_bound` handles complex spectral parameters
using their moduli.
[ComplexAtomicitySpectralBoundary.lean](../Proofs/QMClosure/ComplexAtomicitySpectralBoundary.lean)

`eigenvalue_norm_le_of_power_bound` takes an actual nonzero complex eigenvector
and a fixed operator-power envelope `‖Tⁿ‖ ≤ C qⁿ` for every natural `n`, with
`q > 0`. It derives `‖z‖ ≤ q` for the corresponding eigenvalue. The general normed
space theorem `complementary_operator_scalar_bound` applies this to complementary
operators `A+B=cI`, allowing separate constants for their two envelopes, and
concludes `c ≤ 2q`.
[ComplexAtomicitySpectralBoundary.lean](../Proofs/QMClosure/ComplexAtomicitySpectralBoundary.lean)

`finite_dimensional_complementary_operator_scalar_bound` assumes a
finite-dimensional nontrivial complex normed space, `A+B=cI`, positive `q`, and
both fixed all-power envelopes. Algebraic closedness supplies an eigenvalue and
a nonzero eigenvector inside the proof, yielding `c ≤ 2q`. The earlier general
normed-space theorem retains its explicit eigenvector premise.
[ComplexAtomicitySpectralBoundary.lean](../Proofs/QMClosure/ComplexAtomicitySpectralBoundary.lean)

These signatures close the earlier coefficient-field and complex-modulus gaps.
They require actual operator norm bounds in the chosen space. Real-complexification,
norm transfer to quotient representations, the graph-preserver Lie group,
real-kernel/Levi and Zariski arguments, weight classification and full atomicity
retain separate proof obligations.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

## Next interfaces

The next formalization agenda is to establish inheritance of fixed uniform power
envelopes under invariant subspaces and quotients, including the required
complexification and quotient norm statements. The geometric route must then
derive the original uniform bounds from pure-marginal fibres. This is a
remaining connection between the spectral kernels and their intended atomicity
application. [Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)

Operational phase construction, complete destructive-process extension,
rank/dimension selection, pair-cone reconstruction and ancilla equality remain
active. The new kernels leave independent primitive origin, full atomicity,
completed QM reconstruction, Born origin and physical-scale origins open.
[Operational research ledger](../Proofs/MetaLang/V8OperationalPrimitiveResearchLedger.lean)
