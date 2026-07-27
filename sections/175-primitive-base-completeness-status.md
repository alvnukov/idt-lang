## 175. Primitive Base Completeness Status

Status: `primitive_base_completeness_audit_v3_corrected`

Provenance of this revision: `INVENTORY_AUDIT.md` (2026-07-27), a mechanical
inventory of all 127 `Proofs/**/*.lean` artifacts. Statuses below were brought
into agreement with the actual content of the cited files. Eight rows were
lowered, one was raised.

Method boundary: the audit read sources and `.lake/build` timestamps. It did not
run `lake build`. Compile status below is inferred from `.olean` presence and
mtime, not from a compiler run.

### 175.1. Current Primitive Base

Candidate primitive set. Not established as minimal, not established as
complete.

| # | Primitive | Role | Derived from B0 | Lean status |
|---|-----------|------|-----------------|-------------|
| 1 | B0 = (C, O, I, R) | context-first combinatorics | base | — |
| 2 | F = finite_facticization_stability | blocks negative facticization weights | claimed NO | `not_proved_wrong_statement` |
| 3 | Q = oriented_inheritance_holonomy | provides signed/phase-like comparison directions | claimed NO | `argued_only` (no theorem in file) |
| 4 | action_quantum | dimensional anchor (M^1 L^2 T^-1) | claimed NO | `argued_only` (no theorem in file) |

Open inconsistency, not resolved by this revision: the base is written here as
`B0 = (C, O, I, R)`, but `01-primitives.md` and
`Proofs/MetaLang/V8ContextFirstPrimitiveBase.lean` both use
`B0 = (C, O, I, R, D)`, and `174.47` uses `B1' = (C, O, I, R, D_cl, F, Q)`.
`V7PrimitiveCandidateStack.lean` additionally marks `L` (loss accounting) as a
core primitive; `L` does not appear in this section at all. Four statements of
the base are live in the repository simultaneously. Reconciling them is a
theory decision and is deferred.

### 175.2. Lean artifact status

| Result | File | Status |
|--------|------|--------|
| B0 satisfied without F (countermodel) | V7FPrimitiveIndependence.lean | `not_proved_wrong_statement` |
| F -> a >= 0 for 2x2 | V7PositiveGeometryGeneral.lean | `formal_proof` (linarith) |
| F -> c >= 0 for 2x2 | V7PositiveGeometryGeneral.lean | `formal_proof` (linarith) |
| F -> a+2b+c >= 0 for 2x2 | V7PositiveGeometryGeneral.lean | `formal_proof` (linarith) |
| F -> a-2b+c >= 0 for 2x2 | V7PositiveGeometryGeneral.lean | `formal_proof` (linarith) |
| F -> ac >= b^2 for 2x2 | V7PositiveGeometryGeneral.lean | `formal_proof` (case split + nlinarith) — **raised**, no axiom present |
| Identity form is PSD | V7PositiveGeometryConcrete.lean | `formal_proof` |
| [[1,2],[2,1]] rejected by F | V7PositiveGeometryConcrete.lean | `formal_proof` (counterexample) |
| [[2,1,1,2]] is PSD | V7PositiveGeometryConcrete.lean | `formal_proof` |
| [[1,3,1]] rejected by F | V7PositiveGeometryConcrete.lean | `formal_proof` (counterexample) |
| [[1,0.5,1]] is PSD | V7PositiveGeometryConcrete.lean | `formal_proof` |
| Product exhaustion from B0 | V7ProductContextExhaustion.lean | `not_proved_empty_artifact` |
| Local tomography from B0 | V7LocalTomography.lean | `not_proved_empty_artifact`, never compiled |
| Bounded correlations from B0+F | V7BoundedCorrelations.lean | `not_proved_empty_artifact`, never compiled |
| Hilbert carrier selection | V7HilbertCarrierSelection.lean | `not_proved_empty_artifact` + axiom |
| Born rule derivation | V7BornRuleDerivation.lean | `not_proved_empty_artifact` + axiom |
| Metric geometry projection | V7MetricGeometryProjection.lean | `not_proved_empty_artifact` |
| D_G = 4 NOT derivable | V7DimensionAnalysis.lean | `not_proved_empty_artifact` |

Meaning of the lowered statuses:

- `not_proved_empty_artifact`: every theorem in the file has the form
  `True := trivial` or `<hypotheses> -> True`. Nothing is asserted, so nothing
  is proved. Example, from `V7BoundedCorrelations.lean`:

  ```lean
  axiom facticizationStability : True
  theorem noSignalling  : True := trivial
  theorem tsirelsonLike : True := trivial
  ```

- `not_proved_wrong_statement`: the file compiles and proves a theorem, but not
  the one claimed. In `V7FPrimitiveIndependence.lean` the B0 model is degenerate
  (`D := True`; `C`, `O`, `I` do not appear) and `F` is encoded as
  `∀ c1 c2 a, R c2 a → R c1 a`, i.e. "all contexts agree on facticizability".
  That is a denial of contextuality — a proposition the theory is committed to
  rejecting — so its independence from B0 carries no weight for F.

### 175.3. Separately proved measure results

These are real machine-checked results, but they are not derivations of the
listed structure. They are theorems about an assumed structure.

| Result | File | Status |
|--------|------|--------|
| additivity over disjoint sets with vanishing cross term | ExclusivityAdditivityProof.lean | `formal_proof` |
| three-set coarse-graining consistency | CoarseGrainingConsistencyProof.lean | `formal_proof` |
| invariance under W/Γ-preserving bijection | OperationalEquivalenceProbabilityProof.lean | `formal_proof` |
| PSD kernel implies nonnegative measure | ContextNormalizationProof.lean | `formal_proof` |

Import boundary that must be declared: all four assume

```lean
variable (W : H → ℂ)
variable (Γ : H → H → ℂ)
def actualizationMeasure (A : Finset H) : ℂ :=
  ∑ h ∈ A, ∑ h' ∈ A, W h * star (W h') * Γ h h'
```

This is a sesquilinear form on a complex space with Hermitian kernel. Per
`01-primitives.md`, `W : H → ℂ` is classified as `QM carrier import / readout
scaffold`. The file headers nevertheless declare
`Forbidden imports: born_rule, kolmogorov_axioms_assumed, hilbert_space`.
The headers are inconsistent with the signatures and must be corrected.

### 175.4. Derivation chain

```
B0 = (C, O, I, R)
  + product exhaustion        (NOT PROVED - empty artifact)
  + local tomography          (NOT PROVED - empty artifact)
  + bounded correlations      (NOT PROVED - empty artifact)
  + clock chains              (NOT PROVED - empty artifact)
  + source response           (NOT PROVED - empty artifact)
  + coarse-graining           (NOT PROVED - empty artifact)

F (independence from B0 NOT established)
  + no negative directions    (NOT PROVED)
  + PSD for 2x2               (PROVED, full characterization incl. ac >= b^2)
  + boxworld rejected         (NOT PROVED - empty artifact)

B0 + F + Q + D_cl
  -> positive comparison geometry   (NOT PROVED)
  -> Hilbert carrier selection      (NOT PROVED - empty artifact + axiom)
  + additivity                      (PROVED, assumes W : H -> C)
  + operational equivalence         (PROVED, assumes W : H -> C)
  -> Born rule                      (NOT PROVED - empty artifact + axiom)

B0 + clock chains + source response + coarse-graining
  -> metric geometry                (NOT PROVED - empty artifact)

+ action_quantum
  -> dimensional physics (M, L, T)  (calibration, carries no information
                                     about the world; see 145-147)
```

### 175.5. Open gaps

| Gap | Status | Impact |
|-----|--------|--------|
| D_G = 4 | open; non-derivability asserted but NOT proved | the cited file is an empty artifact |
| alpha_em | open | coupling not derived |
| ac >= b^2 for 2x2 | closed | proved in V7PositiveGeometryGeneral.lean |
| ac >= b^2 for general n | open | needs non-linear arithmetic at general rank |
| PSD -> F | open | converse direction |
| Universal Born | open | finite Born also NOT proved; earlier "finite Born proved" was based on an empty artifact |
| Tsirelson value 2*sqrt(2) | open | boundedness itself is not proved; see 175.2 |
| Einstein equations | open | metric projection is an empty artifact |
| Compile status | open | 15 files never compiled, 27 stale; `lake build` not run |

### 175.6. What is irreducible

Nothing is established as irreducible.

| Primitive | Claimed reason | Actual status |
|-----------|----------------|---------------|
| F (facticization stability) | B0 has no stability constraint | independence not proved; cited countermodel targets a different proposition |
| Q (oriented inheritance) | B0 has no orientation data | no theorem exists; file contains prose only |
| action_quantum | B0 has no dimensionful quantities | no theorem exists; and per 145-147 this is a calibration choice, not a fact about the world |

The general obstruction: the repository has no formal notion of reduction or
interpretation between primitive bases. Without it, "irreducible" and "lowest"
are not statable claims. `lowerBaseDerivesB1` and its neighbours in
`FullQMSectorClosure.lean` and `V8StoppedResearchFrontier.lean` are `Prop`
placeholder fields, not definitions.

### 175.7. Honest assessment

```
What is proved (formal, machine-checked):
  - full PSD characterization of a real 2x2 comparison form,
    including ac >= b^2
  - additivity, coarse-graining consistency, operational-equivalence
    invariance, and nonnegativity for the actualization measure
    -- all four assuming W : H -> C and Hermitian Gamma

What is NOT proved:
  - independence of F, Q, or action_quantum from B0
  - product exhaustion, local tomography, bounded correlations
  - no-signalling, Tsirelson boundedness, boxworld rejection
  - Hilbert carrier selection
  - Born rule, finite or universal
  - metric geometry projection
  - non-derivability of D_G = 4
  - alpha_em, or any other dimensionless constant

What is irreducible:
  - nothing established; the question is not yet statable

Total: 447 lines of genuine mathematics out of 25,028 (1.8%).
All of it is downstream of an assumed complex sesquilinear structure.
The theory has produced zero dimensionless numbers.
```
