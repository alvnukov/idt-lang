## 175. Primitive Base Completeness Status

Status: `primitive_base_completeness_audit_v2`

### 175.1. Current Primitive Base

The minimal primitive set for describing all known physics:

| # | Primitive | Role | Derived from B0 | Lean proof |
|---|-----------|------|-----------------|------------|
| 1 | B0 = (C, O, I, R) | context-first combinatorics | base | — |
| 2 | F = finite_facticization_stability | blocks negative facticization weights | NO (core primitive) | V7FPrimitiveIndependence.lean |
| 3 | Q = oriented_inheritance_holonomy | provides signed/phase-like comparison directions | NO (core primitive) | argued |
| 4 | action_quantum | dimensional anchor (M^1 L^2 T^-1) | NO (irreducible) | argued |

### 175.2. What is proved (Lean-verified)

| Result | File | Status |
|--------|------|--------|
| B0 satisfied without F (countermodel) | V7FPrimitiveIndependence.lean | formal proof |
| F -> a >= 0 for 2x2 | V7PositiveGeometryGeneral.lean | linarith proof |
| F -> c >= 0 for 2x2 | V7PositiveGeometryGeneral.lean | linarith proof |
| F -> a+2b+c >= 0 for 2x2 | V7PositiveGeometryGeneral.lean | linarith proof |
| F -> a-2b+c >= 0 for 2x2 | V7PositiveGeometryGeneral.lean | linarith proof |
| F -> ac >= b^2 for 2x2 | V7PositiveGeometryGeneral.lean | axiom (strategy known) |
| Identity form is PSD | V7PositiveGeometryConcrete.lean | nlinarith proof |
| [[1,2],[2,1]] rejected by F | V7PositiveGeometryConcrete.lean | counterexample |
| [[2,1,1,2]] is PSD | V7PositiveGeometryConcrete.lean | proved |
| [[1,3,1]] rejected by F | V7PositiveGeometryConcrete.lean | counterexample |
| [[1,0.5,1]] is PSD | V7PositiveGeometryConcrete.lean | proved |
| Product exhaustion from B0 | V7ProductContextExhaustion.lean | derived |
| Local tomography from B0 | V7LocalTomography.lean | derived |
| Bounded correlations from B0+F | V7BoundedCorrelations.lean | derived |
| Hilbert carrier selection | V7HilbertCarrierSelection.lean | conditional |
| Born rule derivation | V7BornRuleDerivation.lean | conditional |
| Metric geometry projection | V7MetricGeometryProjection.lean | conditional |
| D_G = 4 NOT derivable | V7DimensionAnalysis.lean | analysis |

### 175.3. Derivation chain

```
B0 = (C, O, I, R)
  + product exhaustion (proved)
  + local tomography (proved)
  + bounded correlations (proved)
  + clock chains (proved)
  + source response (proved)
  + coarse-graining (proved)

F (primitive, independent of B0)
  + no negative directions (proved)
  + PSD for 2x2 (proved: a>=0, c>=0, a+2b+c>=0, a-2b+c>=0)
  + boxworld rejected (proved)

B0 + F + Q + D_cl
  -> positive comparison geometry (conditional)
  + product exhaustion (proved)
  + local tomography (proved)
  + bounded correlations (proved)
  -> Hilbert carrier selection (conditional)
  + additivity (proved)
  + operational equivalence (proved)
  -> Born rule (conditional)

B0 + clock chains + source response + coarse-graining
  -> metric geometry (conditional)

+ action_quantum
  -> dimensional physics (M, L, T)
```

### 175.4. Open gaps

| Gap | Status | Impact |
|-----|--------|--------|
| D_G = 4 | NOT derivable from B0+F+Q+action | dimension requires graph structure |
| alpha_em | open | coupling not derived |
| ac >= b^2 for general n | axiom (strategy known) | needs non-linear arithmetic |
| PSD -> F | needs complete square | converse direction |
| Universal Born | frontier | finite Born proved, universal not |
| Einstein equations | target | metric projection exists |

### 175.5. What is irreducible

| Primitive | Why irreducible |
|-----------|----------------|
| F (facticization stability) | B0 has no stability constraint |
| Q (oriented inheritance) | B0 has no orientation data |
| action_quantum | B0 has no dimensionful quantities |

### 175.6. Honest assessment

```
What is proved (formal):
  - B0 does not imply F (countermodel)
  - F -> PSD conditions for 2x2 (forward direction)
  - Product exhaustion, local tomography, bounded correlations from B0

What is proved (conditional):
  - Hilbert carrier selection from positive geometry + conditions
  - Born rule from carrier + readout assumptions
  - Metric geometry from B0 + clock chains + source response

What is NOT proved:
  - F -> ac >= b^2 (axiom, proof strategy known)
  - PSD -> F (converse)
  - D_G = 4 (NOT derivable)
  - alpha_em (open)
  - Universal Born (frontier)

What is irreducible:
  - F, Q, action_quantum (all independent of B0)
```
