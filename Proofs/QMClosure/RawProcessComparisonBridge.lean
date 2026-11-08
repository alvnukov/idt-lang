import Proofs.QMClosure.RawLocalMidpointCompatibility
import Proofs.QMClosure.RawFourPointGramBridge

/-!
# Explicit additive process-comparison bridge

The two-port comparison is the sum of two supplied single-port comparisons.
The bridge assumes calibration under the quarter-turn and attenuation maps,
and nonexpansion of this particular comparison under the complete gate.
These assumptions are explicit mathematical inputs. Reversibility alone is
used only to strengthen an assumed nonexpansion law to an isometry law.
-/

namespace IDT.QMClosure.RawProcessComparisonBridge

noncomputable section

open RawMidpointGramGeometry RawLocalMidpointCompatibility

variable {V : Type*}

def pairComparison (D : V → V → ℝ) (p q : V × V) : ℝ :=
  D p.1 q.1 + D p.2 q.2

def PairComparisonNonexpanding (D : V → V → ℝ)
    (F : V × V → V × V) : Prop :=
  ∀ p q, pairComparison D (F p) (F q) ≤ pairComparison D p q

theorem pairComparison_swap (D : V → V → ℝ) (p q : V × V) :
    pairComparison D p.swap q.swap = pairComparison D p q := by
  simp only [pairComparison, Prod.fst_swap, Prod.snd_swap]
  exact add_comm _ _

/-- Order-four gate dynamics make an assumed global nonexpansion exact. -/
theorem pairComparison_isometry_of_nonexpanding
    (D : V → V → ℝ) (F : V × V → V × V)
    (hsquare : ∀ p, F (F p) = p.swap)
    (hgate : PairComparisonNonexpanding D F) (p q : V × V) :
    pairComparison D (F p) (F q) = pairComparison D p q := by
  apply le_antisymm (hgate p q)
  have hreverse := hgate (F p) (F q)
  rw [hsquare p, hsquare q, pairComparison_swap] at hreverse
  exact hreverse

/-- The existing four-point Gram route preserves the supplied additive
comparison under the actual complete operation. -/
theorem pairComparison_isometry_of_fourPointPositive
    (D : RawSparseConservationSelection.Contract V) (G : V → V → ℝ)
    (hk : RawFourPointGramBridge.LocalKernel D G)
    (hfour : RawGramGeometry.GramNonnegative G 4) (p q : V × V) :
    pairComparison (squaredDistance G) (D.operation p) (D.operation q) =
      pairComparison (squaredDistance G) p q := by
  let S (r s : V × V) : ℝ := G r.1 s.1 + G r.2 s.2
  have hright (x y z : V) :
      G x (RawSparseConservationSelection.m D y z) =
        G x (RawSparseConservationSelection.B D z) +
          G x (RawSparseConservationSelection.A D y) := by
    rw [hk.symmetric x _, RawFourPointGramBridge.G_m D G hk hfour]
    rw [hk.symmetric y _, RawFourPointGramBridge.B_adjoint D G hk x y,
      hk.symmetric z _, hk.adjoint x z]
    ring
  have htransfer (r s : V × V) :
      S (D.operation r) s = S r (D.operation s).swap := by
    rcases r with ⟨x, y⟩
    rcases s with ⟨z, w⟩
    simp only [S, RawSparseConservationSelection.operation_eq,
      Prod.fst_swap, Prod.snd_swap]
    rw [RawFourPointGramBridge.G_m D G hk hfour,
      RawFourPointGramBridge.G_m D G hk hfour, hright, hright]
    ring
  have hisometry (r s : V × V) : S (D.operation r) (D.operation s) = S r s := by
    rw [htransfer, D.square]
    rfl
  have hselfp := hisometry p p
  have hselfq := hisometry q q
  have hcross := hisometry p q
  dsimp [S] at hselfp hselfq hcross
  dsimp [pairComparison, squaredDistance]
  linarith

theorem pairComparisonNonexpanding_of_fourPointPositive
    (D : RawSparseConservationSelection.Contract V) (G : V → V → ℝ)
    (hk : RawFourPointGramBridge.LocalKernel D G)
    (hfour : RawGramGeometry.GramNonnegative G 4) :
    PairComparisonNonexpanding (squaredDistance G) D.operation := by
  intro p q
  exact le_of_eq (pairComparison_isometry_of_fourPointPositive D G hk hfour p q)

/-- The residual is retained before its nonnegativity is used. -/
theorem calibrated_midpoint_bound_with_residual
    (D : V → V → ℝ) (F : V × V → V × V)
    (J B : V → V) (zero : V) (mid : V → V → V)
    (hquarter : ∀ x y, D (J x) (J y) = D x y)
    (hhalf : ∀ x y, D (B x) (B y) = D x y / 2)
    (hreference : ∀ z, B (F (z, J z)).1 = z)
    (hzero : ∀ z, (F (z, J z)).2 = zero)
    (hmid : ∀ x y, B (F (x, J y)).1 = mid x y)
    (hgate : PairComparisonNonexpanding D F) (x y z : V) :
    2 * D (mid x y) z + D (F (x, J y)).2 zero ≤ D x z + D y z := by
  have hfirst := hhalf (F (x, J y)).1 (F (z, J z)).1
  rw [hmid x y, hreference z] at hfirst
  have h := hgate (x, J y) (z, J z)
  simp only [pairComparison, hquarter, hzero] at h
  linarith

theorem calibrated_midpoint_convex
    (D : V → V → ℝ) (hnonneg : ∀ x y, 0 ≤ D x y)
    (F : V × V → V × V) (J B : V → V) (zero : V)
    (mid : V → V → V)
    (hquarter : ∀ x y, D (J x) (J y) = D x y)
    (hhalf : ∀ x y, D (B x) (B y) = D x y / 2)
    (hreference : ∀ z, B (F (z, J z)).1 = z)
    (hzero : ∀ z, (F (z, J z)).2 = zero)
    (hmid : ∀ x y, B (F (x, J y)).1 = mid x y)
    (hgate : PairComparisonNonexpanding D F) (x y z : V) :
    D (mid x y) z ≤ (D x z + D y z) / 2 := by
  have h := calibrated_midpoint_bound_with_residual D F J B zero mid
    hquarter hhalf hreference hzero hmid hgate x y z
  linarith [hnonneg (F (x, J y)).2 zero]

/-- Symmetry supplies precisely the orientation used by squared Jensen. -/
theorem squaredMidpointConvex_of_calibrated_processComparison
    (G : V → V → ℝ) (hsym : ∀ x y, G x y = G y x)
    (hnonneg : NonnegativeSquaredDistances G)
    (F : V × V → V × V) (J B : V → V) (zero : V)
    (mid : V → V → V)
    (hquarter : ∀ x y, squaredDistance G (J x) (J y) = squaredDistance G x y)
    (hhalf : ∀ x y, squaredDistance G (B x) (B y) = squaredDistance G x y / 2)
    (hreference : ∀ z, B (F (z, J z)).1 = z)
    (hzero : ∀ z, (F (z, J z)).2 = zero)
    (hmid : ∀ x y, B (F (x, J y)).1 = mid x y)
    (hgate : PairComparisonNonexpanding (squaredDistance G) F) :
    SquaredMidpointConvex G mid := by
  have hdist (x y : V) : squaredDistance G x y = squaredDistance G y x := by
    unfold squaredDistance
    rw [hsym x y]
    ring
  intro z x y
  have h := calibrated_midpoint_convex (squaredDistance G) hnonneg F J B zero mid
    hquarter hhalf hreference hzero hmid hgate x y z
  simpa only [hdist (mid x y) z, hdist x z, hdist y z] using h

end
end IDT.QMClosure.RawProcessComparisonBridge
