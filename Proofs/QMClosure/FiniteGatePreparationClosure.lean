import Proofs.QMClosure.FiniteGateFrameCoordinates
import Proofs.QMClosure.FiniteGatePreparationBounds
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# Compact spatial preparation closure and an attained positive radius

The closure below is a mathematical closure in the usual topology on real
coordinate triples. No topology is assumed on the original vector space.
No availability of these additional limit points as physical states is claimed.
The coordinate bounds follow from the checked binary-segment preparation bounds.
-/

noncomputable section

namespace IDT.QMClosure.FiniteGatePreparationClosure

open Set FiniteGateFrameDimension FiniteGateFrameCoordinates

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

abbrev SpatialPoint := ℝ × ℝ × ℝ

/-- The first spatial coordinate is unscaled. The other scales are arbitrary. -/
def spatial {F : Frame V} (C : AxisCoordinates F) (k l : ℝ) (v : V) : SpatialPoint :=
  (C.equiv v 1, k * C.equiv v 2, l * C.equiv v 3)

def spatialPreparations (F : Frame V) (C : AxisCoordinates F) (k l : ℝ) :
    Set SpatialPoint := spatial C k l '' F.preparations

/-- Only the real-coordinate image receives a mathematical closure. -/
def preparationClosure (F : Frame V) (C : AxisCoordinates F) (k l : ℝ) :
    Set SpatialPoint := closure (spatialPreparations F C k l)

def sqnorm (p : SpatialPoint) : ℝ := p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2

def coordinateBox (M : ℝ) : Set SpatialPoint :=
  Icc (-M) M ×ˢ (Icc (-M) M ×ˢ Icc (-M) M)

private def coordinateFunctional {F : Frame V} (C : AxisCoordinates F) (i : Fin 4) :
    V →ₗ[ℝ] ℝ := (LinearMap.proj i).comp C.equiv.toLinearMap

theorem continuous_sqnorm : Continuous sqnorm := by
  unfold sqnorm
  fun_prop

theorem sqnorm_nonneg (p : SpatialPoint) : 0 ≤ sqnorm p := by
  dsimp [sqnorm]
  positivity

variable (F : Frame V) (C : AxisCoordinates F) (k l : ℝ)

/-- One positive box bounds every spatial preparation simultaneously. -/
theorem spatialPreparations_bounded_box :
    ∃ M > 0, spatialPreparations F C k l ⊆ coordinateBox M := by
  obtain ⟨Bx, hx⟩ := FiniteGatePreparationBounds.Frame.functional_preparation_bound
    F (coordinateFunctional C 1)
  obtain ⟨By, hy⟩ := FiniteGatePreparationBounds.Frame.functional_preparation_bound
    F (k • coordinateFunctional C 2)
  obtain ⟨Bz, hz⟩ := FiniteGatePreparationBounds.Frame.functional_preparation_bound
    F (l • coordinateFunctional C 3)
  let M := |Bx| + |By| + |Bz| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hBx : Bx ≤ M := by
    dsimp [M]
    linarith [le_abs_self Bx, abs_nonneg By, abs_nonneg Bz]
  have hBy : By ≤ M := by
    dsimp [M]
    linarith [le_abs_self By, abs_nonneg Bx, abs_nonneg Bz]
  have hBz : Bz ≤ M := by
    dsimp [M]
    linarith [le_abs_self Bz, abs_nonneg Bx, abs_nonneg By]
  refine ⟨M, hM, ?_⟩
  rintro p ⟨v, hv, rfl⟩
  have hxv := hx v hv
  have hyv := hy v hv
  have hzv := hz v hv
  change |C.equiv v 1| ≤ Bx at hxv
  change |k * C.equiv v 2| ≤ By at hyv
  change |l * C.equiv v 3| ≤ Bz at hzv
  change (C.equiv v 1 ∈ Icc (-M) M) ∧
    (k * C.equiv v 2 ∈ Icc (-M) M) ∧ (l * C.equiv v 3 ∈ Icc (-M) M)
  exact ⟨abs_le.1 (hxv.trans hBx), abs_le.1 (hyv.trans hBy), abs_le.1 (hzv.trans hBz)⟩

/-- The same closed box contains the entire mathematical closure. -/
theorem preparationClosure_bounded_box :
    ∃ M > 0, preparationClosure F C k l ⊆ coordinateBox M := by
  obtain ⟨M, hM, hbound⟩ := spatialPreparations_bounded_box F C k l
  refine ⟨M, hM, closure_minimal hbound ?_⟩
  exact isClosed_Icc.prod (isClosed_Icc.prod isClosed_Icc)

theorem preparationClosure_nonempty : (preparationClosure F C k l).Nonempty := by
  obtain ⟨v, hv⟩ := F.nonempty
  exact ⟨spatial C k l v, subset_closure ⟨v, hv, rfl⟩⟩

theorem preparationClosure_compact : IsCompact (preparationClosure F C k l) := by
  obtain ⟨M, _, hbound⟩ := preparationClosure_bounded_box F C k l
  have hbox : IsCompact (coordinateBox M) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  exact hbox.of_isClosed_subset isClosed_closure hbound

/-- Spanning preparations cannot all have zero first spatial coordinate. -/
theorem exists_preparation_nonzero_x :
    ∃ v ∈ F.preparations, C.equiv v 1 ≠ 0 := by
  by_contra hn
  push Not at hn
  let f := coordinateFunctional C 1
  have hker : F.preparations ⊆ LinearMap.ker f := by
    intro v hv
    change C.equiv v 1 = 0
    exact hn v hv
  have htop : (⊤ : Submodule ℝ V) ≤ LinearMap.ker f := by
    rw [← F.spanning]
    exact Submodule.span_le.2 hker
  have heval : f (C.equiv.symm (axis 1)) = 0 := htop (by trivial)
  change C.equiv (C.equiv.symm (axis 1)) 1 = 0 at heval
  simp [axis, quad] at heval

/-- The unscaled first coordinate supplies a positive squared-radius witness
for every choice of the other two coordinate scales, including zero scales. -/
theorem preparationClosure_contains_positive_sqnorm :
    ∃ p ∈ preparationClosure F C k l, 0 < sqnorm p := by
  obtain ⟨v, hv, hvx⟩ := exists_preparation_nonzero_x F C
  refine ⟨spatial C k l v, subset_closure ⟨v, hv, rfl⟩, ?_⟩
  dsimp [sqnorm, spatial]
  nlinarith [sq_pos_of_ne_zero hvx, sq_nonneg (k * C.equiv v 2),
    sq_nonneg (l * C.equiv v 3)]

theorem preparationClosure_contains_nonzero :
    ∃ p ∈ preparationClosure F C k l, p ≠ (0, 0, 0) := by
  obtain ⟨p, hp, hpos⟩ := preparationClosure_contains_positive_sqnorm F C k l
  refine ⟨p, hp, ?_⟩
  intro hzero
  rw [hzero] at hpos
  norm_num [sqnorm] at hpos

/-- A single positive radius bounds the whole closure and is attained in it. -/
theorem preparationClosure_attained_positive_radius :
    ∃ R > 0, (∀ p ∈ preparationClosure F C k l, sqnorm p ≤ R ^ 2) ∧
      (∃ p ∈ preparationClosure F C k l, sqnorm p = R ^ 2) := by
  obtain ⟨p, hp, hmax⟩ := (preparationClosure_compact F C k l).exists_isMaxOn
    (preparationClosure_nonempty F C k l) continuous_sqnorm.continuousOn
  obtain ⟨q, hq, hqpos⟩ := preparationClosure_contains_positive_sqnorm F C k l
  have hpositive : 0 < sqnorm p := lt_of_lt_of_le hqpos ((isMaxOn_iff.1 hmax) q hq)
  let R := Real.sqrt (sqnorm p)
  have hR : 0 < R := Real.sqrt_pos.2 hpositive
  have hRsq : R ^ 2 = sqnorm p := Real.sq_sqrt hpositive.le
  refine ⟨R, hR, ?_, p, hp, hRsq.symm⟩
  intro q hq
  rw [hRsq]
  exact (isMaxOn_iff.1 hmax) q hq

end IDT.QMClosure.FiniteGatePreparationClosure
