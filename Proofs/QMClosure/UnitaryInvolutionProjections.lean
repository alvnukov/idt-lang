import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

namespace IDT.QMClosure.UnitaryInvolutionProjections

noncomputable section

/-!
Mathematical projection calculus for a supplied involutive complex linear
isometry. The product adapter constructs that isometry separately; this module
does not impose a physical unitary primitive. Halving and complex scalars are
used only in this mathematical representation. Physical projector availability,
raw-carrier halving, whole-target exhaustion, particle statistics and probability
interpretations are not established here.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def op (S : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H := S

def plus (S : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H :=
  (1 / 2 : ℂ) • (1 + op S)

def minus (S : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H :=
  (1 / 2 : ℂ) • (1 - op S)

theorem plus_apply (S : H ≃ₗᵢ[ℂ] H) (x : H) :
    plus S x = (1 / 2 : ℂ) • (x + S x) := rfl

theorem minus_apply (S : H ≃ₗᵢ[ℂ] H) (x : H) :
    minus S x = (1 / 2 : ℂ) • (x - S x) := rfl

theorem plus_idempotent (S : H ≃ₗᵢ[ℂ] H) (hS : Function.Involutive S) :
    IsIdempotentElem (plus S) := by
  change plus S * plus S = plus S
  ext x
  simp only [ContinuousLinearMap.mul_apply, plus_apply, map_smul, map_add, hS x]
  module

theorem minus_idempotent (S : H ≃ₗᵢ[ℂ] H) (hS : Function.Involutive S) :
    IsIdempotentElem (minus S) := by
  change minus S * minus S = minus S
  ext x
  simp only [ContinuousLinearMap.mul_apply, minus_apply, map_smul, map_sub, hS x]
  module

theorem plus_add_minus (S : H ≃ₗᵢ[ℂ] H) :
    plus S + minus S = ContinuousLinearMap.id ℂ H := by
  ext x
  simp only [ContinuousLinearMap.add_apply, plus_apply, minus_apply,
    ContinuousLinearMap.id_apply]
  module

theorem plus_comp_minus (S : H ≃ₗᵢ[ℂ] H) (hS : Function.Involutive S) :
    (plus S).comp (minus S) = 0 := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, plus_apply, minus_apply, map_smul,
    map_sub, hS x, ContinuousLinearMap.zero_apply]
  module

theorem minus_comp_plus (S : H ≃ₗᵢ[ℂ] H) (hS : Function.Involutive S) :
    (minus S).comp (plus S) = 0 := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, plus_apply, minus_apply, map_smul,
    map_add, hS x, ContinuousLinearMap.zero_apply]
  module

theorem plus_norm_sq (S : H ≃ₗᵢ[ℂ] H) (x : H) :
    ‖plus S x‖ ^ 2 = (‖x‖ ^ 2 + (inner ℂ x (S x)).re) / 2 := by
  rw [plus_apply, norm_smul, mul_pow, norm_add_sq (𝕜 := ℂ), S.norm_map]
  norm_num [norm_div]
  ring

theorem minus_norm_sq (S : H ≃ₗᵢ[ℂ] H) (x : H) :
    ‖minus S x‖ ^ 2 = (‖x‖ ^ 2 - (inner ℂ x (S x)).re) / 2 := by
  rw [minus_apply, norm_smul, mul_pow, norm_sub_sq (𝕜 := ℂ), S.norm_map]
  norm_num [norm_div]
  ring

theorem range_plus_closed (S : H ≃ₗᵢ[ℂ] H) (hS : Function.Involutive S) :
    IsClosed ((plus S).range : Set H) :=
  ContinuousLinearMap.IsIdempotentElem.isClosed_range (plus_idempotent S hS)

theorem range_minus_closed (S : H ≃ₗᵢ[ℂ] H) (hS : Function.Involutive S) :
    IsClosed ((minus S).range : Set H) :=
  ContinuousLinearMap.IsIdempotentElem.isClosed_range (minus_idempotent S hS)

section Adjoint

variable [CompleteSpace H]

theorem op_adjoint (S : H ≃ₗᵢ[ℂ] H) (hS : Function.Involutive S) :
    (op S).adjoint = op S := by
  change ContinuousLinearMap.adjoint (S : H →L[ℂ] H) = (S : H →L[ℂ] H)
  rw [S.adjoint_eq_symm]
  ext x
  apply S.injective
  change S (S.symm x) = S (S x)
  rw [S.apply_symm_apply, hS x]

theorem op_selfAdjoint (S : H ≃ₗᵢ[ℂ] H) (hS : Function.Involutive S) :
    IsSelfAdjoint (op S) := op_adjoint S hS

theorem plus_selfAdjoint (S : H ≃ₗᵢ[ℂ] H) (hS : Function.Involutive S) :
    IsSelfAdjoint (plus S) := by
  change star (plus S) = plus S
  have hs : star (op S) = op S := op_selfAdjoint S hS
  simp only [plus, star_smul, star_add, star_one, hs]
  norm_num

theorem minus_selfAdjoint (S : H ≃ₗᵢ[ℂ] H) (hS : Function.Involutive S) :
    IsSelfAdjoint (minus S) := by
  change star (minus S) = minus S
  have hs : star (op S) = op S := op_selfAdjoint S hS
  simp only [minus, star_smul, star_sub, star_one, hs]
  norm_num

theorem mixed_inner (S : H ≃ₗᵢ[ℂ] H) (hS : Function.Involutive S) (x y : H) :
    inner ℂ (plus S x) (minus S y) = 0 := by
  have hz : plus S (minus S y) = 0 := by
    have he := congrArg (fun T : H →L[ℂ] H => T y) (plus_comp_minus S hS)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] using he
  calc
    inner ℂ (plus S x) (minus S y) = inner ℂ x (plus S (minus S y)) := by
      rw [← ContinuousLinearMap.adjoint_inner_right, (plus_selfAdjoint S hS).adjoint_eq]
    _ = 0 := by rw [hz, inner_zero_right]

end Adjoint

/-- A continuous idempotent's closed range is generated densely by its images
of any family whose complex linear span is dense. -/
theorem range_eq_closedSpan {I : Type*} (P : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (f : I → H) (hdense : Dense (Submodule.span ℂ (Set.range f) : Set H)) :
    P.range = (Submodule.span ℂ (Set.range (fun i => P (f i)))).topologicalClosure := by
  let M : Submodule ℂ H := Submodule.span ℂ (Set.range f)
  have hM : M.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp hdense
  have hmap : M.map P.toLinearMap = Submodule.span ℂ (Set.range (fun i => P (f i))) := by
    dsimp only [M]
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  apply le_antisymm
  · have he := M.topologicalClosure_map P
    rw [hM, Submodule.map_top, hmap] at he
    exact he
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨f i, rfl⟩
    · exact ContinuousLinearMap.IsIdempotentElem.isClosed_range hP

theorem plus_range_eq_closedSpan {I : Type*} (S : H ≃ₗᵢ[ℂ] H)
    (hS : Function.Involutive S) (f : I → H)
    (hdense : Dense (Submodule.span ℂ (Set.range f) : Set H)) :
    (plus S).range =
      (Submodule.span ℂ (Set.range (fun i => plus S (f i)))).topologicalClosure :=
  range_eq_closedSpan (plus S) (plus_idempotent S hS) f hdense

theorem minus_range_eq_closedSpan {I : Type*} (S : H ≃ₗᵢ[ℂ] H)
    (hS : Function.Involutive S) (f : I → H)
    (hdense : Dense (Submodule.span ℂ (Set.range f) : Set H)) :
    (minus S).range =
      (Submodule.span ℂ (Set.range (fun i => minus S (f i)))).topologicalClosure :=
  range_eq_closedSpan (minus S) (minus_idempotent S hS) f hdense

/-- Nonzero range is detected on any family with dense complex linear span;
idempotence is not needed for this detection theorem. -/
theorem range_ne_bot_iff {I : Type*} (P : H →L[ℂ] H) (f : I → H)
    (hdense : Dense (Submodule.span ℂ (Set.range f) : Set H)) :
    P.range ≠ ⊥ ↔ ∃ i, P (f i) ≠ 0 := by
  classical
  constructor
  · intro hn
    by_contra hh
    have hz : P = 0 := by
      apply ContinuousLinearMap.ext_on hdense
      rintro _ ⟨i, rfl⟩
      have hi : P (f i) = 0 := by
        by_contra hi
        exact hh ⟨i, hi⟩
      simpa only [ContinuousLinearMap.zero_apply] using hi
    apply hn
    rw [hz]
    simp
  · rintro ⟨i, hi⟩ hrange
    have hm : P (f i) ∈ (⊥ : Submodule ℂ H) := by
      rw [← hrange]
      exact ⟨f i, rfl⟩
    exact hi (by simpa using hm)

end

end IDT.QMClosure.UnitaryInvolutionProjections
