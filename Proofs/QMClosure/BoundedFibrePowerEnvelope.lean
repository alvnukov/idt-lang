import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-! Uniform operator-power envelopes from bounded algebraically spanning sets
and fixed-success marginal fibres. Completeness is used for uniform boundedness.
The geometric endpoint supplies positivity, marginal naturality, a local endpoint
eigenrelation and boundedness of the fibre. No physical origin of those maps or
fibre properties, and no full atomicity theorem, is asserted here.
-/

namespace IDT.QMClosure.BoundedFibrePowerEnvelope

open Set

section UniformBoundedness

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*}

/-- Points on which a linear family is bounded form an algebraic submodule. -/
def pointwiseBoundedSubmodule (g : ι → E →L[ℝ] F) : Submodule ℝ E where
  carrier := {x | ∃ C : ℝ, ∀ i, ‖g i x‖ ≤ C}
  zero_mem' := ⟨0, by intro i; simp⟩
  add_mem' := by
    rintro x y ⟨C, hC⟩ ⟨D, hD⟩
    refine ⟨C + D, fun i => ?_⟩
    calc
      ‖g i (x + y)‖ = ‖g i x + g i y‖ := by rw [map_add]
      _ ≤ ‖g i x‖ + ‖g i y‖ := norm_add_le _ _
      _ ≤ C + D := add_le_add (hC i) (hD i)
  smul_mem' := by
    rintro a x ⟨C, hC⟩
    refine ⟨‖a‖ * C, fun i => ?_⟩
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC i) (norm_nonneg a)

/-- Algebraic spanning propagates pointwise boundedness to every vector. -/
theorem pointwise_bounded_of_span (g : ι → E →L[ℝ] F) (S : Set E)
    (hspan : Submodule.span ℝ S = ⊤)
    (hS : ∀ x ∈ S, ∃ C : ℝ, ∀ i, ‖g i x‖ ≤ C) :
    ∀ x, ∃ C : ℝ, ∀ i, ‖g i x‖ ≤ C := by
  have hle : Submodule.span ℝ S ≤ pointwiseBoundedSubmodule g :=
    Submodule.span_le.mpr hS
  rw [hspan] at hle
  intro x
  exact hle (Submodule.mem_top : x ∈ (⊤ : Submodule ℝ E))

/-- Uniform boundedness supplies one nonnegative constant for the whole family. -/
theorem uniform_bound_of_pointwise_bounded [CompleteSpace E]
    (g : ι → E →L[ℝ] F)
    (h : ∀ x, ∃ C : ℝ, ∀ i, ‖g i x‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ‖g i‖ ≤ C := by
  obtain ⟨C, hC⟩ := banach_steinhaus h
  exact ⟨max C 0, le_max_right _ _, fun i => (hC i).trans (le_max_left _ _)⟩

end UniformBoundedness

section Powers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem power_mapsTo (U : E →L[ℝ] E) {S : Set E} (hU : MapsTo U S S)
    (n : ℕ) : MapsTo (U ^ n) S S := by
  induction n with
  | zero =>
    intro x hx
    simpa only [pow_zero, ContinuousLinearMap.one_apply] using hx
  | succ n ih =>
    intro x hx
    simpa only [pow_succ', ContinuousLinearMap.mul_apply] using hU (ih hx)

/-- Scalar rescaling commutes with every power of a continuous linear operator. -/
theorem power_smul (a : ℝ) (U : E →L[ℝ] E) (n : ℕ) :
    (a • U) ^ n = a ^ n • (U ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', ih, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [mul_comm (a ^ n) a]

/-- An invariant bounded algebraically spanning set bounds every operator power
on a real Banach space. -/
theorem bounded_spanning_set_power_bound [CompleteSpace E]
    (U : E →L[ℝ] E) (S : Set E) (hbounded : Bornology.IsBounded S)
    (hspan : Submodule.span ℝ S = ⊤) (hU : MapsTo U S S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖U ^ n‖ ≤ C := by
  obtain ⟨M, hM⟩ := hbounded.exists_norm_le
  apply uniform_bound_of_pointwise_bounded (fun n : ℕ => U ^ n)
  apply pointwise_bounded_of_span _ S hspan
  intro x hx
  exact ⟨M, fun n => hM _ (power_mapsTo U hU n hx)⟩

/-- Exact fixed-success scaling of a bounded spanning set gives a q-power envelope. -/
theorem scaled_bounded_spanning_set_power_bound [CompleteSpace E]
    (T : E →L[ℝ] E) (S : Set E) (q : ℝ) (hq : 0 < q)
    (hbounded : Bornology.IsBounded S) (hspan : Submodule.span ℝ S = ⊤)
    (hsuccess : ∀ x ∈ S, ∃ y ∈ S, T x = q • y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖T ^ n‖ ≤ C * q ^ n := by
  let U : E →L[ℝ] E := q⁻¹ • T
  have hU : MapsTo U S S := by
    intro x hx
    obtain ⟨y, hy, heq⟩ := hsuccess x hx
    simpa [U, heq, smul_smul, ne_of_gt hq] using hy
  have hT : T = q • U := by simp [U, smul_smul, ne_of_gt hq]
  obtain ⟨C, hC, hbound⟩ := bounded_spanning_set_power_bound U S hbounded hspan hU
  refine ⟨C, hC, fun n => ?_⟩
  have hp : T ^ n = q ^ n • U ^ n := by
    calc
      T ^ n = (q • U) ^ n := congrArg (fun X : E →L[ℝ] E => X ^ n) hT
      _ = _ := power_smul q U n
  rw [hp, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq.le n)]
  exact (mul_le_mul_of_nonneg_left (hbound n) (pow_nonneg hq.le n)).trans_eq
    (mul_comm _ _)

end Powers

section Fibre

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def fibreDifferences (K : Set V) : Set V :=
  {x | ∃ v ∈ K, ∃ w ∈ K, x = v - w}

/-- This span can include ordinary reference directions. Identifying a
product-invisible sector, an invariant quotient, or a common carrier requires
separate containment and selection arguments. -/
def fibreSpan (K : Set V) : Submodule ℝ V := Submodule.span ℝ (fibreDifferences K)

/-- Fixed-success fibre scaling preserves its algebraic difference span. -/
theorem fixed_success_fibre_invariant (T : V →L[ℝ] V) (K : Set V) (q : ℝ)
    (hsuccess : ∀ v ∈ K, ∃ w ∈ K, T v = q • w) :
    ∀ v ∈ fibreSpan K, T v ∈ fibreSpan K := by
  have hgen : fibreDifferences K ⊆ (fibreSpan K).comap T.toLinearMap := by
    rintro x ⟨v, hv, w, hw, rfl⟩
    obtain ⟨v', hv', hTv⟩ := hsuccess v hv
    obtain ⟨w', hw', hTw⟩ := hsuccess w hw
    change T (v - w) ∈ fibreSpan K
    rw [map_sub, hTv, hTw, ← smul_sub]
    exact Submodule.smul_mem _ q (Submodule.subset_span ⟨v', hv', w', hw', rfl⟩)
  exact Submodule.span_le.mpr hgen

/-- The exact fixed-success law supplies the invariance needed to restrict the
ambient branch map to the entire fibre difference span. -/
noncomputable def restrictedFibreOperator
    (T : V →L[ℝ] V) (K : Set V) (q : ℝ)
    (hsuccess : ∀ v ∈ K, ∃ w ∈ K, T v = q • w) :
    fibreSpan K →L[ℝ] fibreSpan K :=
  (T.comp (fibreSpan K).subtypeL).codRestrict (fibreSpan K)
    (fun v => fixed_success_fibre_invariant T K q hsuccess v v.property)

@[simp]
theorem restrictedFibreOperator_apply
    (T : V →L[ℝ] V) (K : Set V) (q : ℝ)
    (hsuccess : ∀ v ∈ K, ∃ w ∈ K, T v = q • w) (v : fibreSpan K) :
    (restrictedFibreOperator T K q hsuccess v : V) = T v := rfl

/-- Every restricted power is the ambient power on the same vector. -/
@[simp]
theorem restrictedFibreOperator_pow_apply
    (T : V →L[ℝ] V) (K : Set V) (q : ℝ)
    (hsuccess : ∀ v ∈ K, ∃ w ∈ K, T v = q • w)
    (n : ℕ) (v : fibreSpan K) :
    ((restrictedFibreOperator T K q hsuccess ^ n) v : V) = (T ^ n) (v : V) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', ContinuousLinearMap.mul_apply,
      restrictedFibreOperator_apply, ih]

/-- The subtype inclusion intertwines the restricted and ambient operators. -/
theorem subtype_restrictedFibreOperator
    (T : V →L[ℝ] V) (K : Set V) (q : ℝ)
    (hsuccess : ∀ v ∈ K, ∃ w ∈ K, T v = q • w) :
    (fibreSpan K).subtypeL.comp (restrictedFibreOperator T K q hsuccess) =
      T.comp (fibreSpan K).subtypeL := by
  ext v
  rfl

/-- Bounded fixed-success fibres give a uniform power envelope on their entire
algebraic difference span. Finite dimension supplies completeness of that span. -/
theorem fixed_success_fibre_power_envelope [FiniteDimensional ℝ V]
    (T : V →L[ℝ] V) (K : Set V) (q : ℝ) (hq : 0 < q)
    (hbounded : Bornology.IsBounded K)
    (hsuccess : ∀ v ∈ K, ∃ w ∈ K, T v = q • w) :
    (∀ v ∈ fibreSpan K, T v ∈ fibreSpan K) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ v ∈ fibreSpan K,
        ‖(T ^ n) v‖ ≤ C * q ^ n * ‖v‖ := by
  refine ⟨fixed_success_fibre_invariant T K q hsuccess, ?_⟩
  let U : V →L[ℝ] V := q⁻¹ • T
  have hU : MapsTo U K K := by
    intro x hx
    obtain ⟨y, hy, heq⟩ := hsuccess x hx
    simpa [U, heq, smul_smul, ne_of_gt hq] using hy
  have hT : T = q • U := by simp [U, smul_smul, ne_of_gt hq]
  obtain ⟨M, hM⟩ := hbounded.exists_norm_le
  have hgen : fibreDifferences K ⊆ pointwiseBoundedSubmodule (fun n : ℕ => U ^ n) := by
    rintro x ⟨v, hv, w, hw, rfl⟩
    refine ⟨M + M, fun n => ?_⟩
    rw [map_sub]
    exact (norm_sub_le _ _).trans
      (add_le_add (hM _ (power_mapsTo U hU n hv)) (hM _ (power_mapsTo U hU n hw)))
  have hspan : fibreSpan K ≤ pointwiseBoundedSubmodule (fun n : ℕ => U ^ n) :=
    Submodule.span_le.mpr hgen
  let g : ℕ → fibreSpan K →L[ℝ] V := fun n => (U ^ n).comp (fibreSpan K).subtypeL
  have hpointwise : ∀ x : fibreSpan K, ∃ C : ℝ, ∀ n, ‖g n x‖ ≤ C := by
    intro x
    exact hspan x.property
  have hcomplete : CompleteSpace (fibreSpan K) := inferInstance
  -- Uniform boundedness uses the norm-induced uniform structure. The subtype
  -- structure is definitionally equal, so transfer its completeness explicitly.
  letI : @CompleteSpace (fibreSpan K)
      (inferInstance : SeminormedAddCommGroup (fibreSpan K)).toPseudoMetricSpace.toUniformSpace :=
    hcomplete
  letI : Norm (fibreSpan K →L[ℝ] V) := ContinuousLinearMap.hasOpNorm
  obtain ⟨C₀, hbound₀⟩ := banach_steinhaus (g := g) hpointwise
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound (n : ℕ) : ‖g n‖ ≤ C := (hbound₀ n).trans (le_max_left _ _)
  refine ⟨C, hC, fun n v hv => ?_⟩
  have hu : ‖(U ^ n) v‖ ≤ C * ‖v‖ := by
    calc
      _ = ‖g n ⟨v, hv⟩‖ := rfl
      _ ≤ ‖g n‖ * ‖(⟨v, hv⟩ : fibreSpan K)‖ := (g n).le_opNorm _
      _ ≤ C * ‖v‖ := mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg v)
  have hp : T ^ n = q ^ n • U ^ n := by
    calc
      T ^ n = (q • U) ^ n := congrArg (fun X : V →L[ℝ] V => X ^ n) hT
      _ = _ := power_smul q U n
  rw [hp, ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hq.le n)]
  exact (mul_le_mul_of_nonneg_left hu (pow_nonneg hq.le n)).trans_eq (by ring)

/-- The derived restricted operator has the operator-norm power envelope used
by surjective image and quotient transfer theorems. -/
theorem fixed_success_restricted_fibre_power_envelope [FiniteDimensional ℝ V]
    (T : V →L[ℝ] V) (K : Set V) (q : ℝ) (hq : 0 < q)
    (hbounded : Bornology.IsBounded K)
    (hsuccess : ∀ v ∈ K, ∃ w ∈ K, T v = q • w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ContinuousLinearMap.opNorm (restrictedFibreOperator T K q hsuccess ^ n) ≤ C * q ^ n := by
  obtain ⟨C, hC, hbound⟩ :=
    (fixed_success_fibre_power_envelope T K q hq hbounded hsuccess).2
  refine ⟨C, hC, fun n => ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (pow_nonneg hq.le n))
  intro v
  change ‖((restrictedFibreOperator T K q hsuccess ^ n) v : V)‖ ≤
    C * q ^ n * ‖(v : V)‖
  rw [restrictedFibreOperator_pow_apply]
  exact hbound n v v.property

end Fibre

section Marginal

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommGroup W] [Module ℝ W]

def marginalFibre (C : Set V) (marginal : V →ₗ[ℝ] W) (x : W) : Set V :=
  {v | v ∈ C ∧ marginal v = x}

/-- Positivity, naturality and a fixed local endpoint eigenrelation derive the
exact fixed-success law on a supplied marginal fibre. -/
theorem marginal_fibre_fixed_success
    (C : Set V) (marginal : V →ₗ[ℝ] W) (x : W)
    (T : V →L[ℝ] V) (L : W →ₗ[ℝ] W) (q : ℝ) (hq : 0 < q)
    (hscale : ∀ a : ℝ, 0 ≤ a → ∀ v ∈ C, a • v ∈ C)
    (hpositive : MapsTo T C C)
    (hnatural : marginal.comp T.toLinearMap = L.comp marginal)
    (hlocal : L x = q • x) :
    ∀ v ∈ marginalFibre C marginal x,
      ∃ w ∈ marginalFibre C marginal x, T v = q • w := by
  intro v hv
  refine ⟨q⁻¹ • T v, ⟨hscale _ (inv_nonneg.mpr hq.le) _ (hpositive hv.1), ?_⟩, ?_⟩
  · have hn : marginal (T v) = L (marginal v) := DFunLike.congr_fun hnatural v
    rw [map_smul, hn, hv.2, hlocal, smul_smul, inv_mul_cancel₀ (ne_of_gt hq), one_smul]
  · simp [smul_smul, ne_of_gt hq]

/-- A bounded marginal fibre supplies its invariant difference-span power
envelope under positive natural branch maps and a local eigenrelation. -/
theorem bounded_marginal_fibre_power_envelope [FiniteDimensional ℝ V]
    (C : Set V) (marginal : V →ₗ[ℝ] W) (x : W)
    (T : V →L[ℝ] V) (L : W →ₗ[ℝ] W) (q : ℝ) (hq : 0 < q)
    (hscale : ∀ a : ℝ, 0 ≤ a → ∀ v ∈ C, a • v ∈ C)
    (hpositive : MapsTo T C C)
    (hnatural : marginal.comp T.toLinearMap = L.comp marginal)
    (hlocal : L x = q • x)
    (hbounded : Bornology.IsBounded (marginalFibre C marginal x)) :
    (∀ v ∈ fibreSpan (marginalFibre C marginal x),
      T v ∈ fibreSpan (marginalFibre C marginal x)) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∀ v ∈ fibreSpan (marginalFibre C marginal x),
        ‖(T ^ n) v‖ ≤ B * q ^ n * ‖v‖ := by
  exact fixed_success_fibre_power_envelope T _ q hq hbounded
    (marginal_fibre_fixed_success C marginal x T L q hq hscale hpositive hnatural hlocal)

end Marginal

namespace VariableSuccessControl

def K : Set (ℝ × ℝ) := {v | v.1 = 1 ∧ |v.2| ≤ 1}

def direction : ℝ × ℝ := (0, 1)

def program : ℝ × ℝ := (1, 0)

noncomputable def variableT : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  ({ toFun := fun v => (v.1 / 2 + v.2 / 4, 0)
     map_add' := by intro v w; ext <;> dsimp <;> ring
     map_smul' := by intro a v; ext <;> dsimp <;> ring } :
    (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)).toContinuousLinearMap

theorem K_bounded : Bornology.IsBounded K := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1, fun v hv => ?_⟩
  rw [Prod.norm_def]
  exact max_le (by simp [hv.1]) (by simpa only [Real.norm_eq_abs] using hv.2)

theorem direction_mem : direction ∈ fibreSpan K := by
  apply Submodule.subset_span
  refine ⟨(1, 1), by norm_num [K], (1, 0), by norm_num [K], ?_⟩
  ext <;> norm_num [direction]

theorem direction_nonzero : direction ≠ 0 := by simp [direction]

theorem fibreSpan_first_zero (v : ℝ × ℝ) (hv : v ∈ fibreSpan K) : v.1 = 0 := by
  have hle : fibreSpan K ≤ LinearMap.ker (LinearMap.fst ℝ ℝ ℝ) := by
    apply Submodule.span_le.mpr
    rintro z ⟨v, hv, w, hw, rfl⟩
    change v.1 - w.1 = 0
    rw [hv.1, hw.1, sub_self]
  exact hle hv

/-- The fixed-success theorem applies on a bounded fibre with nonzero differences. -/
theorem constant_success_nontrivial_power_envelope (q : ℝ) (hq : 0 < q) :
    (∃ v ∈ fibreSpan K, v ≠ 0) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ v ∈ fibreSpan K,
        ‖((q • ContinuousLinearMap.id ℝ (ℝ × ℝ)) ^ n) v‖ ≤ C * q ^ n * ‖v‖ := by
  refine ⟨⟨direction, direction_mem, direction_nonzero⟩, ?_⟩
  exact (fixed_success_fibre_power_envelope (q • ContinuousLinearMap.id ℝ (ℝ × ℝ))
    K q hq K_bounded (fun v hv => ⟨v, hv, by simp⟩)).2

/-- Variable success stays uniformly between one quarter and three quarters,
and every normalized output is the same program in K. -/
theorem variable_success_normalized_output :
    program ∈ K ∧ ∀ v ∈ K, ∃ a : ℝ,
      (1 / 4 : ℝ) ≤ a ∧ a ≤ (3 / 4 : ℝ) ∧ variableT v = a • program := by
  refine ⟨by norm_num [program, K], fun v hv => ?_⟩
  have habs := abs_le.mp hv.2
  refine ⟨v.1 / 2 + v.2 / 4, ?_, ?_, ?_⟩
  · rw [hv.1]
    linarith
  · rw [hv.1]
    linarith
  · ext <;> simp [variableT, program]

theorem variable_direction_not_mem : variableT direction ∉ fibreSpan K := by
  intro h
  have hzero := fibreSpan_first_zero _ h
  norm_num [variableT, direction] at hzero

/-- Bounded variable success cannot replace the exact fixed-success law. -/
theorem variable_success_not_invariant :
    ¬ (∀ v ∈ fibreSpan K, variableT v ∈ fibreSpan K) := by
  intro h
  exact variable_direction_not_mem (h direction direction_mem)

end VariableSuccessControl

end IDT.QMClosure.BoundedFibrePowerEnvelope
