import Proofs.QMClosure.InitialColumnOrderReadoutCore
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# A dyadically homogeneous detector response on the literal initial carrier

This explicit mathematical response satisfies the four supplied base laws,
continuity of its complex-coordinate formula, and generator stationarity.
A concrete initial preparation violates numerical self-squaring. The process
operation below is literal semiring multiplication. No physical copying,
complete probabilistic operational model, or QM closure is asserted.
-/

namespace IDT.QMClosure.InitialDyadicDetectorCountermodel

noncomputable section

open TransparentFourthInitialHistoryPresentation
open TransparentFourthInitialNormalForm
open InitialCountGeometry InitialPreparedCountOrder InitialEchoCoordinates
open scoped Pointwise

/-- The dyadic scale orbit with its limiting origin included. -/
def dyadicSet : Set ℝ := {0} ∪ Set.range (fun k : ℤ => (2 : ℝ) ^ k)

lemma zero_mem_dyadicSet : (0 : ℝ) ∈ dyadicSet := by simp [dyadicSet]

lemma zpow_mem_dyadicSet (k : ℤ) : (2 : ℝ) ^ k ∈ dyadicSet :=
  Or.inr ⟨k, rfl⟩

lemma dyadicSet_nonempty : dyadicSet.Nonempty := ⟨0, zero_mem_dyadicSet⟩

lemma two_smul_dyadicSet : (2 : ℝ) • dyadicSet = dyadicSet := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
    rcases hy with hy | ⟨k, rfl⟩
    · have hy0 : y = 0 := Set.mem_singleton_iff.mp hy
      simp [hy0, zero_mem_dyadicSet]
    · have he : (2 : ℝ) * 2 ^ k = 2 ^ (k + 1) := by
        rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
        ring
      simpa only [smul_eq_mul, he] using zpow_mem_dyadicSet (k + 1)
  · intro hx
    rcases hx with hx | ⟨k, rfl⟩
    · have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
      subst x
      exact Set.mem_smul_set.mpr ⟨0, zero_mem_dyadicSet, by simp⟩
    · apply Set.mem_smul_set.mpr
      refine ⟨(2 : ℝ) ^ (k - 1), zpow_mem_dyadicSet (k - 1), ?_⟩
      change (2 : ℝ) * 2 ^ (k - 1) = 2 ^ k
      have he := zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0) (k - 1)
      rw [sub_add_cancel] at he
      nlinarith [he]

/-- A continuous, strictly increasing perturbation using distance to the orbit. -/
def profile (x : ℝ) : ℝ := x + (1 / 2 : ℝ) * Metric.infDist x dyadicSet

@[simp] theorem profile_zero : profile 0 = 0 := by
  simp [profile, Metric.infDist_zero_of_mem zero_mem_dyadicSet]

@[simp] theorem profile_one : profile 1 = 1 := by
  have h1 : (1 : ℝ) ∈ dyadicSet := by simpa using zpow_mem_dyadicSet 0
  simp [profile, Metric.infDist_zero_of_mem h1]

theorem profile_continuous : Continuous profile :=
  continuous_id.add (continuous_const.mul (Metric.continuous_infDist_pt dyadicSet))

theorem profile_strictMono : StrictMono profile := by
  intro x y hxy
  have hd := Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := dyadicSet)
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy.le)] at hd
  dsimp [profile]
  linarith

theorem profile_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ profile x := by
  dsimp [profile]
  have hd := Metric.infDist_nonneg (x := x) (s := dyadicSet)
  linarith

theorem profile_double (x : ℝ) : profile (2 * x) = 2 * profile x := by
  have hd : Metric.infDist (2 * x) dyadicSet = 2 * Metric.infDist x dyadicSet := by
    simpa only [smul_eq_mul, two_smul_dyadicSet,
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
      (infDist_smul₀ (𝕜 := ℝ) (by norm_num : (2 : ℝ) ≠ 0) dyadicSet x)
  dsimp [profile]
  rw [hd]
  ring

theorem profile_half (x : ℝ) : profile (x / 2) = profile x / 2 := by
  have hh := profile_double (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hh
  linarith

lemma infDist_five_halves : Metric.infDist (5 / 2 : ℝ) dyadicSet = 1 / 2 := by
  apply le_antisymm
  · have hu := Metric.infDist_le_dist_of_mem (x := (5 / 2 : ℝ))
      (by simpa using zpow_mem_dyadicSet 1)
    norm_num [Real.dist_eq] at hu ⊢
    exact hu
  · apply (Metric.le_infDist dyadicSet_nonempty).2
    intro y hy
    rcases hy with hy | ⟨k, rfl⟩
    · have hy0 : y = 0 := Set.mem_singleton_iff.mp hy
      subst y
      norm_num [Real.dist_eq]
    · rw [Real.dist_eq]
      by_cases hk : k ≤ 1
      · have hp := zpow_le_zpow_right₀ (a := (2 : ℝ)) (by norm_num) hk
        norm_num at hp
        linarith [le_abs_self ((5 / 2 : ℝ) - 2 ^ k)]
      · have hk2 : (2 : ℤ) ≤ k := by omega
        have hp := zpow_le_zpow_right₀ (a := (2 : ℝ)) (by norm_num) hk2
        norm_num at hp
        linarith [neg_le_abs ((5 / 2 : ℝ) - 2 ^ k)]

lemma infDist_twentyfive_quarters :
    Metric.infDist (25 / 4 : ℝ) dyadicSet = 7 / 4 := by
  apply le_antisymm
  · have hu := Metric.infDist_le_dist_of_mem (x := (25 / 4 : ℝ))
      (by simpa using zpow_mem_dyadicSet 3)
    norm_num [Real.dist_eq] at hu ⊢
    exact hu
  · apply (Metric.le_infDist dyadicSet_nonempty).2
    intro y hy
    rcases hy with hy | ⟨k, rfl⟩
    · have hy0 : y = 0 := Set.mem_singleton_iff.mp hy
      subst y
      norm_num [Real.dist_eq]
    · rw [Real.dist_eq]
      by_cases hk : k ≤ 2
      · have hp := zpow_le_zpow_right₀ (a := (2 : ℝ)) (by norm_num) hk
        norm_num at hp
        linarith [le_abs_self ((25 / 4 : ℝ) - 2 ^ k)]
      · have hk3 : (3 : ℤ) ≤ k := by omega
        have hp := zpow_le_zpow_right₀ (a := (2 : ℝ)) (by norm_num) hk3
        norm_num at hp
        linarith [neg_le_abs ((25 / 4 : ℝ) - 2 ^ k)]

theorem profile_five_halves : profile (5 / 2) = 11 / 4 := by
  norm_num [profile, infDist_five_halves]

theorem profile_twentyfive_quarters : profile (25 / 4) = 57 / 8 := by
  norm_num [profile, infDist_twentyfive_quarters]

/-- The detector is defined on each actual initial preparation. -/
def W (p : P) : ℝ := profile (N p)

@[simp] theorem W_zero : W 0 = 0 := by simp [W, N, InitialCountGeometry.normSq]

@[simp] theorem W_one : W 1 = 1 := by simp [W, N, InitialCountGeometry.normSq]

theorem W_nonneg (p : P) : 0 ≤ W p := profile_nonneg (normSq_nonnegative p)

theorem W_halfA (p : P) : W (a * p) = W p / 2 := by
  unfold W
  rw [(InitialColumnOrderReadoutCore.half_responses
    InitialColumnOrderReadoutCore.norm_model p).1, profile_half]

theorem W_halfB (p : P) : W (b * p) = W p / 2 := by
  unfold W
  rw [(InitialColumnOrderReadoutCore.half_responses
    InitialColumnOrderReadoutCore.norm_model p).2, profile_half]

theorem base_contract : InitialColumnOrderReadoutCore.BaseContract W where
  normalized := W_one
  column := by intro p; rw [W_halfA, W_halfB]; ring
  cIncreasing := by
    intro p
    exact profile_strictMono.monotone
      (InitialColumnOrderReadoutCore.norm_model.cIncreasing p)
  preparedOrder := by
    intro p n m n' m' hn hm
    exact profile_strictMono.monotone
      (InitialColumnOrderReadoutCore.norm_model.preparedOrder p n m n' m' hn hm)

/-- This model has exact c equality in addition to the base increase law. -/
theorem W_c (p : P) : W (c * p) = W p := by
  change profile (Complex.normSq (E (c * p))) = profile (Complex.normSq (E p))
  simp only [map_mul, evaluation_c, one_mul]

/-- The response depends only on the explicit complex coordinate. -/
theorem W_ext {p q : P} (h : E p = E q) : W p = W q := by
  change profile (Complex.normSq (E p)) = profile (Complex.normSq (E q))
  rw [h]

theorem W_null (p : P) (hp : E p = 0) : W p = 0 := by
  change profile (Complex.normSq (E p)) = 0
  rw [hp]
  simpa using profile_zero

theorem W_null_insertion (p z : P) (hz : E z = 0) : W (p + z) = W p := by
  apply W_ext
  simp only [map_add, hz, add_zero]

theorem W_all_null_sum {ι : Type*} (s : Finset ι) (p : ι → P)
    (h : ∀ i ∈ s, E (p i) = 0) : W (∑ i ∈ s, p i) = 0 := by
  apply W_null
  rw [map_sum]
  exact Finset.sum_eq_zero h

/-- Ambient continuity is a property of this coordinate formula. -/
def ambientDetector (z : ℂ) : ℝ := profile (Complex.normSq z)

theorem ambientDetector_continuous : Continuous ambientDetector :=
  profile_continuous.comp Complex.continuous_normSq

theorem coordinate_formula (p : P) : W p = ambientDetector (E p) := rfl

theorem generator_stationarity (p : P) :
    W (a * p) = W a * W p ∧ W (b * p) = W b * W p := by
  have ha : W a = 1 / 2 := by simpa using W_halfA 1
  have hb : W b = 1 / 2 := by simpa using W_halfB 1
  rw [W_halfA, W_halfB, ha, hb]
  constructor <;> ring

/-- Finite a/b words have the expected half-gain at every preparation. -/
theorem finite_word_gain (m n : ℕ) (p : P) :
    W (a ^ m * b ^ n * p) = (1 / 2 : ℝ) ^ (m + n) * W p := by
  induction m generalizing p with
  | zero =>
      simp only [pow_zero, one_mul, Nat.zero_add]
      induction n generalizing p with
      | zero => simp
      | succ n ih =>
          rw [pow_succ', mul_assoc, W_halfB, ih, pow_succ]
          ring
  | succ m ih =>
      rw [pow_succ', mul_assoc, mul_assoc, W_halfA]
      rw [← mul_assoc, ih]
      rw [show m + 1 + n = (m + n) + 1 by omega, pow_succ]
      ring

/-- An explicit finite initial term witnessing the response discrepancy. -/
def witness : P := 1 + a

lemma witness_norm : N witness = 5 / 2 := by
  norm_num [N, InitialCountGeometry.normSq, witness, map_add, map_one,
    evaluation_a, complexA, Complex.normSq_apply]

lemma witness_square_norm : N (witness ^ 2) = 25 / 4 := by
  calc
    N (witness ^ 2) = N witness * N witness := by
      simpa only [pow_two] using InitialCountGeometry.normSq_mul witness witness
    _ = 25 / 4 := by norm_num [witness_norm]

theorem witness_values :
    W witness = 11 / 4 ∧ W (witness ^ 2) = 57 / 8 ∧ (W witness) ^ 2 = 121 / 16 := by
  have hp : W witness = 11 / 4 := by rw [W, witness_norm, profile_five_halves]
  have hpp : W (witness ^ 2) = 57 / 8 := by
    rw [W, witness_square_norm, profile_twentyfive_quarters]
  exact ⟨hp, hpp, by rw [hp]; norm_num⟩

theorem self_square_fails : ¬ ∀ p : P, W (p ^ 2) = W p ^ 2 := by
  intro h
  have hh := h witness
  rw [witness_values.2.1, witness_values.2.2] at hh
  norm_num at hh

theorem W_ne_N : W ≠ N := by
  intro h
  have hh := congrFun h witness
  rw [witness_values.1, witness_norm] at hh
  norm_num at hh

theorem nonmultiplicative : ¬ ∀ p q : P, W (p * q) = W p * W q := by
  intro h
  apply self_square_fails
  intro p
  simpa only [pow_two] using h p p

/-- Literal multiplication supplies an algebraic process action. -/
def act (p s : P) : P := p * s

/-- Distinct initial coefficients act distinctly, as witnessed at the unit. -/
theorem act_injective : Function.Injective (fun p : P => act p) := by
  intro p q hpq
  have h := congrFun hpq (1 : P)
  simpa only [act, mul_one] using h

theorem act_identity (s : P) : act 1 s = s := one_mul s

theorem act_serial (p q s : P) : act (p * q) s = act p (act q s) :=
  mul_assoc p q s

theorem act_coherent_addition (p q s : P) :
    act (p + q) s = act p s + act q s := add_mul p q s

theorem act_input_addition (p s t : P) :
    act p (s + t) = act p s + act p t := mul_add p s t

/-- Exact action composition coexists with failure of response self-squaring. -/
theorem process_square_countercontrol :
    (∀ p s : P, act (p ^ 2) s = act p (act p s)) ∧
      W (act (witness ^ 2) 1) ≠ (W (act witness 1)) ^ 2 := by
  constructor
  · intro p s
    simpa only [pow_two] using act_serial p p s
  · simp only [act, mul_one]
    rw [witness_values.2.1, witness_values.2.2]
    norm_num

end
end IDT.QMClosure.InitialDyadicDetectorCountermodel
