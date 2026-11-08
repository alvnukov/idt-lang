import Proofs.QMClosure.PairComparisonReconstruction
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Rigidity of an exact fixed finite-outcome affinity representation

A normalized nonnegative law on one fixed finite outcome domain cannot give
the exact, everywhere positive logarithmic-affinity comparison of a nontrivial
pair-comparison reconstruction. The raw preparation carrier may be infinite.
The repeated preparations used below come from the derived quotient addition.
No preparation addition, boundedness, or Hilbert completeness is a premise.

This is a universal mathematical obstruction for an exact full-carrier family.
It makes no claim about detector origin, ordinary finite experiments, or QM
closure, and supplies no common-channel or physical-availability premise.
-/

namespace IDT.QMClosure.FiniteOutcomeAffinityRigidity

noncomputable section

open scoped BigOperators

universe u v

/-- Classical affinity of two finite nonnegative laws. -/
def affinity {Ω : Type v} [Fintype Ω] (p q : Ω → ℝ) : ℝ :=
  ∑ ω, Real.sqrt (p ω * q ω)

/-- Every normalized row has a coordinate at least the reciprocal cardinality. -/
theorem exists_large_coordinate {Ω : Type v} [Fintype Ω] [Nonempty Ω]
    (p : Ω → ℝ) (hp : ∑ ω, p ω = 1) :
    ∃ ω, (Fintype.card Ω : ℝ)⁻¹ ≤ p ω := by
  classical
  have hm : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hs : (∑ _ω : Ω, (Fintype.card Ω : ℝ)⁻¹) = 1 := by
    simp [ne_of_gt hm]
  obtain ⟨ω, _, hω⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty
    (show (∑ _ω : Ω, (Fintype.card Ω : ℝ)⁻¹) ≤ ∑ ω, p ω by rw [hs, hp])
  exact ⟨ω, hω⟩

/-- In one more row than outcomes, two distinct rows have affinity at least 1/m. -/
theorem finite_affinity_packing {Ω : Type v} [Fintype Ω] [Nonempty Ω]
    (p : Fin (Fintype.card Ω + 1) → Ω → ℝ)
    (hpos : ∀ i ω, 0 ≤ p i ω) (hnorm : ∀ i, ∑ ω, p i ω = 1) :
    ∃ i j, i ≠ j ∧ (Fintype.card Ω : ℝ)⁻¹ ≤ affinity (p i) (p j) := by
  classical
  choose f hf using fun i => exists_large_coordinate (p i) (hnorm i)
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  refine ⟨i, j, hij, ?_⟩
  have hc : 0 ≤ (Fintype.card Ω : ℝ)⁻¹ := by positivity
  have hj : (Fintype.card Ω : ℝ)⁻¹ ≤ p j (f i) := by simpa [heq] using hf j
  have hmul := mul_le_mul (hf i) hj hc (hpos i (f i))
  have hsqrt := Real.sqrt_le_sqrt hmul
  rw [Real.sqrt_mul_self hc] at hsqrt
  apply hsqrt.trans
  exact Finset.single_le_sum (fun ω _ => Real.sqrt_nonneg (p i ω * p j ω))
    (Finset.mem_univ (f i))

/-- Affinity one forces equality of the normalized nonnegative rows. -/
theorem law_eq_of_affinity_one {Ω : Type v} [Fintype Ω] (p q : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω)
    (hnp : ∑ ω, p ω = 1) (hnq : ∑ ω, q ω = 1)
    (ha : affinity p q = 1) : p = q := by
  classical
  have hsum : (∑ ω, (Real.sqrt (p ω) - Real.sqrt (q ω)) ^ 2) = 0 := by
    calc
      _ = (∑ ω, p ω) + (∑ ω, q ω) - 2 * affinity p q := by
        simp only [affinity, Finset.mul_sum, ← Finset.sum_add_distrib,
          ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro ω _
        rw [Real.sqrt_mul (hp ω)]
        nlinarith [Real.sq_sqrt (hp ω), Real.sq_sqrt (hq ω)]
      _ = 0 := by rw [hnp, hnq, ha]; norm_num
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun ω (_ : ω ∈ Finset.univ) => sq_nonneg (Real.sqrt (p ω) - Real.sqrt (q ω)))).mp hsum
  funext ω
  have heq : Real.sqrt (p ω) = Real.sqrt (q ω) :=
    sub_eq_zero.mp (sq_eq_zero_iff.mp (hz ω (Finset.mem_univ _)))
  have hs := congrArg (fun t : ℝ => t ^ 2) heq
  simpa only [Real.sq_sqrt (hp ω), Real.sq_sqrt (hq ω)] using hs

variable {V : Type u} {Ω : Type v} [Fintype Ω]

/-- Every natural multiple of a feature has a raw representative, by derived addition. -/
theorem exists_feature_nat_multiple (D : PairComparisonReconstruction.Contract V)
    (x : V) (n : ℕ) : ∃ z : V, D.feature z = (n : ℝ) • D.feature x := by
  let d := D.observedData.quotientData
  let q : ℕ → D.observedData.Space :=
    Nat.rec d.chosenZero (fun _ y => d.addition y (D.observedData.classOf x))
  have hn (n : ℕ) : d.feature (q n) =
      (n : ℝ) • D.feature x := by
    induction n with
    | zero => simpa [q] using d.feature_zero
    | succ n ih =>
      change d.feature (d.addition (q n) (D.observedData.classOf x)) = _
      rw [d.feature_add, ih]
      simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
      rfl
  obtain ⟨z, hz⟩ := Quotient.exists_rep (q n)
  change D.observedData.classOf z = q n at hz
  refine ⟨z, ?_⟩
  change d.feature (D.observedData.classOf z) = _
  rw [hz]
  exact hn n

/-- Exact finite-outcome logarithmic affinity forces every feature to vanish.
This algebraic conclusion also allows zero overlap under Lean's totalized log.
Equality of laws below separately requires strictly positive affinity. -/
theorem feature_eq_zero (D : PairComparisonReconstruction.Contract V)
    (K : V → Ω → ℝ) (hK : ∀ x ω, 0 ≤ K x ω)
    (hnorm : ∀ x, ∑ ω, K x ω = 1)
    (hcomparison : ∀ x y, D.comparison x y = -Real.log (affinity (K x) (K y)))
    (x : V) : D.feature x = 0 := by
  classical
  have hnΩ : Nonempty Ω := by
    by_contra hempty
    haveI : IsEmpty Ω := not_nonempty_iff.mp hempty
    have := hnorm D.chosenZero
    simp at this
  letI : Nonempty Ω := hnΩ
  have hm : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  by_contra hx
  have hq : 0 < ‖D.feature x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (Real.log (Fintype.card Ω) / ‖D.feature x‖ ^ 2))
  have hN1 : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hNlog : Real.log (Fintype.card Ω) < (N : ℝ) * ‖D.feature x‖ ^ 2 :=
    (div_lt_iff₀ hq).mp ((le_max_right _ _).trans_lt hN)
  have hNlarge : Real.log (Fintype.card Ω) < (N : ℝ) ^ 2 * ‖D.feature x‖ ^ 2 := by
    have hs : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    exact hNlog.trans_le (mul_le_mul_of_nonneg_right hs hq.le)
  choose z hz using fun i : Fin (Fintype.card Ω + 1) =>
    exists_feature_nat_multiple D x (i.val * N)
  obtain ⟨i, j, hij, ha⟩ := finite_affinity_packing (fun i => K (z i))
    (fun i => hK (z i)) (fun i => hnorm (z i))
  have hsep : (1 : ℝ) ≤ ((i.val : ℝ) - (j.val : ℝ)) ^ 2 := by
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hord : i.val + 1 ≤ j.val ∨ j.val + 1 ≤ i.val := by omega
    rcases hord with h | h
    · have hh : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast h
      nlinarith [sq_nonneg ((i.val : ℝ) - (j.val : ℝ) + 1)]
    · have hh : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast h
      nlinarith [sq_nonneg ((i.val : ℝ) - (j.val : ℝ) - 1)]
  have hdist : (N : ℝ) ^ 2 * ‖D.feature x‖ ^ 2 ≤ D.comparison (z i) (z j) := by
    rw [D.comparison_eq_norm_sub_sq, hz i, hz j, ← sub_smul, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    simp only [Nat.cast_mul]
    calc
      _ ≤ (((i.val : ℝ) - (j.val : ℝ)) ^ 2 * (N : ℝ) ^ 2) * ‖D.feature x‖ ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hsep
          (mul_nonneg (sq_nonneg (N : ℝ)) (sq_nonneg ‖D.feature x‖))]
      _ = _ := by ring
  have hlog := Real.log_le_log (inv_pos.mpr hm) ha
  rw [Real.log_inv] at hlog
  rw [hcomparison] at hdist
  linarith

/-- The represented comparison vanishes identically. -/
theorem comparison_eq_zero (D : PairComparisonReconstruction.Contract V)
    (K : V → Ω → ℝ) (hK : ∀ x ω, 0 ≤ K x ω)
    (hnorm : ∀ x, ∑ ω, K x ω = 1)
    (hcomparison : ∀ x y, D.comparison x y = -Real.log (affinity (K x) (K y)))
    (x y : V) : D.comparison x y = 0 := by
  rw [D.comparison_eq_norm_sub_sq, feature_eq_zero D K hK hnorm hcomparison x,
    feature_eq_zero D K hK hnorm hcomparison y]
  simp

/-- Every contextual observation class coincides in the reconstructed quotient. -/
theorem observed_quotient_subsingleton (D : PairComparisonReconstruction.Contract V)
    (K : V → Ω → ℝ) (hK : ∀ x ω, 0 ≤ K x ω)
    (hnorm : ∀ x, ∑ ω, K x ω = 1)
    (hcomparison : ∀ x y, D.comparison x y = -Real.log (affinity (K x) (K y))) :
    Subsingleton D.observedData.Space := by
  refine ⟨fun a b => Quotient.inductionOn₂ a b ?_⟩
  intro x y
  apply Quotient.sound
  apply (D.feature_eq_iff_observationalEq x y).mp
  rw [feature_eq_zero D K hK hnorm hcomparison x,
    feature_eq_zero D K hK hnorm hcomparison y]

/-- All normalized laws coincide on the entire raw carrier. -/
theorem all_laws_equal (D : PairComparisonReconstruction.Contract V)
    (K : V → Ω → ℝ) (hK : ∀ x ω, 0 ≤ K x ω)
    (hnorm : ∀ x, ∑ ω, K x ω = 1)
    (hpositive : ∀ x y, 0 < affinity (K x) (K y))
    (hcomparison : ∀ x y, D.comparison x y = -Real.log (affinity (K x) (K y)))
    (x y : V) : K x = K y := by
  have hzero := comparison_eq_zero D K hK hnorm hcomparison x y
  have hlog : Real.log (affinity (K x) (K y)) = 0 := by
    rw [hcomparison] at hzero
    linarith
  have ha : affinity (K x) (K y) = 1 := by
    rcases Real.log_eq_zero.mp hlog with h | h | h
    · exact False.elim ((ne_of_gt (hpositive x y)) h)
    · exact h
    · linarith [hpositive x y]
  exact law_eq_of_affinity_one (K x) (K y) (hK x) (hK y) (hnorm x) (hnorm y) ha

end

end IDT.QMClosure.FiniteOutcomeAffinityRigidity
