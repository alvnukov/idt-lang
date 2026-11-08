import Proofs.QMClosure.NormalizedEchoReadout

namespace IDT.QMClosure.NormalizedEchoReadoutControls

open NormalizedEchoReadout

noncomputable section

/-- Nonzero-support indicator. Global continuity is deliberately absent. -/
def supportWeight (z : ℂ) : ℝ := if z = 0 then 0 else 1

theorem support_nonnegative (z : ℂ) : 0 ≤ supportWeight z := by
  unfold supportWeight
  split <;> norm_num

theorem support_multiplicative (z t : ℂ) :
    supportWeight (z * t) = supportWeight z * supportWeight t := by
  classical
  by_cases hz : z = 0 <;> by_cases ht : t = 0 <;>
    simp [supportWeight, hz, ht]

theorem support_conjugation (z : ℂ) : supportWeight (star z) = supportWeight z := by
  simp [supportWeight]

/-- Every normalized pair has exactly one nonzero branch. -/
theorem support_normalized_echo : NormalizedEcho supportWeight := by
  intro a b hab
  classical
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hb
      simp [supportWeight, ha, hb] at hab
    simp [ha, hb, supportWeight]
  · by_cases hb : b = 0
    · simp [ha, hb, supportWeight]
    · simp [supportWeight, ha, hb] at hab

theorem support_parallelogram_fails :
    supportWeight ((1 : ℂ) + 1) + supportWeight ((1 : ℂ) - 1) ≠
      2 * supportWeight 1 + 2 * supportWeight 1 := by
  norm_num [supportWeight]

/-- This control isolates continuity from the other global echo laws. -/
theorem support_discontinuous : ¬ Continuous supportWeight := by
  intro hc
  have h : WeightLaws supportWeight := {
    continuous := hc
    nonnegative := support_nonnegative
    zero := by simp [supportWeight]
    one := by simp [supportWeight]
    multiplicative := support_multiplicative
    conjugation := support_conjugation }
  exact support_parallelogram_fails (h.parallelogram support_normalized_echo 1 1)

/-- Continuous quartic raw weight. Only deterministic contexts are admitted
in the restricted echo control below. -/
def quarticWeight (z : ℂ) : ℝ := (Complex.normSq z)^2

theorem quartic_laws : WeightLaws quarticWeight where
  continuous := Complex.continuous_normSq.pow 2
  nonnegative z := sq_nonneg _
  zero := by simp [quarticWeight]
  one := by simp [quarticWeight]
  multiplicative z t := by simp [quarticWeight, Complex.normSq_mul, mul_pow]
  conjugation z := by simp [quarticWeight, Complex.normSq_conj]

/-- Every positive response level still has an actual real scalar preimage. -/
theorem quartic_positive_real_level {r : ℝ} (hr : 0 < r) :
    ∃ c : ℝ, 0 ≤ c ∧ quarticWeight (c : ℂ) = r := by
  refine ⟨Real.sqrt (Real.sqrt r), Real.sqrt_nonneg _, ?_⟩
  unfold quarticWeight
  rw [Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt (Real.sqrt_nonneg r),
    Real.sq_sqrt hr.le]

/-- Explicit restriction to a single unit-phase branch and a zero branch. -/
def DeterministicContext (a b : ℂ) : Prop :=
  (Complex.normSq a = 1 ∧ b = 0) ∨ (a = 0 ∧ Complex.normSq b = 1)

theorem deterministic_context_normalized {a b : ℂ} (hab : DeterministicContext a b) :
    quarticWeight a + quarticWeight b = 1 := by
  rcases hab with ⟨ha, rfl⟩ | ⟨rfl, hb⟩ <;> simp [quarticWeight, *]

theorem deterministic_context_echo {a b : ℂ} (hab : DeterministicContext a b) :
    quarticWeight (a * star a + b * star b) = 1 := by
  rcases hab with ⟨ha, rfl⟩ | ⟨rfl, hb⟩ <;>
    simp [quarticWeight, Complex.mul_conj, *]

theorem quartic_parallelogram_fails :
    quarticWeight ((1 : ℂ) + 1) + quarticWeight ((1 : ℂ) - 1) ≠
      2 * quarticWeight 1 + 2 * quarticWeight 1 := by
  norm_num [quarticWeight, Complex.normSq_apply]

/-- Restricted admitted echoes do not establish the full echo premise. -/
theorem quartic_not_normalized_echo : ¬ NormalizedEcho quarticWeight := by
  intro he
  exact quartic_parallelogram_fails (quartic_laws.parallelogram he 1 1)

end

end IDT.QMClosure.NormalizedEchoReadoutControls
