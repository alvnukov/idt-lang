import Proofs.QMClosure.AtomicitySpectralBoundary
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Nat.Choose.Sum

namespace IDT.QMClosure.ComplementaryPowerEnvelope

/-!
Complementary operators on one nontrivial normed carrier cannot have uniform
power-envelope rates whose sum is smaller than the complementary scalar's norm.
The argument uses commuting binomial powers and the existing scalar envelope
obstruction. No finite-dimensionality or completeness hypothesis is required.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [Nontrivial E]

omit [Nontrivial E] in
/-- Scalar complementarity forces the two operators to commute. -/
theorem complementary_commute (A B : E →L[𝕜] E) (c : 𝕜)
    (hcomp : A + B = c • ContinuousLinearMap.id 𝕜 E) : Commute A B := by
  have hc : Commute A (c • (1 : E →L[𝕜] E)) := by
    show A * (c • 1) = (c • 1) * A
    simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  have hb : B = c • (1 : E →L[𝕜] E) - A := by
    change B = c • ContinuousLinearMap.id 𝕜 E - A
    rw [← hcomp]
    abel
  rw [hb]
  exact hc.sub_right (Commute.refl A)

/-- A uniform envelope constant is nonnegative already at the zeroth power. -/
theorem envelope_constant_nonnegative (A : E →L[𝕜] E) (C q : ℝ)
    (h : ∀ n : ℕ, ‖A ^ n‖ ≤ C * q ^ n) : 0 ≤ C := by
  have hzero := h 0
  simp only [pow_zero, norm_one, mul_one] at hzero
  exact le_trans zero_le_one hzero

omit [Nontrivial E] in
/-- Commuting operators inherit the sum of their envelope rates. -/
theorem commuting_sum_power_bound (A B : E →L[𝕜] E)
    (CA CB qA qB : ℝ) (hcomm : Commute A B)
    (hA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * qA ^ n)
    (hB : ∀ n : ℕ, ‖B ^ n‖ ≤ CB * qB ^ n) (n : ℕ) :
    ‖(A + B) ^ n‖ ≤ CA * CB * (qA + qB) ^ n := by
  rw [hcomm.add_pow']
  calc
    ‖∑ m ∈ Finset.antidiagonal n, n.choose m.1 • (A ^ m.1 * B ^ m.2)‖ ≤
        ∑ m ∈ Finset.antidiagonal n, ‖n.choose m.1 • (A ^ m.1 * B ^ m.2)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.antidiagonal n,
        (n.choose m.1 : ℝ) * (CA * qA ^ m.1 * (CB * qB ^ m.2)) := by
      apply Finset.sum_le_sum
      intro m hm
      calc
        ‖n.choose m.1 • (A ^ m.1 * B ^ m.2)‖ ≤
            (n.choose m.1 : ℝ) * ‖A ^ m.1 * B ^ m.2‖ := norm_nsmul_le
        _ ≤ (n.choose m.1 : ℝ) * (CA * qA ^ m.1 * (CB * qB ^ m.2)) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact (norm_mul_le _ _).trans
            (mul_le_mul (hA m.1) (hB m.2) (norm_nonneg _)
              ((norm_nonneg _).trans (hA m.1)))
    _ = CA * CB * ∑ m ∈ Finset.antidiagonal n,
        (n.choose m.1 : ℝ) * (qA ^ m.1 * qB ^ m.2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = CA * CB * (qA + qB) ^ n := by
      congr 1
      symm
      simpa only [nsmul_eq_mul] using (Commute.all qA qB).add_pow' n

/-- The power norm of the scalar complementary sum on a nontrivial carrier. -/
theorem complementary_sum_power_norm (A B : E →L[𝕜] E) (c : 𝕜)
    (hcomp : A + B = c • ContinuousLinearMap.id 𝕜 E) (n : ℕ) :
    ‖(A + B) ^ n‖ = ‖c‖ ^ n := by
  rw [hcomp]
  change ‖(c • (1 : E →L[𝕜] E)) ^ n‖ = ‖c‖ ^ n
  simp [smul_pow, norm_smul, norm_pow]

/-- Both uniform envelopes and the scalar complement must hold on the same
nontrivial normed carrier. Their positive rates bound the scalar norm. -/
theorem complementary_operator_rate_bound (A B : E →L[𝕜] E) (c : 𝕜)
    (CA CB qA qB : ℝ) (hqA : 0 < qA) (hqB : 0 < qB)
    (hcomp : A + B = c • ContinuousLinearMap.id 𝕜 E)
    (hA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * qA ^ n)
    (hB : ∀ n : ℕ, ‖B ^ n‖ ≤ CB * qB ^ n) : ‖c‖ ≤ qA + qB := by
  have hcomm := complementary_commute A B c hcomp
  by_contra hbound
  apply AtomicitySpectralBoundary.power_envelope_impossible (add_pos hqA hqB)
    (lt_of_not_ge hbound)
  intro n
  rw [← complementary_sum_power_norm A B c hcomp n]
  exact commuting_sum_power_bound A B CA CB qA qB hcomm hA hB n

/-- Equal real rates bound the real complementary scalar by twice the rate. -/
theorem complementary_operator_equal_rate_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [Nontrivial F]
    (A B : F →L[ℝ] F) (c CA CB q : ℝ) (hq : 0 < q)
    (hcomp : A + B = c • ContinuousLinearMap.id ℝ F)
    (hA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * q ^ n)
    (hB : ∀ n : ℕ, ‖B ^ n‖ ≤ CB * q ^ n) : c ≤ 2 * q := by
  have h := complementary_operator_rate_bound A B c CA CB q q hq hq hcomp hA hB
  have hc : c ≤ ‖c‖ := le_abs_self c
  linarith

end IDT.QMClosure.ComplementaryPowerEnvelope
