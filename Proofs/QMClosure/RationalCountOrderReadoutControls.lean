import Proofs.QMClosure.RationalCountOrderReadout

/-!
# Prime-family failure of universal count order

For every finite rational Gaussian evaluation set, the existing prime family
can agree with norm square there and retain its actual balanced echo. Its raw
response drops from count p to count p+1, exposing failure of the universal
count-order premise. The selected prime depends on the finite set.
-/

namespace IDT.QMClosure.RationalCountOrderReadoutControls

open RationalEchoRegularityControl RationalCountOrderReadout

noncomputable section

theorem valuation_prime_succ (p : ℕ) [Fact (Nat.Prime p)] :
    padicValRat p ((p : ℚ) + 1) = 0 := by
  have hp : Nat.Prime p := Fact.out
  have hpQ : 0 < (p : ℚ) := by exact_mod_cast hp.pos
  have hsum : (p : ℚ) + 1 ≠ 0 := ne_of_gt (by linarith)
  have hvals : padicValRat p (p : ℚ) ≠ padicValRat p (1 : ℚ) := by
    rw [padicValRat.self hp.one_lt, padicValRat.one]
    norm_num
  have he := padicValRat.add_eq_min (p := p) hsum (ne_of_gt hpQ) one_ne_zero hvals
  rw [padicValRat.self hp.one_lt, padicValRat.one] at he
  norm_num at he
  exact he

theorem weightAt_prime_succ (p : ℕ) [Fact (Nat.Prime p)] :
    weightAt p (((p + 1 : ℕ) : ℚ), 0) = ((p : ℝ) + 1) ^ 2 := by
  have hp : Nat.Prime p := Fact.out
  have hpQ : 0 < (p : ℚ) := by exact_mod_cast hp.pos
  have hsum : (p : ℚ) + 1 ≠ 0 := ne_of_gt (by linarith)
  have hnorm : normQ (((p + 1 : ℕ) : ℚ), 0) = ((p : ℚ) + 1) ^ 2 := by
    simp [normQ]
  have hv : padicValRat p (normQ (((p + 1 : ℕ) : ℚ), 0)) = 0 := by
    rw [hnorm, padicValRat.pow hsum, valuation_prime_succ]
    norm_num
  unfold weightAt qWeightAt
  rw [hv, zpow_zero, mul_one, hnorm]
  norm_cast

theorem weightAt_count_drop (p : ℕ) [Fact (Nat.Prime p)] (hp : 2 < p) :
    weightAt p (scalar (p + 1 : ℕ)) < weightAt p (scalar p) := by
  change weightAt p (((p + 1 : ℕ) : ℚ), 0) < weightAt p ((p : ℚ), 0)
  rw [weightAt_prime_succ, weightAt_real_prime]
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp
  have hstep : (p : ℝ) + 1 < (p : ℝ) ^ 2 := by nlinarith
  calc
    ((p : ℝ) + 1) ^ 2 < ((p : ℝ) ^ 2) ^ 2 :=
      (sq_lt_sq₀ (by linarith) (sq_nonneg _)).mpr hstep
    _ = (p : ℝ) ^ 4 := by ring

theorem prime_weight_not_count_order (p : ℕ) [Fact (Nat.Prime p)] (hp : 2 < p) :
    ¬ ∀ n : ℕ, weightAt p (scalar n) ≤ weightAt p (scalar (n + 1 : ℕ)) := by
  intro hcount
  exact (not_lt_of_ge (hcount p)) (weightAt_count_drop p hp)

/-- The finite-agreement prime retains its actual nondegenerate balanced
echo while violating the additional universal count-order schema. -/
theorem finite_agreement_with_count_violation (S : Finset Carrier) :
    ∃ p : ℕ, p.Prime ∧ 2 < p ∧
      (∀ z ∈ S, weightAt p z = (normQ z : ℝ)) ∧
      balanced ≠ (0, 0) ∧ weightAt p balanced = 1 / 2 ∧
      weightAt p balanced + weightAt p balanced = 1 ∧
      weightAt p (gmul balanced (gconj balanced) + gmul balanced (gconj balanced)) = 1 ∧
      ¬ ∀ n : ℕ, weightAt p (scalar n) ≤ weightAt p (scalar (n + 1 : ℕ)) := by
  obtain ⟨p, hp, hpgt, hmatch, hbal, hhalf, hnorm, he, _, _⟩ := finite_readout_wall S
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  exact ⟨p, hp, hpgt, hmatch, hbal, hhalf, hnorm, he,
    prime_weight_not_count_order p hpgt⟩

end

end IDT.QMClosure.RationalCountOrderReadoutControls
