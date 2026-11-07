import Proofs.QMClosure.NativeBinaryPhaseCounting

/-!
# Signed phase-count variation

These statements concern arbitrary real weights and exact finite mass
identities. A bound across all depths is an explicit analytic hypothesis;
no physical budget, positivity, or actualization is supplied by this module.
-/

namespace IDT.QMClosure.NativeSignedPhaseVariation

noncomputable section
open NativeBinaryPhaseCounting
open scoped BigOperators

def variation (k : ℕ) (q : Fin 4 → ℝ) : ℝ :=
  ∑ j, realCount (4*k+1) j * |q j|

/-- The finite-depth deviation is controlled by signed total variation. -/
theorem mass_deviation_mul_bound (k : ℕ) (hk : 1 ≤ k)
    (q : Fin 4 → ℝ) (p r : ℝ)
    (hp : ∑ j, realCount (4*k+1) j * q j = p)
    (hr : ∑ j, realCount (4*k) j * q j = r) :
    2*((4 : ℝ)^k-1)*|r-p/2| ≤ variation k q := by
  let M : ℝ := (4 : ℝ)^k
  have hM : 1 < M := by
    have h := nat_add_one_le_four_pow k
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    dsimp [M]
    linarith
  have hlow : M*(M-1)/2 * (∑ j, |q j|) ≤ variation k q := by
    calc
      _ = ∑ j, (M*(M-1)/2) * |q j| := Finset.mul_sum _ _ _
      _ ≤ ∑ j, realCount (4*k+1) j * |q j| :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right
          (coefficient_lower k hk j) (abs_nonneg (q j)))
      _ = variation k q := rfl
  have herr : |r-p/2| ≤ M/4 * (∑ j, |q j|) := by
    calc
      |r-p/2| = |∑ j, (realCount (4*k) j - realCount (4*k+1) j / 2) * q j| := by
        congr 1
        rw [← hr, ← hp]
        simp only [sub_mul, div_mul_eq_mul_div, Finset.sum_sub_distrib,
          Finset.sum_div]
      _ ≤ ∑ j, |(realCount (4*k) j - realCount (4*k+1) j / 2) * q j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, (M/4) * |q j| := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (coefficient_deviation k hk j)
          (abs_nonneg (q j))
      _ = M/4 * (∑ j, |q j|) := (Finset.mul_sum _ _ _).symm
  have hmul := mul_le_mul_of_nonneg_left herr (by linarith : 0 ≤ 2*(M-1))
  change 2*(M-1)*|r-p/2| ≤ variation k q
  nlinarith

/-- A single finite upper bound at every required depth forces exact halving. -/
theorem phase_count_mass_halving_of_bounded_variation (p r C : ℝ)
    (h : ∀ k : ℕ, 1 ≤ k → ∃ q : Fin 4 → ℝ,
      (∑ j, realCount (4*k+1) j * q j) = p ∧
      (∑ j, realCount (4*k) j * q j) = r ∧ variation k q ≤ C) : r = p/2 := by
  by_contra he
  have hd : 0 < |r-p/2| := abs_pos.mpr (sub_ne_zero.mpr he)
  obtain ⟨n, hn⟩ := exists_nat_gt (C / (2*|r-p/2|))
  have hC : C < (n : ℝ) * (2*|r-p/2|) :=
    (div_lt_iff₀ (by positivity : 0 < 2*|r-p/2|)).mp hn
  obtain ⟨q, hp, hr, hV⟩ := h (n+1) (by omega)
  have hb := mass_deviation_mul_bound (n+1) (by omega) q p r hp hr
  have hpow := nat_add_one_le_four_pow (n+1)
  push_cast at hpow
  have hmul := mul_le_mul_of_nonneg_right hpow (le_of_lt hd)
  nlinarith

end
end IDT.QMClosure.NativeSignedPhaseVariation
