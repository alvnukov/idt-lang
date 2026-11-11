import Proofs.QMClosure.SemiringReciprocalCrossClassification
import Mathlib.Data.Complex.Basic

/-!
A complex-valued mathematical witness for the complete selected reciprocal-cross
contract. The squared norm readout is explicitly supplied. This construction
establishes nonvacuity of the conditional algebraic contract.
-/

noncomputable section

namespace IDT.QMClosure.ReciprocalCrossQuadraticWitness

open SemiringReciprocalCrossClassification CountCrossIncrementRigidity

def A : ℂ := (1 + Complex.I) / 2

def B : ℂ := (1 - Complex.I) / 2

def W (z : ℂ) : ℝ := Complex.normSq z

theorem conjugate_pair : B = star A := by
  simp [A, B, sub_eq_add_neg]

theorem halfA_value : W A = 1 / 2 := by
  norm_num [A, W, Complex.normSq_div, Complex.normSq_apply]

theorem halfB_value : W B = 1 / 2 := by
  norm_num [B, W, Complex.normSq_div, Complex.normSq_apply]

theorem laws : Laws A B 2 W := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [A, B]
    ring
  · dsimp [A, B]
    have hi : Complex.I ^ 2 = -1 := Complex.I_sq
    calc
      _ = (1 - Complex.I ^ 2) / 2 := by ring
      _ = 1 := by rw [hi]; norm_num
  · exact Complex.normSq_one
  · intro p
    change Complex.normSq (A * p) = Complex.normSq p / 2
    rw [Complex.normSq_mul]
    change W A * W p = W p / 2
    rw [halfA_value]
    ring
  · intro p
    change Complex.normSq (B * p) = Complex.normSq p / 2
    rw [Complex.normSq_mul]
    change W B * W p = W p / 2
    rw [halfB_value]
    ring

theorem nonnegative (z : ℂ) : 0 ≤ W z := Complex.normSq_nonneg z

theorem faithful (z : ℂ) (h : W z = 0) : z = 0 := Complex.normSq_eq_zero.mp h

theorem count_value (n m : ℕ) :
    grid A B W n m = ((n : ℝ) ^ 2 + (m : ℝ) ^ 2) / 2 := by
  dsimp [grid, bag, W]
  rw [Complex.normSq_apply]
  simp [A, B]
  ring

theorem mixed_zero (n m : ℕ) : mixed (grid A B W) n m = 0 := by
  dsimp [mixed]
  rw [count_value, count_value, count_value, count_value]
  push_cast
  ring

theorem uniform_sign : UniformMixedSign A B W := by
  left
  intro n m
  rw [mixed_zero]

theorem finite_contrast : W ((2 : ℂ) * A) ≠ W 1 := by
  have he := count_value 2 0
  have hv : W ((2 : ℂ) * A) = 2 := by
    norm_num [grid, bag] at he
    exact he
  rw [hv]
  norm_num [W]

theorem selected_destructive_witness :
    (2 : ℕ) = 2 ∧ A ^ 2 + B ^ 2 = 0 ∧ (4 : ℂ) * A ^ 4 + 1 = 0 :=
  selected_destructive laws uniform_sign finite_contrast faithful

theorem additive_inverse_witness (z : ℂ) : ∃ y : ℂ, z + y = 0 :=
  additive_inverse_exists_of_faithful laws faithful z

end IDT.QMClosure.ReciprocalCrossQuadraticWitness
