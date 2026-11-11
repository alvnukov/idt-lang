import Mathlib

/-!
An integer reciprocal-cross count identity has exactly two normalized solutions.
All conclusions concern real sequences. No sign or continuity is assumed here.
-/

noncomputable section

namespace IDT.QMClosure.IntegerReciprocalCountClassification

def Recurrence (d : ℕ) (g : ℕ → ℝ) : Prop :=
  ∀ n k, g (d * n + k) + g k = 2 * g n + 2 * g (n + k)

/-- Four finite instances eliminate the shift by d. -/
theorem second_difference {d : ℕ} {g : ℕ → ℝ}
    (h1 : g 1 = 1 / 2) (h : Recurrence d g) (k : ℕ) :
    g (k + 2) - 2 * g (k + 1) + g k = g 2 - 1 := by
  have e0 := h 1 k
  have e1 := h 1 (k + 1)
  have ed := h 1 (k + d)
  have e2 := h 2 k
  simp only [Nat.mul_one, Nat.mul_two] at e0 e1 ed e2
  rw [h1] at e0 e1 ed
  have p0 : 1 + k = k + 1 := by omega
  have p1 : 1 + (k + 1) = k + 2 := by omega
  have pd : 1 + (k + d) = d + (k + 1) := by omega
  have p2 : 2 + k = k + 2 := by omega
  have pdd : d + (k + d) = (d + d) + k := by omega
  rw [p0] at e0
  rw [p1] at e1
  rw [pd, pdd] at ed
  have pkd : k + d = d + k := by omega
  rw [pkd] at ed
  rw [p2] at e2
  linarith

/-- Finite second differences determine the complete sequence. -/
theorem polynomial_formula {d : ℕ} {g : ℕ → ℝ}
    (h0 : g 0 = 0) (h1 : g 1 = 1 / 2) (h : Recurrence d g) (k : ℕ) :
    g k = ((g 2 - 1) * (k : ℝ) ^ 2 + (2 - g 2) * (k : ℝ)) / 2 := by
  let F : ℕ → ℝ := fun n =>
    ((g 2 - 1) * (n : ℝ) ^ 2 + (2 - g 2) * (n : ℝ)) / 2
  have hF0 : F 0 = 0 := by dsimp [F]; ring
  have hF1 : F 1 = 1 / 2 := by dsimp [F]; norm_num
  have hF : ∀ n, F (n + 2) - 2 * F (n + 1) + F n = g 2 - 1 := by
    intro n
    dsimp [F]
    push_cast
    ring
  have hp : ∀ n, g n = F n ∧ g (n + 1) = F (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨h0.trans hF0.symm, by simpa using h1.trans hF1.symm⟩
    | succ n ih =>
        refine ⟨by simpa only [Nat.succ_eq_add_one] using ih.2, ?_⟩
        have hg := second_difference h1 h n
        have hf := hF n
        have he : g (n + 2) = F (n + 2) := by linarith [ih.1, ih.2]
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using he
  exact (hp k).1

/-- This disjunction is exhaustive for every natural d, including zero and one. -/
theorem classification {d : ℕ} {g : ℕ → ℝ}
    (h0 : g 0 = 0) (h1 : g 1 = 1 / 2) (h : Recurrence d g) :
    (d = 2 ∧ ∀ n, g n = (n : ℝ) ^ 2 / 2) ∨
      (d = 4 ∧ ∀ n, g n = (n : ℝ) / 2) := by
  have hd0 : g d = 2 := by
    have he := h 1 0
    norm_num [h0, h1] at he
    exact he
  have hd1 : g (d + 1) = 1 / 2 + 2 * g 2 := by
    have he := h 1 1
    simp only [Nat.mul_one] at he
    rw [h1] at he
    linarith
  have f0 := polynomial_formula h0 h1 h d
  have f1 := polynomial_formula h0 h1 h (d + 1)
  push_cast at f1
  have hf : ((d : ℝ) - 2) * (g 2 - 1) = 0 := by
    nlinarith
  by_cases hd : d = 2
  · have ht : g 2 = 2 := by simpa [hd] using hd0
    left
    refine ⟨hd, fun n => ?_⟩
    rw [polynomial_formula h0 h1 h n, ht]
    ring
  · have hdn : (d : ℝ) - 2 ≠ 0 := by
      intro he
      have he' : (d : ℝ) = 2 := by linarith
      exact hd (by exact_mod_cast he')
    have ht : g 2 = 1 := by
      have he := (mul_eq_zero.mp hf).resolve_left hdn
      linarith
    have hd4 : d = 4 := by
      rw [ht] at f0
      have he : (d : ℝ) = 4 := by nlinarith
      exact_mod_cast he
    right
    refine ⟨hd4, fun n => ?_⟩
    rw [polynomial_formula h0 h1 h n, ht]
    ring

theorem quadratic_iff_finite_contrast {d : ℕ} {g : ℕ → ℝ}
    (h0 : g 0 = 0) (h1 : g 1 = 1 / 2) (h : Recurrence d g) :
    g 2 ≠ 1 ↔ d = 2 ∧ ∀ n, g n = (n : ℝ) ^ 2 / 2 := by
  obtain hq | hl := classification h0 h1 h
  · constructor
    · intro _; exact hq
    · intro _; norm_num [hq.2 2]
  · constructor
    · intro hc; exact False.elim (hc (by norm_num [hl.2 2]))
    · intro hq; omega

theorem linear_iff_unit_second_value {d : ℕ} {g : ℕ → ℝ}
    (h0 : g 0 = 0) (h1 : g 1 = 1 / 2) (h : Recurrence d g) :
    g 2 = 1 ↔ d = 4 ∧ ∀ n, g n = (n : ℝ) / 2 := by
  obtain hq | hl := classification h0 h1 h
  · constructor
    · intro hc
      have he := hq.2 2
      norm_num at he
      linarith
    · intro hl; omega
  · constructor
    · intro _; exact hl
    · intro _; norm_num [hl.2 2]

theorem cubic_impossible {g : ℕ → ℝ}
    (h0 : g 0 = 0) (h1 : g 1 = 1 / 2) (h : Recurrence 3 g) : False := by
  obtain hq | hl := classification h0 h1 h <;> omega

end IDT.QMClosure.IntegerReciprocalCountClassification
