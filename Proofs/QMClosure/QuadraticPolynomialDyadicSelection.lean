import Proofs.QMClosure.FiniteDifferencePolynomial
import Mathlib.Algebra.BigOperators.Fin

/-!
# Dyadic and quarter-turn selection of a bivariate quadratic polynomial

A supplied polynomial representation, integer-lattice doubling with factor four,
and quarter-turn invariance determine a scalar multiple of the sum of squares.
The scalar is the value at `(1, 0)`. The zero polynomial is included.
-/

noncomputable section

namespace IDT.TranslationRankGap

open MvPolynomial

private def exponentPair (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b

private theorem exponentPair_coordinates (d : Fin 2 →₀ ℕ) :
    exponentPair (d 0) (d 1) = d := by
  ext i
  fin_cases i <;> simp [exponentPair]

private theorem monomial_fin_two (d : Fin 2 →₀ ℕ) (a : ℂ) :
    monomial d a =
      C a * (X 0 : MvPolynomial (Fin 2) ℂ) ^ d 0 * X 1 ^ d 1 := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_pow, Fin.prod_univ_two]
  ring

private def dyadicSubstitution (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial (Fin 2) ℂ :=
  eval₂ C (fun i => C 2 * X i) P

private theorem dyadicSubstitution_monomial (d : Fin 2 →₀ ℕ) (a : ℂ) :
    dyadicSubstitution (monomial d a) =
      monomial d ((2 : ℂ) ^ (d 0 + d 1) * a) := by
  simp only [dyadicSubstitution, monomial_fin_two, eval₂_mul,
    eval₂_C, eval₂_pow, eval₂_X, mul_pow, map_mul, map_pow, pow_add]
  ring

private theorem coeff_dyadicSubstitution
    (P : MvPolynomial (Fin 2) ℂ) (d : Fin 2 →₀ ℕ) :
    coeff d (dyadicSubstitution P) =
      (2 : ℂ) ^ (d 0 + d 1) * coeff d P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial e a =>
      rw [dyadicSubstitution_monomial]
      by_cases h : e = d
      · subst e
        simp
      · simp [h]
  | add P Q ihP ihQ =>
      simp only [dyadicSubstitution, eval₂_add, coeff_add] at ihP ihQ ⊢
      rw [ihP, ihQ, mul_add]

private theorem eval_dyadicSubstitution
    (P : MvPolynomial (Fin 2) ℂ) (x : Fin 2 → ℂ) :
    eval x (dyadicSubstitution P) = eval (fun i => 2 * x i) P := by
  change eval x (eval₂ C (fun i => C 2 * X i) P) = _
  rw [← MvPolynomial.eval_assoc]
  simp only [Function.comp_def, map_mul, eval_C, eval_X]

private theorem dyadic_polynomial_identity
    (P : MvPolynomial (Fin 2) ℂ)
    (hscale : ∀ m n : ℤ,
      eval ![((2 * m : ℤ) : ℂ), ((2 * n : ℤ) : ℂ)] P =
        4 * eval ![(m : ℂ), (n : ℂ)] P) :
    dyadicSubstitution P = C 4 * P := by
  apply polynomial_unique_on_integer_lattice
  intro m n
  rw [eval_dyadicSubstitution, map_mul, eval_C]
  have hx :
      (fun i => (2 : ℂ) * ![(m : ℂ), (n : ℂ)] i) =
        ![((2 * m : ℤ) : ℂ), ((2 * n : ℤ) : ℂ)] := by
    funext i
    fin_cases i <;> simp
  rw [hx]
  exact hscale m n

private theorem coeff_eq_zero_of_degree_ne_two
    (P : MvPolynomial (Fin 2) ℂ)
    (hscale : ∀ m n : ℤ,
      eval ![((2 * m : ℤ) : ℂ), ((2 * n : ℤ) : ℂ)] P =
        4 * eval ![(m : ℂ), (n : ℂ)] P)
    (d : Fin 2 →₀ ℕ) (hd : d 0 + d 1 ≠ 2) : coeff d P = 0 := by
  have hcoeff := congrArg (coeff d) (dyadic_polynomial_identity P hscale)
  rw [coeff_dyadicSubstitution, coeff_C_mul] at hcoeff
  have hpow : (2 : ℂ) ^ (d 0 + d 1) ≠ 4 := by
    intro h
    have hnat : (2 : ℕ) ^ (d 0 + d 1) = 4 := by exact_mod_cast h
    have hnat' : (2 : ℕ) ^ (d 0 + d 1) = 2 ^ 2 := by
      change (2 : ℕ) ^ (d 0 + d 1) = 4
      exact hnat
    exact hd (Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)) hnat')
  have hzero : ((2 : ℂ) ^ (d 0 + d 1) - 4) * coeff d P = 0 := by
    linear_combination hcoeff
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hpow)

private theorem quadratic_form_of_coeff_vanish
    (P : MvPolynomial (Fin 2) ℂ)
    (hvanish : ∀ d : Fin 2 →₀ ℕ, d 0 + d 1 ≠ 2 → coeff d P = 0) :
    P = C (coeff (exponentPair 2 0) P) * X 0 ^ 2 +
      C (coeff (exponentPair 1 1) P) * (X 0 * X 1) +
      C (coeff (exponentPair 0 2) P) * X 1 ^ 2 := by
  classical
  have h11_20 : exponentPair 1 1 ≠ exponentPair 2 0 := by
    intro h
    have h0 := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
    norm_num [exponentPair] at h0
  have h02_20 : exponentPair 0 2 ≠ exponentPair 2 0 := by
    intro h
    have h0 := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
    norm_num [exponentPair] at h0
  have h02_11 : exponentPair 0 2 ≠ exponentPair 1 1 := by
    intro h
    have h0 := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
    norm_num [exponentPair] at h0
  have hform :
      C (coeff (exponentPair 2 0) P) * X 0 ^ 2 +
        C (coeff (exponentPair 1 1) P) * (X 0 * X 1) +
        C (coeff (exponentPair 0 2) P) * X 1 ^ 2 =
      monomial (exponentPair 2 0) (coeff (exponentPair 2 0) P) +
        monomial (exponentPair 1 1) (coeff (exponentPair 1 1) P) +
        monomial (exponentPair 0 2) (coeff (exponentPair 0 2) P) := by
    simp [monomial_fin_two, exponentPair, mul_assoc]
  rw [hform]
  apply MvPolynomial.ext
  intro d
  by_cases h20 : exponentPair 2 0 = d
  · subst d
    simp [h11_20, h02_20]
  by_cases h11 : exponentPair 1 1 = d
  · subst d
    simp [h20, h02_11]
  by_cases h02 : exponentPair 0 2 = d
  · subst d
    simp [h20, h11]
  have hd : d 0 + d 1 ≠ 2 := by
    intro hdegree
    have hcases :
        (d 0 = 2 ∧ d 1 = 0) ∨
          (d 0 = 1 ∧ d 1 = 1) ∨ (d 0 = 0 ∧ d 1 = 2) := by omega
    rcases hcases with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
    · apply h20
      simpa [h0, h1] using exponentPair_coordinates d
    · apply h11
      simpa [h0, h1] using exponentPair_coordinates d
    · apply h02
      simpa [h0, h1] using exponentPair_coordinates d
  simp [h20, h11, h02, hvanish d hd]

/--
Integer-lattice dyadic scaling and quarter-turn symmetry determine the entire
supplied polynomial, including its zero case.
-/
theorem polynomial_eq_scalar_norm_of_dyadic_rotation
    (P : MvPolynomial (Fin 2) ℂ)
    (hscale : ∀ m n : ℤ,
      eval ![((2 * m : ℤ) : ℂ), ((2 * n : ℤ) : ℂ)] P =
        4 * eval ![(m : ℂ), (n : ℂ)] P)
    (hrot : ∀ m n : ℤ,
      eval ![((-n : ℤ) : ℂ), (m : ℂ)] P =
        eval ![(m : ℂ), (n : ℂ)] P) :
    P = C (eval ![1, 0] P) * (X 0 ^ 2 + X 1 ^ 2) := by
  let A := coeff (exponentPair 2 0) P
  let B := coeff (exponentPair 1 1) P
  let D := coeff (exponentPair 0 2) P
  have hquad :
      P = C A * X 0 ^ 2 + C B * (X 0 * X 1) + C D * X 1 ^ 2 :=
    quadratic_form_of_coeff_vanish P (coeff_eq_zero_of_degree_ne_two P hscale)
  have hDA : D = A := by
    have h := hrot 1 0
    simpa [hquad] using h
  have hB : B = 0 := by
    have h := hrot 1 1
    simp [hquad] at h
    linear_combination (-1 / 2 : ℂ) * h
  have hA : eval ![1, 0] P = A := by simp [hquad]
  calc
    P = C A * X 0 ^ 2 + C B * (X 0 * X 1) + C D * X 1 ^ 2 := hquad
    _ = C (eval ![1, 0] P) * (X 0 ^ 2 + X 1 ^ 2) := by
      rw [hA, hB, hDA]
      simp
      ring

/-- Unit calibration fixes the remaining scalar in the entire polynomial. -/
theorem polynomial_eq_norm_of_dyadic_rotation_of_calibrated
    (P : MvPolynomial (Fin 2) ℂ)
    (hscale : ∀ m n : ℤ,
      eval ![((2 * m : ℤ) : ℂ), ((2 * n : ℤ) : ℂ)] P =
        4 * eval ![(m : ℂ), (n : ℂ)] P)
    (hrot : ∀ m n : ℤ,
      eval ![((-n : ℤ) : ℂ), (m : ℂ)] P =
        eval ![(m : ℂ), (n : ℂ)] P)
    (hcal : eval ![1, 0] P = 1) : P = X 0 ^ 2 + X 1 ^ 2 := by
  simpa [hcal] using polynomial_eq_scalar_norm_of_dyadic_rotation P hscale hrot

/--
A supplied global polynomial representation transfers the scalar norm selection
to the original integer-lattice function.
-/
theorem polynomial_readout_eq_scalar_norm_of_dyadic_rotation
    (f : IntegerLattice → ℂ) (P : MvPolynomial (Fin 2) ℂ)
    (hP : ∀ m n : ℤ, f (m, n) = eval ![(m : ℂ), (n : ℂ)] P)
    (hscale : ∀ z : IntegerLattice, f (z + z) = 4 * f z)
    (hrot : ∀ m n : ℤ, f (-n, m) = f (m, n)) :
    ∀ z : IntegerLattice,
      f z = f (1, 0) * ((z.1 : ℂ) ^ 2 + (z.2 : ℂ) ^ 2) := by
  have hs : ∀ m n : ℤ,
      eval ![((2 * m : ℤ) : ℂ), ((2 * n : ℤ) : ℂ)] P =
        4 * eval ![(m : ℂ), (n : ℂ)] P := by
    intro m n
    have hz : ((m, n) : IntegerLattice) + (m, n) = (2 * m, 2 * n) := by
      ext <;> simp <;> ring
    have h := hscale (m, n)
    rw [hz, hP, hP] at h
    exact h
  have hr : ∀ m n : ℤ,
      eval ![((-n : ℤ) : ℂ), (m : ℂ)] P =
        eval ![(m : ℂ), (n : ℂ)] P := by
    intro m n
    rw [← hP, ← hP]
    exact hrot m n
  have hpoly := polynomial_eq_scalar_norm_of_dyadic_rotation P hs hr
  rintro ⟨m, n⟩
  rw [hP m n, hP 1 0]
  conv_lhs => rw [hpoly]
  simp

/-- Unit calibration of the represented readout gives the normalized norm. -/
theorem polynomial_readout_eq_norm_of_dyadic_rotation_of_calibrated
    (f : IntegerLattice → ℂ) (P : MvPolynomial (Fin 2) ℂ)
    (hP : ∀ m n : ℤ, f (m, n) = eval ![(m : ℂ), (n : ℂ)] P)
    (hscale : ∀ z : IntegerLattice, f (z + z) = 4 * f z)
    (hrot : ∀ m n : ℤ, f (-n, m) = f (m, n))
    (hcal : f (1, 0) = 1) :
    ∀ z : IntegerLattice, f z = (z.1 : ℂ) ^ 2 + (z.2 : ℂ) ^ 2 := by
  simpa [hcal] using
    polynomial_readout_eq_scalar_norm_of_dyadic_rotation f P hP hscale hrot

end IDT.TranslationRankGap
