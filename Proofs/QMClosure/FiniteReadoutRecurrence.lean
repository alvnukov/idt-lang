import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Monic

/-!
# Polynomial recurrences of finite linear readouts

Polynomial evaluation at the forward shift gives actual sequence recurrences.
Cayley--Hamilton supplies an annihilator of each fixed finite matrix readout;
a monic annihilator makes the first `natDegree` values determine the sequence.
These are algebraic statements, with no stochastic or physical interpretation.
-/

namespace IDT.QMClosure.FiniteReadoutRecurrence

open Polynomial Finset

noncomputable section

variable {K : Type*} [CommRing K]

/-- The forward shift on scalar sequences. -/
def shift : Module.End K (ℕ → K) where
  toFun u n := u (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A polynomial acts on a sequence by evaluating at the forward shift. -/
def applyPolynomial (p : K[X]) (u : ℕ → K) : ℕ → K :=
  (aeval (shift : Module.End K (ℕ → K)) p) u

@[simp] theorem shift_pow_apply (k : ℕ) (u : ℕ → K) (n : ℕ) :
    ((shift : Module.End K (ℕ → K)) ^ k) u n = u (n + k) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ']
      change ((shift : Module.End K (ℕ → K)) ^ k) u (n + 1) = _
      rw [ih]
      congr 1
      omega

@[simp] theorem applyPolynomial_add (p q : K[X]) (u : ℕ → K) :
    applyPolynomial (p + q) u = applyPolynomial p u + applyPolynomial q u := by
  simp [applyPolynomial]

@[simp] theorem applyPolynomial_mul (p q : K[X]) (u : ℕ → K) :
    applyPolynomial (p * q) u = applyPolynomial p (applyPolynomial q u) := by
  simp [applyPolynomial, Module.End.mul_apply]

@[simp] theorem applyPolynomial_zero_sequence (p : K[X]) :
    applyPolynomial p (0 : ℕ → K) = 0 := by
  simp [applyPolynomial]

@[simp] theorem applyPolynomial_C (c : K) (u : ℕ → K) (n : ℕ) :
    applyPolynomial (C c) u n = c * u n := by
  simp [applyPolynomial, Module.algebraMap_end_eq_smul_id]

@[simp] theorem applyPolynomial_X_pow (k : ℕ) (u : ℕ → K) (n : ℕ) :
    applyPolynomial (X ^ k) u n = u (n + k) := by
  simp [applyPolynomial]

theorem applyPolynomial_eq_sum (p : K[X]) (u : ℕ → K) (n : ℕ) :
    applyPolynomial p u n =
      ∑ k ∈ range (p.natDegree + 1), p.coeff k * u (n + k) := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow]
  simp [applyPolynomial, map_sum, Module.End.mul_apply,
    Module.algebraMap_end_eq_smul_id]

theorem applyPolynomial_const (p : K[X]) (c : K) :
    applyPolynomial p (fun _ => c) = fun _ => p.eval 1 * c := by
  funext n
  rw [applyPolynomial_eq_sum, Polynomial.eval_eq_sum_range]
  simp [sum_mul]

/-- A monic recurrence and zero initial window force the whole sequence to vanish. -/
theorem eq_zero_of_initial (p : K[X]) (hp : p.Monic) (u : ℕ → K)
    (hrec : applyPolynomial p u = 0)
    (hinit : ∀ n < p.natDegree, u n = 0) : u = 0 := by
  funext n
  change u n = 0
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < p.natDegree
      · exact hinit n hn
      · have hdn : p.natDegree ≤ n := le_of_not_gt hn
        have hr := congrFun hrec (n - p.natDegree)
        rw [applyPolynomial_eq_sum, sum_range_succ, hp.coeff_natDegree, one_mul] at hr
        have hs : ∑ k ∈ range p.natDegree,
            p.coeff k * u (n - p.natDegree + k) = 0 := by
          apply sum_eq_zero
          intro k hk
          rw [ih (n - p.natDegree + k) (by have := mem_range.mp hk; omega), mul_zero]
        simpa only [hs, zero_add, Nat.sub_add_cancel hdn, Pi.zero_apply] using hr

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The sequence of a fixed linear observation of matrix powers. -/
theorem applyPolynomial_matrix_powers (A : Matrix S S K)
    (L : Matrix S S K →ₗ[K] K) (p : K[X]) (n : ℕ) :
    applyPolynomial p (fun k => L (A ^ k)) n = L (A ^ n * aeval A p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [applyPolynomial_add, Pi.add_apply, map_add, mul_add, hp, hq]
  | monomial k c =>
      rw [← C_mul_X_pow_eq_monomial, applyPolynomial_mul, applyPolynomial_C,
        applyPolynomial_X_pow]
      simp [Algebra.algebraMap_eq_smul_one, pow_add]

/-- Cayley--Hamilton annihilates every fixed linear observation of matrix powers. -/
theorem charpoly_annihilates (A : Matrix S S K) (L : Matrix S S K →ₗ[K] K) :
    applyPolynomial A.charpoly (fun n => L (A ^ n)) = 0 := by
  funext n
  rw [applyPolynomial_matrix_powers, Matrix.aeval_self_charpoly]
  simp

end

end IDT.QMClosure.FiniteReadoutRecurrence
