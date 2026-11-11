import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Algebraic polynomial extraction from global coordinate differences

The hypotheses are global coordinate finite-difference annihilators on ℤ × ℤ.
The proof uses Lagrange interpolation and induction on the difference order.
It does not infer either annihilator from a finite-rank hypothesis.
-/

noncomputable section

namespace IDT.TranslationRankGap

open Finset Function

abbrev IntegerLattice := ℤ × ℤ

private theorem fwdDiff_iter_sub_int (f g : ℤ → ℂ) (d : ℕ) :
    (fwdDiff (1 : ℤ))^[d] (f - g) =
      (fwdDiff (1 : ℤ))^[d] f - (fwdDiff (1 : ℤ))^[d] g := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [Function.iterate_succ_apply', ih]
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      funext z
      simp only [fwdDiff, Pi.sub_apply]
      abel

/-- A globally shift-invariant integer sequence is determined by its value at zero. -/
private theorem integer_function_eq_zero_of_step
    (f : ℤ → ℂ) (hzero : f 0 = 0)
    (hstep : ∀ z : ℤ, f (z + 1) = f z) : f = 0 := by
  funext z
  change f z = 0
  induction z using Int.induction_on with
  | zero => exact hzero
  | succ z ih => exact (hstep z).trans ih
  | pred z ih =>
      have hz : -(z : ℤ) - 1 + 1 = -(z : ℤ) := by ring
      have hs := hstep (-(z : ℤ) - 1)
      rw [hz] at hs
      exact hs.symm.trans ih

/--
The first `d` values determine a globally order-`d` annihilated integer sequence.

The induction uses a global annihilator for the next difference. Its final
shift-invariance step covers both positive and negative integers.
-/
private theorem integer_function_eq_zero_of_fwdDiff
    (d : ℕ) (f : ℤ → ℂ)
    (hnil : (fwdDiff (1 : ℤ))^[d] f = 0)
    (hfirst : ∀ j : ℕ, j < d → f (j : ℤ) = 0) : f = 0 := by
  induction d generalizing f with
  | zero => simpa only [Function.iterate_zero, id_eq] using hnil
  | succ d ih =>
      have hnextnil :
          (fwdDiff (1 : ℤ))^[d] (fwdDiff (1 : ℤ) f) = 0 := by
        simpa only [Function.iterate_succ_apply] using hnil
      have hnextfirst :
          ∀ j : ℕ, j < d → fwdDiff (1 : ℤ) f (j : ℤ) = 0 := by
        intro j hj
        have hcast : (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) := by omega
        simp only [fwdDiff, hcast]
        rw [hfirst (j + 1) (by omega), hfirst j (by omega), sub_self]
      have hnext : fwdDiff (1 : ℤ) f = 0 :=
        ih (fwdDiff (1 : ℤ) f) hnextnil hnextfirst
      apply integer_function_eq_zero_of_step f (hfirst 0 (by omega))
      intro z
      exact sub_eq_zero.mp (congr_fun hnext z)

/-- Equality on `0, …, d - 1` propagates to the full integer line. -/
private theorem integer_function_eq_of_fwdDiff
    (d : ℕ) (f g : ℤ → ℂ)
    (hf : (fwdDiff (1 : ℤ))^[d] f = 0)
    (hg : (fwdDiff (1 : ℤ))^[d] g = 0)
    (hfirst : ∀ j : ℕ, j < d → f (j : ℤ) = g (j : ℤ)) : f = g := by
  apply sub_eq_zero.mp
  apply integer_function_eq_zero_of_fwdDiff d (f - g)
  · rw [fwdDiff_iter_sub_int, hf, hg, sub_self]
  · intro j hj
    exact sub_eq_zero.mpr (hfirst j hj)

/-- Forward differences commute with evaluation along the integer embedding. -/
private theorem fwdDiff_iter_eval_int
    (p : Polynomial ℂ) (d : ℕ) (z : ℤ) :
    (fwdDiff (1 : ℤ))^[d] (fun t : ℤ => p.eval (t : ℂ)) z =
      (fwdDiff (1 : ℂ))^[d] p.eval (z : ℂ) := by
  induction d generalizing z with
  | zero => rfl
  | succ d ih =>
      simp only [Function.iterate_succ_apply', fwdDiff]
      rw [ih, ih]
      simp

/-- A polynomial of degree below `d` has globally vanishing `d`th integer difference. -/
private theorem polynomial_integer_fwdDiff_eq_zero
    (p : Polynomial ℂ) (d : ℕ) (hp : p.degree < (d : WithBot ℕ)) :
    (fwdDiff (1 : ℤ))^[d] (fun z : ℤ => p.eval (z : ℂ)) = 0 := by
  by_cases hpzero : p = 0
  · subst p
    funext z
    simp [fwdDiff_iter_eq_sum_shift]
  · have hdegree : p.natDegree < d :=
      (Polynomial.natDegree_lt_iff_degree_lt hpzero).mpr hp
    have hpoly : (fwdDiff (1 : ℂ))^[d] p.eval = 0 :=
      Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdegree
    funext z
    rw [fwdDiff_iter_eval_int]
    exact congr_fun hpoly (z : ℂ)

private theorem natural_nodes_injective (d : ℕ) :
    Set.InjOn (fun j : ℕ => (j : ℂ)) (Finset.range d) := by
  intro a ha b hb hab
  change (a : ℂ) = (b : ℂ) at hab
  exact_mod_cast hab

/-- The interpolant uses the consecutive nodes `0, …, d - 1`. -/
private def integerInterpolant (d : ℕ) (f : ℤ → ℂ) : Polynomial ℂ :=
  Lagrange.interpolate (Finset.range d) (fun j : ℕ => (j : ℂ))
    (fun j : ℕ => f (j : ℤ))

/-- A global finite-difference annihilator gives polynomial evaluation on all of `ℤ`. -/
private theorem integerInterpolant_spec
    (d : ℕ) (f : ℤ → ℂ)
    (hnil : (fwdDiff (1 : ℤ))^[d] f = 0) (z : ℤ) :
    f z = (integerInterpolant d f).eval (z : ℂ) := by
  have hdegree : (integerInterpolant d f).degree < (d : WithBot ℕ) := by
    simpa only [integerInterpolant, Finset.card_range] using
      Lagrange.degree_interpolate_lt (fun j : ℕ => f (j : ℤ))
        (natural_nodes_injective d)
  have hinterp :
      (fwdDiff (1 : ℤ))^[d]
        (fun t : ℤ => (integerInterpolant d f).eval (t : ℂ)) = 0 :=
    polynomial_integer_fwdDiff_eq_zero _ d hdegree
  have heq : f = fun t : ℤ => (integerInterpolant d f).eval (t : ℂ) := by
    apply integer_function_eq_of_fwdDiff d f _ hnil hinterp
    intro j hj
    simpa only [integerInterpolant, Int.cast_natCast] using
      (Lagrange.eval_interpolate_at_node (fun k : ℕ => f (k : ℤ))
        (natural_nodes_injective d) (Finset.mem_range.mpr hj)).symm
  exact congr_fun heq z

/-- Restricting the coordinate difference to a horizontal line preserves every iterate. -/
private theorem horizontal_fwdDiff_iter
    (h : IntegerLattice → ℂ) (d : ℕ) (x y : ℤ) :
    (fwdDiff (1 : ℤ))^[d] (fun t : ℤ => h (t, y)) x =
      (fwdDiff ((1, 0) : IntegerLattice))^[d] h (x, y) := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih =>
      simp only [Function.iterate_succ_apply', fwdDiff]
      rw [ih, ih]
      simp

/-- Restricting the coordinate difference to a vertical line preserves every iterate. -/
private theorem vertical_fwdDiff_iter
    (h : IntegerLattice → ℂ) (e : ℕ) (x y : ℤ) :
    (fwdDiff (1 : ℤ))^[e] (fun t : ℤ => h (x, t)) y =
      (fwdDiff ((0, 1) : IntegerLattice))^[e] h (x, y) := by
  induction e generalizing y with
  | zero => rfl
  | succ e ih =>
      simp only [Function.iterate_succ_apply', fwdDiff]
      rw [ih, ih]
      simp

/-- Regard a univariate polynomial as a polynomial in the selected coordinate. -/
private def coordinatePolynomial (i : Fin 2) (p : Polynomial ℂ) :
    MvPolynomial (Fin 2) ℂ :=
  p.eval₂ MvPolynomial.C (MvPolynomial.X i)

private theorem eval_coordinatePolynomial
    (i : Fin 2) (p : Polynomial ℂ) (x : Fin 2 → ℂ) :
    MvPolynomial.eval x (coordinatePolynomial i p) = p.eval (x i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [coordinatePolynomial, Polynomial.eval₂_add, map_add,
        Polynomial.eval_add] at hp hq ⊢
      rw [hp, hq]
  | monomial n a =>
      simp [coordinatePolynomial, Polynomial.eval₂_monomial, Polynomial.eval_monomial]

/--
Two global coordinate annihilators suffice for a polynomial representation on `ℤ²`.

The proof first interpolates each horizontal line, then replaces each of its
finitely many coefficient slices by a vertical interpolant. The zero-order
cases are included through the empty interpolation set.
-/
theorem exists_polynomial_of_coordinate_fwdDiff_eq_zero
    (h : IntegerLattice → ℂ) (d e : ℕ)
    (hx : (fwdDiff ((1, 0) : IntegerLattice))^[d] h = 0)
    (hy : (fwdDiff ((0, 1) : IntegerLattice))^[e] h = 0) :
    ∃ P : MvPolynomial (Fin 2) ℂ,
      ∀ m n : ℤ, h (m, n) = MvPolynomial.eval ![(m : ℂ), (n : ℂ)] P := by
  classical
  have hhorizontal (n : ℤ) :
      (fwdDiff (1 : ℤ))^[d] (fun m : ℤ => h (m, n)) = 0 := by
    funext m
    rw [horizontal_fwdDiff_iter]
    exact congr_fun hx (m, n)
  have hvertical (m : ℤ) :
      (fwdDiff (1 : ℤ))^[e] (fun n : ℤ => h (m, n)) = 0 := by
    funext n
    rw [vertical_fwdDiff_iter]
    exact congr_fun hy (m, n)
  let Q : ℕ → Polynomial ℂ := fun j =>
    integerInterpolant e (fun n : ℤ => h ((j : ℤ), n))
  have hQ (j : ℕ) (n : ℤ) : h ((j : ℤ), n) = (Q j).eval (n : ℂ) :=
    integerInterpolant_spec e _ (hvertical (j : ℤ)) n
  let P : MvPolynomial (Fin 2) ℂ :=
    ∑ j ∈ Finset.range d,
      coordinatePolynomial 0
          (Lagrange.basis (Finset.range d) (fun k : ℕ => (k : ℂ)) j) *
        coordinatePolynomial 1 (Q j)
  refine ⟨P, ?_⟩
  intro m n
  calc
    h (m, n) =
        (integerInterpolant d (fun t : ℤ => h (t, n))).eval (m : ℂ) :=
      integerInterpolant_spec d _ (hhorizontal n) m
    _ = ∑ j ∈ Finset.range d,
          h ((j : ℤ), n) *
            (Lagrange.basis (Finset.range d) (fun k : ℕ => (k : ℂ)) j).eval
              (m : ℂ) := by
      simp only [integerInterpolant, Lagrange.interpolate_apply,
        Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C]
    _ = ∑ j ∈ Finset.range d,
          (Lagrange.basis (Finset.range d) (fun k : ℕ => (k : ℂ)) j).eval
              (m : ℂ) * (Q j).eval (n : ℂ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hQ]
      exact mul_comm _ _
    _ = MvPolynomial.eval ![(m : ℂ), (n : ℂ)] P := by
      simp [P, eval_coordinatePolynomial]

/-- The full integer lattice determines an arbitrary bivariate complex polynomial uniquely. -/
theorem polynomial_unique_on_integer_lattice
    (P Q : MvPolynomial (Fin 2) ℂ)
    (h : ∀ m n : ℤ,
      MvPolynomial.eval ![(m : ℂ), (n : ℂ)] P =
        MvPolynomial.eval ![(m : ℂ), (n : ℂ)] Q) : P = Q := by
  have hinj : Function.Injective (fun z : ℤ => (z : ℂ)) := by
    intro a b hab
    change (a : ℂ) = (b : ℂ) at hab
    exact_mod_cast hab
  apply MvPolynomial.funext_set
    (fun _ : Fin 2 => Set.range (fun z : ℤ => (z : ℂ)))
    (fun _ => Set.infinite_range_of_injective hinj)
  intro x hx
  obtain ⟨m, hm⟩ := hx 0 (Set.mem_univ 0)
  obtain ⟨n, hn⟩ := hx 1 (Set.mem_univ 1)
  have hx' : x = ![(m : ℂ), (n : ℂ)] := by
    funext i
    fin_cases i
    · simpa using hm.symm
    · simpa using hn.symm
  rw [hx']
  exact h m n

/-- The polynomial representation obtained from the two annihilators is unique. -/
theorem existsUnique_polynomial_of_coordinate_fwdDiff_eq_zero
    (h : IntegerLattice → ℂ) (d e : ℕ)
    (hx : (fwdDiff ((1, 0) : IntegerLattice))^[d] h = 0)
    (hy : (fwdDiff ((0, 1) : IntegerLattice))^[e] h = 0) :
    ∃! P : MvPolynomial (Fin 2) ℂ,
      ∀ m n : ℤ, h (m, n) = MvPolynomial.eval ![(m : ℂ), (n : ℂ)] P := by
  obtain ⟨P, hP⟩ := exists_polynomial_of_coordinate_fwdDiff_eq_zero h d e hx hy
  refine ⟨P, hP, ?_⟩
  intro Q hQ
  apply polynomial_unique_on_integer_lattice Q P
  intro m n
  exact (hQ m n).symm.trans (hP m n)

end IDT.TranslationRankGap
