import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic

/-!
# Quadratic selection on Gaussian integers

This is an algebraic classification of a supplied real-valued function on the
Gaussian integers. Normalization, invariance under multiplication by `i`, and
the parallelogram identity determine the sum of the coordinate squares.
Positivity and continuity are not assumptions. No native-circuit response or
physical probability interpretation is constructed by this module.
-/

namespace IDT.QMClosure.GaussianIntegerQuadraticSelection

noncomputable section
set_option maxHeartbeats 2000000

abbrev G := GaussianInt
def ii : G := ⟨0, 1⟩

def Parallelogram (q : G → ℝ) : Prop :=
  ∀ z w, q (z + w) + q (z - w) = 2*q z + 2*q w

/-- The parallelogram recurrence gives every natural affine line exactly. -/
theorem nat_affine (q : G → ℝ) (hpar : Parallelogram q) (x y : G) (n : ℕ) :
    q ((n : G)*x + y) = (n : ℝ)^2*q x +
      (n : ℝ)*(q (x+y)-q x-q y) + q y := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => norm_num; ring
  | more n ih ih1 =>
    have h := hpar (((n+1 : ℕ) : G)*x+y) x
    have hplus : (((n+1 : ℕ) : G)*x+y)+x = ((n+2 : ℕ) : G)*x+y := by
      push_cast
      ring
    have hminus : (((n+1 : ℕ) : G)*x+y)-x = (n : G)*x+y := by
      push_cast
      ring
    rw [hplus, hminus, ih, ih1] at h
    push_cast at h ⊢
    linear_combination h

theorem nat_orthogonal_pair (q : G → ℝ) (hzero : q 0 = 0)
    (hpar : Parallelogram q) (x y : G)
    (hx : q x = 1) (hy : q y = 1) (hxy : q (x+y) = 2) (m n : ℕ) :
    q ((m : G)*x + (n : G)*y) = (m : ℝ)^2 + (n : ℝ)^2 := by
  have hn : q ((n : G)*y) = (n : ℝ)^2 := by
    simpa [hzero, hy] using nat_affine q hpar y 0 n
  have hxny : q (x+(n : G)*y) = (n : ℝ)^2+1 := by
    have h := nat_affine q hpar y x n
    have hyx : q (y+x) = 2 := by simpa [add_comm] using hxy
    rw [hy, hx, hyx] at h
    norm_num at h
    simpa only [add_comm] using h
  have h := nat_affine q hpar x ((n : G)*y) m
  rw [hx, hn, hxny] at h
  nlinarith

theorem gaussian_integer_quadratic_selection (q : G → ℝ)
    (hzero : q 0 = 0) (hone : q 1 = 1)
    (hrot : ∀ z, q (ii*z) = q z) (hpar : Parallelogram q) (g : G) :
    q g = (g.re : ℝ)^2 + (g.im : ℝ)^2 := by
  have hneg (z : G) : q (-z) = q z := by
    have h := hpar 0 z
    simp only [zero_add, zero_sub, hzero, mul_zero, zero_add] at h
    linarith
  have hi : q ii = 1 := by simpa using (hrot 1).trans hone
  have hsum_eq : q (1+ii) = q (1-ii) := by
    have h := hrot (1-ii)
    rw [show ii*(1-ii) = 1+ii by decide] at h
    exact h
  have hsum : q (1+ii) = 2 := by
    have h := hpar 1 ii
    rw [hone, hi] at h
    linarith
  have hdiff : q (1-ii) = 2 := hsum_eq.symm.trans hsum
  have hnegOne : q (-1) = 1 := (hneg 1).trans hone
  have hnegI : q (-ii) = 1 := (hneg ii).trans hi
  have hminus_plus : q (-1+ii) = 2 := by
    rw [show (-1+ii : G) = -(1-ii) by ring, hneg]
    exact hdiff
  have hplus_minus : q (1 + -ii) = 2 := by simpa [sub_eq_add_neg] using hdiff
  have hminus_minus : q (-1 + -ii) = 2 := by
    rw [show (-1 + -ii : G) = -(1+ii) by ring, hneg]
    exact hsum
  rcases g with ⟨a, b⟩
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      have h := nat_orthogonal_pair q hzero hpar 1 ii hone hi hsum m n
      have he : (m : G)*1 + (n : G)*ii = ⟨Int.ofNat m, Int.ofNat n⟩ := by
        ext <;> simp [ii]
      rw [he] at h
      simpa using h
    | negSucc n =>
      have h := nat_orthogonal_pair q hzero hpar 1 (-ii) hone hnegI hplus_minus m (n+1)
      have he : (m : G)*1 + ((n+1 : ℕ) : G)*(-ii) = ⟨Int.ofNat m, Int.negSucc n⟩ := by
        ext <;> simp [ii, Int.negSucc_eq]
      rw [he] at h
      simp [Int.negSucc_eq] at h ⊢
      nlinarith
  | negSucc m =>
    cases b with
    | ofNat n =>
      have h := nat_orthogonal_pair q hzero hpar (-1) ii hnegOne hi hminus_plus (m+1) n
      have he : ((m+1 : ℕ) : G)*(-1) + (n : G)*ii = ⟨Int.negSucc m, Int.ofNat n⟩ := by
        ext <;> simp [ii, Int.negSucc_eq]
      rw [he] at h
      simp [Int.negSucc_eq] at h ⊢
      nlinarith
    | negSucc n =>
      have h := nat_orthogonal_pair q hzero hpar (-1) (-ii)
        hnegOne hnegI hminus_minus (m+1) (n+1)
      have he : ((m+1 : ℕ) : G)*(-1) + ((n+1 : ℕ) : G)*(-ii) =
          ⟨Int.negSucc m, Int.negSucc n⟩ := by
        ext <;> simp [ii, Int.negSucc_eq]
      rw [he] at h
      simp [Int.negSucc_eq] at h ⊢
      nlinarith

end
end IDT.QMClosure.GaussianIntegerQuadraticSelection
