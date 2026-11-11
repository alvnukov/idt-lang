import Proofs.QMClosure.SemiringReciprocalCrossClassification
import Mathlib.Algebra.DualNumber

/-!
Explicit mathematical controls for the d=4 linear branch.
The dual-number readout is globally nonnegative and faithful at zero, and its
mixed count increments vanish. Its distinct generators therefore show that
nondegeneracy alone does not select d=2. Analytic regularity is outside this file.
-/

noncomputable section

namespace IDT.QMClosure.ReciprocalCrossClassificationControls

open SemiringReciprocalCrossClassification CountCrossIncrementRigidity

namespace Classical

def A : ℝ := 1 / 2

def W (x : ℝ) : ℝ := |x|

theorem laws : Laws A A 4 W := by
  refine ⟨by norm_num [A], by norm_num [A], by norm_num [W], ?_, ?_⟩ <;>
    intro p <;> simp [A, W, abs_mul] <;> ring

theorem nonnegative (x : ℝ) : 0 ≤ W x := abs_nonneg x

theorem faithful (x : ℝ) (h : W x = 0) : x = 0 := abs_eq_zero.mp h

theorem count_value (n m : ℕ) : grid A A W n m = ((n : ℝ) + (m : ℝ)) / 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  dsimp [grid, bag, A, W]
  rw [abs_of_nonneg (by positivity)]
  ring

theorem mixed_zero (n m : ℕ) : mixed (grid A A W) n m = 0 := by
  dsimp [mixed]
  rw [count_value, count_value, count_value, count_value]
  push_cast
  ring

theorem finite_contrast_fails : W ((2 : ℝ) * A) = W 1 := by norm_num [A, W]

end Classical

namespace Dual

abbrev Carrier := DualNumber ℝ

def A : Carrier := (1 / 2, 1 / 2)

def B : Carrier := (1 / 2, -(1 / 2))

def eps : Carrier := (0, 1)

def W (x : Carrier) : ℝ := if x.fst = 0 then |x.snd| else |x.fst|

theorem nonnegative (x : Carrier) : 0 ≤ W x := by
  dsimp [W]
  split_ifs <;> exact abs_nonneg _

theorem faithful (x : Carrier) (h : W x = 0) : x = 0 := by
  by_cases hx : x.fst = 0
  · apply TrivSqZeroExt.ext
    · simpa using hx
    · have hs : |x.snd| = 0 := by simpa [W, hx] using h
      simpa using abs_eq_zero.mp hs
  · have hs : |x.fst| = 0 := by simpa [W, hx] using h
    exact False.elim (hx (abs_eq_zero.mp hs))

/-- Every dual element with scalar part one half has the same half-transfer law. -/
theorem half_of_fst_half (c p : Carrier) (hc : c.fst = 1 / 2) :
    W (c * p) = W p / 2 := by
  by_cases hp : p.fst = 0
  · simp [W, TrivSqZeroExt.fst_mul, DualNumber.snd_mul, hc, hp, abs_mul]
    <;> ring
  · have hcp : (c * p).fst ≠ 0 := by
      rw [TrivSqZeroExt.fst_mul, hc]
      exact mul_ne_zero (by norm_num) hp
    simp [W, hcp, hp, TrivSqZeroExt.fst_mul, hc, abs_mul]
    <;> ring

theorem laws : Laws A B 4 W := by
  have hfst4 : (4 : Carrier).fst = 4 := rfl
  have hsnd4 : (4 : Carrier).snd = 0 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply TrivSqZeroExt.ext <;> norm_num [A, B]
  · apply TrivSqZeroExt.ext <;>
      norm_num [A, B, TrivSqZeroExt.fst_mul, DualNumber.snd_mul, hfst4, hsnd4]
  · norm_num [W]
  · intro p
    exact half_of_fst_half A p (by norm_num [A])
  · intro p
    exact half_of_fst_half B p (by norm_num [B])

theorem distinct : A ≠ B := by
  intro he
  have hs := congrArg TrivSqZeroExt.snd he
  norm_num [A, B] at hs

theorem difference : A - B = eps := by
  apply TrivSqZeroExt.ext <;> norm_num [A, B, eps]

theorem eps_nonzero : eps ≠ 0 := by
  intro he
  have hs := congrArg TrivSqZeroExt.snd he
  norm_num [eps] at hs

theorem eps_square : eps * eps = 0 := by
  apply TrivSqZeroExt.ext <;>
    norm_num [eps, TrivSqZeroExt.fst_mul, DualNumber.snd_mul]

theorem count_value (n m : ℕ) : grid A B W n m = ((n : ℝ) + (m : ℝ)) / 2 := by
  have hfst : (bag A B n m).fst = ((n : ℝ) + (m : ℝ)) / 2 := by
    simp [bag, A, B, TrivSqZeroExt.fst_mul]
    <;> ring
  by_cases hz : n + m = 0
  · have hn : n = 0 := by omega
    have hm : m = 0 := by omega
    subst n
    subst m
    norm_num [grid, bag, W]
  · have htotal : (0 : ℝ) < (n : ℝ) + (m : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hz
    have hp : (0 : ℝ) < ((n : ℝ) + (m : ℝ)) / 2 := by positivity
    change W (bag A B n m) = _
    simp only [W, hfst, if_neg (ne_of_gt hp), abs_of_pos hp]

theorem mixed_zero (n m : ℕ) : mixed (grid A B W) n m = 0 := by
  dsimp [mixed]
  rw [count_value, count_value, count_value, count_value]
  push_cast
  ring

theorem uniform_sign : UniformMixedSign A B W := by
  left
  intro n m
  rw [mixed_zero]

theorem finite_contrast_fails : W ((2 : Carrier) * A) = W 1 := by
  have hfst2 : (2 : Carrier).fst = 2 := rfl
  have hsnd2 : (2 : Carrier).snd = 0 := rfl
  norm_num [A, W, TrivSqZeroExt.fst_mul, DualNumber.snd_mul, hfst2, hsnd2]

theorem cross_value : W (A * B) = 1 / 4 := by
  norm_num [A, B, W, TrivSqZeroExt.fst_mul, DualNumber.snd_mul]

theorem difference_value : W (A - B) = 1 := by
  rw [difference]
  norm_num [eps, W]

theorem eps_value : W eps = 1 := by norm_num [eps, W]

theorem zero_value : W 0 = 0 := by norm_num [W]

theorem not_multiplicative : ¬ ∀ x y : Carrier, W (x * y) = W x * W y := by
  intro hm
  have he := hm eps eps
  rw [eps_square, zero_value, eps_value] at he
  norm_num at he

def reflect (x : Carrier) : Carrier := (x.fst, -x.snd)

theorem reflect_involutive (x : Carrier) : reflect (reflect x) = x := by
  apply TrivSqZeroExt.ext <;> simp [reflect]

theorem reflect_add (x y : Carrier) : reflect (x + y) = reflect x + reflect y := by
  apply TrivSqZeroExt.ext <;> simp [reflect, neg_add, add_comm]

theorem reflect_mul (x y : Carrier) : reflect (x * y) = reflect x * reflect y := by
  apply TrivSqZeroExt.ext <;>
    simp [reflect, TrivSqZeroExt.fst_mul, DualNumber.snd_mul] <;> ring

theorem reflect_unit : reflect 1 = 1 := by
  apply TrivSqZeroExt.ext <;> simp [reflect]

theorem reflect_readout (x : Carrier) : W (reflect x) = W x := by
  simp [W, reflect]

theorem twice (x : Carrier) : W ((2 : Carrier) * x) = 2 * W x := by
  have hfst2 : (2 : Carrier).fst = 2 := rfl
  have hsnd2 : (2 : Carrier).snd = 0 := rfl
  by_cases hx : x.fst = 0
  · simp [W, hx, TrivSqZeroExt.fst_mul, DualNumber.snd_mul, abs_mul, hfst2, hsnd2]
    <;> ring
  · have ht : ((2 : Carrier) * x).fst ≠ 0 := by
      simp [TrivSqZeroExt.fst_mul, hx, hfst2]
    simp [W, hx, ht, TrivSqZeroExt.fst_mul, abs_mul, hfst2]

end Dual

section SquareZeroFree

variable {R : Type*} [CommRing R]

theorem linear_square_zero {a b : R} {W : R → ℝ} (h : Laws a b 4 W) :
    (a - b) * (a - b) = 0 := by
  have hr : (4 : R) * (a * b) = 1 := by simpa using h.reciprocal
  calc
    _ = (a + b) * (a + b) - (4 : R) * (a * b) := by ring
    _ = 0 := by rw [h.transparent, hr]; ring

/-- Square-zero freedom is an explicit structural input for this alternative exclusion. -/
theorem quadratic_of_square_zero_free {a b : R} {d : ℕ} {W : R → ℝ}
    (h : Laws a b d W) (hs : UniformMixedSign a b W)
    (hz : ∀ x : R, x * x = 0 → x = 0) (hne : a ≠ b) :
    d = 2 ∧ ∀ n m, grid a b W n m = ((n : ℝ) ^ 2 + (m : ℝ) ^ 2) / 2 := by
  obtain hq | hl := classification h hs
  · exact hq
  · have hd := hl.1
    subst d
    have he := hz (a - b) (linear_square_zero h)
    exact False.elim (hne (sub_eq_zero.mp he))

end SquareZeroFree

end IDT.QMClosure.ReciprocalCrossClassificationControls
