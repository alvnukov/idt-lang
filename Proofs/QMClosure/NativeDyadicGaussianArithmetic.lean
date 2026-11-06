import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic

/-!
# Gaussian integer arithmetic for three-coordinate native descent

These are exact integer statements. No physical readout or unrestricted
dimension synthesis assertion is imported or inferred.
-/

namespace IDT.QMClosure.NativeDyadicGaussianArithmetic

set_option maxHeartbeats 2000000

abbrev G := GaussianInt

def pi : G := ⟨1, 1⟩
def ii : G := ⟨0, 1⟩
def EvenPi (z : G) : Prop := z.re % 2 = z.im % 2

def halfPi (z : G) : G := ⟨(z.re + z.im) / 2, (z.im - z.re) / 2⟩
def halfTwo (z : G) : G := ⟨z.re / 2, z.im / 2⟩

@[simp] theorem norm_pi : Zsqrtd.norm pi = 2 := by norm_num [pi, Zsqrtd.norm]
@[simp] theorem norm_ii : Zsqrtd.norm ii = 1 := by norm_num [ii, Zsqrtd.norm]
theorem pi_ne_zero : pi ≠ 0 := by decide
theorem norm_formula (z : G) : z.norm = z.re * z.re + z.im * z.im := by
  simp [Zsqrtd.norm]

theorem mul_halfPi (z : G) (h : EvenPi z) : pi * halfPi z = z := by
  apply Zsqrtd.ext <;> simp [pi, halfPi]
  all_goals unfold EvenPi at h; omega

theorem sq_mod_four (x : ℤ) : (x * x) % 4 = x % 2 := by
  have hx : 0 ≤ x % 4 ∧ x % 4 < 4 := ⟨Int.emod_nonneg _ (by norm_num),
    Int.emod_lt_of_pos _ (by norm_num)⟩
  have h := Int.mul_emod x x 4
  rcases hx with ⟨hl, hu⟩
  interval_cases he : x % 4 <;> norm_num [he] at h <;> omega

theorem norm_mod_four (z : G) : z.norm % 4 = (z.re % 2 + z.im % 2) % 4 := by
  rw [norm_formula, Int.add_emod, sq_mod_four, sq_mod_four]

theorem norm_halfPi (z : G) (h : EvenPi z) : 2 * (halfPi z).norm = z.norm := by
  conv_rhs => rw [← mul_halfPi z h, Zsqrtd.norm_mul, norm_pi]

theorem opposite_divisible (z w : G)
    (hr : z.re % 2 = w.im % 2) (hi : z.im % 2 = w.re % 2) :
    ∃ q : G, ii * z + w = pi ^ 2 * q := by
  refine ⟨⟨(z.re + w.im) / 2, (z.im - w.re) / 2⟩, ?_⟩
  apply Zsqrtd.ext <;>
    norm_num [ii, pi, pow_two]
  all_goals omega

def Opposite (z w : G) : Prop :=
  z.re % 2 = w.im % 2 ∧ z.im % 2 = w.re % 2

theorem three_parity (x y z : G)
    (hr : (x + y + z).re % 2 = 0) (hi : (x + y + z).im % 2 = 0)
    (hn : (x.norm + y.norm + z.norm) % 4 = 0) :
    (EvenPi x ∧ EvenPi y ∧ EvenPi z) ∨
    (Opposite x y ∧ EvenPi z) ∨
    (Opposite x z ∧ EvenPi y) ∨
    (Opposite y z ∧ EvenPi x) := by
  simp only [Zsqrtd.re_add, Zsqrtd.im_add] at hr hi
  have hx := norm_mod_four x
  have hy := norm_mod_four y
  have hz := norm_mod_four z
  unfold EvenPi Opposite
  omega

theorem pow_pi_even (k : ℕ) :
    (pi ^ (k + 2)).re % 2 = 0 ∧ (pi ^ (k + 2)).im % 2 = 0 := by
  rw [pow_add]
  norm_num [pi, pow_two]

theorem pow_two_mod_four (k : ℕ) : (2 ^ (k + 2) : ℤ) % 4 = 0 := by
  rw [pow_add]
  norm_num [Int.mul_emod]

theorem sq_ge_self (n : ℤ) : n ≤ n * n := by
  by_cases h : n ≤ 0
  · nlinarith [sq_nonneg n]
  · have : 1 ≤ n := by omega
    nlinarith

theorem sum_one_norm_one (x y z : G)
    (hs : x + y + z = 1) (hn : x.norm + y.norm + z.norm = 1) :
    (x = 1 ∧ y = 0 ∧ z = 0) ∨ (x = 0 ∧ y = 1 ∧ z = 0) ∨
    (x = 0 ∧ y = 0 ∧ z = 1) := by
  have hr := congrArg Zsqrtd.re hs
  have hi := congrArg Zsqrtd.im hs
  simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one] at hr hi
  simp only [norm_formula] at hn
  have hxr := sq_ge_self x.re
  have hxi := sq_ge_self x.im
  have hyr := sq_ge_self y.re
  have hyi := sq_ge_self y.im
  have hzr := sq_ge_self z.re
  have hzi := sq_ge_self z.im
  have bxr : x.re = 0 ∨ x.re = 1 := by
    have : x.re * x.re = x.re := by nlinarith
    have : x.re * (x.re - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h <;> omega
  have byr : y.re = 0 ∨ y.re = 1 := by
    have : y.re * y.re = y.re := by nlinarith
    have : y.re * (y.re - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h <;> omega
  have bzr : z.re = 0 ∨ z.re = 1 := by
    have : z.re * z.re = z.re := by nlinarith
    have : z.re * (z.re - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h <;> omega
  have hxim : x.im = 0 := by nlinarith [sq_nonneg x.im, sq_nonneg y.im, sq_nonneg z.im]
  have hyim : y.im = 0 := by nlinarith [sq_nonneg x.im, sq_nonneg y.im, sq_nonneg z.im]
  have hzim : z.im = 0 := by nlinarith [sq_nonneg x.im, sq_nonneg y.im, sq_nonneg z.im]
  rcases bxr with h | h <;> rcases byr with h' | h' <;> rcases bzr with h'' | h''
  all_goals simp_all [Zsqrtd.ext_iff]

private theorem binary_of_squares {a b c d e f : ℤ}
    (hs : a + b + c + d + e + f = 2)
    (hn : a*a + b*b + c*c + d*d + e*e + f*f = 2) : a = 0 ∨ a = 1 := by
  have ha := sq_ge_self a
  have hb := sq_ge_self b
  have hc := sq_ge_self c
  have hd := sq_ge_self d
  have he := sq_ge_self e
  have hf := sq_ge_self f
  have : a * (a - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h | h <;> omega

/-- The exponent-one case includes the three all-even representatives. -/
theorem sum_pi_norm_two (x y z : G)
    (hs : x + y + z = pi) (hn : x.norm + y.norm + z.norm = 2) :
    (x = pi ∧ y = 0 ∧ z = 0) ∨ (x = 0 ∧ y = pi ∧ z = 0) ∨
    (x = 0 ∧ y = 0 ∧ z = pi) ∨
    (x = 1 ∧ y = ii ∧ z = 0) ∨ (x = ii ∧ y = 1 ∧ z = 0) ∨
    (x = 1 ∧ y = 0 ∧ z = ii) ∨ (x = ii ∧ y = 0 ∧ z = 1) ∨
    (x = 0 ∧ y = 1 ∧ z = ii) ∨ (x = 0 ∧ y = ii ∧ z = 1) := by
  have hr := congrArg Zsqrtd.re hs
  have hi := congrArg Zsqrtd.im hs
  simp only [Zsqrtd.re_add, Zsqrtd.im_add, pi] at hr hi
  simp only [norm_formula] at hn
  have hb (a b c d e f : ℤ) (h : a + b + c + d + e + f = 2)
      (n : a*a + b*b + c*c + d*d + e*e + f*f = 2) :=
    binary_of_squares h n
  have bxr := hb x.re x.im y.re y.im z.re z.im (by omega) (by nlinarith)
  have bxi := hb x.im x.re y.re y.im z.re z.im (by omega) (by nlinarith)
  have byr := hb y.re x.re x.im y.im z.re z.im (by omega) (by nlinarith)
  have byi := hb y.im x.re x.im y.re z.re z.im (by omega) (by nlinarith)
  have bzr := hb z.re x.re x.im y.re y.im z.im (by omega) (by nlinarith)
  have bzi := hb z.im x.re x.im y.re y.im z.re (by omega) (by nlinarith)
  rcases bxr with h | h <;> rcases bxi with h' | h' <;>
    rcases byr with j | j <;> rcases byi with j' | j' <;>
    rcases bzr with l | l <;> rcases bzi with l' | l'
  all_goals simp_all [Zsqrtd.ext_iff, pi, ii]

def LegalTriple (k : ℕ) (x y z : G) : Prop :=
  x + y + z = pi ^ k ∧ x.norm + y.norm + z.norm = (2 : ℤ) ^ k

theorem divide_all (k : ℕ) (x y z : G) (h : LegalTriple (k + 1) x y z)
    (hx : EvenPi x) (hy : EvenPi y) (hz : EvenPi z) :
    LegalTriple k (halfPi x) (halfPi y) (halfPi z) := by
  constructor
  · apply mul_left_cancel₀ pi_ne_zero
    calc
      pi * (halfPi x + halfPi y + halfPi z) = x + y + z := by
        rw [mul_add, mul_add, mul_halfPi x hx, mul_halfPi y hy, mul_halfPi z hz]
      _ = pi ^ (k + 1) := h.1
      _ = pi * pi ^ k := pow_succ' _ _
  · have hnx := norm_halfPi x hx
    have hny := norm_halfPi y hy
    have hnz := norm_halfPi z hz
    have hn := h.2
    rw [pow_succ] at hn
    linarith

theorem pair_norm (x y : G) :
    (ii * x + y).norm + (x + ii * y).norm = 2 * (x.norm + y.norm) := by
  simp [norm_formula, ii]
  ring

theorem ii_add_one : ii + 1 = pi := by decide

/-- A single legal pair gate lowers the displayed exponent by one. -/
theorem divide_pair (k : ℕ) (x y z : G) (h : LegalTriple (k + 1) x y z)
    (ho : Opposite x y) (hz : EvenPi z) :
    ∃ x' y' z' : G, LegalTriple k x' y' z' ∧
      pi ^ 2 * x' = ii * x + y ∧ pi ^ 2 * y' = x + ii * y ∧ pi * z' = z := by
  obtain ⟨x', hx⟩ := opposite_divisible x y ho.1 ho.2
  obtain ⟨y', hy⟩ := opposite_divisible y x ho.2.symm ho.1.symm
  have hy' : pi ^ 2 * y' = x + ii * y := by rw [← hy, add_comm]
  have hx' := hx.symm
  have hz' := mul_halfPi z hz
  refine ⟨x', y', halfPi z, ⟨?_, ?_⟩, hx', hy', hz'⟩
  · apply mul_left_cancel₀ (pow_ne_zero 2 pi_ne_zero)
    calc
      pi ^ 2 * (x' + y' + halfPi z) =
          (ii * x + y) + (x + ii * y) + pi * z := by
        rw [mul_add, mul_add, hx', hy']
        congr 1
        rw [pow_two, mul_assoc, hz']
      _ = pi * (x + y + z) := by rw [← ii_add_one]; ring
      _ = pi ^ 2 * pi ^ k := by rw [h.1, pow_succ']; ring
  · have hnx := congrArg Zsqrtd.norm hx'
    have hny := congrArg Zsqrtd.norm hy'
    have hnz := norm_halfPi z hz
    have hp := pair_norm x y
    have hn := h.2
    have hpi : (pi ^ 2).norm = 4 := by norm_num [pow_two, Zsqrtd.norm_mul]
    rw [Zsqrtd.norm_mul, hpi] at hnx hny
    rw [pow_succ] at hn
    linarith

end IDT.QMClosure.NativeDyadicGaussianArithmetic
