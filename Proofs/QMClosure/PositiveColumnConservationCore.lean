import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

/-!
Real order and arbitrarily deep positive serial descendants turn conservation
of one binary column into equal branches when the commuting coefficients have
equal fourth powers. This core uses no native representation or norm selector.
The conditional statements in this module are checked by Lean.
-/

namespace IDT.QMClosure.PositiveColumnConservationCore

noncomputable section

private theorem vanish_of_dyadic_bound {d s : ℝ} (hd : 0 ≤ d)
    (hbound : ∀ n : ℕ, (2 : ℝ) ^ n * d ≤ s) : d = 0 := by
  by_contra hne
  have hpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (s / d) (by norm_num : (1 : ℝ) < 2)
  have hlarge : s < (2 : ℝ) ^ n * d := (div_lt_iff₀ hpos).mp hn
  exact (not_lt_of_ge (hbound n)) hlarge

private theorem opposite_equal
    (x y z t : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ x n ∧ 0 ≤ y n ∧ 0 ≤ z n ∧ 0 ≤ t n)
    (hx : ∀ n, x n = 2 * x (n + 1) + y (n + 1) + t (n + 1))
    (hy : ∀ n, y n = 2 * y (n + 1) + z (n + 1) + x (n + 1))
    (hz : ∀ n, z n = 2 * z (n + 1) + t (n + 1) + y (n + 1))
    (ht : ∀ n, t n = 2 * t (n + 1) + x (n + 1) + z (n + 1)) :
    x 0 = z 0 := by
  let S (n : ℕ) := x n + y n + z n + t n
  let D (n : ℕ) := x n - z n
  have hS (n : ℕ) : S n = 4 * S (n + 1) := by
    dsimp [S]
    linarith [hx n, hy n, hz n, ht n]
  have hD (n : ℕ) : D n = 2 * D (n + 1) := by
    dsimp [D]
    linarith [hx n, hz n]
  have hDS (n : ℕ) : |D n| ≤ S n := by
    obtain ⟨hx0, hy0, hz0, ht0⟩ := hpos n
    apply abs_le.mpr
    dsimp [D, S]
    constructor <;> linarith
  have hSscale (n : ℕ) : S 0 = (4 : ℝ) ^ n * S n := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        S 0 = (4 : ℝ) ^ n * S n := ih
        _ = (4 : ℝ) ^ n * (4 * S (n + 1)) := by rw [hS n]
        _ = (4 : ℝ) ^ (n + 1) * S (n + 1) := by rw [pow_succ]; ring
  have hDscale (n : ℕ) : |D 0| = (2 : ℝ) ^ n * |D n| := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        |D 0| = (2 : ℝ) ^ n * |D n| := ih
        _ = (2 : ℝ) ^ n * (2 * |D (n + 1)|) := by
          rw [hD n, abs_mul]
          norm_num
        _ = (2 : ℝ) ^ (n + 1) * |D (n + 1)| := by rw [pow_succ]; ring
  have hbound (n : ℕ) : (2 : ℝ) ^ n * |D 0| ≤ S 0 := by
    have hpow : (2 : ℝ) ^ n * (2 : ℝ) ^ n = (4 : ℝ) ^ n := by
      rw [← mul_pow]
      norm_num
    calc
      (2 : ℝ) ^ n * |D 0| = (4 : ℝ) ^ n * |D n| := by
        rw [hDscale n, ← mul_assoc, hpow]
      _ ≤ (4 : ℝ) ^ n * S n :=
        mul_le_mul_of_nonneg_left (hDS n) (by positivity)
      _ = S 0 := (hSscale n).symm
  have hzero := vanish_of_dyadic_bound (abs_nonneg (D 0)) hbound
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

/-- A positive four-cycle satisfying the two-step column recurrence is constant
across its four slots at the initial layer. -/
theorem four_cycle_equal
    (x y z t : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ x n ∧ 0 ≤ y n ∧ 0 ≤ z n ∧ 0 ≤ t n)
    (hx : ∀ n, x n = 2 * x (n + 1) + y (n + 1) + t (n + 1))
    (hy : ∀ n, y n = 2 * y (n + 1) + z (n + 1) + x (n + 1))
    (hz : ∀ n, z n = 2 * z (n + 1) + t (n + 1) + y (n + 1))
    (ht : ∀ n, t n = 2 * t (n + 1) + x (n + 1) + z (n + 1)) :
    x 0 = y 0 ∧ x 0 = z 0 ∧ x 0 = t 0 := by
  have hxz := opposite_equal x y z t hpos hx hy hz ht
  have hyt := opposite_equal y z t x
    (fun n => ⟨(hpos n).2.1, (hpos n).2.2.1, (hpos n).2.2.2, (hpos n).1⟩)
    hy hz ht hx
  have hparity : x 0 + z 0 = y 0 + t 0 := by
    linarith [hx 0, hy 0, hz 0, ht 0]
  exact ⟨by linarith, hxz, by linarith⟩

section Serial

variable {M : Type*} [CommMonoid M]
variable (a b : M) (W : M → ℝ) (S : Set M)
variable (ha : ∀ q ∈ S, a * q ∈ S) (hb : ∀ q ∈ S, b * q ∈ S)
variable (hcons : ∀ q ∈ S, W (a * q) + W (b * q) = W q)

private theorem power_mem (c : M) (hc : ∀ q ∈ S, c * q ∈ S)
    (n : ℕ) {q : M} (hq : q ∈ S) : c ^ n * q ∈ S := by
  induction n with
  | zero => simpa using hq
  | succ n ih =>
    simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hc _ ih

include ha hb hcons in
private theorem two_step {q : M} (hq : q ∈ S) :
    W q = W (a * (a * q)) + 2 * W (a * (b * q)) + W (b * (b * q)) := by
  have h0 := hcons q hq
  have h1 := hcons (a * q) (ha q hq)
  have h2 := hcons (b * q) (hb q hq)
  have hcomm : b * (a * q) = a * (b * q) := by ac_rfl
  rw [hcomm] at h1
  linarith

include ha hb hcons in
private theorem three_step {q : M} (hq : q ∈ S) :
    W q = W (a ^ 3 * q) + 3 * W (a ^ 2 * b * q) +
      3 * W (a * b ^ 2 * q) + W (b ^ 3 * q) := by
  have h0 := hcons q hq
  have h1 := hcons (a * q) (ha q hq)
  have h2 := hcons (b * q) (hb q hq)
  have h3 := hcons (a * (a * q)) (ha _ (ha q hq))
  have h4 := hcons (a * (b * q)) (ha _ (hb q hq))
  have h5 := hcons (b * (b * q)) (hb _ (hb q hq))
  simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc, mul_left_comm, mul_comm]
    at h0 h1 h2 h3 h4 h5 ⊢
  linarith

include ha hb hcons in
private theorem shifted_row (u v w : M)
    (haa : a * a * u = (a * b) * v)
    (hbb : b * b * u = (a * b) * w)
    (n : ℕ) (p : M) (hq : (a * b) ^ n * u * p ∈ S) :
    W ((a * b) ^ n * u * p) =
      W ((a * b) ^ (n + 1) * v * p) +
      2 * W ((a * b) ^ (n + 1) * u * p) +
      W ((a * b) ^ (n + 1) * w * p) := by
  have h := two_step a b W S ha hb hcons hq
  have eaa : a * (a * ((a * b) ^ n * u * p)) =
      (a * b) ^ (n + 1) * v * p := by
    calc
      _ = (a * b) ^ n * (a * a * u) * p := by ac_rfl
      _ = (a * b) ^ n * ((a * b) * v) * p := by rw [haa]
      _ = _ := by rw [pow_succ]; ac_rfl
  have eab : a * (b * ((a * b) ^ n * u * p)) =
      (a * b) ^ (n + 1) * u * p := by rw [pow_succ]; ac_rfl
  have ebb : b * (b * ((a * b) ^ n * u * p)) =
      (a * b) ^ (n + 1) * w * p := by
    calc
      _ = (a * b) ^ n * (b * b * u) * p := by ac_rfl
      _ = (a * b) ^ n * ((a * b) * w) * p := by rw [hbb]
      _ = _ := by rw [pow_succ]; ac_rfl
  simpa only [eaa, eab, ebb] using h

include ha hb hcons in
/-- Source-local balance. Every required preparation is obtained by serial
multiplication by the two supplied commuting coefficients. Equal fourth powers
are the complete algebraic premise used in this generic theorem. -/
theorem local_branch_balance (hfour : a ^ 4 = b ^ 4)
    (hpos : ∀ q ∈ S, 0 ≤ W q) {p : M} (hp : p ∈ S) :
    W (a * p) = W p / 2 ∧ W (b * p) = W p / 2 := by
  let u : M := a ^ 4
  let v : M := a ^ 3 * b
  let w : M := a ^ 2 * b ^ 2
  let t : M := a * b ^ 3
  have hu : u * p ∈ S := power_mem S a ha 4 hp
  have hv : v * p ∈ S := by
    simpa only [v, mul_assoc] using power_mem S a ha 3 (hb p hp)
  have hw : w * p ∈ S := by
    simpa only [w, mul_assoc] using
      power_mem S a ha 2 (power_mem S b hb 2 hp)
  have ht : t * p ∈ S := by
    simpa only [t, mul_assoc] using ha _ (power_mem S b hb 3 hp)
  have hab : ∀ q ∈ S, (a * b) * q ∈ S := by
    intro q hq
    simpa only [mul_assoc] using ha _ (hb q hq)
  have mem (n : ℕ) {c : M} (hc : c * p ∈ S) :
      (a * b) ^ n * c * p ∈ S := by
    simpa only [mul_assoc] using power_mem S (a * b) hab n hc
  let x (n : ℕ) := W ((a * b) ^ n * u * p)
  let y (n : ℕ) := W ((a * b) ^ n * v * p)
  let z (n : ℕ) := W ((a * b) ^ n * w * p)
  let f (n : ℕ) := W ((a * b) ^ n * t * p)
  have aa0 : a * a * u = (a * b) * t := by
    dsimp [u, t]
    rw [hfour]
    simp only [pow_succ, pow_zero, one_mul, mul_one]
    ac_rfl
  have bb0 : b * b * u = (a * b) * v := by
    dsimp [u, v]
    simp only [pow_succ, pow_zero, one_mul, mul_one]
    ac_rfl
  have aa1 : a * a * v = (a * b) * u := by
    dsimp [v, u]
    simp only [pow_succ, pow_zero, one_mul, mul_one]
    ac_rfl
  have bb1 : b * b * v = (a * b) * w := by
    dsimp [v, w]
    simp only [pow_succ, pow_zero, one_mul, mul_one]
    ac_rfl
  have aa2 : a * a * w = (a * b) * v := by
    dsimp [w, v]
    simp only [pow_succ, pow_zero, one_mul, mul_one]
    ac_rfl
  have bb2 : b * b * w = (a * b) * t := by
    dsimp [w, t]
    simp only [pow_succ, pow_zero, one_mul, mul_one]
    ac_rfl
  have aa3 : a * a * t = (a * b) * w := by
    dsimp [t, w]
    simp only [pow_succ, pow_zero, one_mul, mul_one]
    ac_rfl
  have bb3 : b * b * t = (a * b) * u := by
    dsimp [t, u]
    rw [hfour]
    simp only [pow_succ, pow_zero, one_mul, mul_one]
    ac_rfl
  have hx (n : ℕ) : x n = 2 * x (n + 1) + y (n + 1) + f (n + 1) := by
    have h := shifted_row a b W S ha hb hcons u t v aa0 bb0 n p (mem n hu)
    change x n = f (n + 1) + 2 * x (n + 1) + y (n + 1) at h
    linarith
  have hy (n : ℕ) : y n = 2 * y (n + 1) + z (n + 1) + x (n + 1) := by
    have h := shifted_row a b W S ha hb hcons v u w aa1 bb1 n p (mem n hv)
    change y n = x (n + 1) + 2 * y (n + 1) + z (n + 1) at h
    linarith
  have hz (n : ℕ) : z n = 2 * z (n + 1) + f (n + 1) + y (n + 1) := by
    have h := shifted_row a b W S ha hb hcons w v t aa2 bb2 n p (mem n hw)
    change z n = y (n + 1) + 2 * z (n + 1) + f (n + 1) at h
    linarith
  have hf (n : ℕ) : f n = 2 * f (n + 1) + x (n + 1) + z (n + 1) := by
    have h := shifted_row a b W S ha hb hcons t w u aa3 bb3 n p (mem n ht)
    change f n = z (n + 1) + 2 * f (n + 1) + x (n + 1) at h
    linarith
  obtain ⟨hxy, hxz, hxf⟩ := four_cycle_equal x y z f
    (fun n => ⟨hpos _ (mem n hu), hpos _ (mem n hv),
      hpos _ (mem n hw), hpos _ (mem n ht)⟩) hx hy hz hf
  dsimp [x, y, z, f, u, v, w, t] at hxy hxz hxf
  simp only [pow_zero, one_mul] at hxy hxz hxf
  have hlast : W (b ^ 4 * p) = W (a ^ 4 * p) := by rw [hfour]
  have hA := three_step a b W S ha hb hcons (ha p hp)
  have hB := three_step a b W S ha hb hcons (hb p hp)
  have h0 := hcons p hp
  simp only [pow_succ, pow_zero, one_mul, mul_one, mul_assoc, mul_left_comm, mul_comm]
    at hA hB hxy hxz hxf hlast h0 ⊢
  constructor <;> linarith

end Serial

end

end IDT.QMClosure.PositiveColumnConservationCore
