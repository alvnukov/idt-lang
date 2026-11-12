import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

/-!
# Finite cyclic averaging

Pure numerical finite-cycle estimates.
The positive direction is `j + 1` throughout. Polynomial coefficient
convolution with `j - 1` requires a separate reindexing argument.

The `n = 1` case is included: its block length is zero and its
contraction factor is zero. No proof divides by the block length.
-/

noncomputable section

namespace IDT.QMClosure.FiniteCyclicAveraging

open scoped BigOperators

variable {n : ℕ} [NeZero n]

/-- Normalized real averaging in the positive cyclic direction. -/
def P (v : ZMod n → ℝ) (j : ZMod n) : ℝ :=
  (v j + v (j + 1)) / 2

/-- Unnormalized averaging, including its integer specialization. -/
def T {A : Type*} [Add A] (v : ZMod n → A) (j : ZMod n) : A :=
  v j + v (j + 1)

/-- The common mixing block length. -/
def blockLength (n : ℕ) : ℕ := n - 1

/-- Lower bound on every coefficient in a mixing block. -/
def delta (n : ℕ) : ℝ := ((2 : ℝ) ^ blockLength n)⁻¹

/-- Uniform zero-sum contraction factor. -/
def q (n : ℕ) : ℝ := 1 - (n : ℝ) * delta n

@[simp] theorem blockLength_one : blockLength 1 = 0 := rfl
@[simp] theorem delta_one : delta 1 = 1 := by norm_num [delta]
@[simp] theorem q_one : q 1 = 0 := by norm_num [q]

@[simp] theorem blockLength_two : blockLength 2 = 1 := rfl
@[simp] theorem delta_two : delta 2 = (1 : ℝ) / 2 := by norm_num [delta]
@[simp] theorem q_two : q 2 = 0 := by norm_num [q, delta]

private theorem nat_pos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)

private theorem nat_real_pos : (0 : ℝ) < n := by
  exact_mod_cast (nat_pos (n := n))

private theorem nat_real_one_le : (1 : ℝ) ≤ n := by
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))

/-- A cyclic shift permutes the finite phase sum. -/
theorem sum_shift (v : ZMod n → ℝ) :
    (∑ j, v (j + 1)) = ∑ j, v j := by
  let e : ZMod n ≃ ZMod n :=
    { toFun := fun j => j + 1
      invFun := fun j => j - 1
      left_inv := by intro j; simp
      right_inv := by intro j; simp }
  exact Fintype.sum_equiv e (fun j => v (j + 1)) v (fun _ => rfl)

/-- Averaging preserves the finite sum. -/
theorem P_sum (v : ZMod n → ℝ) :
    (∑ j, P v j) = ∑ j, v j := by
  change (∑ j, (v j + v (j + 1)) / 2) = ∑ j, v j
  rw [← Finset.sum_div, Finset.sum_add_distrib, sum_shift]
  ring

@[simp] theorem P_const (c : ℝ) : P (fun _ : ZMod n => c) = fun _ => c := by
  funext j
  simp [P]

/-- Averaging preserves coordinatewise nonnegativity. -/
theorem P_nonneg {v : ZMod n → ℝ} (hv : ∀ j, 0 ≤ v j) :
    ∀ j, 0 ≤ P v j := by
  intro j
  exact div_nonneg (add_nonneg (hv j) (hv (j + 1))) (by norm_num)

/-- Every iterate preserves the finite sum. -/
theorem P_iterate_sum (m : ℕ) (v : ZMod n → ℝ) :
    (∑ j, ((P (n := n))^[m]) v j) = ∑ j, v j := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', P_sum, ih]

@[simp] theorem P_iterate_const (m : ℕ) (c : ℝ) :
    ((P (n := n))^[m]) (fun _ => c) = fun _ => c := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, P_const]

/-- Every iterate preserves coordinatewise nonnegativity. -/
theorem P_iterate_nonneg (m : ℕ) {v : ZMod n → ℝ}
    (hv : ∀ j, 0 ≤ v j) : ∀ j, 0 ≤ ((P (n := n))^[m]) v j := by
  induction m with
  | zero => exact hv
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact P_nonneg ih

/-- Affine translation commutes with every averaging iterate. -/
theorem P_iterate_const_add (m : ℕ) (c : ℝ) (v : ZMod n → ℝ) :
    ∀ j, ((P (n := n))^[m]) (fun j => c + v j) j =
      c + ((P (n := n))^[m]) v j := by
  induction m with
  | zero => intro j; rfl
  | succ m ih =>
      intro j
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change (((P^[m]) (fun j => c + v j) j) +
        ((P^[m]) (fun j => c + v j) (j + 1))) / 2 =
        c + (((P^[m]) v j) + ((P^[m]) v (j + 1))) / 2
      rw [ih j, ih (j + 1)]
      ring

/-- Subtracting a constant commutes with every averaging iterate. -/
theorem P_iterate_sub_const (m : ℕ) (c : ℝ) (v : ZMod n → ℝ) :
    ∀ j, ((P (n := n))^[m]) (fun j => v j - c) j =
      ((P (n := n))^[m]) v j - c := by
  induction m with
  | zero => intro j; rfl
  | succ m ih =>
      intro j
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change (((P^[m]) (fun j => v j - c) j) +
        ((P^[m]) (fun j => v j - c) (j + 1))) / 2 =
        (((P^[m]) v j) + ((P^[m]) v (j + 1))) / 2 - c
      rw [ih j, ih (j + 1)]
      ring

/-- Constant minus a vector also commutes with every averaging iterate. -/
theorem P_iterate_const_sub (m : ℕ) (c : ℝ) (v : ZMod n → ℝ) :
    ∀ j, ((P (n := n))^[m]) (fun j => c - v j) j =
      c - ((P (n := n))^[m]) v j := by
  induction m with
  | zero => intro j; rfl
  | succ m ih =>
      intro j
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change (((P^[m]) (fun j => c - v j) j) +
        ((P^[m]) (fun j => c - v j) (j + 1))) / 2 =
        c - (((P^[m]) v j) + ((P^[m]) v (j + 1))) / 2
      rw [ih j, ih (j + 1)]
      ring

/-- The unnormalized real iterate equals a positive scalar times the
normalized iterate. -/
theorem T_real_iterate (m : ℕ) (v : ZMod n → ℝ) :
    ∀ j, ((T (n := n))^[m]) v j =
      (2 : ℝ)^m * ((P (n := n))^[m]) v j := by
  induction m with
  | zero => intro j; simp
  | succ m ih =>
      intro j
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change ((T^[m]) v j) + ((T^[m]) v (j + 1)) =
        (2 : ℝ)^(m + 1) * ((((P^[m]) v j) + ((P^[m]) v (j + 1))) / 2)
      rw [ih j, ih (j + 1), pow_succ]
      ring

private theorem T_iterate_nonneg (m : ℕ) {v : ZMod n → ℝ}
    (hv : ∀ j, 0 ≤ v j) : ∀ j, 0 ≤ ((T (n := n))^[m]) v j := by
  induction m with
  | zero => exact hv
  | succ m ih =>
      intro j
      rw [Function.iterate_succ_apply']
      exact add_nonneg (ih j) (ih (j + 1))

/-- The endpoint path has coefficient one before normalization. -/
private theorem endpoint_le_T_iterate (m : ℕ) {v : ZMod n → ℝ}
    (hv : ∀ j, 0 ≤ v j) :
    ∀ j, v (j + (m : ZMod n)) ≤ ((T (n := n))^[m]) v j := by
  induction m with
  | zero => intro j; simp
  | succ m ih =>
      intro j
      have hend : v (j + ((m + 1 : ℕ) : ZMod n)) ≤
          ((T (n := n))^[m]) v (j + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm]
          using ih (j + 1)
      have hleft := T_iterate_nonneg m hv j
      rw [Function.iterate_succ_apply']
      change v (j + ((m + 1 : ℕ) : ZMod n)) ≤
        ((T^[m]) v j) + ((T^[m]) v (j + 1))
      linarith

/-- Retain every displacement from zero through `m` with coefficient one.
All additional binomial paths are nonnegative. This avoids requiring an
explicit binomial coefficient normal form for the same lower bound. -/
private theorem prefix_le_T_iterate (m : ℕ) {v : ZMod n → ℝ}
    (hv : ∀ j, 0 ≤ v j) :
    ∀ j, (∑ r ∈ Finset.range (m + 1), v (j + (r : ZMod n))) ≤
      ((T (n := n))^[m]) v j := by
  induction m with
  | zero => intro j; simp
  | succ m ih =>
      intro j
      have hend : v (j + ((m + 1 : ℕ) : ZMod n)) ≤
          ((T (n := n))^[m]) v (j + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm]
          using endpoint_le_T_iterate m hv (j + 1)
      rw [Finset.sum_range_succ, Function.iterate_succ_apply']
      exact add_le_add (ih j) hend

/-- Exactly `n` consecutive phases cover the finite cycle once. -/
private theorem sum_consecutive (v : ZMod n → ℝ) (j : ZMod n) :
    (∑ r ∈ Finset.range n, v (j + (r : ZMod n))) = ∑ x, v x := by
  classical
  refine Finset.sum_bij (fun r _ => j + (r : ZMod n))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro r hr s hs hrs
    have hcast : (r : ZMod n) = (s : ZMod n) := add_left_cancel hrs
    have hval := congrArg ZMod.val hcast
    simpa only [ZMod.val_natCast_of_lt (Finset.mem_range.mp hr),
      ZMod.val_natCast_of_lt (Finset.mem_range.mp hs)] using hval
  · intro x _
    refine ⟨(x - j).val, Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
    change j + ((x - j).val : ZMod n) = x
    rw [ZMod.natCast_zmod_val]
    abel

/-- Every mixing-block coefficient is at least `delta n`, expressed
as the equivalent bound for an arbitrary nonnegative vector. -/
theorem P_block_lower {v : ZMod n → ℝ} (hv : ∀ j, 0 ≤ v j)
    (j : ZMod n) :
    delta n * (∑ x, v x) ≤ ((P (n := n))^[blockLength n]) v j := by
  have hlen : blockLength n + 1 = n := by
    dsimp [blockLength]
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
  have h := prefix_le_T_iterate (blockLength n) hv j
  rw [hlen, sum_consecutive, T_real_iterate] at h
  have hpow : (0 : ℝ) < 2 ^ blockLength n := pow_pos (by norm_num) _
  have hdiv : (∑ x, v x) / (2 : ℝ)^blockLength n ≤
      ((P (n := n))^[blockLength n]) v j := by
    apply (div_le_iff₀ hpow).2
    nlinarith [h]
  simpa only [delta, div_eq_mul_inv, mul_comm] using hdiv

/-- The coefficient lower bound is strictly positive. -/
theorem delta_pos : 0 < delta n := by
  exact inv_pos.mpr (pow_pos (by norm_num) _)

/-- The sum of the row lower bounds is at most one. -/
theorem n_mul_delta_le_one : (n : ℝ) * delta n ≤ 1 := by
  have h := P_block_lower (n := n) (v := fun _ => 1) (fun _ => by norm_num) 0
  simpa only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    mul_one, P_iterate_const, mul_comm] using h

/-- Degenerate exact mixing (`q = 0`) is allowed. -/
theorem q_nonneg : 0 ≤ q n := by
  dsimp [q]
  linarith [n_mul_delta_le_one (n := n)]

/-- Strict contraction holds for every positive finite cycle. -/
theorem q_lt_one : q n < 1 := by
  have hpos : 0 < (n : ℝ) * delta n := mul_pos nat_real_pos delta_pos
  dsimp [q]
  linarith

/-- One block contracts every zero-sum vector within its supplied uniform
coordinate bound. The bound is part of the conclusion used for variable
terminal vectors in the backward theorem. -/
theorem P_block_abs_le {v : ZMod n → ℝ} {C : ℝ}
    (hzero : (∑ j, v j) = 0) (hC : 0 ≤ C) (hv : ∀ j, |v j| ≤ C)
    (j : ZMod n) :
    |((P (n := n))^[blockLength n]) v j| ≤ q n * C := by
  have hplus : ∀ x, 0 ≤ C + v x := by
    intro x
    have hx := (abs_le.mp (hv x)).1
    linarith
  have hminus : ∀ x, 0 ≤ C - v x := by
    intro x
    have hx := (abs_le.mp (hv x)).2
    linarith
  have hsumplus : (∑ x, (C + v x)) = (n : ℝ) * C := by
    simp [Finset.sum_add_distrib, hzero, ZMod.card]
  have hsumminus : (∑ x, (C - v x)) = (n : ℝ) * C := by
    simp [Finset.sum_sub_distrib, hzero, ZMod.card]
  have hp := P_block_lower hplus j
  have hm := P_block_lower hminus j
  rw [hsumplus, P_iterate_const_add] at hp
  rw [hsumminus, P_iterate_const_sub] at hm
  apply abs_le.mpr
  dsimp [q]
  constructor <;> nlinarith [hp, hm]

/-- Uniform block iteration estimate, with a freely supplied input vector
and coordinate bound. -/
theorem P_blocks_abs_le (k : ℕ) {v : ZMod n → ℝ} {C : ℝ}
    (hzero : (∑ j, v j) = 0) (hC : 0 ≤ C) (hv : ∀ j, |v j| ≤ C) :
    ∀ j, |((P (n := n))^[k * blockLength n]) v j| ≤ (q n)^k * C := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
      intro j
      have hz : (∑ x, ((P (n := n))^[k * blockLength n]) v x) = 0 := by
        rw [P_iterate_sum, hzero]
      have hbound := P_block_abs_le hz
        (mul_nonneg (pow_nonneg (q_nonneg (n := n)) k) hC) ih j
      rw [Nat.succ_mul, Nat.add_comm (k * blockLength n) (blockLength n),
        Function.iterate_add_apply]
      simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hbound

/-- The terminal input may vary with the block number. -/
theorem P_variable_terminal_abs_le (g : ℕ → ZMod n → ℝ) {C : ℝ}
    (hzero : ∀ k, (∑ j, g k j) = 0) (hC : 0 ≤ C)
    (hg : ∀ k j, |g k j| ≤ C) (k : ℕ) (j : ZMod n) :
    |((P (n := n))^[k * blockLength n]) (g k) j| ≤ (q n)^k * C :=
  P_blocks_abs_le k (hzero k) hC (hg k) j

/-- A geometric factor eventually makes any fixed nonnegative bound
smaller than a positive tolerance, including `q = 0`. -/
private theorem exists_geom_mul_lt {r C ε : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ k : ℕ, r^k * C < ε := by
  have hCp : 0 < C + 1 := by linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hCp) hr1
  refine ⟨k, ?_⟩
  have hbig : r^k * (C + 1) < ε := (lt_div_iff₀ hCp).mp hk
  nlinarith [pow_nonneg hr0 k]

/-- Uniform geometric estimates force the fixed quantity to vanish. -/
private theorem eq_zero_of_uniform_geom_bound {r C x : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hC : 0 ≤ C) (hx : ∀ k : ℕ, |x| ≤ r^k * C) : x = 0 := by
  by_contra hne
  obtain ⟨k, hk⟩ := exists_geom_mul_lt hr0 hr1 hC (abs_pos.mpr hne)
  exact (not_lt_of_ge (hx k)) hk

/-- Integer convolution is transported by the ordinary integer-to-real
cast. Its coefficients remain integers throughout the source iteration. -/
theorem intCast_T_iterate (m : ℕ) (v : ZMod n → ℤ) :
    ∀ j, ((((T (n := n))^[m]) v j : ℤ) : ℝ) =
      ((T (n := n))^[m]) (fun j => (v j : ℝ)) j := by
  induction m with
  | zero => intro j; rfl
  | succ m ih =>
      intro j
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change (((T^[m]) v j + (T^[m]) v (j + 1) : ℤ) : ℝ) =
        (T^[m]) (fun j => (v j : ℝ)) j +
        (T^[m]) (fun j => (v j : ℝ)) (j + 1)
      rw [Int.cast_add, ih j, ih (j + 1)]

/-- Positive augmentation is eventually smoothed into strictly positive
integer coefficients by finite cyclic convolution with `[1,1]`. -/
theorem exists_T_iterate_pos (v : ZMod n → ℤ) (hsum : 0 < ∑ j, v j) :
    ∃ K : ℕ, ∀ j, 0 < ((T (n := n))^[K]) v j := by
  let V : ZMod n → ℝ := fun j => (v j : ℝ)
  let μ : ℝ := (∑ j, V j) / (n : ℝ)
  let u : ZMod n → ℝ := fun j => V j - μ
  let C : ℝ := ∑ j, |u j|
  have hsumR : 0 < ∑ j, V j := by
    dsimp [V]
    exact_mod_cast hsum
  have hμ : 0 < μ := div_pos hsumR nat_real_pos
  have hu : (∑ j, u j) = 0 := by
    dsimp [u]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    dsimp [μ]
    field_simp [ne_of_gt (nat_real_pos (n := n))] <;> ring
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have huC : ∀ j, |u j| ≤ C := by
    intro j
    exact Finset.single_le_sum (fun x _ => abs_nonneg (u x)) (Finset.mem_univ j)
  obtain ⟨k, hk⟩ := exists_geom_mul_lt (q_nonneg (n := n))
    (q_lt_one (n := n)) hC hμ
  let K := k * blockLength n
  refine ⟨K, fun j => ?_⟩
  have hcenter := P_blocks_abs_le k hu hC huC j
  have hV : V = fun j => μ + u j := by
    funext x
    dsimp [u]
    ring
  have hP : 0 < ((P (n := n))^[K]) V j := by
    rw [hV, P_iterate_const_add]
    have hlo := (abs_le.mp hcenter).1
    dsimp [K]
    linarith
  have hT : 0 < ((T (n := n))^[K]) V j := by
    rw [T_real_iterate]
    exact mul_pos (pow_pos (by norm_num) K) hP
  have hcast : 0 < ((((T (n := n))^[K]) v j : ℤ) : ℝ) := by
    rw [intCast_T_iterate]
    exact hT
  exact_mod_cast hcast

/-- Nonnegative-coefficient wrapper of strict eventual positivity. -/
theorem exists_T_iterate_nonneg (v : ZMod n → ℤ) (hsum : 0 < ∑ j, v j) :
    ∃ K : ℕ, ∀ j, 0 ≤ ((T (n := n))^[K]) v j := by
  obtain ⟨K, hK⟩ := exists_T_iterate_pos v hsum
  exact ⟨K, fun j => (hK j).le⟩

private theorem backward_iterate (f : ℕ → ZMod n → ℝ)
    (hrec : ∀ k, f k = P (f (k + 1))) (r m : ℕ) :
    f r = ((P (n := n))^[m]) (f (r + m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        f r = ((P (n := n))^[m]) (f (r + m)) := ih
        _ = ((P (n := n))^[m + 1]) (f (r + (m + 1))) := by
          rw [Function.iterate_succ_apply, ← Nat.add_assoc]
          exact congrArg ((P (n := n))^[m]) (hrec (r + m))

/-- A nonnegative family harmonic backwards under finite cyclic averaging
is phase-constant at every level, with its common value fixed by the
initial total mass. The terminal vector varies with the mixing-block
number. Its mass bound supplies the uniform estimate required below. -/
theorem backward_nonnegative_harmonic_constant
    (f : ℕ → ZMod n → ℝ)
    (hf : ∀ k j, 0 ≤ f k j)
    (hrec : ∀ k j, f k j = (f (k + 1) j + f (k + 1) (j + 1)) / 2) :
    ∀ k j, f k j = (∑ x, f 0 x) / (n : ℝ) := by
  let S : ℝ := ∑ x, f 0 x
  let μ : ℝ := S / (n : ℝ)
  have hrecFun : ∀ k, f k = P (f (k + 1)) := by
    intro k
    funext j
    exact hrec k j
  have hS : 0 ≤ S := Finset.sum_nonneg (fun x _ => hf 0 x)
  have hsum : ∀ k, (∑ x, f k x) = S := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        calc
          (∑ x, f (k + 1) x) = ∑ x, P (f (k + 1)) x := (P_sum _).symm
          _ = ∑ x, f k x := by rw [← hrecFun k]
          _ = S := ih
  have hupper : ∀ k j, f k j ≤ S := by
    intro k j
    rw [← hsum k]
    exact Finset.single_le_sum (fun x _ => hf k x) (Finset.mem_univ j)
  have hμ0 : 0 ≤ μ := div_nonneg hS nat_real_pos.le
  have hμS : μ ≤ S := by
    dsimp [μ]
    apply (div_le_iff₀ (nat_real_pos (n := n))).2
    have hmul := mul_le_mul_of_nonneg_left (nat_real_one_le (n := n)) hS
    simpa only [mul_one] using hmul
  have hcenterSum : ∀ t, (∑ x, (f t x - μ)) = 0 := by
    intro t
    rw [Finset.sum_sub_distrib, hsum t]
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    dsimp [μ]
    field_simp [ne_of_gt (nat_real_pos (n := n))] <;> ring
  have hcenterBound : ∀ t j, |f t j - μ| ≤ S := by
    intro t j
    apply abs_le.mpr
    constructor <;> linarith [hf t j, hupper t j]
  intro r j
  have hbound : ∀ k : ℕ, |f r j - μ| ≤ (q n)^k * S := by
    intro k
    let g : ℕ → ZMod n → ℝ := fun t x => f (r + t * blockLength n) x - μ
    have h := P_variable_terminal_abs_le g
      (fun t => hcenterSum (r + t * blockLength n)) hS
      (fun t x => hcenterBound (r + t * blockLength n) x) k j
    have heq : ((P (n := n))^[k * blockLength n]) (g k) j = f r j - μ := by
      change ((P (n := n))^[k * blockLength n])
        (fun x => f (r + k * blockLength n) x - μ) j = f r j - μ
      rw [P_iterate_sub_const]
      exact congrArg (fun v : ZMod n → ℝ => v j - μ)
        (backward_iterate f hrecFun r (k * blockLength n)).symm
    rw [heq] at h
    exact h
  have hz := eq_zero_of_uniform_geom_bound
    (q_nonneg (n := n)) (q_lt_one (n := n)) hS hbound
  exact sub_eq_zero.mp hz

end IDT.QMClosure.FiniteCyclicAveraging

end
