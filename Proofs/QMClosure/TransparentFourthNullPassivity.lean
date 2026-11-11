import Proofs.QMClosure.TransparentFourthInitialHistoryPresentation

/-!
# Fixed-defect passivity and null-sector insertion

Lean kernel-checked conditional readout criteria.
The statements concern the literal positive fourth-rejoin presentation.
All readout laws and the global one-sided inequality are supplied premises.
The equivalence proved here is a local criterion under those premises.
-/

namespace IDT.QMClosure.TransparentFourthNullPassivity

noncomputable section

open TransparentFourthInitialHistoryPresentation

abbrev P := TransparentFourthInitialHistoryPresentation.Presentation

def c : P := 2 * a * b

def FixedTNonincrease (W : P → ℝ) : Prop := ∀ x, W (x + T) ≤ W x

def FixedTNondecrease (W : P → ℝ) : Prop := ∀ x, W x ≤ W (x + T)

def NullInsertion (W : P → ℝ) : Prop := ∀ x p, W (x + e * p) = W x

lemma e_mul_a : e * a = T :=
  (FourthRejoinIdempotent.pair_mul_sector pairContract).2.2.1

lemma e_mul_b : e * b = T :=
  (FourthRejoinIdempotent.pair_mul_sector pairContract).2.2.2

lemma e_mul_T : e * T = T :=
  FourthRejoinIdempotent.sector_mul_defect pairContract

lemma e_eq_two_mul_ea : e = 2 * (e * a) := by
  calc
    e = 2 * T := rfl
    _ = 2 * (e * a) := by rw [e_mul_a]

lemma c_mul_e : c * e = T := by
  calc
    c * e = (2 : P) * (e * a) * b := by unfold c; ring
    _ = (2 : P) * T * b := by rw [e_mul_a]
    _ = e * b := by rfl
    _ = T := e_mul_b

lemma c_add_T : c + T = 1 := by
  simpa only [c, T, FourthRejoinIdempotent.defect, mul_assoc,
    add_comm] using FourthRejoinIdempotent.transparency_square
      pairContract.commute pairContract.sum

lemma c_mul_one_add_e : c * (1 + e) = 1 := by
  rw [mul_add, mul_one, c_mul_e, c_add_T]

lemma c_mul_T : c * T = a * T := by
  calc
    c * T = c * (e * a) := by rw [e_mul_a]
    _ = (c * e) * a := by ring
    _ = a * T := by rw [c_mul_e]; ring

lemma sector_monomial_refine (d k : ℕ) :
    e * a ^ d = (2 : P) ^ k * (e * a ^ (d + k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        e * a ^ d = (2 : P) ^ k * (e * a ^ (d + k)) := ih
        _ = (2 : P) ^ k * ((2 * (e * a)) * a ^ (d + k)) := by
          rw [← e_eq_two_mul_ea]
        _ = (2 : P) ^ (k + 1) * (e * a ^ (d + (k + 1))) := by
          rw [pow_succ, show d + (k + 1) = (d + k) + 1 by omega, pow_succ]
          ring

lemma sector_monomial_mul (d k : ℕ) :
    (e * a ^ d) * (e * a ^ k) = e * a ^ (d + k) := by
  calc
    (e * a ^ d) * (e * a ^ k) = (e * e) * (a ^ d * a ^ k) := by ring
    _ = e * a ^ (d + k) := by rw [e_idempotent, pow_add]

/-- The e-supported positive grammar has one dyadic monomial normal form. -/
theorem sector_normal_form (p : P) :
    ∃ N d : ℕ, e * p = (N : P) * (e * a ^ d) := by
  apply presentation_induction
    (motive := fun p => ∃ N d : ℕ, e * p = (N : P) * (e * a ^ d))
  · exact ⟨0, 0, by simp⟩
  · exact ⟨1, 0, by simp⟩
  · exact ⟨1, 1, by simp⟩
  · exact ⟨1, 1, by simp only [Nat.cast_one, pow_one, one_mul, e_mul_b, e_mul_a]⟩
  · intro x y hx hy
    obtain ⟨N, d, hN⟩ := hx
    obtain ⟨M, k, hM⟩ := hy
    refine ⟨N * 2 ^ k + M * 2 ^ d, d + k, ?_⟩
    calc
      e * (x + y) = e * x + e * y := mul_add _ _ _
      _ = (N : P) * (e * a ^ d) + (M : P) * (e * a ^ k) := by rw [hN, hM]
      _ = (N : P) * ((2 : P) ^ k * (e * a ^ (d + k))) +
          (M : P) * ((2 : P) ^ d * (e * a ^ (d + k))) := by
        rw [sector_monomial_refine d k, sector_monomial_refine k d,
          Nat.add_comm k d]
      _ = ((N * 2 ^ k + M * 2 ^ d : ℕ) : P) * (e * a ^ (d + k)) := by
        push_cast
        ring
  · intro x y hx hy
    obtain ⟨N, d, hN⟩ := hx
    obtain ⟨M, k, hM⟩ := hy
    refine ⟨N * M, d + k, ?_⟩
    calc
      e * (x * y) = (e * e) * (x * y) := by rw [e_idempotent]
      _ = (e * x) * (e * y) := by ring
      _ = ((N : P) * (e * a ^ d)) * ((M : P) * (e * a ^ k)) := by rw [hN, hM]
      _ = ((N * M : ℕ) : P) * (e * a ^ (d + k)) := by
        rw [Nat.cast_mul]
        calc
          _ = ((N : P) * M) * ((e * a ^ d) * (e * a ^ k)) := by ring
          _ = _ := by rw [sector_monomial_mul]

lemma positive_normal_coefficient {p : P} (hp : p ≠ 0) {N d : ℕ}
    (h : e * p = (N : P) * (e * a ^ d)) : 0 < N := by
  by_contra hn
  have hN : N = 0 := by omega
  have hz : e * p = 0 := by simpa only [hN, Nat.cast_zero, zero_mul] using h
  have hs := congrArg shadow hz
  simp only [map_mul, shadow_e, one_mul, map_zero] at hs
  exact hp (shadow_zero_detection p hs)

/-- Two null-sector terms admit a common dyadic degree. -/
theorem common_sector_normal_form (x p : P) :
    ∃ N M d : ℕ,
      e * x = (N : P) * (e * a ^ d) ∧
      e * p = (M : P) * (e * a ^ d) := by
  obtain ⟨N, d, hN⟩ := sector_normal_form x
  obtain ⟨M, k, hM⟩ := sector_normal_form p
  refine ⟨N * 2 ^ k, M * 2 ^ d, d + k, ?_, ?_⟩
  · rw [hN, sector_monomial_refine d k]
    push_cast
    ring
  · rw [hM, sector_monomial_refine k d, Nat.add_comm k d]
    push_cast
    ring

lemma c_pow_mul_T (d : ℕ) : c ^ d * T = T * a ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        c ^ (d + 1) * T = c * (c ^ d * T) := by rw [pow_succ]; ring
        _ = c * (T * a ^ d) := by rw [ih]
        _ = (c * T) * a ^ d := by ring
        _ = T * a ^ (d + 1) := by rw [c_mul_T, pow_succ]; ring

lemma c_pow_mul_inverse (d : ℕ) : c ^ d * (1 + e) ^ d = 1 := by
  rw [← mul_pow, c_mul_one_add_e, one_pow]

section Readout

variable (W : P → ℝ) (hhalf : ∀ p, W (a * p) = W p / 2)
  (htrans : ∀ p, W (c * p) = W p)

include htrans in
lemma readout_c_pow (d : ℕ) (p : P) : W (c ^ d * p) = W p := by
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        W (c ^ (d + 1) * p) = W (c * (c ^ d * p)) := by congr 1; rw [pow_succ]; ring
        _ = W (c ^ d * p) := htrans _
        _ = W p := ih

include htrans in
lemma readout_inverse_pow (d : ℕ) (p : P) : W ((1 + e) ^ d * p) = W p := by
  have h := readout_c_pow W htrans d ((1 + e) ^ d * p)
  rw [← mul_assoc, c_pow_mul_inverse, one_mul] at h
  exact h.symm

include hhalf htrans in
lemma sector_readout_zero (p : P) : W (e * p) = 0 := by
  have ht := htrans (e * p)
  have hh := hhalf (e * p)
  have hc : c * (e * p) = a * (e * p) := by
    calc
      c * (e * p) = (c * e) * p := by ring
      _ = (e * a) * p := by rw [c_mul_e, e_mul_a]
      _ = a * (e * p) := by ring
  rw [hc] at ht
  linarith

include hhalf htrans in
lemma zero_readout : W 0 = 0 := by
  simpa using sector_readout_zero W hhalf htrans 0

include htrans in
/-- Transport uses only the supplied c invariance and its positive inverse. -/
lemma fixedT_to_monomial_nonincrease (hpass : FixedTNonincrease W) (d : ℕ) (x : P) :
    W (x + T * a ^ d) ≤ W x := by
  have h := hpass ((1 + e) ^ d * x)
  have hleft : c ^ d * ((1 + e) ^ d * x + T) = x + T * a ^ d := by
    rw [mul_add, ← mul_assoc, c_pow_mul_inverse, one_mul, c_pow_mul_T]
  have hl := readout_c_pow W htrans d ((1 + e) ^ d * x + T)
  rw [hleft] at hl
  rw [← hl, readout_inverse_pow W htrans d x] at h
  exact h

lemma repeated_shift_nonincrease {z : P}
    (hz : ∀ x, W (x + z) ≤ W x) (n : ℕ) (x : P) :
    W (x + (n : P) * z) ≤ W x := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        W (x + ((n + 1 : ℕ) : P) * z) = W ((x + (n : P) * z) + z) := by
          congr 1
          push_cast
          ring
        _ ≤ W (x + (n : P) * z) := hz _
        _ ≤ W x := ih

include htrans in
lemma sector_insertion_nonincrease (hpass : FixedTNonincrease W) (x p : P) :
    W (x + e * p) ≤ W x := by
  obtain ⟨N, d, hN⟩ := sector_normal_form p
  have hz := fixedT_to_monomial_nonincrease W htrans hpass d
  have h := repeated_shift_nonincrease W hz (2 * N) x
  have he : ((2 * N : ℕ) : P) * (T * a ^ d) = e * p := by
    rw [hN, e, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rwa [he] at h

end Readout

lemma two_pow_ge_succ (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

lemma inverse_pow_expansion (n : ℕ) (x : P) :
    (1 + e) ^ n * x = x + (((2 ^ n - 1 : ℕ) : P) * (e * x)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpos : 1 ≤ 2 ^ n := by
        have hbound := two_pow_ge_succ n
        omega
      have hcoef : 2 ^ (n + 1) - 1 = (2 ^ n - 1) + (2 ^ n - 1) + 1 := by
        rw [pow_succ]
        omega
      calc
        (1 + e) ^ (n + 1) * x = (1 + e) * ((1 + e) ^ n * x) := by rw [pow_succ]; ring
        _ = (1 + e) * (x + (((2 ^ n - 1 : ℕ) : P) * (e * x))) := by rw [ih]
        _ = x + (((2 ^ (n + 1) - 1 : ℕ) : P) * (e * x)) := by
          rw [hcoef]
          push_cast
          have hid : e * (e * x) = e * x := by rw [← mul_assoc, e_idempotent]
          calc
            _ = x + (((2 ^ n - 1 : ℕ) : P) * (e * x) +
              (((2 ^ n - 1 : ℕ) : P) * (e * (e * x))) + e * x) := by ring
            _ = _ := by rw [hid]; ring

/-- At every nonzero base preparation, c invariance and one global fixed-T
inequality suffice. The value at zero is absent from this statement. -/
theorem nonzero_null_insertion_of_fixedT_nonincrease (W : P → ℝ)
    (htrans : ∀ p, W (c * p) = W p)
    (hpass : FixedTNonincrease W) (x : P) (hx : x ≠ 0) (p : P) :
    W (x + e * p) = W x := by
  obtain ⟨N, M, d, hN, hM⟩ := common_sector_normal_form x p
  have hNpos : 0 < N := positive_normal_coefficient hx hN
  let K : ℕ := 2 ^ M - 1
  have hMle : M ≤ K := by dsimp [K]; have := two_pow_ge_succ M; omega
  have hlarge : M ≤ K * N := by
    have hKN : K ≤ K * N := by nlinarith
    exact hMle.trans hKN
  let r : P := ((K * N - M : ℕ) : P) * a ^ d
  have hbalance : (K : P) * (e * x) = e * p + e * r := by
    rw [hN, hM]
    dsimp [r]
    have hcoef : K * N = M + (K * N - M) := by omega
    calc
      (K : P) * ((N : P) * (e * a ^ d)) = ((K * N : ℕ) : P) * (e * a ^ d) := by
        push_cast
        ring
      _ = ((M : P) + ((K * N - M : ℕ) : P)) * (e * a ^ d) := by
        apply congrArg (fun n : P => n * (e * a ^ d))
        simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : P)) hcoef
      _ = _ := by ring
  have hinv : W (x + e * p + e * r) = W x := by
    have hi := readout_inverse_pow W htrans M x
    rw [inverse_pow_expansion] at hi
    change W (x + (K : P) * (e * x)) = W x at hi
    rw [hbalance] at hi
    simpa only [add_assoc] using hi
  apply le_antisymm
  · exact sector_insertion_nonincrease W htrans hpass x p
  · calc
      W x = W ((x + e * p) + e * r) := hinv.symm
      _ ≤ W (x + e * p) := sector_insertion_nonincrease W htrans hpass _ r

/-- The extra scalar calibration exactly supplies the missing zero-base case. -/
theorem nullInsertion_of_calibrated_fixedT_nonincrease (W : P → ℝ)
    (htrans : ∀ p, W (c * p) = W p)
    (hcal : W T = W 0)
    (hpass : FixedTNonincrease W) : NullInsertion W := by
  have hsector : ∀ p, W (e * p) = W 0 := by
    intro p
    by_cases hp : e * p = 0
    · rw [hp]
    · have hfirst := nonzero_null_insertion_of_fixedT_nonincrease W htrans hpass
        (e * p) hp T
      have hsecond := nonzero_null_insertion_of_fixedT_nonincrease W htrans hpass
        T T_ne_zero p
      rw [e_mul_T] at hfirst
      calc
        W (e * p) = W (e * p + T) := hfirst.symm
        _ = W (T + e * p) := by rw [add_comm]
        _ = W T := hsecond
        _ = W 0 := hcal
  intro x p
  by_cases hx : x = 0
  · subst x
    simpa only [zero_add] using hsector p
  · exact nonzero_null_insertion_of_fixedT_nonincrease W htrans hpass x hx p

/-- The earlier half-context law supplies calibration as a special case. -/
theorem nullInsertion_of_fixedT_nonincrease (W : P → ℝ)
    (hhalf : ∀ p, W (a * p) = W p / 2)
    (htrans : ∀ p, W (c * p) = W p)
    (hpass : FixedTNonincrease W) : NullInsertion W := by
  apply nullInsertion_of_calibrated_fixedT_nonincrease W htrans _ hpass
  have hT := sector_readout_zero W hhalf htrans T
  rw [e_mul_T] at hT
  exact hT.trans (zero_readout W hhalf htrans).symm

/-- Nonnegativity and a zero empty readout supply calibration in the
nonincrease direction. -/
theorem nullInsertion_of_nonnegative_fixedT_nonincrease (W : P → ℝ)
    (htrans : ∀ p, W (c * p) = W p)
    (hzero : W 0 = 0) (hnonnegative : ∀ p, 0 ≤ W p)
    (hpass : FixedTNonincrease W) : NullInsertion W := by
  apply nullInsertion_of_calibrated_fixedT_nonincrease W htrans _ hpass
  apply le_antisymm
  · simpa only [zero_add] using hpass 0
  · rw [hzero]
    exact hnonnegative T

/-- Negation transfers the calibrated statement to the reversed inequality. -/
theorem nullInsertion_of_calibrated_fixedT_nondecrease (W : P → ℝ)
    (htrans : ∀ p, W (c * p) = W p)
    (hcal : W T = W 0)
    (hpass : FixedTNondecrease W) : NullInsertion W := by
  have hn := nullInsertion_of_calibrated_fixedT_nonincrease (fun p => -W p)
    (by
      intro p
      change -W (c * p) = -W p
      rw [htrans])
    (by
      change -W T = -W 0
      rw [hcal])
    (by intro x; exact neg_le_neg (hpass x))
  intro x p
  have := hn x p
  linarith

/-- The same conclusion follows from the reversed global inequality. -/
theorem nullInsertion_of_fixedT_nondecrease (W : P → ℝ)
    (hhalf : ∀ p, W (a * p) = W p / 2)
    (htrans : ∀ p, W (c * p) = W p)
    (hpass : FixedTNondecrease W) : NullInsertion W := by
  have hn := nullInsertion_of_fixedT_nonincrease (fun p => -W p)
    (by
      intro p
      change -W (a * p) = -W p / 2
      rw [hhalf]
      ring)
    (by
      intro p
      change -W (c * p) = -W p
      rw [htrans])
    (by intro x; exact neg_le_neg (hpass x))
  intro x p
  have := hn x p
  linarith

lemma fixedT_equality_of_nullInsertion (W : P → ℝ) (hnull : NullInsertion W) :
    ∀ x, W (x + T) = W x := by
  intro x
  simpa only [e_mul_T] using hnull x T

theorem fixedT_nonincrease_iff_nullInsertion (W : P → ℝ)
    (hhalf : ∀ p, W (a * p) = W p / 2)
    (htrans : ∀ p, W (c * p) = W p) :
    FixedTNonincrease W ↔ NullInsertion W := by
  refine ⟨nullInsertion_of_fixedT_nonincrease W hhalf htrans, ?_⟩
  intro h x
  exact le_of_eq (fixedT_equality_of_nullInsertion W h x)


/-- The criterion is equivalent under its explicit invariance and calibration. -/
theorem calibrated_fixedT_nonincrease_iff_nullInsertion (W : P → ℝ)
    (htrans : ∀ p, W (c * p) = W p) (hcal : W T = W 0) :
    FixedTNonincrease W ↔ NullInsertion W := by
  refine ⟨nullInsertion_of_calibrated_fixedT_nonincrease W htrans hcal, ?_⟩
  intro h x
  exact le_of_eq (fixedT_equality_of_nullInsertion W h x)

end

end IDT.QMClosure.TransparentFourthNullPassivity
