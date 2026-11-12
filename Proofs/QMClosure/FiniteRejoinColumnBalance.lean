import Proofs.QMClosure.FiniteCyclicAveraging
import Proofs.QMClosure.TransparentPositivePowerRejoin

/-!
# Finite-rejoin first-column balance

The numerical finite-cycle rigidity theorem supplies the balance argument.
Only pair commutation is derived. The ambient semiring is arbitrary.
-/

noncomputable section

namespace IDT.QMClosure.FiniteRejoinColumnBalance

open IDT.TransparentPositivePowerRejoin

variable {S : Type*} [Semiring S] {a b : S} {n : ℕ}

/-- The positive inverse word for the second branch of an equal rejoin. -/
def bInv (a b : S) (n : ℕ) : S :=
  inverseWordB a b (n - 1) (n - 1)

/-- The actual finite-phase preparation, constructed from positive words. -/
def rho (a b : S) (n : ℕ) : S :=
  a * bInv a b n

private theorem inverse_power_right {x y : S} (hxy : x * y = 1) (k : ℕ) :
    x ^ k * y ^ k = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        x ^ (k + 1) * y ^ (k + 1) = x ^ k * (x * y) * y ^ k := by
          rw [pow_succ, pow_succ']
          simp only [mul_assoc]
        _ = 1 := by rw [hxy, mul_one, ih]

/-- The explicit phase has the required branch, commutation and period identities. -/
theorem rho_data (hn : 0 < n) (hsum : a + b = 1) (hcycle : a ^ n = b ^ n) :
    rho a b n * b = a ∧ b * rho a b n = a ∧
      Commute (rho a b n) b ∧ rho a b n ^ n = 1 := by
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_of_lt hn)
  have hinv : bInv a b n * b = 1 ∧ b * bInv a b n = 1 := by
    exact geometric_inverse_b (n - 1) (n - 1) hsum
      (by simpa only [hpred] using hcycle)
  have hab := commute_of_transparent_finite_rejoin n hn hsum hcycle
  have hrb : rho a b n * b = a := by
    change (a * bInv a b n) * b = a
    rw [mul_assoc, hinv.1, mul_one]
  have hbr : b * rho a b n = a := by
    change b * (a * bInv a b n) = a
    calc
      b * (a * bInv a b n) = (b * a) * bInv a b n := (mul_assoc _ _ _).symm
      _ = (a * b) * bInv a b n := by rw [hab.eq]
      _ = a * (b * bInv a b n) := mul_assoc _ _ _
      _ = a := by rw [hinv.2, mul_one]
  have hcomm : Commute (rho a b n) b := by
    change rho a b n * b = b * rho a b n
    exact hrb.trans hbr.symm
  have hpow : rho a b n ^ n * b ^ n = b ^ n := by
    rw [← hcomm.mul_pow, hrb, hcycle]
  have hcancel := inverse_power_right hinv.2 n
  refine ⟨hrb, hbr, hcomm, ?_⟩
  calc
    rho a b n ^ n = rho a b n ^ n * (b ^ n * bInv a b n ^ n) := by
      rw [hcancel, mul_one]
    _ = (rho a b n ^ n * b ^ n) * bInv a b n ^ n := (mul_assoc _ _ _).symm
    _ = b ^ n * bInv a b n ^ n := by rw [hpow]
    _ = 1 := hcancel

private theorem power_mod_cycle {r : S} (hr : r ^ n = 1) (k : ℕ) :
    r ^ (k % n) = r ^ k := by
  calc
    r ^ (k % n) = r ^ (k % n) * (r ^ n) ^ (k / n) := by rw [hr]; simp
    _ = r ^ (k % n + n * (k / n)) := by rw [pow_add, pow_mul]
    _ = r ^ k := by rw [Nat.mod_add_div]

/-- Successor phases wrap correctly, including the one-point cycle. -/
private theorem cyclic_power_step [NeZero n] {r : S} (hr : r ^ n = 1)
    (j : ZMod n) : r ^ (j + 1).val = r ^ (j.val + 1) := by
  by_cases hn1 : n = 1
  · subst n
    have hr1 : r = 1 := by simpa only [pow_one] using hr
    simp [hr1]
  · rw [ZMod.val_add, ZMod.val_one'' hn1, power_mod_cycle hr]

/-- Nonnegative first-column conservation forces invariance under the
explicit finite phase. The numerical rigidity theorem is an imported proof. -/
theorem phase_invariant (hn : 0 < n) (hsum : a + b = 1)
    (hcycle : a ^ n = b ^ n) (W : S → ℝ)
    (hnonneg : ∀ p, 0 ≤ W p)
    (hcolumn : ∀ p, W (a * p) + W (b * p) = W p) :
    ∀ p, W (rho a b n * p) = W p := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨hrb, hbr, hcomm, hperiod⟩ := rho_data hn hsum hcycle
  intro p
  let f : ℕ → ZMod n → ℝ :=
    fun k j => (2 : ℝ) ^ k * W (b ^ k * rho a b n ^ j.val * p)
  have hf : ∀ k j, 0 ≤ f k j := by
    intro k j
    exact mul_nonneg (pow_nonneg (by norm_num) k) (hnonneg _)
  have hrec : ∀ k j, f k j = (f (k + 1) j + f (k + 1) (j + 1)) / 2 := by
    intro k j
    have hA : a * (b ^ k * rho a b n ^ j.val * p) =
        b ^ (k + 1) * rho a b n ^ (j + 1).val * p := by
      calc
        a * (b ^ k * rho a b n ^ j.val * p) =
            (b * rho a b n) * b ^ k * rho a b n ^ j.val * p := by
          rw [hbr]
          simp only [mul_assoc]
        _ = b * (rho a b n * b ^ k) * rho a b n ^ j.val * p := by
          simp only [mul_assoc]
        _ = b * (b ^ k * rho a b n) * rho a b n ^ j.val * p := by
          rw [(hcomm.pow_right k).eq]
        _ = (b * b ^ k) * (rho a b n * rho a b n ^ j.val) * p := by
          simp only [mul_assoc]
        _ = b ^ (k + 1) * rho a b n ^ (j.val + 1) * p := by
          rw [← pow_succ', ← pow_succ']
        _ = b ^ (k + 1) * rho a b n ^ (j + 1).val * p := by
          rw [cyclic_power_step hperiod]
    have hB : b * (b ^ k * rho a b n ^ j.val * p) =
        b ^ (k + 1) * rho a b n ^ j.val * p := by
      rw [pow_succ']
      simp only [mul_assoc]
    have hscaled := congrArg (fun x : ℝ => (2 : ℝ) ^ k * x)
      (hcolumn (b ^ k * rho a b n ^ j.val * p))
    rw [hA, hB] at hscaled
    dsimp [f]
    simp only [pow_succ] at hscaled ⊢
    nlinarith only [hscaled]
  have hconstant :=
    FiniteCyclicAveraging.backward_nonnegative_harmonic_constant f hf hrec
  have hone : rho a b n ^ (1 : ZMod n).val = rho a b n := by
    simpa only [zero_add, ZMod.val_zero, zero_add, pow_one] using
      (cyclic_power_step hperiod (0 : ZMod n))
  have heq := (hconstant 0 (1 : ZMod n)).trans (hconstant 0 (0 : ZMod n)).symm
  simpa only [f, pow_zero, one_mul, ZMod.val_zero, hone] using heq

/-- Every natural power of the constructed finite phase preserves the response. -/
theorem phase_power_invariant (hn : 0 < n) (hsum : a + b = 1)
    (hcycle : a ^ n = b ^ n) (W : S → ℝ)
    (hnonneg : ∀ p, 0 ≤ W p)
    (hcolumn : ∀ p, W (a * p) + W (b * p) = W p) (k : ℕ) :
    ∀ p, W (rho a b n ^ k * p) = W p := by
  intro p
  induction k with
  | zero => simp
  | succ k ih =>
      have h := phase_invariant hn hsum hcycle W hnonneg hcolumn
        (rho a b n ^ k * p)
      simpa only [pow_succ', mul_assoc] using h.trans ih

/-- Exact terminal interface. No additional readout premises are supplied. -/
theorem half_responses {S : Type*} [Semiring S] {a b : S} {n : Nat}
    (hn : 0 < n) (hsum : a + b = 1) (hcycle : a ^ n = b ^ n)
    (W : S → Real) (hnonneg : ∀ p, 0 ≤ W p)
    (hcolumn : ∀ p, W (a * p) + W (b * p) = W p) :
    ∀ p, W (a * p) = W p / 2 ∧ W (b * p) = W p / 2 := by
  obtain ⟨hrb, _, _, _⟩ := rho_data hn hsum hcycle
  intro p
  have hbalance := phase_invariant hn hsum hcycle W hnonneg hcolumn (b * p)
  rw [← mul_assoc, hrb] at hbalance
  have hsumResponse := hcolumn p
  constructor <;> linarith

end IDT.QMClosure.FiniteRejoinColumnBalance

end
