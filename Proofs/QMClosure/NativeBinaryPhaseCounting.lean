import Mathlib.Tactic

/-!
# Binary phase counts and conditional mass selection

`phaseCount` counts a binary refinement by its number of B choices modulo four:
an A choice keeps the phase and a B choice advances it. The recurrence, rather
than a fitted finite table, defines every depth. A concrete native-circuit tree
adapter must separately identify its leaf cardinalities with these counts.

The final theorem concerns nonnegative real weights satisfying two displayed
mass identities at every required depth. It does not itself construct native
trees, prove a probability embedding contract, select a physical probability
law, or establish QM closure. Its limit step uses only the Archimedean order
of the real numbers, with no continuity premise on the varying weights.
-/

namespace IDT.QMClosure.NativeBinaryPhaseCounting

noncomputable section
open scoped BigOperators
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def phasePred (r : Fin 4) : Fin 4 :=
  match r.val with
  | 0 => 3
  | 1 => 0
  | 2 => 1
  | _ => 2

def phaseCount : ℕ → Fin 4 → ℕ
  | 0 => fun r => if r.val = 0 then 1 else 0
  | m + 1 => fun r => phaseCount m r + phaseCount m (phasePred r)

theorem phaseCount_zero : phaseCount 0 = ![1, 0, 0, 0] := by
  funext r
  fin_cases r <;> rfl
theorem phaseCount_succ (m : ℕ) (r : Fin 4) :
    phaseCount (m + 1) r = phaseCount m r + phaseCount m (phasePred r) := rfl

/-- A later binary-leaf cardinality adapter needs only this base and recurrence. -/
theorem phaseCount_unique (f : ℕ → Fin 4 → ℕ)
    (hzero : f 0 = ![1, 0, 0, 0])
    (hstep : ∀ m r, f (m + 1) r = f m r + f m (phasePred r)) :
    ∀ m, f m = phaseCount m := by
  intro m
  induction m with
  | zero => exact hzero.trans phaseCount_zero.symm
  | succ m ih =>
    funext r
    rw [hstep, ih, phaseCount_succ]

def realCount (m : ℕ) (r : Fin 4) : ℝ := phaseCount m r

theorem realCount_succ (m : ℕ) (r : Fin 4) :
    realCount (m + 1) r = realCount m r + realCount m (phasePred r) := by
  simp [realCount, phaseCount]

def fourStep (v : Fin 4 → ℝ) (r : Fin 4) : ℝ :=
  match r.val with
  | 0 => 2*v 0 + 4*v 1 + 6*v 2 + 4*v 3
  | 1 => 4*v 0 + 2*v 1 + 4*v 2 + 6*v 3
  | 2 => 6*v 0 + 4*v 1 + 2*v 2 + 4*v 3
  | _ => 4*v 0 + 6*v 1 + 4*v 2 + 2*v 3

theorem realCount_four_step (m : ℕ) : realCount (m + 4) = fourStep (realCount m) := by
  funext r
  fin_cases r
  · change realCount (m + 4) 0 = fourStep (realCount m) 0
    norm_num [realCount, phaseCount, phasePred, fourStep]
    ring
  · change realCount (m + 4) 1 = fourStep (realCount m) 1
    norm_num [realCount, phaseCount, phasePred, fourStep]
    ring
  · change realCount (m + 4) 2 = fourStep (realCount m) 2
    norm_num [realCount, phaseCount, phasePred, fourStep]
    ring
  · change realCount (m + 4) 3 = fourStep (realCount m) 3
    norm_num [realCount, phaseCount, phasePred, fourStep]
    ring

def fourForm (k : ℕ) (r : Fin 4) : ℝ :=
  match r.val with
  | 0 => ((16 : ℝ)^k + 2*(-4 : ℝ)^k)/4
  | 1 => (16 : ℝ)^k/4
  | 2 => ((16 : ℝ)^k - 2*(-4 : ℝ)^k)/4
  | _ => (16 : ℝ)^k/4

def nextForm (k : ℕ) (r : Fin 4) : ℝ :=
  match r.val with
  | 0 => ((16 : ℝ)^k + (-4 : ℝ)^k)/2
  | 1 => ((16 : ℝ)^k + (-4 : ℝ)^k)/2
  | _ => ((16 : ℝ)^k - (-4 : ℝ)^k)/2

/-- The exceptional depth zero is excluded explicitly. -/
theorem phaseCount_four (k : ℕ) (hk : 1 ≤ k) : realCount (4*k) = fourForm k := by
  cases k with
  | zero => omega
  | succ l =>
    induction l with
    | zero =>
      funext r
      fin_cases r <;> norm_num [realCount, phaseCount, phasePred, fourForm]
    | succ l ih =>
      rw [show 4*(l+1+1) = 4*(l+1)+4 by omega, realCount_four_step, ih (by omega)]
      funext r
      fin_cases r <;> simp [fourStep, fourForm, pow_succ] <;> ring

theorem phaseCount_four_add_one (k : ℕ) (hk : 1 ≤ k) :
    realCount (4*k+1) = nextForm k := by
  funext r
  rw [realCount_succ]
  rw [phaseCount_four k hk]
  fin_cases r <;> simp [fourForm, nextForm, phasePred] <;> ring

theorem four_pow_square (k : ℕ) : (16 : ℝ)^k = (4 : ℝ)^k * (4 : ℝ)^k := by
  rw [← mul_pow]
  norm_num

theorem coefficient_lower (k : ℕ) (hk : 1 ≤ k) (r : Fin 4) :
    (4 : ℝ)^k * ((4 : ℝ)^k - 1) / 2 ≤ realCount (4*k+1) r := by
  have hs : |(-4 : ℝ)^k| = (4 : ℝ)^k := by simp [abs_pow]
  have hsb := abs_le.mp (le_of_eq hs)
  have hp := four_pow_square k
  rw [phaseCount_four_add_one k hk]
  fin_cases r <;> simp only [nextForm] <;> nlinarith [hsb.1, hsb.2]

theorem coefficient_deviation (k : ℕ) (hk : 1 ≤ k) (r : Fin 4) :
    |realCount (4*k) r - realCount (4*k+1) r / 2| ≤ (4 : ℝ)^k / 4 := by
  have hs : |(-4 : ℝ)^k| = (4 : ℝ)^k := by simp [abs_pow]
  have hsb := abs_le.mp (le_of_eq hs)
  rw [phaseCount_four k hk, phaseCount_four_add_one k hk]
  fin_cases r <;> simp only [fourForm, nextForm] <;>
    rw [abs_le] <;> constructor <;> nlinarith [hsb.1, hsb.2]

theorem nat_add_one_le_four_pow (k : ℕ) : (k : ℝ) + 1 ≤ (4 : ℝ)^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- A finite-depth bound; weights may vary freely between different depths. -/
theorem mass_deviation_mul_bound (k : ℕ) (hk : 1 ≤ k)
    (q : Fin 4 → ℝ) (hq : ∀ j, 0 ≤ q j) (p r : ℝ)
    (hp : ∑ j, realCount (4*k+1) j * q j = p)
    (hr : ∑ j, realCount (4*k) j * q j = r) :
    2*((4 : ℝ)^k-1)*|r-p/2| ≤ p := by
  let M : ℝ := (4 : ℝ)^k
  have hM : 1 < M := by
    have h := nat_add_one_le_four_pow k
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    dsimp [M]
    linarith
  have hlow : M*(M-1)/2 * (∑ j, q j) ≤ p := by
    calc
      _ = ∑ j, (M*(M-1)/2) * q j := Finset.mul_sum _ _ _
      _ ≤ ∑ j, realCount (4*k+1) j * q j :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right
          (coefficient_lower k hk j) (hq j))
      _ = p := hp
  have herr : |r-p/2| ≤ M/4 * (∑ j, q j) := by
    calc
      |r-p/2| = |∑ j, (realCount (4*k) j - realCount (4*k+1) j / 2) * q j| := by
        congr 1
        rw [← hr, ← hp]
        simp only [sub_mul, div_mul_eq_mul_div, Finset.sum_sub_distrib,
          Finset.sum_div]
      _ ≤ ∑ j, |(realCount (4*k) j - realCount (4*k+1) j / 2) * q j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, (M/4) * q j := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_of_nonneg (hq j)]
        exact mul_le_mul_of_nonneg_right (coefficient_deviation k hk j) (hq j)
      _ = M/4 * (∑ j, q j) := (Finset.mul_sum _ _ _).symm
  have hmul := mul_le_mul_of_nonneg_left herr (by linarith : 0 ≤ 2*(M-1))
  change 2*(M-1)*|r-p/2| ≤ p
  nlinarith

theorem mass_deviation_bound (k : ℕ) (hk : 1 ≤ k)
    (q : Fin 4 → ℝ) (hq : ∀ j, 0 ≤ q j) (p r : ℝ)
    (hp : ∑ j, realCount (4*k+1) j * q j = p)
    (hr : ∑ j, realCount (4*k) j * q j = r) :
    |r-p/2| ≤ p / (2*((4 : ℝ)^k-1)) := by
  have h := nat_add_one_le_four_pow k
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  apply (le_div_iff₀ (by linarith : 0 < 2*((4 : ℝ)^k-1))).mpr
  simpa [mul_comm] using mass_deviation_mul_bound k hk q hq p r hp hr

/-- Conditional real-mass selection, with no continuity assumption on any weights. -/
theorem phase_count_mass_halving (p r : ℝ)
    (h : ∀ k : ℕ, 1 ≤ k → ∃ q : Fin 4 → ℝ, (∀ j, 0 ≤ q j) ∧
      (∑ j, (phaseCount (4*k+1) j : ℝ) * q j) = p ∧
      (∑ j, (phaseCount (4*k) j : ℝ) * q j) = r) : r = p/2 := by
  by_contra he
  have hd : 0 < |r-p/2| := abs_pos.mpr (sub_ne_zero.mpr he)
  obtain ⟨n, hn⟩ := exists_nat_gt (p / (2*|r-p/2|))
  have hp : p < (n : ℝ) * (2*|r-p/2|) :=
    (div_lt_iff₀ (by positivity : 0 < 2*|r-p/2|)).mp hn
  obtain ⟨q, hq, htotal, hbranch⟩ := h (n+1) (by omega)
  have hb := mass_deviation_mul_bound (n+1) (by omega) q hq p r htotal hbranch
  have hpow := nat_add_one_le_four_pow (n+1)
  push_cast at hpow
  have hmul := mul_le_mul_of_nonneg_right hpow (le_of_lt hd)
  nlinarith

end
end IDT.QMClosure.NativeBinaryPhaseCounting
