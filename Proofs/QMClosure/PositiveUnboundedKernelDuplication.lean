import Mathlib

/-!
# Positive unrestricted Newton kernels

Every input uses only a finite rectangle of coefficients. No order cutoff,
continuity, limit argument or physics-specific representation is supplied.
The finite-difference identities below establish inversion and duplication.
-/

noncomputable section

namespace IDT.QMClosure.PositiveUnboundedKernelDuplication

open scoped BigOperators

abbrev Sequence := ℕ → ℝ
abbrev Kernel := ℕ → ℕ → ℝ

/-- The finite Newton transform of an unrestricted sequence. -/
def newton (c : Sequence) (n : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (n + 1), (n.choose r : ℝ) * c r

def difference (f : Sequence) : Sequence := fun n => f (n + 1) - f n

def coefficient (f : Sequence) (j : ℕ) : ℝ := ((difference^[j]) f) 0

theorem coefficient_succ (f : Sequence) (j : ℕ) :
    coefficient f (j + 1) = coefficient (difference f) j := by
  simp only [coefficient, Function.iterate_succ_apply]

theorem newton_succ (c : Sequence) (n : ℕ) :
    newton c (n + 1) = newton c n + newton (fun r => c (r + 1)) n := by
  simpa only [newton] using Finset.sum_choose_succ_mul (fun r _ => c r) n

theorem newton_add (c d : Sequence) :
    newton (fun r => c r + d r) = fun n => newton c n + newton d n := by
  funext n
  simp [newton, mul_add, Finset.sum_add_distrib]

theorem newton_smul (a : ℝ) (c : Sequence) :
    newton (fun r => a * c r) = fun n => a * newton c n := by
  funext n
  simp only [newton, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem difference_newton (c : Sequence) :
    difference (newton c) = newton (fun r => c (r + 1)) := by
  funext n
  rw [difference, newton_succ]
  ring

theorem coefficient_newton (c : Sequence) (j : ℕ) :
    coefficient (newton c) j = c j := by
  induction j generalizing c with
  | zero => simp [coefficient, newton]
  | succ j ih =>
      rw [coefficient_succ, difference_newton, ih]

/-- Finite Newton inversion, proved from Pascal recursion. -/
theorem newton_coefficient (f : Sequence) (n : ℕ) :
    newton (coefficient f) n = f n := by
  induction n generalizing f with
  | zero => simp [newton, coefficient]
  | succ n ih =>
      rw [newton_succ, ih]
      have hshift : (fun r => coefficient f (r + 1)) = coefficient (difference f) := by
        funext r
        exact coefficient_succ f r
      rw [hshift, ih]
      simp only [difference]
      ring

theorem newton_injective : Function.Injective newton := by
  intro c d h
  funext j
  simpa only [coefficient_newton] using congrArg (fun f => coefficient f j) h

theorem difference_sum {E : Type*} (s : Finset E) (f : E → Sequence) :
    difference (fun n => ∑ e ∈ s, f e n) =
      fun n => ∑ e ∈ s, difference (f e) n := by
  funext n
  simp [difference, Finset.sum_sub_distrib]

theorem difference_smul (a : ℝ) (f : Sequence) :
    difference (fun n => a * f n) = fun n => a * difference f n := by
  funext n
  simp only [difference]
  ring

theorem coefficient_sum {E : Type*} (s : Finset E) (f : E → Sequence) (j : ℕ) :
    coefficient (fun n => ∑ e ∈ s, f e n) j = ∑ e ∈ s, coefficient (f e) j := by
  induction j generalizing f with
  | zero => simp [coefficient]
  | succ j ih =>
      rw [coefficient_succ, difference_sum, ih]
      apply Finset.sum_congr rfl
      intro e he
      exact (coefficient_succ (f e) j).symm

theorem coefficient_smul (a : ℝ) (f : Sequence) (j : ℕ) :
    coefficient (fun n => a * f n) j = a * coefficient f j := by
  induction j generalizing f with
  | zero => simp [coefficient]
  | succ j ih =>
      rw [coefficient_succ, difference_smul, ih, coefficient_succ]

/-- A two-shift operator used solely to prove finite identities. -/
def weightedStep (a b : ℝ) (q : ℕ) (f : Sequence) : Sequence :=
  fun n => a * f (n + q) + b * f (n + q + 1)

/-- The binomial expansion of a finite iterate, including zero coefficients. -/
theorem weightedStep_iterate (a b : ℝ) (q : ℕ) (f : Sequence) (j n : ℕ) :
    ((weightedStep a b q)^[j]) f n =
      ∑ r ∈ Finset.range (j + 1),
        (j.choose r : ℝ) * a ^ (j - r) * b ^ r * f (n + q * j + r) := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', weightedStep, ih, ih]
      have hsplit := Finset.sum_choose_succ_mul
        (fun r s => a ^ s * b ^ r * f (n + q * (j + 1) + r)) j
      symm
      calc
        _ = (∑ r ∈ Finset.range (j + 1),
              (j.choose r : ℝ) * a ^ (j + 1 - r) * b ^ r *
                f (n + q * (j + 1) + r)) +
            ∑ r ∈ Finset.range (j + 1),
              (j.choose r : ℝ) * a ^ (j - r) * b ^ (r + 1) *
                f (n + q * (j + 1) + (r + 1)) := by
          simpa only [mul_assoc] using hsplit
        _ = _ := by
          congr 1
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r hr
            have hrj : r ≤ j := by simpa using Finset.mem_range.mp hr
            have hexp : j + 1 - r = (j - r) + 1 := by omega
            have harg : n + q * (j + 1) + r = n + q + q * j + r := by
              simp only [Nat.mul_add, Nat.mul_one]
              omega
            rw [hexp, pow_succ, harg]
            ring
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r hr
            have harg : n + q * (j + 1) + (r + 1) =
                n + q + 1 + q * j + r := by
              simp only [Nat.mul_add, Nat.mul_one]
              omega
            rw [pow_succ, harg]
            ring

/-- The canonical coefficient is the finite signed Möbius sum. -/
theorem coefficient_formula (f : Sequence) (j : ℕ) :
    coefficient f j = ∑ r ∈ Finset.range (j + 1),
      (j.choose r : ℝ) * (-1 : ℝ) ^ (j - r) * f r := by
  have hstep : difference = weightedStep (-1) 1 0 := by
    funext g n
    simp only [difference, weightedStep, Nat.add_zero, one_mul]
    ring
  simpa only [coefficient, hstep, Nat.zero_mul, Nat.zero_add, one_pow, mul_one]
    using weightedStep_iterate (-1) 1 0 f j 0

/-- The positive duplication coefficient in one coordinate. -/
def duplicateOne (c : Sequence) (j : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (j + 1), (j.choose r : ℝ) * 2 ^ (j - r) * c (j + r)

def duplicationStep (c : Sequence) : Sequence :=
  fun n => 2 * c (n + 1) + c (n + 2)

theorem duplicationStep_iterate (c : Sequence) (j : ℕ) :
    ((duplicationStep^[j]) c) 0 = duplicateOne c j := by
  have hstep : duplicationStep = weightedStep 2 1 1 := by
    funext f n
    simp [duplicationStep, weightedStep, Nat.add_assoc]
  simpa only [hstep, duplicateOne, Nat.one_mul, Nat.zero_add, one_pow, mul_one]
    using weightedStep_iterate 2 1 1 c j 0

theorem difference_double_newton (c : Sequence) :
    difference (fun n => newton c (2 * n)) =
      fun n => newton (duplicationStep c) (2 * n) := by
  funext n
  have harg : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
  rw [difference, harg, newton_succ, newton_succ, newton_succ]
  have hsplit : duplicationStep c =
      fun r => (2 * c (r + 1)) + c ((r + 1) + 1) := by
    funext r
    simp [duplicationStep, Nat.add_assoc]
  rw [hsplit, newton_add, newton_smul]
  ring

theorem coefficient_double_newton (c : Sequence) (j : ℕ) :
    coefficient (fun n => newton c (2 * n)) j = duplicateOne c j := by
  have hiter (j : ℕ) : coefficient (fun n => newton c (2 * n)) j =
      ((duplicationStep^[j]) c) 0 := by
    induction j generalizing c with
    | zero => simp [coefficient, newton]
    | succ j ih =>
        rw [coefficient_succ, difference_double_newton, ih,
          Function.iterate_succ_apply]
  rw [hiter, duplicationStep_iterate]

/-- Duplication is established by inversion, with no recurrence premise on c. -/
theorem newton_duplicateOne (c : Sequence) (n : ℕ) :
    newton (duplicateOne c) n = newton c (2 * n) := by
  have h := newton_coefficient (fun n => newton c (2 * n)) n
  have hcoeff : coefficient (fun n => newton c (2 * n)) = duplicateOne c := by
    funext j
    exact coefficient_double_newton c j
  rw [hcoeff] at h
  exact h

/-- Each input contains a finite rectangle, regardless of global support. -/
def transform (κ : Kernel) (n m : ℕ) : ℝ :=
  newton (fun j => newton (κ j) m) n

/-- The unique canonical coefficient function of any supplied count readout. -/
def canonical (F : Kernel) (j k : ℕ) : ℝ :=
  coefficient (fun m => coefficient (fun n => F n m) j) k

theorem canonical_transform (κ : Kernel) : canonical (transform κ) = κ := by
  funext j k
  simp only [canonical, transform, coefficient_newton]

theorem transform_canonical (F : Kernel) : transform (canonical F) = F := by
  funext n m
  change newton (fun j => newton
    (coefficient (fun m => coefficient (fun n => F n m) j)) m) n = F n m
  simp only [newton_coefficient]

theorem transform_injective : Function.Injective transform := by
  intro κ κ' h
  simpa only [canonical_transform] using congrArg canonical h

/-- Arbitrary signed-kernel existence holds for every count readout. -/
theorem exists_signed_kernel (F : Kernel) : ∃ κ, transform κ = F :=
  ⟨canonical F, transform_canonical F⟩

theorem canonical_formula (F : Kernel) (j k : ℕ) :
    canonical F j k =
      ∑ r ∈ Finset.range (j + 1), (j.choose r : ℝ) *
        ∑ s ∈ Finset.range (k + 1), (k.choose s : ℝ) *
          (-1 : ℝ) ^ (j + k - (r + s)) * F r s := by
  unfold canonical
  rw [coefficient_formula]
  simp_rw [coefficient_formula]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  have hrj : r ≤ j := by simpa using Finset.mem_range.mp hr
  have hsk : s ≤ k := by simpa using Finset.mem_range.mp hs
  have hexp : j + k - (r + s) = (j - r) + (k - s) := by omega
  rw [hexp, pow_add]
  ring

/-- Occupied originals select one twin in two ways, or both twins in one way. -/
def duplicate (κ : Kernel) (j k : ℕ) : ℝ :=
  duplicateOne (fun t => duplicateOne (κ t) k) j

theorem duplicate_formula (κ : Kernel) (j k : ℕ) :
    duplicate κ j k =
      ∑ r ∈ Finset.range (j + 1), ∑ s ∈ Finset.range (k + 1),
        (j.choose r : ℝ) * (k.choose s : ℝ) *
          2 ^ (j - r) * 2 ^ (k - s) * κ (j + r) (k + s) := by
  simp only [duplicate, duplicateOne, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  ring

theorem canonical_double_transform (κ : Kernel) :
    canonical (fun n m => transform κ (2 * n) (2 * m)) = duplicate κ := by
  funext j k
  unfold canonical transform
  simp_rw [coefficient_double_newton]
  unfold duplicate duplicateOne
  rw [coefficient_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [coefficient_smul, coefficient_double_newton]
  rfl

/-- Universal exact duplication for unrestricted kernels. -/
theorem transform_duplicate (κ : Kernel) (n m : ℕ) :
    transform (duplicate κ) n m = transform κ (2 * n) (2 * m) := by
  rw [← canonical_double_transform, transform_canonical]

theorem transform_four_mul (κ : Kernel) :
    transform (fun j k => 4 * κ j k) = fun n m => 4 * transform κ n m := by
  funext n m
  simp only [transform, newton_smul]

/-- Universal doubling of the readout forces coefficient-level duplication. -/
theorem duplicate_eq_four_mul {κ : Kernel}
    (hdouble : ∀ n m, transform κ (2 * n) (2 * m) = 4 * transform κ n m) :
    duplicate κ = fun j k => 4 * κ j k := by
  apply transform_injective
  funext n m
  rw [transform_duplicate, hdouble, transform_four_mul]

/-- Under positivity on the successor cone, retain the diagonal contribution. -/
theorem diagonal_le_duplicate {κ : Kernel} (j k : ℕ)
    (hpos : ∀ r s, 0 ≤ κ (j + r) (k + s)) :
    2 ^ (j + k) * κ j k ≤ duplicate κ j k := by
  have hinner (r : ℕ) : 0 ≤ duplicateOne (κ (j + r)) k := by
    apply Finset.sum_nonneg
    intro s hs
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (hpos r s)
  have hinner0 : 2 ^ k * κ j k ≤ duplicateOne (κ j) k := by
    have h := Finset.single_le_sum
      (s := Finset.range (k + 1))
      (f := fun s => (k.choose s : ℝ) * 2 ^ (k - s) * κ j (k + s))
      (fun s hs => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity))
        (by simpa using hpos 0 s))
      (by simp : 0 ∈ Finset.range (k + 1))
    simpa only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
      Nat.add_zero] using h
  have houter : 2 ^ j * duplicateOne (κ j) k ≤ duplicate κ j k := by
    have h := Finset.single_le_sum
      (s := Finset.range (j + 1))
      (f := fun r => (j.choose r : ℝ) * 2 ^ (j - r) * duplicateOne (κ (j + r)) k)
      (fun r hr => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity))
        (hinner r))
      (by simp : 0 ∈ Finset.range (j + 1))
    simpa only [duplicate, duplicateOne, Nat.choose_zero_right, Nat.cast_one,
      one_mul, Nat.sub_zero, Nat.add_zero] using h
  calc
    2 ^ (j + k) * κ j k = 2 ^ j * (2 ^ k * κ j k) := by rw [pow_add]; ring
    _ ≤ 2 ^ j * duplicateOne (κ j) k := mul_le_mul_of_nonneg_left hinner0 (by positivity)
    _ ≤ _ := houter

theorem four_lt_two_pow {d : ℕ} (hd : 2 < d) : (4 : ℝ) < 2 ^ d := by
  calc
    (4 : ℝ) < 2 ^ 3 := by norm_num
    _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) (by omega)

theorem positive_high_coefficient_zero {κ : Kernel}
    (hdup : duplicate κ = fun j k => 4 * κ j k) (j k : ℕ) (hdegree : 2 < j + k)
    (hpos : ∀ r s, 0 ≤ κ (j + r) (k + s)) : κ j k = 0 := by
  have hbound := diagonal_le_duplicate j k hpos
  rw [hdup] at hbound
  have hself : 0 ≤ κ j k := by simpa using hpos 0 0
  have hpow := four_lt_two_pow hdegree
  apply le_antisymm _ hself
  by_contra hnot
  have hstrict := mul_lt_mul_of_pos_right hpow (lt_of_not_ge hnot)
  linarith

/-- A diagonal collapse uses only vanishing of strict total-degree successors. -/
theorem duplicate_eq_diagonal {κ : Kernel} (j k : ℕ)
    (hzero : ∀ r s, j + k < r + s → κ r s = 0) :
    duplicate κ j k = 2 ^ (j + k) * κ j k := by
  unfold duplicate duplicateOne
  simp only [Finset.mul_sum]
  rw [Finset.sum_eq_single 0]
  · rw [Finset.sum_eq_single 0]
    · simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
        Nat.add_zero]
      rw [pow_add]
      ring
    · intro s hs hs0
      simp only [Nat.add_zero]
      rw [hzero j (k + s) (by omega)]
      ring
    · simp
  · intro r hr hr0
    apply Finset.sum_eq_zero
    intro s hs
    rw [hzero (j + r) (k + s) (by omega)]
    ring
  · simp

/-- One descending finite step also eliminates a possibly signed head degree. -/
theorem decrease_cutoff {κ : Kernel} {K : ℕ}
    (hdup : duplicate κ = fun j k => 4 * κ j k) (hK : 2 < K)
    (hzero : ∀ j k, K < j + k → κ j k = 0) :
    ∀ j k, K - 1 < j + k → κ j k = 0 := by
  intro j k hdegree
  by_cases hhigh : K < j + k
  · exact hzero j k hhigh
  · have heq : j + k = K := by omega
    have hdiag := duplicate_eq_diagonal j k (fun r s h => hzero r s (by omega))
    rw [hdup] at hdiag
    have hpow := four_lt_two_pow (show 2 < j + k by omega)
    have hfactor : (2 ^ (j + k) - (4 : ℝ)) * κ j k = 0 := by nlinarith [hdiag]
    exact (mul_eq_zero.mp hfactor).resolve_left (ne_of_gt (sub_pos.mpr hpow))

theorem cutoff_to_two {κ : Kernel}
    (hdup : duplicate κ = fun j k => 4 * κ j k) (K : ℕ)
    (hzero : ∀ j k, K < j + k → κ j k = 0) :
    ∀ j k, 2 < j + k → κ j k = 0 := by
  have hdesc : ∀ N : ℕ, (∀ j k, N < j + k → κ j k = 0) →
      ∀ j k, 2 < j + k → κ j k = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        intro hN
        by_cases hle : N ≤ 2
        · exact fun j k h => hN j k (by omega)
        · exact ih (N - 1) (by omega) (decrease_cutoff hdup (by omega) hN)
  exact hdesc K hzero

/-- One uniform total-degree positivity threshold permits any finite signed head. -/
def EventuallyNonnegative (κ : Kernel) : Prop :=
  ∃ D : ℕ, ∀ j k, D < j + k → 0 ≤ κ j k

/-- Universal doubling plus eventual positivity forces order at most two. -/
theorem support_le_two_of_eventuallyNonnegative {κ : Kernel}
    (hdouble : ∀ n m, transform κ (2 * n) (2 * m) = 4 * transform κ n m)
    (hpos : EventuallyNonnegative κ) :
    ∀ j k, 2 < j + k → κ j k = 0 := by
  obtain ⟨D, hD⟩ := hpos
  have hdup := duplicate_eq_four_mul hdouble
  apply cutoff_to_two hdup (max D 2)
  intro j k hjk
  apply positive_high_coefficient_zero hdup j k (by omega)
  intro r s
  exact hD (j + r) (k + s) (by omega)

/-- Everywhere positivity is a special case of the uniform-tail condition. -/
theorem support_le_two_of_nonnegative {κ : Kernel}
    (hdouble : ∀ n m, transform κ (2 * n) (2 * m) = 4 * transform κ n m)
    (hpos : ∀ j k, 0 ≤ κ j k) :
    ∀ j k, 2 < j + k → κ j k = 0 :=
  support_le_two_of_eventuallyNonnegative hdouble ⟨0, fun j k _ => hpos j k⟩

/-- Low-degree duplication identities do not require positivity. -/
theorem duplicate_low_relations {κ : Kernel}
    (hdouble : ∀ n m, transform κ (2 * n) (2 * m) = 4 * transform κ n m) :
    κ 0 0 = 0 ∧ κ 2 0 = 2 * κ 1 0 ∧ κ 0 2 = 2 * κ 0 1 := by
  have hdup := duplicate_eq_four_mul hdouble
  have h00 := congrFun (congrFun hdup 0) 0
  have h10 := congrFun (congrFun hdup 1) 0
  have h01 := congrFun (congrFun hdup 0) 1
  norm_num [duplicate, duplicateOne, Finset.sum_range_succ] at h00 h10 h01
  constructor
  · linarith
  constructor <;> linarith

/-- Generic calibrated order-two kernel, independent of native representations. -/
def quadraticKernel (j k : ℕ) : ℝ :=
  if (j = 1 ∧ k = 0) ∨ (j = 0 ∧ k = 1) then 1 / 2
  else if (j = 2 ∧ k = 0) ∨ (j = 0 ∧ k = 2) then 1 else 0

/-- Calibration is supplied at precisely the three small count bags. -/
theorem eq_quadraticKernel_of_eventuallyNonnegative {κ : Kernel}
    (hdouble : ∀ n m, transform κ (2 * n) (2 * m) = 4 * transform κ n m)
    (hpos : EventuallyNonnegative κ)
    (h10 : transform κ 1 0 = 1 / 2) (h01 : transform κ 0 1 = 1 / 2)
    (h11 : transform κ 1 1 = 1) : κ = quadraticKernel := by
  have hsupport := support_le_two_of_eventuallyNonnegative hdouble hpos
  obtain ⟨h00, h20, h02⟩ := duplicate_low_relations hdouble
  norm_num [transform, newton, Finset.sum_range_succ, h00] at h10 h01 h11
  have hc10 : κ 1 0 = 1 / 2 := by linarith
  have hc01 : κ 0 1 = 1 / 2 := by linarith
  have hc11 : κ 1 1 = 0 := by linarith
  have hc20 : κ 2 0 = 1 := by linarith
  have hc02 : κ 0 2 = 1 := by linarith
  funext j k
  by_cases hhigh : 2 < j + k
  · rw [hsupport j k hhigh]
    symm
    simp only [quadraticKernel]
    split_ifs <;> first | omega | rfl
  · have hj : j ≤ 2 := by omega
    have hk : k ≤ 2 := by omega
    interval_cases j <;> interval_cases k
    all_goals first | omega | norm_num [quadraticKernel, h00, hc10, hc01, hc11, hc20, hc02]

theorem newton_one (n : ℕ) : newton (fun _ => 1) n = (2 : ℝ) ^ n := by
  have h := congrArg (fun N : ℕ => (N : ℝ)) (Nat.sum_range_choose n)
  simpa [newton] using h

theorem allOne_transform (n m : ℕ) :
    transform (fun _ _ => 1) n m = (2 : ℝ) ^ (n + m) := by
  calc
    _ = newton (fun _ => (2 : ℝ) ^ m) n := by simp only [transform, newton_one]
    _ = 2 ^ m * newton (fun _ => 1) n := by
      simpa only [mul_one] using congrFun (newton_smul ((2 : ℝ) ^ m) (fun _ => 1)) n
    _ = 2 ^ (n + m) := by rw [newton_one, pow_add]; ring

/-- Positive unbounded support alone is inhabited, with no doubling claim. -/
theorem allOne_nonnegative : ∀ j k : ℕ, 0 ≤ (fun _ _ => (1 : ℝ)) j k := by
  intro j k
  norm_num

theorem allOne_unbounded_support : ∀ D : ℕ, ∃ j k : ℕ,
    D < j + k ∧ (fun _ _ => (1 : ℝ)) j k ≠ 0 := by
  intro D
  exact ⟨D + 1, 0, by omega, by norm_num⟩

theorem allOne_not_doubling :
    ¬∀ n m, transform (fun _ _ => 1) (2 * n) (2 * m) =
      4 * transform (fun _ _ => 1) n m := by
  intro h
  have h00 := h 0 0
  norm_num [transform, newton] at h00


/-- A positive unrestricted tail preserves the calibrated order-two head. -/
def calibratedPositiveTail (j k : ℕ) : ℝ :=
  quadraticKernel j k + if 3 ≤ j + k then 1 else 0

theorem calibratedPositiveTail_nonnegative (j k : ℕ) :
    0 ≤ calibratedPositiveTail j k := by
  unfold calibratedPositiveTail quadraticKernel
  split_ifs <;> norm_num

theorem calibratedPositiveTail_high_degree (j k : ℕ) (hdegree : 3 ≤ j + k) :
    calibratedPositiveTail j k = 1 := by
  have hfirst : ¬((j = 1 ∧ k = 0) ∨ (j = 0 ∧ k = 1)) := by omega
  have hsecond : ¬((j = 2 ∧ k = 0) ∨ (j = 0 ∧ k = 2)) := by omega
  simp [calibratedPositiveTail, quadraticKernel, hfirst, hsecond, hdegree]

theorem calibratedPositiveTail_unbounded_positive_support :
    ∀ D : ℕ, ∃ j k : ℕ, D < j + k ∧ 0 < calibratedPositiveTail j k := by
  intro D
  refine ⟨max (D + 1) 3, 0, ?_, ?_⟩
  · have h := le_max_left (D + 1) 3
    omega
  · rw [calibratedPositiveTail_high_degree]
    · norm_num
    · have h := le_max_right (D + 1) 3
      omega

theorem calibratedPositiveTail_zero_zero : calibratedPositiveTail 0 0 = 0 := by
  norm_num [calibratedPositiveTail, quadraticKernel]

theorem calibratedPositiveTail_transform_one_zero :
    transform calibratedPositiveTail 1 0 = 1 / 2 := by
  norm_num [transform, newton, Finset.sum_range_succ, calibratedPositiveTail, quadraticKernel]

theorem calibratedPositiveTail_transform_zero_one :
    transform calibratedPositiveTail 0 1 = 1 / 2 := by
  norm_num [transform, newton, Finset.sum_range_succ, calibratedPositiveTail, quadraticKernel]

theorem calibratedPositiveTail_transform_one_one :
    transform calibratedPositiveTail 1 1 = 1 := by
  norm_num [transform, newton, Finset.sum_range_succ, calibratedPositiveTail, quadraticKernel]

theorem calibratedPositiveTail_transform_two_zero :
    transform calibratedPositiveTail 2 0 = 2 := by
  norm_num [transform, newton, Finset.sum_range_succ, calibratedPositiveTail, quadraticKernel]

theorem calibratedPositiveTail_transform_four_zero :
    transform calibratedPositiveTail 4 0 = 13 := by
  norm_num [transform, newton, Finset.sum_range_succ, calibratedPositiveTail, quadraticKernel, Nat.choose]

/-- The calibrated positive-tail response violates doubling on the (2,0) bag. -/
theorem calibratedPositiveTail_not_doubling :
    ¬∀ n m, transform calibratedPositiveTail (2 * n) (2 * m) =
      4 * transform calibratedPositiveTail n m := by
  intro h
  have h20 := h 2 0
  change transform calibratedPositiveTail 4 0 =
    4 * transform calibratedPositiveTail 2 0 at h20
  rw [calibratedPositiveTail_transform_four_zero,
    calibratedPositiveTail_transform_two_zero] at h20
  norm_num at h20

end IDT.QMClosure.PositiveUnboundedKernelDuplication
