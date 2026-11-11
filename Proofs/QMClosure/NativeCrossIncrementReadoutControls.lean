import Proofs.QMClosure.NativeCrossIncrementReadoutSelection
import Proofs.QMClosure.NativeRegularReadoutCountercontrol
import Proofs.QMClosure.PositiveUnboundedKernelDuplication

/-!
Concrete countercontrols for local sign and coordinate monotonicity.
The real-coordinate derivative certificate uses 0 ≤ c ≤ 1/16. The nonnorm
counterexamples use 0 < c. All count values belong to the existing native
regular counterfamily.
-/

noncomputable section

namespace IDT.QMClosure.NativeCrossIncrementReadoutControls

open NativeInitialHistoryPresentation
open NativeGeneratorMixtureReadout
open OriginalOccurrenceKernel
open NativeCrossIncrementReadoutSelection
open NativeRegularReadoutCountercontrol
open CountCrossIncrementRigidity
open PositiveUnboundedKernelDuplication

attribute [local instance] presentationCommRing presentationCharZero

private theorem newton_subtract (c d : Sequence) :
    newton (fun j => c j - d j) = fun n => newton c n - newton d n := by
  funext n
  simp [newton, mul_sub, Finset.sum_sub_distrib]

theorem mixed_transform (κ : PositiveUnboundedKernelDuplication.Kernel) (n m : ℕ) :
    mixed (transform κ) n m = transform (fun j k => κ (j + 1) (k + 1)) n m := by
  have h1 := newton_succ (fun j => newton (κ j) (m + 1)) n
  have h0 := newton_succ (fun j => newton (κ j) m) n
  change newton (fun j => newton (κ j) (m + 1)) (n + 1) -
    newton (fun j => newton (κ j) m) (n + 1) -
    newton (fun j => newton (κ j) (m + 1)) n +
    newton (fun j => newton (κ j) m) n = _
  calc
    _ = newton (fun j => newton (κ (j + 1)) (m + 1)) n -
        newton (fun j => newton (κ (j + 1)) m) n := by rw [h1, h0]; ring
    _ = newton (fun j => newton (κ (j + 1)) (m + 1) -
        newton (κ (j + 1)) m) n := (congrFun (newton_subtract _ _) n).symm
    _ = _ := by
      apply congrArg (fun c => newton c n)
      funext j
      exact congrFun (difference_newton (κ (j + 1))) m

theorem nonnegative_canonical_implies_mixed_nonnegative (f : Grid)
    (hκ : ∀ j k, 0 ≤ canonical f j k) : ∀ n m, 0 ≤ mixed f n m := by
  intro n m
  have hm := mixed_transform (canonical f) n m
  rw [transform_canonical] at hm
  rw [hm]
  unfold transform newton
  apply Finset.sum_nonneg
  intro j hj
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (Nat.cast_nonneg _) (hκ (j + 1) (k + 1))

def orAxis (n : ℕ) : ℝ := if n = 0 then 0 else 1 / 2

def orGrid (n m : ℕ) : ℝ := orAxis n + orAxis m

theorem orGrid_mixed (n m : ℕ) : mixed orGrid n m = 0 := by
  dsimp [mixed, orGrid]
  ring

theorem orAxis_monotone : Monotone orAxis := by
  intro n m hnm
  unfold orAxis
  split_ifs <;> norm_num at * <;> omega

theorem orGrid_monotone_left (m : ℕ) : Monotone (fun n => orGrid n m) := by
  intro n k hnk
  change orAxis n + orAxis m ≤ orAxis k + orAxis m
  linarith [orAxis_monotone hnk]

theorem orGrid_monotone_right (n : ℕ) : Monotone (orGrid n) := by
  intro m k hmk
  change orAxis n + orAxis m ≤ orAxis n + orAxis k
  linarith [orAxis_monotone hmk]

theorem orGrid_calibrations :
    orGrid 0 0 = 0 ∧ orGrid 1 0 = 1 / 2 ∧ orGrid 0 1 = 1 / 2 ∧ orGrid 1 1 = 1 := by
  norm_num [orGrid, orAxis]

theorem orGrid_not_dyadic : ¬ Dyadic orGrid := by
  intro hd
  have hh := hd 1 0
  norm_num [orGrid, orAxis] at hh

private theorem coefficient_supported_zero (f : Sequence)
    (hs : ∀ n, 0 < n → f n = 0) (j : ℕ) :
    coefficient f j = (-1 : ℝ) ^ j * f 0 := by
  induction j generalizing f with
  | zero => simp [coefficient]
  | succ j ih =>
      rw [coefficient_succ, ih]
      · have h1 := hs 1 (by omega)
        simp only [difference, h1, zero_sub, pow_succ]
        ring
      · intro n hn
        simp [difference, hs n hn, hs (n + 1) (by omega)]

/-- Every positive axis order remains present, with alternating signs. -/
theorem orGrid_canonical_axis (j : ℕ) :
    canonical orGrid (j + 1) 0 = (1 / 2 : ℝ) * (-1 : ℝ) ^ j := by
  have haxis : (fun n => orGrid n 0) = orAxis := by
    funext n
    simp [orGrid, orAxis]
  simp only [canonical, coefficient, Function.iterate_zero_apply]
  change coefficient (fun n => orGrid n 0) (j + 1) = _
  rw [haxis, coefficient_succ, coefficient_supported_zero]
  · norm_num [difference, orAxis]
    ring
  · intro n hn
    simp [difference, orAxis, Nat.ne_of_gt hn, Nat.succ_ne_zero]

theorem orGrid_negative_canonical : canonical orGrid 2 0 = -1 / 2 := by
  convert orGrid_canonical_axis 1 using 1 <;> norm_num

/-- Real count-coordinate extension, including its total-division vacuum. -/
def countWeight (c x y : ℝ) : ℝ :=
  (x ^ 2 + y ^ 2) / 2 + 8 * c * x ^ 2 * y ^ 2 * (x ^ 2 - y ^ 2) ^ 2 /
    (x ^ 2 + y ^ 2) ^ 3

theorem countWeight_symm (c x y : ℝ) : countWeight c x y = countWeight c y x := by
  unfold countWeight
  congr 1
  · ring
  · congr 1 <;> ring

theorem ambientWeight_count_coordinates (c x y : ℝ) :
    ambientWeight c (((x + y) / 2 : ℝ) + (((x - y) / 2 : ℝ) : ℂ) * Complex.I) =
      countWeight c x y := by
  rw [ambientWeight_coordinates]
  have hn : ((x + y) / 2) ^ 2 + ((x - y) / 2) ^ 2 = (x ^ 2 + y ^ 2) / 2 := by ring
  rw [hn]
  by_cases h : x ^ 2 + y ^ 2 = 0
  · have hx : x = 0 := by nlinarith [sq_nonneg y]
    have hy : y = 0 := by nlinarith [sq_nonneg x]
    subst x; subst y
    norm_num [countWeight]
  · unfold countWeight
    field_simp [h] <;> ring

theorem countGrid_counterWeight (c : ℝ) (n m : ℕ) :
    countGrid (counterWeight c) n m = countWeight c n m := by
  have he : complexEval (bagEval n m) =
      ((((n : ℝ) + (m : ℝ)) / 2 : ℝ) : ℂ) +
        (((((n : ℝ) - (m : ℝ)) / 2 : ℝ)) : ℂ) * Complex.I := by
    apply Complex.ext <;>
      simp [bagEval, ComplexModel.a, ComplexModel.b, Complex.div_re, Complex.div_im,
        Complex.mul_re, Complex.mul_im] <;> ring
  unfold countGrid counterWeight
  rw [he, ambientWeight_count_coordinates]

theorem counterWeight_mixed_zero_one (c : ℝ) :
    mixed (countGrid (counterWeight c)) 0 1 = 288 * c / 125 := by
  norm_num [mixed, countGrid_counterWeight, countWeight] <;> ring

theorem counterWeight_mixed_one_one (c : ℝ) :
    mixed (countGrid (counterWeight c)) 1 1 = -576 * c / 125 := by
  norm_num [mixed, countGrid_counterWeight, countWeight] <;> ring

/-- An explicit derivative throughout the real x-axis for each y > 0. -/
theorem countWeight_hasDerivAt (c x y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t => countWeight c t y)
      (x * (1 + 16 * c * y ^ 4 * (x ^ 2 - y ^ 2) * (5 * x ^ 2 - y ^ 2) /
        (x ^ 2 + y ^ 2) ^ 4)) x := by
  have hs : x ^ 2 + y ^ 2 ≠ 0 := by nlinarith [sq_nonneg x, sq_pos_of_pos hy]
  have hx := hasDerivAt_id x
  have hy2 := hasDerivAt_const x (y ^ 2)
  have hbase := ((hx.pow 2).add hy2).div_const 2
  have hnum := (((hx.pow 2).const_mul (8 * c)).mul_const (y ^ 2)).mul
    (((hx.pow 2).sub hy2).pow 2)
  have hden := ((hx.pow 2).add hy2).pow 3
  have hd := hbase.add (hnum.div hden (pow_ne_zero 3 hs))
  convert hd using 1 <;> dsimp [countWeight] <;> field_simp [hs] <;> ring

/-- Polynomial certificate used to bound the derivative correction below. -/
theorem correction_numerator_lower (x y : ℝ) :
    -(x ^ 2 + y ^ 2) ^ 4 ≤ y ^ 4 * (x ^ 2 - y ^ 2) * (5 * x ^ 2 - y ^ 2) := by
  let u := x ^ 2
  let v := y ^ 2
  have hu : 0 ≤ u := sq_nonneg x
  have hv : 0 ≤ v := sq_nonneg y
  have hp : 0 ≤ (u - v) * (5 * u - v) + (u + v) ^ 2 := by
    nlinarith [sq_nonneg (u - v), sq_nonneg u]
  have hvsum : 0 ≤ (u + v) ^ 2 - v ^ 2 := by nlinarith [mul_nonneg hu hv]
  have hA := mul_nonneg (sq_nonneg v) hp
  have hB := mul_nonneg hvsum (sq_nonneg (u + v))
  dsimp [u, v] at hA hB
  nlinarith only [hA, hB]

theorem countWeight_derivative_nonnegative (c x y : ℝ)
    (hc : 0 ≤ c) (hcap : c ≤ 1 / 16) (hx : 0 ≤ x) (hy : 0 < y) :
    0 ≤ x * (1 + 16 * c * y ^ 4 * (x ^ 2 - y ^ 2) * (5 * x ^ 2 - y ^ 2) /
      (x ^ 2 + y ^ 2) ^ 4) := by
  have hs : 0 < x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg x, sq_pos_of_pos hy]
  have hd : 0 < (x ^ 2 + y ^ 2) ^ 4 := pow_pos hs 4
  have hbound := mul_le_mul_of_nonneg_left (correction_numerator_lower x y)
    (show 0 ≤ 16 * c by positivity)
  have hden := mul_nonneg (show 0 ≤ 1 - 16 * c by linarith) (le_of_lt hd)
  apply mul_nonneg hx
  have hrewrite :
      (1 + 16 * c * y ^ 4 * (x ^ 2 - y ^ 2) * (5 * x ^ 2 - y ^ 2) /
        (x ^ 2 + y ^ 2) ^ 4) =
      ((x ^ 2 + y ^ 2) ^ 4 +
        16 * c * y ^ 4 * (x ^ 2 - y ^ 2) * (5 * x ^ 2 - y ^ 2)) /
          (x ^ 2 + y ^ 2) ^ 4 := by field_simp <;> ring
  rw [hrewrite]
  exact (le_div_iff₀ hd).mpr (by nlinarith)

/-- Ordinary real-coordinate monotonicity holds in the accepted parameter range. -/
theorem countWeight_monotone_left (c y : ℝ) (hc : 0 ≤ c)
    (hcap : c ≤ 1 / 16) (hy : 0 ≤ y) :
    MonotoneOn (fun x => countWeight c x y) (Set.Ici 0) := by
  by_cases hy0 : y = 0
  · subst y
    intro x hx z hz hxz
    simp only [Set.mem_Ici] at hx hz
    simp [countWeight]
    nlinarith
  have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  let df := fun x => x * (1 + 16 * c * y ^ 4 * (x ^ 2 - y ^ 2) *
    (5 * x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) ^ 4)
  have hd (x : ℝ) : HasDerivAt (fun t => countWeight c t y) (df x) x :=
    countWeight_hasDerivAt c x y hyp
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
  · exact (continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)).continuousOn
  · intro x hx
    exact (hd x).hasDerivWithinAt
  · intro x hx
    have hxx : 0 ≤ x := by
      have := interior_subset hx
      exact this
    exact countWeight_derivative_nonnegative c x y hc hcap hxx hyp

theorem countWeight_monotone_right (c x : ℝ) (hc : 0 ≤ c)
    (hcap : c ≤ 1 / 16) (hx : 0 ≤ x) :
    MonotoneOn (countWeight c x) (Set.Ici 0) := by
  intro y hy z hz hyz
  rw [countWeight_symm c x y, countWeight_symm c x z]
  exact countWeight_monotone_left c x hc hcap hx hy hz hyz

theorem counterWeight_count_monotone (c : ℝ) (hc : 0 ≤ c) (hcap : c ≤ 1 / 16) :
    (∀ m : ℕ, Monotone (fun n : ℕ => countGrid (counterWeight c) n m)) ∧
    (∀ n : ℕ, Monotone (countGrid (counterWeight c) n)) := by
  constructor
  · intro m n k hnk
    simp only [countGrid_counterWeight]
    apply countWeight_monotone_left c m hc hcap (Nat.cast_nonneg m)
    · change (0 : ℝ) ≤ (n : ℝ)
      positivity
    · change (0 : ℝ) ≤ (k : ℝ)
      positivity
    · exact_mod_cast hnk
  · intro n m k hmk
    simp only [countGrid_counterWeight]
    apply countWeight_monotone_right c n hc hcap (Nat.cast_nonneg n)
    · change (0 : ℝ) ≤ (m : ℝ)
      positivity
    · change (0 : ℝ) ≤ (k : ℝ)
      positivity
    · exact_mod_cast hmk

/-- Coordinate monotonicity coexists with both signs and universal norm failure. -/
theorem monotone_nonnorm_native_countercontrol (c : ℝ) (hc : 0 < c)
    (hcap : c ≤ 1 / 16) :
    NativeTransfer (counterWeight c) ∧
    (∀ m : ℕ, Monotone (fun n : ℕ => countGrid (counterWeight c) n m)) ∧
    (∀ n : ℕ, Monotone (countGrid (counterWeight c) n)) ∧
    0 < mixed (countGrid (counterWeight c)) 0 1 ∧
    mixed (countGrid (counterWeight c)) 1 1 < 0 ∧
    ¬ (∀ p, counterWeight c p = Complex.normSq (complexEval p)) := by
  obtain ⟨hleft, hright⟩ := counterWeight_count_monotone c (le_of_lt hc) hcap
  refine ⟨counterWeight_native c, hleft, hright, ?_, ?_, ?_⟩
  · rw [counterWeight_mixed_zero_one]
    positivity
  · rw [counterWeight_mixed_one_one]
    nlinarith
  · exact counterWeight_not_norm c hc

end IDT.QMClosure.NativeCrossIncrementReadoutControls
