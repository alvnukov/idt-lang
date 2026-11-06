import Proofs.QMClosure.PreparationDisturbanceTradeoff
import Proofs.QMClosure.QuadraticRecordRefinement

namespace IDT.QMClosure.QuadraticRecordRefinementCountermodels

open PreparationRecordObstruction PreparationDisturbanceTradeoff
open QuadraticRecordRefinement

noncomputable section

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

/-!
Supplied real-vector-space controls separate recordwise quadraticity from
nonnegativity, degree-two homogeneity, and quadratic coarse totals. These are
mathematical probability/effect examples, not a construction of physical
detectors, record actualization, or state updates.
-/

/-- The clipping radius is globally nonnegative. -/
def clampBound (a b : ℝ) : ℝ := min (a ^ 2) (b ^ 2) / 2

def clampedCross (a b : ℝ) : ℝ :=
  max (-clampBound a b) (min (clampBound a b) (a * b / 4))

def clampedWeights (v : ℝ × ℝ) : Fin 4 → ℝ :=
  ![v.1 ^ 2 / 2 + clampedCross v.1 v.2,
    v.1 ^ 2 / 2 - clampedCross v.1 v.2,
    v.2 ^ 2 / 2 + clampedCross v.1 v.2,
    v.2 ^ 2 / 2 - clampedCross v.1 v.2]

theorem clampBound_nonnegative (a b : ℝ) : 0 ≤ clampBound a b := by
  exact div_nonneg (le_min (sq_nonneg a) (sq_nonneg b)) (by norm_num)

theorem clampedCross_bounds (a b : ℝ) :
    -clampBound a b ≤ clampedCross a b ∧
      clampedCross a b ≤ clampBound a b := by
  refine ⟨le_max_left _ _, max_le ?_ (min_le_left _ _)⟩
  have := clampBound_nonnegative a b
  linarith

/-- Positivity holds for every real vector, rather than only four samples. -/
theorem clampedWeights_nonnegative (v : ℝ × ℝ) (j : Fin 4) :
    0 ≤ clampedWeights v j := by
  have h := clampedCross_bounds v.1 v.2
  have ha : clampBound v.1 v.2 ≤ v.1 ^ 2 / 2 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hb : clampBound v.1 v.2 ≤ v.2 ^ 2 / 2 :=
    div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  fin_cases j <;> simp [clampedWeights] <;> linarith

theorem clampedWeights_coarse (v : ℝ × ℝ) :
    clampedWeights v 0 + clampedWeights v 1 = v.1 ^ 2 ∧
    clampedWeights v 2 + clampedWeights v 3 = v.2 ^ 2 := by
  constructor <;> simp [clampedWeights]

theorem clampedWeights_total (v : ℝ × ℝ) :
    ∑ j, clampedWeights v j = v.1 ^ 2 + v.2 ^ 2 := by
  simp [clampedWeights, Fin.sum_univ_succ]
  ring

theorem clampBound_homogeneous (t a b : ℝ) :
    clampBound (t * a) (t * b) = t ^ 2 * clampBound a b := by
  unfold clampBound
  rw [mul_pow, mul_pow, ← mul_min_of_nonneg _ _ (sq_nonneg t)]
  ring

theorem clampedCross_homogeneous (t a b : ℝ) :
    clampedCross (t * a) (t * b) = t ^ 2 * clampedCross a b := by
  have hprod : t * a * (t * b) / 4 = t ^ 2 * (a * b / 4) := by ring
  unfold clampedCross
  rw [clampBound_homogeneous, hprod, ← mul_neg,
    ← mul_min_of_nonneg _ _ (sq_nonneg t),
    ← mul_max_of_nonneg _ _ (sq_nonneg t)]

/-- This includes zero and negative scale factors. -/
theorem clampedWeights_homogeneous (t : ℝ) (v : ℝ × ℝ) (j : Fin 4) :
    clampedWeights (t * v.1, t * v.2) j = t ^ 2 * clampedWeights v j := by
  fin_cases j <;> simp [clampedWeights, clampedCross_homogeneous] <;> ring

def realPreparations : Fin 4 → ℝ × ℝ :=
  ![(2, 1), (2, -1), (1, 2), (1, -2)]

def clampedFamily (a j : Fin 4) : ℝ :=
  clampedWeights (realPreparations a) j / 5

/-- The extension reproduces the previously certified finite endpoint exactly. -/
theorem clampedFamily_eq_disturbedFamily : clampedFamily = disturbedFamily := by
  funext a j
  fin_cases a <;> fin_cases j <;>
    norm_num [clampedFamily, realPreparations, clampedWeights, clampedCross,
      clampBound, disturbedFamily]

theorem clampedFamily_endpoint :
    ProbabilityFamily clampedFamily ∧ ParityEquivalent clampedFamily ∧
    (∀ a, marginal clampedFamily recordZ a = targetZ a) ∧
    secondSuccess clampedFamily = 7 / 10 ∧
    meanMarginalError clampedFamily recordX targetX = 1 / 5 := by
  rw [clampedFamily_eq_disturbedFamily]
  exact ⟨disturbedFamily_probability, disturbedFamily_parityEquivalent,
    disturbedFamily_first_calibrated, disturbedFamily_secondSuccess,
    disturbedFamily_second_error⟩

/-- Record zero fails the parallelogram law although the total is quadratic. -/
theorem clampedWeights_parallelogram_failure :
    let u : ℝ × ℝ := (1, -2)
    let v : ℝ × ℝ := (0, 1)
    clampedWeights (u + v) 0 + clampedWeights (u - v) 0 = 1 / 4 ∧
    2 * clampedWeights u 0 + 2 * clampedWeights v 0 = 0 := by
  norm_num [clampedWeights, clampedCross, clampBound]

theorem clampedWeights_not_positiveQuadratic :
    ¬ PositiveQuadratic (fun v : ℝ × ℝ => clampedWeights v 0) := by
  intro h
  have hp := h.parallelogram (1, -2) (0, 1)
  have hf := clampedWeights_parallelogram_failure
  dsimp only at hf
  linarith [hf.1, hf.2]

theorem clampedWeights_total_positiveQuadratic :
    PositiveQuadratic (fun v : ℝ × ℝ => ∑ j, clampedWeights v j) := by
  constructor
  · intro v
    rw [clampedWeights_total]
    positivity
  · intro u v
    simp only [clampedWeights_total, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub]
    ring

/-- A nonvacuous recordwise positive quadratic refinement. -/
def balancedWeights (v : ℝ × ℝ) : Fin 4 → ℝ :=
  ![v.1 ^ 2 / 2, v.1 ^ 2 / 2, v.2 ^ 2 / 2, v.2 ^ 2 / 2]

theorem balancedWeights_positiveQuadratic (j : Fin 4) :
    PositiveQuadratic (fun v : ℝ × ℝ => balancedWeights v j) := by
  constructor
  · intro v
    fin_cases j <;> simp [balancedWeights] <;> positivity
  · intro u v
    fin_cases j <;> simp [balancedWeights] <;> ring

theorem balancedWeights_coarse (v : ℝ × ℝ) :
    balancedWeights v 0 + balancedWeights v 1 = v.1 ^ 2 ∧
    balancedWeights v 2 + balancedWeights v 3 = v.2 ^ 2 := by
  constructor <;> simp [balancedWeights]

def balancedFamily (a j : Fin 4) : ℝ :=
  balancedWeights (realPreparations a) j / 5

theorem balancedFamily_rows :
    balancedFamily =
      ![![2 / 5, 2 / 5, 1 / 10, 1 / 10],
        ![2 / 5, 2 / 5, 1 / 10, 1 / 10],
        ![1 / 10, 1 / 10, 2 / 5, 2 / 5],
        ![1 / 10, 1 / 10, 2 / 5, 2 / 5]] := by
  funext a j
  fin_cases a <;> fin_cases j <;>
    norm_num [balancedFamily, balancedWeights, realPreparations]

theorem balancedFamily_probability : ProbabilityFamily balancedFamily := by
  constructor
  · intro a j
    fin_cases a <;> fin_cases j <;>
      norm_num [balancedFamily, balancedWeights, realPreparations]
  · intro a
    fin_cases a <;>
      norm_num [balancedFamily, balancedWeights, realPreparations, Fin.sum_univ_succ]

theorem balancedFamily_first_calibrated :
    ∀ a, marginal balancedFamily recordZ a = targetZ a := by
  intro a
  fin_cases a <;>
    norm_num [marginal, balancedFamily, balancedWeights, realPreparations,
      recordZ, targetZ, Fin.sum_univ_succ]

theorem balancedFamily_secondSuccess : secondSuccess balancedFamily = 1 / 2 := by
  norm_num [secondSuccess, marginal, balancedFamily, balancedWeights, realPreparations,
    recordX, Fin.sum_univ_succ]

theorem balancedFamily_second_error :
    meanMarginalError balancedFamily recordX targetX = 2 / 5 := by
  norm_num [meanMarginalError, marginal, balancedFamily, balancedWeights,
    realPreparations, recordX, targetX, Fin.sum_univ_succ]

theorem balancedFamily_endpoint :
    ProbabilityFamily balancedFamily ∧
    (∀ a, marginal balancedFamily recordZ a = targetZ a) ∧
    secondSuccess balancedFamily = 1 / 2 ∧
    meanMarginalError balancedFamily recordX targetX = 2 / 5 :=
  ⟨balancedFamily_probability, balancedFamily_first_calibrated,
    balancedFamily_secondSuccess, balancedFamily_second_error⟩

/-- All realization premises hold together for the balanced example. -/
theorem balancedWeights_realizes :
    ∀ a r, balancedWeights (preparations ((1, 0) : ℝ × ℝ) (0, 1) a) r =
      5 * (1 : ℝ) * balancedFamily a r := by
  intro a r
  fin_cases a <;> fin_cases r <;>
    norm_num [preparations, balancedWeights, balancedFamily, realPreparations]

theorem balancedFamily_instantiates_core_bound :
    secondSuccess balancedFamily = 1 / 2 ∧
    standaloneXTargetSuccess - secondSuccess balancedFamily = 2 / 5 ∧
    2 / 5 ≤ meanMarginalError balancedFamily recordX targetX :=
  calibrated_second_record_bound ((1, 0) : ℝ × ℝ) (0, 1) 1 (by norm_num)
    (fun r v => balancedWeights v r) balancedWeights_positiveQuadratic
    balancedFamily balancedFamily_probability balancedWeights_realizes
    balancedFamily_first_calibrated

/-!
A separate state-update control: identical effect weights and repeatable
same-context outcome weights do not select an idempotent vector update.
No phase equivalence or physical instrument is asserted.
-/

abbrev UpdateSpace := (ℝ × ℝ) × (ℝ × ℝ)

def qnorm (v : UpdateSpace) : ℝ :=
  v.1.1 ^ 2 + v.1.2 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2

def projectFirst (v : UpdateSpace) : UpdateSpace := (v.1, (0, 0))

def projectSecond (v : UpdateSpace) : UpdateSpace := ((0, 0), v.2)

def rotateFirst (v : UpdateSpace) : UpdateSpace := ((-v.1.2, v.1.1), (0, 0))

def PreservesAddition (f : UpdateSpace → UpdateSpace) : Prop :=
  ∀ u v, f (u + v) = f u + f v

theorem updateMaps_additive :
    PreservesAddition projectFirst ∧ PreservesAddition projectSecond ∧
      PreservesAddition rotateFirst := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    intro u v
    ext <;> simp [projectFirst, projectSecond, rotateFirst, add_comm]

theorem rotateFirst_same_effect (v : UpdateSpace) :
    qnorm (rotateFirst v) = qnorm (projectFirst v) := by
  dsimp [qnorm, rotateFirst, projectFirst]
  ring

theorem update_total_conservation (v : UpdateSpace) :
    qnorm (rotateFirst v) + qnorm (projectSecond v) = qnorm v := by
  dsimp [qnorm, rotateFirst, projectSecond]
  ring

theorem update_cross_compositions (v : UpdateSpace) :
    rotateFirst (projectSecond v) = 0 ∧ projectSecond (rotateFirst v) = 0 := by
  constructor <;> ext <;> simp [rotateFirst, projectSecond]

theorem update_same_context_weight_repeatability (v : UpdateSpace) :
    qnorm (rotateFirst (rotateFirst v)) = qnorm (rotateFirst v) ∧
    qnorm (projectSecond (projectSecond v)) = qnorm (projectSecond v) := by
  constructor <;> dsimp [qnorm, rotateFirst, projectSecond]
  all_goals ring

/-- The vector update is different and nonidempotent despite equal weights. -/
theorem rotateFirst_not_projection :
    let v : UpdateSpace := ((1, 0), (0, 0))
    rotateFirst v ≠ projectFirst v ∧
      rotateFirst (rotateFirst v) ≠ rotateFirst v := by
  norm_num [rotateFirst, projectFirst]

end

end IDT.QMClosure.QuadraticRecordRefinementCountermodels
