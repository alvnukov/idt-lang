import Mathlib

namespace IDT.QMClosure.PreparationRecordObstruction

noncomputable section

/-!
# Finite preparation-record obstruction

Preparation order and record order are 00, 01, 10, 11. Probabilities and shared
response functions are supplied mathematical data. This module proves a finite
classical record bound, not a derivation of detector events or of quantum theory.
-/

variable {Ω : Type*} [Fintype Ω]

structure ProbabilityFamily (μ : Fin 4 → Ω → ℝ) : Prop where
  nonnegative : ∀ a ω, 0 ≤ μ a ω
  normalized : ∀ a, ∑ ω, μ a ω = 1

def Response (r : Ω → ℝ) : Prop := ∀ ω, 0 ≤ r ω ∧ r ω ≤ 1

def score (a b c d u v : ℝ) : ℝ :=
  a * (u + v) + b * (u + 1 - v) + c * (1 - u + v) + d * (2 - u - v)

def success (μ : Fin 4 → Ω → ℝ) (rZ rX : Ω → ℝ) : ℝ :=
  (∑ ω, score (μ 0 ω) (μ 1 ω) (μ 2 ω) (μ 3 ω) (rZ ω) (rX ω)) / 8

/-- Total variation of the equal-weight even- and odd-parity mixtures. -/
def parityTV (μ : Fin 4 → Ω → ℝ) : ℝ :=
  (∑ ω, |μ 0 ω + μ 3 ω - μ 1 ω - μ 2 ω|) / 4

def ParityEquivalent (μ : Fin 4 → Ω → ℝ) : Prop :=
  ∀ ω, μ 0 ω + μ 3 ω = μ 1 ω + μ 2 ω

def marginal (μ : Fin 4 → Ω → ℝ) (r : Ω → ℝ) (a : Fin 4) : ℝ :=
  ∑ ω, μ a ω * r ω

def targetZ : Fin 4 → ℝ := ![4 / 5, 4 / 5, 1 / 5, 1 / 5]
def targetX : Fin 4 → ℝ := ![9 / 10, 1 / 10, 9 / 10, 1 / 10]

def Calibrated (μ : Fin 4 → Ω → ℝ) (rZ rX : Ω → ℝ) : Prop :=
  (∀ a, marginal μ rZ a = targetZ a) ∧ (∀ a, marginal μ rX a = targetX a)

/-- An algebraic convex expansion, with no detector-independence assumption. -/
theorem score_convex_expansion (a b c d u v : ℝ) :
    score a b c d u v =
      u * v * (2 * a + b + c) + u * (1 - v) * (a + 2 * b + d) +
      (1 - u) * v * (a + 2 * c + d) +
      (1 - u) * (1 - v) * (b + c + 2 * d) := by
  unfold score
  ring

theorem score_bound (a b c d u v : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) :
    score a b c d u v ≤
      (3 / 2 : ℝ) * (a + b + c + d) + |a + d - b - c| / 2 := by
  let B := (3 / 2 : ℝ) * (a + b + c + d) + |a + d - b - c| / 2
  have hp := le_abs_self (a + d - b - c)
  have hn := neg_le_abs (a + d - b - c)
  have h00 : 2 * a + b + c ≤ B := by dsimp [B]; linarith
  have h01 : a + 2 * b + d ≤ B := by dsimp [B]; linarith
  have h10 : a + 2 * c + d ≤ B := by dsimp [B]; linarith
  have h11 : b + c + 2 * d ≤ B := by dsimp [B]; linarith
  have h0 := mul_le_mul_of_nonneg_left h00 (mul_nonneg hu.1 hv.1)
  have h1 := mul_le_mul_of_nonneg_left h01
    (mul_nonneg hu.1 (sub_nonneg.mpr hv.2))
  have h2 := mul_le_mul_of_nonneg_left h10
    (mul_nonneg (sub_nonneg.mpr hu.2) hv.1)
  have h3 := mul_le_mul_of_nonneg_left h11
    (mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hv.2))
  rw [score_convex_expansion]
  calc
    _ ≤ u * v * B + u * (1 - v) * B + (1 - u) * v * B +
        (1 - u) * (1 - v) * B := by linarith
    _ = B := by ring

theorem parityTV_nonnegative (μ : Fin 4 → Ω → ℝ) : 0 ≤ parityTV μ := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

theorem parityTV_le_one (μ : Fin 4 → Ω → ℝ) (law : ProbabilityFamily μ) :
    parityTV μ ≤ 1 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun ω _ =>
    show |μ 0 ω + μ 3 ω - μ 1 ω - μ 2 ω| ≤
        μ 0 ω + μ 1 ω + μ 2 ω + μ 3 ω from by
      apply abs_le.mpr
      constructor <;> have := law.nonnegative 0 ω <;>
        have := law.nonnegative 1 ω <;> have := law.nonnegative 2 ω <;>
        have := law.nonnegative 3 ω <;> linarith)
  simp only [Finset.sum_add_distrib, law.normalized] at h
  unfold parityTV
  linarith

/-- Universal over every finite record space, including stochastic responses. -/
theorem success_le_three_quarters_add_parityTV (μ : Fin 4 → Ω → ℝ)
    (rZ rX : Ω → ℝ) (law : ProbabilityFamily μ)
    (hZ : Response rZ) (hX : Response rX) :
    success μ rZ rX ≤ 3 / 4 + parityTV μ / 4 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun ω _ =>
    score_bound (μ 0 ω) (μ 1 ω) (μ 2 ω) (μ 3 ω) (rZ ω) (rX ω)
      (law.nonnegative 0 ω) (law.nonnegative 1 ω)
      (law.nonnegative 2 ω) (law.nonnegative 3 ω) (hZ ω) (hX ω))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
    law.normalized] at h
  unfold success parityTV
  linarith

theorem parityTV_zero_of_equivalent (μ : Fin 4 → Ω → ℝ)
    (heq : ParityEquivalent μ) : parityTV μ = 0 := by
  unfold parityTV
  have hzero : ∀ ω, μ 0 ω + μ 3 ω - μ 1 ω - μ 2 ω = 0 := by
    intro ω
    have := heq ω
    linarith
  simp [hzero]

theorem success_le_three_quarters_of_equivalent (μ : Fin 4 → Ω → ℝ)
    (rZ rX : Ω → ℝ) (law : ProbabilityFamily μ)
    (hZ : Response rZ) (hX : Response rX) (heq : ParityEquivalent μ) :
    success μ rZ rX ≤ 3 / 4 := by
  have h := success_le_three_quarters_add_parityTV μ rZ rX law hZ hX
  rw [parityTV_zero_of_equivalent μ heq] at h
  linarith

theorem success_marginal_formula (μ : Fin 4 → Ω → ℝ) (rZ rX : Ω → ℝ)
    (law : ProbabilityFamily μ) :
    success μ rZ rX =
      (marginal μ rZ 0 + marginal μ rX 0 +
       marginal μ rZ 1 + 1 - marginal μ rX 1 +
       1 - marginal μ rZ 2 + marginal μ rX 2 +
       2 - marginal μ rZ 3 - marginal μ rX 3) / 8 := by
  unfold success score marginal
  simp only [mul_add, mul_sub, mul_one, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_mul, law.normalized]
  ring

theorem calibrated_success (μ : Fin 4 → Ω → ℝ) (rZ rX : Ω → ℝ)
    (law : ProbabilityFamily μ) (hcal : Calibrated μ rZ rX) :
    success μ rZ rX = 17 / 20 := by
  rw [success_marginal_formula μ rZ rX law]
  simp only [hcal.1, hcal.2]
  norm_num [targetZ, targetX, Matrix.cons_val_two, Matrix.cons_val_three]

theorem calibrated_parityTV_lower_bound (μ : Fin 4 → Ω → ℝ) (rZ rX : Ω → ℝ)
    (law : ProbabilityFamily μ) (hZ : Response rZ) (hX : Response rX)
    (hcal : Calibrated μ rZ rX) : 2 / 5 ≤ parityTV μ := by
  have h := success_le_three_quarters_add_parityTV μ rZ rX law hZ hX
  rw [calibrated_success μ rZ rX law hcal] at h
  linarith

theorem no_calibrated_parity_equivalent_family (μ : Fin 4 → Ω → ℝ)
    (rZ rX : Ω → ℝ) (law : ProbabilityFamily μ)
    (hZ : Response rZ) (hX : Response rX) (hcal : Calibrated μ rZ rX) :
    ¬ ParityEquivalent μ := by
  intro heq
  have h := calibrated_parityTV_lower_bound μ rZ rX law hZ hX hcal
  rw [parityTV_zero_of_equivalent μ heq] at h
  norm_num at h

def sharpFamily : Fin 4 → Fin 4 → ℝ :=
  ![![7 / 10, 1 / 10, 1 / 5, 0], ![1 / 10, 7 / 10, 0, 1 / 5],
    ![1 / 5, 0, 7 / 10, 1 / 10], ![0, 1 / 5, 1 / 10, 7 / 10]]

def recordZ : Fin 4 → ℝ := ![1, 1, 0, 0]
def recordX : Fin 4 → ℝ := ![1, 0, 1, 0]

theorem sharpFamily_probability : ProbabilityFamily sharpFamily := by
  constructor
  · intro a ω
    fin_cases a <;> fin_cases ω <;> norm_num [sharpFamily]
  · intro a
    fin_cases a <;> norm_num [sharpFamily, Fin.sum_univ_succ]

theorem record_responses : Response recordZ ∧ Response recordX := by
  constructor <;> intro ω <;> fin_cases ω <;> norm_num [recordZ, recordX]

theorem sharpFamily_calibrated : Calibrated sharpFamily recordZ recordX := by
  constructor <;> intro a <;> fin_cases a <;>
    norm_num [marginal, sharpFamily, recordZ, recordX, targetZ, targetX,
      Fin.sum_univ_succ]

theorem sharpFamily_success : success sharpFamily recordZ recordX = 17 / 20 :=
  calibrated_success _ _ _ sharpFamily_probability sharpFamily_calibrated

theorem sharpFamily_parityTV : parityTV sharpFamily = 2 / 5 := by
  norm_num [parityTV, sharpFamily, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.cons_val_three]

/-- Joint completion exists: the obstruction is preservation of parity
equivalence, not the existence of a classical joint law. -/
theorem bound_is_attained :
    ProbabilityFamily sharpFamily ∧ Response recordZ ∧ Response recordX ∧
    Calibrated sharpFamily recordZ recordX ∧
    success sharpFamily recordZ recordX = 3 / 4 + parityTV sharpFamily / 4 := by
  refine ⟨sharpFamily_probability, record_responses.1, record_responses.2,
    sharpFamily_calibrated, ?_⟩
  rw [sharpFamily_success, sharpFamily_parityTV]
  norm_num

/-- Machine-visible scope ledger; these tags do not assert missing bridges. -/
inductive BridgeBoundary where
  | probabilityFamilyNormalizationAndSharedResponsesSupplied
  | parityEquivalenceSuppliedWhenUsed
  | finiteRecordRobustBoundAndTightnessProved
  | intensitySharesAsProbabilitiesActualizationOpen
  | equalQuadraticMeansDoNotImplyEqualCompletedDistributions
  | hiddenRecordOperationalEquivalenceNeedsPreparationNoncontextuality
  | jointlyObservablePersistentRecordLawEqualityIsStrongerOperationalCondition
  | arbitraryResetTransportAndStochasticMixingClosureOpen
  | finiteSpacesOnlyNotGeneralMeasurableSpaces
  | doesNotExcludeAllClassicalTheories
  | doesNotDeriveQuantumTheory
  deriving DecidableEq, Repr

def bridgeLedger : List BridgeBoundary := [
  .probabilityFamilyNormalizationAndSharedResponsesSupplied,
  .parityEquivalenceSuppliedWhenUsed,
  .finiteRecordRobustBoundAndTightnessProved,
  .intensitySharesAsProbabilitiesActualizationOpen,
  .equalQuadraticMeansDoNotImplyEqualCompletedDistributions,
  .hiddenRecordOperationalEquivalenceNeedsPreparationNoncontextuality,
  .jointlyObservablePersistentRecordLawEqualityIsStrongerOperationalCondition,
  .arbitraryResetTransportAndStochasticMixingClosureOpen,
  .finiteSpacesOnlyNotGeneralMeasurableSpaces,
  .doesNotExcludeAllClassicalTheories,
  .doesNotDeriveQuantumTheory]

end

end IDT.QMClosure.PreparationRecordObstruction
