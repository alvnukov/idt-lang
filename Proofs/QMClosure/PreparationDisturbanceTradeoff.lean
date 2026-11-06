import Proofs.QMClosure.PreparationRecordObstruction

namespace IDT.QMClosure.PreparationDisturbanceTradeoff

open PreparationRecordObstruction

noncomputable section

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

/-!
# Finite preparation and marginal-error tradeoff

The generic theorem concerns supplied normalized finite probability families and
bounded responses. The sequential specialization uses the two outcomes actually
recorded in one ZX protocol: records 00, 01, 10, 11, with their coordinate
responses. It does not preassign outcomes to incompatible counterfactual
contexts. Equal-parity joint ZX laws and the first-record calibration are
explicit assumptions, not consequences of equal quadratic intensity means.

Each absolute binary event-probability difference equals the total variation
distance between the corresponding binary laws. The mean errors below may be
called disturbance only conditional on calibrated standalone events and the
same instrument, with no postselection and all outcomes retained. These results
constrain compatible probability laws; they do not construct an instrument or
assume projectors or an instrument update rule. Native intensity shares becoming
standalone probabilities remains an open actualization bridge.
-/

variable {Ω : Type*} [Fintype Ω]

/-- Average binary marginal-law total variation over the four preparations. -/
def meanMarginalError (μ : Fin 4 → Ω → ℝ) (r : Ω → ℝ)
    (target : Fin 4 → ℝ) : ℝ :=
  (∑ a, |marginal μ r a - target a|) / 4

theorem meanMarginalError_nonnegative (μ : Fin 4 → Ω → ℝ) (r : Ω → ℝ)
    (target : Fin 4 → ℝ) : 0 ≤ meanMarginalError μ r target := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

theorem meanMarginalError_zero_of_exact (μ : Fin 4 → Ω → ℝ) (r : Ω → ℝ)
    (target : Fin 4 → ℝ) (hexact : ∀ a, marginal μ r a = target a) :
    meanMarginalError μ r target = 0 := by
  simp [meanMarginalError, hexact]

/-- Marginal error can lower the calibrated score by at most half the error sum. -/
theorem success_lower_bound_from_marginal_errors (μ : Fin 4 → Ω → ℝ)
    (rZ rX : Ω → ℝ) (law : ProbabilityFamily μ) :
    17 / 20 - (meanMarginalError μ rZ targetZ +
      meanMarginalError μ rX targetX) / 2 ≤ success μ rZ rX := by
  have hz0 := neg_le_abs (marginal μ rZ 0 - targetZ 0)
  have hz1 := neg_le_abs (marginal μ rZ 1 - targetZ 1)
  have hz2 := le_abs_self (marginal μ rZ 2 - targetZ 2)
  have hz3 := le_abs_self (marginal μ rZ 3 - targetZ 3)
  have hx0 := neg_le_abs (marginal μ rX 0 - targetX 0)
  have hx1 := le_abs_self (marginal μ rX 1 - targetX 1)
  have hx2 := neg_le_abs (marginal μ rX 2 - targetX 2)
  have hx3 := le_abs_self (marginal μ rX 3 - targetX 3)
  rw [success_marginal_formula μ rZ rX law]
  norm_num [meanMarginalError, Fin.sum_univ_succ, targetZ, targetX] at *
  have hlast : (2 : Fin 3).succ = (3 : Fin 4) := rfl
  simp only [hlast]
  linarith

/-- Universal finite-space robustness bound; no event actualization is inferred. -/
theorem parityTV_add_twice_marginal_errors (μ : Fin 4 → Ω → ℝ)
    (rZ rX : Ω → ℝ) (law : ProbabilityFamily μ)
    (hZ : Response rZ) (hX : Response rX) :
    2 / 5 ≤ parityTV μ + 2 * (meanMarginalError μ rZ targetZ +
      meanMarginalError μ rX targetX) := by
  have hlo := success_lower_bound_from_marginal_errors μ rZ rX law
  have hhi := success_le_three_quarters_add_parityTV μ rZ rX law hZ hX
  linarith

/-- Correct first-bit score for an actual two-record protocol. -/
def firstSuccess (μ : Fin 4 → Fin 4 → ℝ) : ℝ :=
  (marginal μ recordZ 0 + marginal μ recordZ 1 +
    (1 - marginal μ recordZ 2) + (1 - marginal μ recordZ 3)) / 4

/-- Signed correct second-bit score; record order is 00, 01, 10, 11. -/
def secondSuccess (μ : Fin 4 → Fin 4 → ℝ) : ℝ :=
  (marginal μ recordX 0 + (1 - marginal μ recordX 1) +
    marginal μ recordX 2 + (1 - marginal μ recordX 3)) / 4

def standaloneXTargetSuccess : ℝ :=
  (targetX 0 + (1 - targetX 1) + targetX 2 + (1 - targetX 3)) / 4

theorem standaloneXTargetSuccess_eq : standaloneXTargetSuccess = 9 / 10 := by
  norm_num [standaloneXTargetSuccess, targetX]

theorem success_eq_mean_stage_success (μ : Fin 4 → Fin 4 → ℝ)
    (law : ProbabilityFamily μ) :
    success μ recordZ recordX = (firstSuccess μ + secondSuccess μ) / 2 := by
  rw [success_marginal_formula μ recordZ recordX law]
  unfold firstSuccess secondSuccess
  ring

theorem firstSuccess_eq_of_calibrated (μ : Fin 4 → Fin 4 → ℝ)
    (hfirst : ∀ a, marginal μ recordZ a = targetZ a) : firstSuccess μ = 4 / 5 := by
  unfold firstSuccess
  simp only [hfirst]
  norm_num [targetZ]

/-- The parity hypothesis is equality of actual joint ZX record mixtures. -/
theorem sequential_second_marginal_error_lower_bound (μ : Fin 4 → Fin 4 → ℝ)
    (law : ProbabilityFamily μ)
    (hfirst : ∀ a, marginal μ recordZ a = targetZ a)
    (heq : ParityEquivalent μ) : 1 / 5 ≤ meanMarginalError μ recordX targetX := by
  have h := parityTV_add_twice_marginal_errors μ recordZ recordX law
    record_responses.1 record_responses.2
  rw [parityTV_zero_of_equivalent μ heq,
    meanMarginalError_zero_of_exact μ recordZ targetZ hfirst] at h
  linarith

theorem sequential_secondSuccess_upper_bound (μ : Fin 4 → Fin 4 → ℝ)
    (law : ProbabilityFamily μ)
    (hfirst : ∀ a, marginal μ recordZ a = targetZ a)
    (heq : ParityEquivalent μ) : secondSuccess μ ≤ 7 / 10 := by
  have h := success_le_three_quarters_of_equivalent μ recordZ recordX law
    record_responses.1 record_responses.2 heq
  rw [success_eq_mean_stage_success μ law, firstSuccess_eq_of_calibrated μ hfirst] at h
  linarith

/-- Explicit comparison with the separately supplied standalone X target. -/
theorem sequential_secondSuccess_gap (μ : Fin 4 → Fin 4 → ℝ)
    (law : ProbabilityFamily μ)
    (hfirst : ∀ a, marginal μ recordZ a = targetZ a)
    (heq : ParityEquivalent μ) :
    1 / 5 ≤ standaloneXTargetSuccess - secondSuccess μ := by
  rw [standaloneXTargetSuccess_eq]
  have h := sequential_secondSuccess_upper_bound μ law hfirst heq
  linarith

/-- Sharp zero-parity-information endpoint, with actual joint outcomes. -/
def disturbedFamily : Fin 4 → Fin 4 → ℝ :=
  ![![1 / 2, 3 / 10, 1 / 5, 0], ![3 / 10, 1 / 2, 0, 1 / 5],
    ![1 / 5, 0, 1 / 2, 3 / 10], ![0, 1 / 5, 3 / 10, 1 / 2]]

theorem disturbedFamily_probability : ProbabilityFamily disturbedFamily := by
  constructor
  · intro a ω
    fin_cases a <;> fin_cases ω <;> norm_num [disturbedFamily]
  · intro a
    fin_cases a <;> norm_num [disturbedFamily, Fin.sum_univ_succ]

theorem disturbedFamily_parityEquivalent : ParityEquivalent disturbedFamily := by
  intro ω
  fin_cases ω <;> norm_num [disturbedFamily]

theorem disturbedFamily_first_calibrated :
    ∀ a, marginal disturbedFamily recordZ a = targetZ a := by
  intro a
  fin_cases a <;>
    norm_num [marginal, disturbedFamily, recordZ, targetZ, Fin.sum_univ_succ]

theorem disturbedFamily_first_error :
    meanMarginalError disturbedFamily recordZ targetZ = 0 :=
  meanMarginalError_zero_of_exact _ _ _ disturbedFamily_first_calibrated

theorem disturbedFamily_second_error :
    meanMarginalError disturbedFamily recordX targetX = 1 / 5 := by
  norm_num [meanMarginalError, marginal, disturbedFamily, recordX, targetX,
    Fin.sum_univ_succ]

theorem disturbedFamily_secondSuccess : secondSuccess disturbedFamily = 7 / 10 := by
  norm_num [secondSuccess, marginal, disturbedFamily, recordX, Fin.sum_univ_succ]

theorem disturbedFamily_success : success disturbedFamily recordZ recordX = 3 / 4 := by
  rw [success_eq_mean_stage_success _ disturbedFamily_probability,
    firstSuccess_eq_of_calibrated _ disturbedFamily_first_calibrated,
    disturbedFamily_secondSuccess]
  norm_num

/-- Both the score bound and the error tradeoff are attained at this endpoint. -/
theorem disturbedFamily_attains_bounds :
    ProbabilityFamily disturbedFamily ∧ ParityEquivalent disturbedFamily ∧
    (∀ a, marginal disturbedFamily recordZ a = targetZ a) ∧
    meanMarginalError disturbedFamily recordZ targetZ = 0 ∧
    meanMarginalError disturbedFamily recordX targetX = 1 / 5 ∧
    secondSuccess disturbedFamily = 7 / 10 ∧
    success disturbedFamily recordZ recordX = 3 / 4 + parityTV disturbedFamily / 4 ∧
    parityTV disturbedFamily + 2 * (meanMarginalError disturbedFamily recordZ targetZ +
      meanMarginalError disturbedFamily recordX targetX) = 2 / 5 := by
  refine ⟨disturbedFamily_probability, disturbedFamily_parityEquivalent,
    disturbedFamily_first_calibrated, disturbedFamily_first_error,
    disturbedFamily_second_error, disturbedFamily_secondSuccess, ?_, ?_⟩
  · rw [disturbedFamily_success,
      parityTV_zero_of_equivalent _ disturbedFamily_parityEquivalent]
    norm_num
  · rw [parityTV_zero_of_equivalent _ disturbedFamily_parityEquivalent,
      disturbedFamily_first_error, disturbedFamily_second_error]
    norm_num

/-- The dependency supplies the complementary zero-error endpoint. -/
theorem undisturbed_endpoint_attains_tradeoff :
    meanMarginalError sharpFamily recordZ targetZ = 0 ∧
    meanMarginalError sharpFamily recordX targetX = 0 ∧
    parityTV sharpFamily + 2 * (meanMarginalError sharpFamily recordZ targetZ +
      meanMarginalError sharpFamily recordX targetX) = 2 / 5 := by
  have hz := meanMarginalError_zero_of_exact sharpFamily recordZ targetZ
    sharpFamily_calibrated.1
  have hx := meanMarginalError_zero_of_exact sharpFamily recordX targetX
    sharpFamily_calibrated.2
  refine ⟨hz, hx, ?_⟩
  rw [hz, hx, sharpFamily_parityTV]
  norm_num

/-- Machine-visible scope ledger; none of these tags supplies an open bridge. -/
inductive BridgeBoundary where
  | finiteProbabilityFamiliesAndBoundedResponsesSupplied
  | genericFiniteSpaceDistinctFromActualJointRecordSpecialization
  | nativeIntensitySharesAsStandaloneProbabilitiesActualizationOpen
  | firstRecordMarginalEqualitySupplied
  | causalReadingNeedsSameInstrumentNoPostselectionAndAllOutcomes
  | equalParityActualJointZXLawsSuppliedWhenUsed
  | allProtocolPreparationEquivalenceIsStrongerThanThisExactAssumption
  | equalQuadraticMeansDoNotImplyEqualParityJointZXLaws
  | errorsAreAverageBinaryLawTotalVariation
  | disturbanceReadingConditionalOnCalibratedStandaloneEvents
  | actualJointRecordsNeedNoHiddenVariableOrPreparationNoncontextualityPremise
  | noProjectorsOrInstrumentUpdateAssumed
  | constrainsProbabilityLawsWithoutConstructingPhysicalInstrument
  | sharpFiniteScoreAndErrorTradeoffProved
  | doesNotExcludeAllClassicalTheories
  | doesNotDeriveQuantumTheory
  deriving DecidableEq, Repr

def bridgeLedger : List BridgeBoundary := [
  .finiteProbabilityFamiliesAndBoundedResponsesSupplied,
  .genericFiniteSpaceDistinctFromActualJointRecordSpecialization,
  .nativeIntensitySharesAsStandaloneProbabilitiesActualizationOpen,
  .firstRecordMarginalEqualitySupplied,
  .causalReadingNeedsSameInstrumentNoPostselectionAndAllOutcomes,
  .equalParityActualJointZXLawsSuppliedWhenUsed,
  .allProtocolPreparationEquivalenceIsStrongerThanThisExactAssumption,
  .equalQuadraticMeansDoNotImplyEqualParityJointZXLaws,
  .errorsAreAverageBinaryLawTotalVariation,
  .disturbanceReadingConditionalOnCalibratedStandaloneEvents,
  .actualJointRecordsNeedNoHiddenVariableOrPreparationNoncontextualityPremise,
  .noProjectorsOrInstrumentUpdateAssumed,
  .constrainsProbabilityLawsWithoutConstructingPhysicalInstrument,
  .sharpFiniteScoreAndErrorTradeoffProved,
  .doesNotExcludeAllClassicalTheories,
  .doesNotDeriveQuantumTheory]

end

end IDT.QMClosure.PreparationDisturbanceTradeoff
