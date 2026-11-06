import Proofs.QMClosure.NormalizedRecordEffects
import Proofs.QMClosure.DyadicEffectDomainActualization

namespace IDT.QMClosure.ConditionalRecordProbabilities

open RawOperationalHilbert NormalizedRecordEffects
open CalibratedEffectActualization DyadicEffectDomainActualization
open scoped BigOperators ComplexOrder

noncomputable section

/-!
Conditional composition of the raw-data effect reconstruction and calibrated
actualization on a supplied event domain. The Hilbert space is the mathematical
output of the raw source data. Inverse-norm normalization takes place only in
that output; it supplies no native normalization operation or physically
available preparation. The event domain, its accounting/closure laws, matched
projector membership and calibration, and branch membership remain premises.
No physical outcome generator, instrument, state update, original-IDT bridge,
Born-rule closure or full-QM closure is established.
-/

variable {V R : Type*} [Fintype R] {U : R → Type*}
variable (source : Data V)

/-- Mathematical normalization in the reconstructed source Hilbert space. -/
def normalizedFeature (x : V) : source.Hilbert :=
  ((‖source.feature x‖⁻¹ : ℝ) : ℂ) • source.feature x

theorem norm_feature_pos (x : V) (positive : 0 < source.weight x) :
    0 < ‖source.feature x‖ := by
  have hsq := source.norm_feature_sq x
  nlinarith [norm_nonneg (source.feature x)]

theorem normalizedFeature_unit (x : V) (positive : 0 < source.weight x) :
    ‖normalizedFeature source x‖ = 1 := by
  rw [normalizedFeature, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (ne_of_gt (norm_feature_pos source x positive))

variable {source} {target : ∀ r, Data (U r)}

/-- The normalized expectation is a consequence of the unnormalized branch
identity and the raw source norm identity, not a probability premise. -/
theorem normalized_effect_expectation (f : Family source target) (x : V) (r : R) :
    (inner ℂ (normalizedFeature source x)
      (f.effect r (normalizedFeature source x))).re =
      (target r).weight (f.channel r x) / source.weight x := by
  rw [normalizedFeature, quadratic_smul, f.effect_expectation,
    Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_pow,
    source.norm_feature_sq]
  ring

variable {D : Set (Op (H := source.Hilbert))}
variable {p : Op (H := source.Hilbert) → ℝ}

/-- Conditional finite record probability formula with every event bridge
explicit: domain law, matched-test membership/calibration, branch membership.
The source and dependent targets carry exactly the contracts of `Data`, and
`Family` supplies normalized mixer naturality and total weight resolution. -/
theorem record_probability (f : Family source target) (x : V)
    (positive : 0 < source.weight x) (law : DomainLaw D p)
    (matched_mem : projector (normalizedFeature source x) ∈ D)
    (calibrated : p (projector (normalizedFeature source x)) = 1)
    (branch_mem : ∀ r, f.effect r ∈ D) (r : R) :
    p (f.effect r) = (target r).weight (f.channel r x) / source.weight x := by
  rw [law.calibrated_probability_eq_expectation
    (normalizedFeature_unit source x positive) matched_mem calibrated (branch_mem r)]
  exact normalized_effect_expectation f x r

/-- The finite probabilities sum to one from the supplied total weight
resolution and positive source weight; no nonempty outcome type is assumed. -/
theorem record_probabilities_sum (f : Family source target) (x : V)
    (positive : 0 < source.weight x) (law : DomainLaw D p)
    (matched_mem : projector (normalizedFeature source x) ∈ D)
    (calibrated : p (projector (normalizedFeature source x)) = 1)
    (branch_mem : ∀ r, f.effect r ∈ D) :
    ∑ r, p (f.effect r) = 1 := by
  simp_rw [record_probability f x positive law matched_mem calibrated branch_mem]
  rw [← Finset.sum_div, f.total, div_self (ne_of_gt positive)]

theorem record_probability_bounds (f : Family source target)
    (law : DomainLaw D p) (branch_mem : ∀ r, f.effect r ∈ D) (r : R) :
    p (f.effect r) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨law.nonnegative _ (branch_mem r), law.probability_le_one (branch_mem r)⟩

/-- Combined conditional probability package, with all assumptions visible. -/
theorem conditional_record_probabilities (f : Family source target) (x : V)
    (positive : 0 < source.weight x) (law : DomainLaw D p)
    (matched_mem : projector (normalizedFeature source x) ∈ D)
    (calibrated : p (projector (normalizedFeature source x)) = 1)
    (branch_mem : ∀ r, f.effect r ∈ D) :
    (∀ r, p (f.effect r) = (target r).weight (f.channel r x) / source.weight x) ∧
    (∑ r, p (f.effect r)) = 1 ∧
    (∀ r, p (f.effect r) ∈ Set.Icc (0 : ℝ) 1) :=
  ⟨record_probability f x positive law matched_mem calibrated branch_mem,
    record_probabilities_sum f x positive law matched_mem calibrated branch_mem,
    record_probability_bounds f law branch_mem⟩

inductive BoundaryRole where
  | rawSourceAndDependentFiniteTargets
  | suppliedNormalizedMixerNaturalityAndTotalWeightResolution
  | suppliedPositiveSourceWeight
  | mathematicalSourceHilbertAndFeatureNormalizationDerived
  | suppliedEventDomainAndDomainLaw
  | suppliedMatchedProjectorMembershipAndCalibration
  | suppliedBranchEffectMembership
  | conditionalWeightRatioBoundsAndFiniteNormalization
  | noNativeNormalizationOrPhysicalPreparationAvailability
  | noOutcomeGeneratorInstrumentOrStateUpdate
  | noOriginalIDTBridgeBornClosureFullQMOrStatusUpgrade
  deriving DecidableEq, Repr

def boundaryRoles : List BoundaryRole := [
  .rawSourceAndDependentFiniteTargets,
  .suppliedNormalizedMixerNaturalityAndTotalWeightResolution,
  .suppliedPositiveSourceWeight,
  .mathematicalSourceHilbertAndFeatureNormalizationDerived,
  .suppliedEventDomainAndDomainLaw,
  .suppliedMatchedProjectorMembershipAndCalibration,
  .suppliedBranchEffectMembership,
  .conditionalWeightRatioBoundsAndFiniteNormalization,
  .noNativeNormalizationOrPhysicalPreparationAvailability,
  .noOutcomeGeneratorInstrumentOrStateUpdate,
  .noOriginalIDTBridgeBornClosureFullQMOrStatusUpgrade]

end

end IDT.QMClosure.ConditionalRecordProbabilities
