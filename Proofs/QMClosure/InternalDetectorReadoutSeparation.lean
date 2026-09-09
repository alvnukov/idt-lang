import Mathlib.Tactic

namespace IDT.QMClosure.InternalDetector

/-!
# Internal absorption does not select the probability law

The field and the detector are represented inside one finite system. Four
Boolean occupation slots include all 16 configurations, including vacuum,
double records and initially excited detectors. An ideal reversible exchange
swaps each field slot with its matching detector slot. Total occupation is
conserved; a single excitation with ready detectors becomes one detector
excitation and empty field slots. Double absorption is excluded by conservation,
not by deleting double-record states from the state space.

This is a deliberately granted finite kinematic model, not a derivation of
photodetection. Boolean occupations, a one-excitation preparation, rational
signed amplitudes, linear transport and an ideal resonant exchange are inputs.
Occupation conservation represents energy conservation only for equal-energy
resonant slots; continuous field modes, recoil and physical energy scales are
not modeled. Equal slot types do not identify photons with matter constituents.

The same transported amplitudes admit square and fourth-power readouts. Both
are positive and normalized on their nonzero support, exclude double records,
and pass the balanced and fully bright/dark interference signatures. They
disagree at amplitudes 3:4. Thus these specific signatures and an internal
detector do not select Born. The fourth-power law is only a countermodel to
these demands: it is not a consistent alternative to all quantum experiments.

A further separator is recorded: splitting one unresolved branch of amplitude
5 into distinguishable submodes of amplitudes 3 and 4 preserves its square
weight and changes its fourth-power weight. The 3-4-5 refinement already assumes
quadratic geometry, so imposing it cannot count as deriving that geometry.

Relation to existing work: InterferenceOrderSelectsTheExponent proves selection
inside natural monomial powers if nonzero I2 and identically zero I3 are imposed.
The fourth-power example below has I3=36 at three unit amplitudes. This file adds
the internal detector and checks its limitations; it does not reopen that gate.

Experimental anchors (external evidence, not Lean proofs):
* Grangier, Roger, Aspect (1986), DOI 10.1209/0295-5075/1/4/004:
  single-photon anticorrelation and interference.
* Jacques et al., https://arxiv.org/abs/0801.0979:
  single-photon interferometry with varying output splitter and complementarity.
* Sinha et al., https://arxiv.org/abs/1007.4193:
  a finite experimental bound on third-order interference, not exact universal
  vanishing. Changing slit boundaries and postselection require separate control.

Reversible transfer produces correlated record amplitudes, not a selected
outcome or an irreversible macroscopic record. Neither decoherence nor the fact
that the observer is internal supplies the probability rule in this model.
-/

structure Configuration where
  fieldLeft : Bool
  fieldRight : Bool
  detectorLeft : Bool
  detectorRight : Bool
  deriving DecidableEq, Repr

def occupation (c : Configuration) : ℕ :=
  (if c.fieldLeft then 1 else 0) + (if c.fieldRight then 1 else 0) +
    (if c.detectorLeft then 1 else 0) + (if c.detectorRight then 1 else 0)

def exchange (c : Configuration) : Configuration :=
  ⟨c.detectorLeft, c.detectorRight, c.fieldLeft, c.fieldRight⟩

theorem exchange_involutive (c : Configuration) : exchange (exchange c) = c := rfl

theorem exchange_conserves_occupation (c : Configuration) :
    occupation (exchange c) = occupation c := by
  rcases c with ⟨fl, fr, dl, dr⟩
  cases fl <;> cases fr <;> cases dl <;> cases dr <;> decide

/-- Applies to every occupation-conserving interaction, not just our exchange. -/
theorem single_excitation_excludes_double_record
    (interaction : Configuration → Configuration)
    (conserves : ∀ c, occupation (interaction c) = occupation c)
    (c : Configuration) (single : occupation c = 1) :
    ¬ ((interaction c).detectorLeft = true ∧
      (interaction c).detectorRight = true) := by
  intro both
  have h := conserves c
  simp only [occupation, both.1, both.2, ite_true] at h
  have hc : occupation c = 1 := single
  unfold occupation at hc
  omega

def leftField : Configuration := ⟨true, false, false, false⟩
def rightField : Configuration := ⟨false, true, false, false⟩
def leftRecord : Configuration := ⟨false, false, true, false⟩
def rightRecord : Configuration := ⟨false, false, false, true⟩
def doubleRecord : Configuration := ⟨false, false, true, true⟩

theorem exchange_transfers_both_paths :
    exchange leftField = leftRecord ∧ exchange rightField = rightRecord := by
  constructor <;> rfl

def preparedAmplitude (a b : ℚ) (c : Configuration) : ℚ :=
  if c = leftField then a else if c = rightField then b else 0

def recordAmplitude (a b : ℚ) (c : Configuration) : ℚ :=
  if c = leftRecord then a else if c = rightRecord then b else 0

/-- The same interaction transports the whole signed amplitude assignment. -/
theorem exchange_transports_amplitudes (a b : ℚ) (c : Configuration) :
    preparedAmplitude a b (exchange c) = recordAmplitude a b c := by
  rcases c with ⟨fl, fr, dl, dr⟩
  cases fl <;> cases fr <;> cases dl <;> cases dr <;>
    simp [preparedAmplitude, recordAmplitude, exchange,
      leftField, rightField, leftRecord, rightRecord]

theorem exchange_preserves_linear_superposition
    (f g : Configuration → ℚ) (s t : ℚ) (c : Configuration) :
    (fun x => s * f x + t * g x) (exchange c) =
      s * f (exchange c) + t * g (exchange c) := rfl

inductive ReadoutRule where
  | square
  | fourth
  deriving DecidableEq, Repr

def weight (rule : ReadoutRule) (a : ℚ) : ℚ :=
  match rule with
  | .square => a ^ 2
  | .fourth => a ^ 4

theorem weight_nonnegative (rule : ReadoutRule) (a : ℚ) : 0 ≤ weight rule a := by
  cases rule <;> simp only [weight] <;> positivity

def probability (rule : ReadoutRule) (a b : ℚ) (c : Configuration) : ℚ :=
  weight rule (recordAmplitude a b c) / (weight rule a + weight rule b)

theorem probability_nonnegative (rule : ReadoutRule) (a b : ℚ)
    (c : Configuration) : 0 ≤ probability rule a b c := by
  exact div_nonneg (weight_nonnegative _ _)
    (add_nonneg (weight_nonnegative _ _) (weight_nonnegative _ _))

theorem probability_supported_on_two_records (rule : ReadoutRule) (a b : ℚ)
    (c : Configuration) (hl : c ≠ leftRecord) (hr : c ≠ rightRecord) :
    probability rule a b c = 0 := by
  cases rule <;> simp [probability, recordAmplitude, hl, hr, weight]

theorem two_record_probabilities_normalized (rule : ReadoutRule) (a b : ℚ)
    (nonzero : weight rule a + weight rule b ≠ 0) :
    probability rule a b leftRecord + probability rule a b rightRecord = 1 := by
  simp only [probability, recordAmplitude]
  norm_num [leftRecord, rightRecord]
  rw [← add_div, div_self nonzero]

theorem double_record_probability_zero (rule : ReadoutRule) (a b : ℚ) :
    probability rule a b doubleRecord = 0 := by
  apply probability_supported_on_two_records <;>
    decide

/-- Signed two-path recombination, with a common normalization omitted.
This grants amplitude addition; it does not derive an optical beam splitter. -/
def recombinedLeftProbability (rule : ReadoutRule) (a b : ℚ) : ℚ :=
  probability rule (a + b) (a - b) leftRecord

def BasicSignatures (rule : ReadoutRule) : Prop :=
  probability rule 1 1 leftRecord = 1 / 2 ∧
  recombinedLeftProbability rule 1 1 = 1 ∧
  recombinedLeftProbability rule 1 (-1) = 0 ∧
  (∀ a b, probability rule a b doubleRecord = 0)

theorem both_rules_pass_basic_signatures (rule : ReadoutRule) :
    BasicSignatures rule := by
  refine ⟨?_, ?_, ?_, double_record_probability_zero rule⟩ <;>
    cases rule <;>
    norm_num [probability, recordAmplitude, weight,
      recombinedLeftProbability, leftRecord, rightRecord]

theorem same_preparation_different_probabilities :
    probability .square 3 4 leftRecord = 9 / 25 ∧
    probability .fourth 3 4 leftRecord = 81 / 337 ∧
    probability .square 3 4 leftRecord ≠ probability .fourth 3 4 leftRecord := by
  norm_num [probability, recordAmplitude, weight]

theorem basic_signatures_do_not_select_a_unique_readout :
    ¬ (∀ r s : ReadoutRule, BasicSignatures r → BasicSignatures s →
      ∀ a b c, probability r a b c = probability s a b c) := by
  intro unique
  exact same_preparation_different_probabilities.2.2
    (unique .square .fourth (both_rules_pass_basic_signatures _)
      (both_rules_pass_basic_signatures _) 3 4 leftRecord)

/-- Refinement means orthogonal/distinguishable submodes, not coherent paths. -/
def refinedLeftProbability (rule : ReadoutRule) (a₁ a₂ b : ℚ) : ℚ :=
  (weight rule a₁ + weight rule a₂) /
    (weight rule a₁ + weight rule a₂ + weight rule b)

theorem square_survives_345_refinement :
    probability .square 5 12 leftRecord = refinedLeftProbability .square 3 4 12 := by
  norm_num [probability, recordAmplitude, weight, refinedLeftProbability]

theorem fourth_fails_345_refinement :
    probability .fourth 5 12 leftRecord ≠ refinedLeftProbability .fourth 3 4 12 := by
  norm_num [probability, recordAmplitude, weight, refinedLeftProbability]

/-- A fixed-weight three-path diagnostic; no setting-dependent normalization. -/
def unitThreePathTerm (rule : ReadoutRule) : ℚ :=
  weight rule 3 - 3 * weight rule 2 + 3 * weight rule 1

theorem three_path_test_separates_rules :
    unitThreePathTerm .square = 0 ∧ unitThreePathTerm .fourth = 36 := by
  norm_num [unitThreePathTerm, weight]

/-! Machine-visible task ledger; entries are open obligations, not proof flags. -/
inductive OpenObligation where
  | deriveOccupationAndSingleExcitationPreparation
  | deriveAmplitudeAdditionAndComplexPhase
  | deriveLocalFieldMatterInteractionAndPhysicalEnergyBalance
  | deriveReadoutConsistencyUnderPhysicallyEquivalentRefinements
  | deriveStableMacroscopicRecordsAndExplainOutcomeStatistics
  | connectFixedWeightInterferenceTestsToDetectorCountsWithoutPostselectionBias
  | testCompositeNoSignallingAndFullInterferenceCurves
  deriving DecidableEq, Repr

def openObligations : List OpenObligation :=
  [ .deriveOccupationAndSingleExcitationPreparation,
    .deriveAmplitudeAdditionAndComplexPhase,
    .deriveLocalFieldMatterInteractionAndPhysicalEnergyBalance,
    .deriveReadoutConsistencyUnderPhysicallyEquivalentRefinements,
    .deriveStableMacroscopicRecordsAndExplainOutcomeStatistics,
    .connectFixedWeightInterferenceTestsToDetectorCountsWithoutPostselectionBias,
    .testCompositeNoSignallingAndFullInterferenceCurves ]

end IDT.QMClosure.InternalDetector
