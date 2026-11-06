import Proofs.QMClosure.RawOperationalSeparation
import Proofs.QMClosure.QuadraticReadoutEffects

namespace IDT.QMClosure.NormalizedRecordEffects

open RawOperationalHilbert QuadraticRecordRefinement
open QuadraticReadoutEffects MixerRecordNaturality
open scoped BigOperators ComplexOrder

noncomputable section

/-!
A conditional adapter from raw operational data and a finite family of
normalized-mixer-natural record channels to mathematical effects. Source and
targets have no supplied raw algebra. Full-carrier normalized naturality and
total readout resolution are explicit additional operational assumptions.
They are not derived here from the underlying IDT primitives. The channels
may be affine with nonzero null vacuum offsets; strict vacuum preservation,
separate branch quadratic laws, and separate phase covariance are not inputs.
-/

variable {V R : Type*} [Fintype R] {U : R → Type*}

/-- Record channels into possibly different raw output carriers. -/
structure Family (source : Data V) (target : ∀ r, Data (U r)) where
  channel : ∀ r, V → U r
  natural : ∀ r, Intertwines source.normalizedOperation (target r).normalizedOperation
    (channel r)
  total : ∀ x, ∑ r, (target r).weight (channel r x) = source.weight x

variable {source : Data V} {target : ∀ r, Data (U r)}

def Family.readout (f : Family source target) (r : R) (x : Data.Carrier source) : ℝ :=
  (target r).weight (f.channel r x)

/-- Nonnegativity and the finite total resolution force null vacuum weight.
The record channel need not send the source vacuum to the target vacuum. -/
theorem Family.branch_vacuum (f : Family source target) (r : R) :
    f.readout r source.chosenZero = 0 := by
  exact finite_branch_vacuum (V := Data.Carrier source) f.readout source.weight
    (fun i x => (target i).nonnegative (f.channel i x)) f.total source.quadratic.zero r

/-- The quadratic branch law is transferred from reconstructed target data. -/
theorem Family.branch_quadratic (f : Family source target) (r : R) :
    PositiveQuadratic (f.readout r) := by
  exact positive_quadratic_pullback source.normalizedOperation (target r).normalizedOperation
    (RawOperationalSeparation.normalized_transparent source)
    (RawOperationalSeparation.normalized_square source)
    (RawOperationalSeparation.normalized_transparent (target r))
    (RawOperationalSeparation.normalized_square (target r))
    (f.channel r) (f.natural r) (target r).weight (target r).quadratic (f.branch_vacuum r)

/-- The SAME source phase preserves each readout, despite affine null offsets.
Phase covariance of the centered channel is a consequence of naturality. -/
theorem Family.branch_phase_invariant (f : Family source target) (r : R)
    (x : Data.Carrier source) : f.readout r (source.phase.J x) = f.readout r x := by
  obtain ⟨M, affine, phase_compatible⟩ := (affine_classification
    source.normalizedOperation (target r).normalizedOperation
    (RawOperationalSeparation.normalized_transparent source)
    (RawOperationalSeparation.normalized_square source)
    (RawOperationalSeparation.normalized_transparent (target r))
    (RawOperationalSeparation.normalized_square (target r))
    (f.channel r)).mp (f.natural r)
  have vacuum : (target r).weight (f.channel r (0 : Data.Carrier source)) = 0 :=
    f.branch_vacuum r
  have remove_offset (u : Data.Carrier source) :
      (target r).weight (f.channel r u) = (target r).weight (M u) := by
    rw [affine u]
    exact (target r).quadratic.null_translate (M u)
      (f.channel r (0 : Data.Carrier source)) vacuum
  change (target r).weight (f.channel r (source.phase.J x)) =
    (target r).weight (f.channel r x)
  rw [remove_offset, remove_offset]
  change (target r).weight (M (OperationalQuadraticReconstruction.phase
    source.normalizedOperation x)) = (target r).weight (M x)
  rw [phase_compatible x]
  exact (target r).reconstruction.phase_invariant (M x)

/-- No branch positivity, quadraticity, phase invariance, or domination is
supplied beyond the raw data and the two explicit record-family assumptions. -/
def Family.toResolution (f : Family source target) : Resolution source.phase R where
  q := f.readout
  positive := f.branch_quadratic
  invariant := f.branch_phase_invariant
  total := f.total

theorem Family.branch_dominated (f : Family source target) (r : R)
    (x : Data.Carrier source) : f.readout r x ≤ source.weight x :=
  f.toResolution.dominated r x

/-- The resulting effect lives on the reconstructed SOURCE Hilbert space. -/
def Family.effect (f : Family source target) (r : R) :
    source.Hilbert →L[ℂ] source.Hilbert :=
  (f.toResolution.branch r).effect source.quadratic

/-- Unnormalized branch expectation equals the supplied output record weight. -/
theorem Family.effect_expectation (f : Family source target) (r : R) (x : V) :
    inner ℂ (source.feature x) (f.effect r (source.feature x)) =
      ((target r).weight (f.channel r x) : ℂ) :=
  (f.toResolution.branch r).effect_diagonal source.quadratic x

theorem Family.effect_positive (f : Family source target) (r : R) :
    (f.effect r).IsPositive :=
  (f.toResolution.branch r).effect_positive source.quadratic

theorem Family.effect_le_one (f : Family source target) (r : R) : f.effect r ≤ 1 :=
  (f.toResolution.branch r).effect_le_one source.quadratic

theorem Family.effect_norm_le (f : Family source target) (r : R) : ‖f.effect r‖ ≤ 1 :=
  (f.toResolution.branch r).effect_norm_le source.quadratic

theorem Family.sum_effect_eq_one (f : Family source target) : ∑ r, f.effect r = 1 :=
  f.toResolution.sum_effect_eq_one source.quadratic

/-- Finite POVM reconstruction, allowing empty outcomes and zero total weight. -/
theorem Family.finite_povm (f : Family source target) :
    (∀ r, (f.effect r).IsPositive) ∧ (∀ r, f.effect r ≤ 1) ∧
    (∀ r, ‖f.effect r‖ ≤ 1) ∧ (∑ r, f.effect r) = 1 :=
  f.toResolution.finite_povm source.quadratic

inductive BoundaryRole where
  | rawSourceAndDependentRawTargets
  | suppliedFullCarrierNormalizedMixerNaturality
  | suppliedFiniteTotalReadoutResolution
  | branchVacuumWeightDerivedNotStrictVacuumPreservation
  | branchQuadraticityAndCommonPhaseInvarianceDerived
  | affineNullOffsetsAllowed
  | constructedSourceHilbertEffectsAndFiniteResolution
  | noRawCarrierAlgebraScalarsTopologyOrHalvingPremise
  | doesNotAssertRawUnnormalizedNaturalityIsNecessary
  | noPhysicalChannelInstrumentOrCompletedStateAvailability
  | noActualizationProjectivityRepeatabilityOrStateUpdate
  | doesNotProveOriginalIDTBridgeOrFullQMOrUpgradeStatus
  deriving DecidableEq, Repr

def boundaryRoles : List BoundaryRole := [
  .rawSourceAndDependentRawTargets,
  .suppliedFullCarrierNormalizedMixerNaturality,
  .suppliedFiniteTotalReadoutResolution,
  .branchVacuumWeightDerivedNotStrictVacuumPreservation,
  .branchQuadraticityAndCommonPhaseInvarianceDerived,
  .affineNullOffsetsAllowed,
  .constructedSourceHilbertEffectsAndFiniteResolution,
  .noRawCarrierAlgebraScalarsTopologyOrHalvingPremise,
  .doesNotAssertRawUnnormalizedNaturalityIsNecessary,
  .noPhysicalChannelInstrumentOrCompletedStateAvailability,
  .noActualizationProjectivityRepeatabilityOrStateUpdate,
  .doesNotProveOriginalIDTBridgeOrFullQMOrUpgradeStatus]

end

end IDT.QMClosure.NormalizedRecordEffects
