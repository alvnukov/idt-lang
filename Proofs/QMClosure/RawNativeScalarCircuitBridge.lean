import Proofs.QMClosure.RawOperationalSeparation
import Proofs.QMClosure.NativeAttenuationCircuit

/-!
A mathematical adapter from the supplied scalar normalized-mixer syntax to the
normalized operation reconstructed from raw operational data. The scalar action
and Hilbert space are constructed outputs; no algebra is supplied on raw `V`.

The feature relation on general inputs is an explicit hypothesis, not a theorem
that arbitrary complex coefficients have raw representatives. The single-input
corollary uses only the reference and chosen raw zero. Finite wire arrays denote
coherent alternatives. No copying, normalization control, physical availability,
outcome probability, calibration, tensor system, or full QM is established.

The original raw operation can differ from its diagonal-normalized operation.
Its diagonal is a mathematical term, not an available copying or inverse-
normalization control. This file retargets syntax only to the normalized gate.
-/

namespace IDT.QMClosure.RawNativeScalarCircuitBridge

noncomputable section

open RawOperationalHilbert MixerGeneratedProcessWall
open PositiveMixerQuadraticReadout

variable {V ι : Type*} (d : Data V) [Fintype ι] [DecidableEq ι]

theorem feature_add (x y : Data.Carrier d) :
    d.feature (x + y) = d.feature x + d.feature y :=
  CanonicalQuadraticHilbert.feature_add d.quadratic d.phase x y

theorem feature_sub (x y : Data.Carrier d) :
    d.feature (x - y) = d.feature x - d.feature y :=
  (CanonicalQuadraticHilbert.featureHom d.quadratic d.phase).map_sub x y

theorem feature_phase (x : Data.Carrier d) :
    d.feature (d.phase.J x) = Complex.I • d.feature x :=
  CanonicalQuadraticHilbert.feature_phase d.quadratic d.phase x

theorem feature_half (x : Data.Carrier d) :
    d.feature (RawOperationalSeparation.half d x) = (2 : ℂ)⁻¹ • d.feature x :=
  CanonicalQuadraticHilbert.feature_half d.quadratic d.phase
    (RawOperationalSeparation.half d) d.reconstruction.halves x

theorem feature_coefficientA (x : Data.Carrier d) :
    d.feature (coefficientA (V := Data.Carrier d) d.phase.J
      (RawOperationalSeparation.half d) x) =
      NativeAttenuationCircuit.a • d.feature x := by
  unfold coefficientA
  rw [feature_half d, feature_add d, feature_phase d, smul_add, smul_smul, ← add_smul]
  congr 1
  unfold NativeAttenuationCircuit.a
  ring

theorem feature_coefficientB (x : Data.Carrier d) :
    d.feature (coefficientB (V := Data.Carrier d) d.phase.J
      (RawOperationalSeparation.half d) x) =
      NativeAttenuationCircuit.b • d.feature x := by
  unfold coefficientB
  rw [feature_half d, feature_sub d, feature_phase d, smul_sub, smul_smul, ← sub_smul]
  congr 1
  unfold NativeAttenuationCircuit.b
  ring

theorem feature_normalized_fst (x y : Data.Carrier d) :
    d.feature (d.normalizedOperation (x, y)).1 =
      NativeAttenuationCircuit.a • d.feature x +
        NativeAttenuationCircuit.b • d.feature y := by
  rw [RawOperationalSeparation.normalized_route]
  exact (feature_add d
    (coefficientA (V := Data.Carrier d) d.phase.J (RawOperationalSeparation.half d) x)
    (coefficientB (V := Data.Carrier d) d.phase.J (RawOperationalSeparation.half d) y)).trans
    (by rw [feature_coefficientA d, feature_coefficientB d])

theorem feature_normalized_snd (x y : Data.Carrier d) :
    d.feature (d.normalizedOperation (x, y)).2 =
      NativeAttenuationCircuit.b • d.feature x +
        NativeAttenuationCircuit.a • d.feature y := by
  rw [RawOperationalSeparation.normalized_route]
  exact (feature_add d
    (coefficientB (V := Data.Carrier d) d.phase.J (RawOperationalSeparation.half d) x)
    (coefficientA (V := Data.Carrier d) d.phase.J (RawOperationalSeparation.half d) y)).trans
    (by rw [feature_coefficientB d, feature_coefficientA d])

/-- Every constructor retains exactly its indices and chronological order. -/
def liftCircuit : Circuit (ι := ι) NativeMixerEventConeExclusion.mixer →
    Circuit (ι := ι) d.normalizedOperation
  | .identity => .identity
  | .pair i j distinct => .pair i j distinct
  | .permute e => .permute e
  | .seq first second => .seq (liftCircuit first) (liftCircuit second)

omit [Fintype ι] in
/-- Conditional feature transport for arbitrary raw inputs. No raw scalar
preparation or faithful representation premise is hidden in the syntax lift. -/
theorem circuit_feature
    (c : Circuit (ι := ι) NativeMixerEventConeExclusion.mixer)
    (v : V) (x : ι → Data.Carrier d) (z : ι → ℂ)
    (hx : ∀ i, d.feature (x i) = z i • d.feature v) (k : ι) :
    d.feature ((liftCircuit d c).eval x k) = c.eval z k • d.feature v := by
  induction c generalizing x z k with
  | identity => exact hx k
  | pair i j distinct =>
      change d.feature (if k = i then (d.normalizedOperation (x i, x j)).1
        else if k = j then (d.normalizedOperation (x i, x j)).2 else x k) =
        (if k = i then (NativeMixerEventConeExclusion.mixer (z i, z j)).1
        else if k = j then (NativeMixerEventConeExclusion.mixer (z i, z j)).2
        else z k) • d.feature v
      by_cases hi : k = i
      · simp only [if_pos hi]
        rw [feature_normalized_fst, hx, hx, NativeAttenuationCircuit.mixer_fst,
          add_smul, mul_smul, mul_smul]
      · by_cases hj : k = j
        · simp only [if_neg hi, if_pos hj]
          rw [feature_normalized_snd, hx, hx, NativeAttenuationCircuit.mixer_snd,
            add_smul, mul_smul, mul_smul]
        · simpa only [if_neg hi, if_neg hj] using hx k
  | permute e => exact hx (e k)
  | seq first second hfirst hsecond =>
      exact hsecond ((liftCircuit d first).eval x) (first.eval z)
        (fun i => hfirst x z hx i) k

omit [Fintype ι] in
/-- Absolute weight identity, including null references and all-null models. -/
theorem circuit_weight
    (c : Circuit (ι := ι) NativeMixerEventConeExclusion.mixer)
    (v : V) (x : ι → Data.Carrier d) (z : ι → ℂ)
    (hx : ∀ i, d.feature (x i) = z i • d.feature v) (k : ι) :
    d.weight ((liftCircuit d c).eval x k) =
      Complex.normSq (c.eval z k) * d.weight v := by
  rw [← d.norm_feature_sq, circuit_feature d c v x z hx k, norm_smul, mul_pow,
    d.norm_feature_sq, Complex.normSq_eq_norm_sq]

omit [Fintype ι] in
/-- A relative weight additionally requires a positive reference weight. -/
theorem circuit_weight_ratio
    (c : Circuit (ι := ι) NativeMixerEventConeExclusion.mixer)
    (v : V) (x : ι → Data.Carrier d) (z : ι → ℂ)
    (hx : ∀ i, d.feature (x i) = z i • d.feature v)
    (positive : 0 < d.weight v) (k : ι) :
    d.weight ((liftCircuit d c).eval x k) / d.weight v =
      Complex.normSq (c.eval z k) := by
  rw [circuit_weight d c v x z hx k]
  exact mul_div_cancel_right₀ _ (ne_of_gt positive)

omit [Fintype ι] in
/-- A raw basis input uses the reference at one wire and the chosen zero at
every other wire; it requires no arbitrary complex raw representatives. -/
theorem single_feature (source : ι) (v : V) (k : ι) :
    d.feature (single (V := Data.Carrier d) source v k) =
      single source (1 : ℂ) k • d.feature v := by
  by_cases h : k = source
  · simp [single, h]
  · simp only [single, h, if_false, zero_smul]
    exact d.feature_zero

omit [Fintype ι] in
theorem single_circuit_feature
    (c : Circuit (ι := ι) NativeMixerEventConeExclusion.mixer)
    (source : ι) (v : V) (k : ι) :
    d.feature ((liftCircuit d c).eval (single (V := Data.Carrier d) source v) k) =
      c.eval (single source (1 : ℂ)) k • d.feature v :=
  circuit_feature d c v _ _ (single_feature d source v) k

omit [Fintype ι] in
theorem single_circuit_weight
    (c : Circuit (ι := ι) NativeMixerEventConeExclusion.mixer)
    (source : ι) (v : V) (k : ι) :
    d.weight ((liftCircuit d c).eval (single (V := Data.Carrier d) source v) k) =
      Complex.normSq (c.eval (single source (1 : ℂ)) k) * d.weight v :=
  circuit_weight d c v _ _ (single_feature d source v) k

omit [Fintype ι] in
/-- Division is justified only for a strictly positive reference weight. -/
theorem single_circuit_weight_ratio
    (c : Circuit (ι := ι) NativeMixerEventConeExclusion.mixer)
    (source : ι) (v : V) (positive : 0 < d.weight v) (k : ι) :
    d.weight ((liftCircuit d c).eval (single (V := Data.Carrier d) source v) k) /
        d.weight v = Complex.normSq (c.eval (single source (1 : ℂ)) k) := by
  rw [single_circuit_weight]
  exact mul_div_cancel_right₀ _ (ne_of_gt positive)

/-- Explicit limits of the mathematical scalar adapter. -/
inductive BoundaryRole where
  | originalRawOperationMayDifferFromDerivedNormalizedGate
  | rawDiagonalIsMathematicalTermNotCopyingOrNormalizationControl
  | identicalWireIndicesPermutationAndChronologicalCircuitSyntax
  | constructedHilbertScalarsNotSuppliedRawCarrierAlgebra
  | generalFeatureRelationIsHypothesisNotArbitraryRawPreparation
  | singleInputUsesOnlyReferenceAndChosenZero
  | absoluteWeightIdentityAllowsNullReferenceAndAllNullModels
  | relativeWeightRequiresStrictlyPositiveReferenceWeight
  | finiteWireArraysAreCoherentAlternativesNotTensorSystems
  | noPhysicalGateAvailabilityProbabilityActualizationOrCalibration
  | noArbitraryRawFaithfulnessOrGaussianDyadicQuotientClaim
  | doesNotProveFullQMOrUpgradeManifestStatus
  deriving DecidableEq, Repr

def boundaryRoles : List BoundaryRole := [
  .originalRawOperationMayDifferFromDerivedNormalizedGate,
  .rawDiagonalIsMathematicalTermNotCopyingOrNormalizationControl,
  .identicalWireIndicesPermutationAndChronologicalCircuitSyntax,
  .constructedHilbertScalarsNotSuppliedRawCarrierAlgebra,
  .generalFeatureRelationIsHypothesisNotArbitraryRawPreparation,
  .singleInputUsesOnlyReferenceAndChosenZero,
  .absoluteWeightIdentityAllowsNullReferenceAndAllNullModels,
  .relativeWeightRequiresStrictlyPositiveReferenceWeight,
  .finiteWireArraysAreCoherentAlternativesNotTensorSystems,
  .noPhysicalGateAvailabilityProbabilityActualizationOrCalibration,
  .noArbitraryRawFaithfulnessOrGaussianDyadicQuotientClaim,
  .doesNotProveFullQMOrUpgradeManifestStatus]

end

end IDT.QMClosure.RawNativeScalarCircuitBridge
