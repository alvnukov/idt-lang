import Proofs.QMClosure.InfinitesimalPairReadoutSelection
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace IDT.QMClosure.FixedReferenceBalanceBridge

noncomputable section

/-!
# Conditional fixed-reference bridge to infinitesimal response selection

The supplied readout is an UNCONDITIONAL reference-event probability, with one
shared context-independent nonnegative response `F` and the same positive
reference weight `R`. Its denominator must account for every trial outcome,
including loss and environment. The stationarity contract below is supplied;
it is not derived from causality, normalization, or Bell no-signalling.

Affine probes encode only velocities at zero. They do not assert physical
accessibility or finite-time invariance of the Euler map `I + t A`. A physical
operation must independently realize the stated merge-compatible velocity.

The result is a conditional mathematical bridge. It does not derive its
operational assumptions, primitive real completion, Born actualization,
complex structure, composites, full QM, GR, or physical constants.
-/

/-- With a fixed positive numerator, equality of unconditional reference
probabilities is exactly equality of the other total represented weight. -/
theorem reference_probability_eq_iff (R S S' : ℝ) (hR : 0 < R)
    (hS : 0 ≤ S) (hS' : 0 ≤ S') :
    R / (R + S) = R / (R + S') ↔ S = S' := by
  have hden : R + S ≠ 0 := ne_of_gt (by linarith)
  have hden' : R + S' ≠ 0 := ne_of_gt (by linarith)
  constructor
  · intro h
    have hcross := (div_eq_div_iff hden hden').mp h
    have hprod : R * S = R * S' := by nlinarith [hcross]
    exact mul_left_cancel₀ (ne_of_gt hR) hprod
  · rintro rfl
    rfl

/-- If additional active channels have weight `L`, reference invariance fixes
`S + L`, rather than the selected weight `S` on its own. -/
theorem reference_probability_with_extra_channels_eq_iff (R S S' L L' : ℝ)
    (hR : 0 < R) (hS : 0 ≤ S) (hS' : 0 ≤ S')
    (hL : 0 ≤ L) (hL' : 0 ≤ L') :
    R / (R + S + L) = R / (R + S' + L') ↔ S + L = S' + L' := by
  simpa only [add_assoc] using
    reference_probability_eq_iff R (S + L) (S' + L') hR
      (add_nonneg hS hL) (add_nonneg hS' hL')

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A fixed reference event alongside two channels with a shared response.
Interpretation as a probability requires the explicit unconditional-readout
and exhaustive-outcome bridges described above. -/
def referenceProbability (R : ℝ) (F : V → ℝ) (x y : V) : ℝ :=
  R / (R + F x + F y)

/-- Chain rule along arbitrary supplied differentiable paths. The path values
and velocities are mathematical data, not a physical accessibility theorem. -/
theorem hasDerivAt_reference_probability (R : ℝ) (hR : 0 < R) (F : V → ℝ)
    (hF : Differentiable ℝ F) (nonnegative : ∀ x, 0 ≤ F x)
    (X Y : ℝ → V) (x y u v : V) (hX0 : X 0 = x) (hY0 : Y 0 = y)
    (hX : HasDerivAt X u 0) (hY : HasDerivAt Y v 0) :
    HasDerivAt (fun t => referenceProbability R F (X t) (Y t))
      (-R / (R + F x + F y) ^ 2 *
        ((fderiv ℝ F x) u + (fderiv ℝ F y) v)) 0 := by
  have hx : HasDerivAt (fun t => F (X t)) ((fderiv ℝ F x) u) 0 := by
    simpa only [Function.comp_def, hX0] using
      (hF x).hasFDerivAt.comp_hasDerivAt_of_eq 0 hX hX0.symm
  have hy : HasDerivAt (fun t => F (Y t)) ((fderiv ℝ F y) v) 0 := by
    simpa only [Function.comp_def, hY0] using
      (hF y).hasFDerivAt.comp_hasDerivAt_of_eq 0 hY hY0.symm
  have hden : R + F (X 0) + F (Y 0) ≠ 0 :=
    ne_of_gt (by rw [hX0, hY0]; linarith [nonnegative x, nonnegative y])
  have hd := ((hasDerivAt_const (0 : ℝ) R).add hx).add hy
  have hq := (hasDerivAt_const (0 : ℝ) R).div hd hden
  change HasDerivAt (fun t => R / (R + F (X t) + F (Y t)))
    ((0 * (R + F (X 0) + F (Y 0)) -
      R * (0 + (fderiv ℝ F x) u + (fderiv ℝ F y) v)) /
      (R + F (X 0) + F (Y 0)) ^ 2) 0 at hq
  simp only [hX0, hY0, zero_mul, zero_add, zero_sub] at hq
  convert hq using 1 <;> ring

/-- First-order stationarity of the supplied reference-event readout is
equivalent to zero derivative of the full represented pair response. -/
theorem stationary_reference_iff_balance_along_paths (R : ℝ) (hR : 0 < R)
    (F : V → ℝ) (hF : Differentiable ℝ F) (nonnegative : ∀ x, 0 ≤ F x)
    (X Y : ℝ → V) (x y u v : V) (hX0 : X 0 = x) (hY0 : Y 0 = y)
    (hX : HasDerivAt X u 0) (hY : HasDerivAt Y v 0) :
    HasDerivAt (fun t => referenceProbability R F (X t) (Y t)) 0 0 ↔
      (fderiv ℝ F x) u + (fderiv ℝ F y) v = 0 := by
  have h := hasDerivAt_reference_probability R hR F hF nonnegative
    X Y x y u v hX0 hY0 hX hY
  have hden : R + F x + F y ≠ 0 :=
    ne_of_gt (by linarith [nonnegative x, nonnegative y])
  have hcoeff : -R / (R + F x + F y) ^ 2 ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr (ne_of_gt hR)) (pow_ne_zero 2 hden)
  constructor
  · intro stationary
    exact (mul_eq_zero.mp (h.unique stationary)).resolve_left hcoeff
  · intro balance
    simpa only [balance, mul_zero] using h

/-- Canonical velocity notation, tested only at zero. No finite-time
conservation or physically realizable Euler operation is asserted. -/
def ReferenceStationarity (R : ℝ) (F : V → ℝ) (a b c d : ℝ) : Prop :=
  ∀ x y, HasDerivAt
    (fun t : ℝ => referenceProbability R F
      (x + t • (a • x + b • y)) (y + t • (c • x + d • y))) 0 0

/-- The fixed-reference readout contract is exactly the balance hypothesis
used by the existing conditional infinitesimal selection theorem. -/
theorem reference_stationarity_iff_balance (R : ℝ) (hR : 0 < R) (F : V → ℝ)
    (hF : Differentiable ℝ F) (nonnegative : ∀ x, 0 ≤ F x) (a b c d : ℝ) :
    ReferenceStationarity R F a b c d ↔
      InfinitesimalPairReadoutSelection.Balance F a b c d := by
  have affine (x u : V) : HasDerivAt (fun t : ℝ => x + t • u) u 0 := by
    simpa only [one_smul, zero_add] using
      (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const u)
  constructor
  · intro stationary x y
    exact (stationary_reference_iff_balance_along_paths R hR F hF nonnegative
      _ _ x y _ _ (by simp) (by simp) (affine _ _) (affine _ _)).mp
      (stationary x y)
  · intro balance x y
    exact (stationary_reference_iff_balance_along_paths R hR F hF nonnegative
      _ _ x y _ _ (by simp) (by simp) (affine _ _) (affine _ _)).mpr
      (balance x y)

/-- Conditional selection from an unconditional reference-event stationarity
contract. No Hessian, bilinear pair law, or dark curvature is assumed. -/
theorem reference_stationarity_selects_bilinear (R : ℝ) (hR : 0 < R)
    (F : V → ℝ) (hF : Differentiable ℝ F) (nonnegative : ∀ x, 0 ≤ F x)
    (zero : F 0 = 0) (v₀ : V) (positive : 0 < F v₀)
    (a b c d : ℝ) (exchange : b ≠ 0 ∨ c ≠ 0)
    (stationary : ReferenceStationarity R F a b c d) :
    a = 0 ∧ d = 0 ∧ c = -b ∧ b ≠ 0 ∧
      ∃ B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ,
        (∀ x y, B x y = B y x) ∧
        (∀ x, F x = B x x / 2) ∧ (∀ x, 0 ≤ B x x) := by
  exact InfinitesimalPairReadoutSelection.differentiable_balance_selects_bilinear
    F hF nonnegative zero v₀ positive a b c d exchange
    ((reference_stationarity_iff_balance R hR F hF nonnegative a b c d).mp stationary)

/-- Zero third additive difference follows from the conditional selection
theorem, rather than being an additional readout assumption. -/
theorem reference_stationarity_zero_third_difference (R : ℝ) (hR : 0 < R)
    (F : V → ℝ) (hF : Differentiable ℝ F) (nonnegative : ∀ x, 0 ≤ F x)
    (zero : F 0 = 0) (v₀ : V) (positive : 0 < F v₀)
    (a b c d : ℝ) (exchange : b ≠ 0 ∨ c ≠ 0)
    (stationary : ReferenceStationarity R F a b c d) (x y z : V) :
    F (x + y + z) - F (x + y) - F (x + z) - F (y + z) +
      F x + F y + F z - F 0 = 0 := by
  exact InfinitesimalPairReadoutSelection.differentiable_balance_zero_third_difference
    F hF nonnegative zero v₀ positive a b c d exchange
    ((reference_stationarity_iff_balance R hR F hF nonnegative a b c d).mp stationary)
    x y z

/-- Open physical/primitive obligations; constructors are data, not proofs.
The candidate calibration criterion keeps channel/reference odds unchanged under
independently specified preparation-preserving context embeddings. Normalization
makes this equivalent to the existing common-response representation, not a
weaker derivation of its origin. Preparation identity must not be defined by equal
odds or by the whole context; this is not invariance across arbitrary incompatible
measurements. -/
inductive OpenBridge where
  | deriveNativePreparationIdentityAcrossContexts
  | establishReferenceRelativeCalibrationNaturality
  | accountAllTrialOutcomes
  | establishUnconditionalCoarseEventInvariance
  | realizeFixedMergeCompatibleVelocity
  | controlFiniteCalibrationErrorsBeforeDerivativeClaims
  | derivePrimitiveRealCompletion
  | derivePhaseAndComplexStructure
  | deriveActualization
  | deriveCompositesAndBellConstraints
  | derivePhysicalScales
  deriving DecidableEq, Repr

/-- This ledger records only open bridges, without changing proof status. -/
def openBridges : List OpenBridge :=
  [ .deriveNativePreparationIdentityAcrossContexts,
    .establishReferenceRelativeCalibrationNaturality,
    .accountAllTrialOutcomes,
    .establishUnconditionalCoarseEventInvariance,
    .realizeFixedMergeCompatibleVelocity,
    .controlFiniteCalibrationErrorsBeforeDerivativeClaims,
    .derivePrimitiveRealCompletion,
    .derivePhaseAndComplexStructure,
    .deriveActualization,
    .deriveCompositesAndBellConstraints,
    .derivePhysicalScales ]

end

end IDT.QMClosure.FixedReferenceBalanceBridge
