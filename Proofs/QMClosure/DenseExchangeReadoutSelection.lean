import Proofs.QMClosure.AttenuationTangentReadoutSelection
import Mathlib.Topology.DenseEmbedding

/-!
# Conditional quadratic selection from dense operator exchange

The real normed operational completion, independently fixed native scalar and
coherent operations, differentiable nonnegative response, and complete raw
response conservation are supplied. The integrated theorem additionally supplies
one common attenuation, reference calibration, and physically accessible actual
vacuum tangents. Dense directional coverage means norm approximation by sums of
the two exchange ranges. It supplies no uniform bound on the inputs needed for
an approximation, no exact controllability, and no physical accessibility proof.

No scalar/isotropic exchange, finite dimension, completeness, continuous
derivative, Hessian, bounded inverse, or live response is needed for selection.
The resulting form may vanish. Native origin, actualization, complex structure,
composites, physical scales, and full QM remain open.
-/

namespace IDT.QMClosure.DenseExchangeReadoutSelection

noncomputable section

open Filter Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Operator balance uses the actual derivative and all operational pairs. -/
def Balance (F : V → ℝ) (A B C D : V →L[ℝ] V) : Prop :=
  ∀ x y, (fderiv ℝ F x) (A x + B y) + (fderiv ℝ F y) (C x + D y) = 0

/-- Nonnegativity at a zero vacuum forces its actual directional derivative
to vanish; no nonzero response witness is required. -/
theorem derivative_zero_at_vacuum (F : V → ℝ) (hF : Differentiable ℝ F)
    (nonnegative : ∀ x, 0 ≤ F x) (zero : F 0 = 0) (v : V) :
    (fderiv ℝ F 0) v = 0 := by
  have hmin : IsLocalMin (fun t : ℝ => F (t • v)) 0 := by
    apply Eventually.of_forall
    intro t
    simpa only [zero_smul, zero] using nonnegative (t • v)
  have hd := InfinitesimalPairReadoutSelection.hasDerivAt_ray F hF v 0
  simpa only [zero_smul] using hd.deriv.symm.trans hmin.deriv_eq_zero

/-- Continuity in the direction extends annihilation of both exchange ranges
to every direction. There is no bound on preimages in this argument. -/
theorem annihilator_of_dense_exchange (B C : V →L[ℝ] V)
    (coverage : DenseRange (fun p : V × V => B p.1 + C p.2))
    (L : V →L[ℝ] ℝ) (hB : ∀ y, L (B y) = 0) (hC : ∀ y, L (C y) = 0) :
    ∀ v, L v = 0 := by
  intro v
  exact coverage.induction_on v (isClosed_eq L.continuous continuous_const)
    (fun p => by rw [map_add, hB, hC, add_zero])

/-- Dense exchange makes the derivative algebraically linear in its base point.
The derivative is only assumed continuous in its direction argument. -/
theorem derivative_linear_in_base (F : V → ℝ) (hF : Differentiable ℝ F)
    (nonnegative : ∀ x, 0 ≤ F x) (zero : F 0 = 0)
    (A B C D : V →L[ℝ] V) (balance : Balance F A B C D)
    (coverage : DenseRange (fun p : V × V => B p.1 + C p.2)) :
    (∀ x z v, (fderiv ℝ F (x + z)) v = (fderiv ℝ F x) v + (fderiv ℝ F z) v) ∧
    (∀ (r : ℝ) x v, (fderiv ℝ F (r • x)) v = r * (fderiv ℝ F x) v) := by
  have vacuum := derivative_zero_at_vacuum F hF nonnegative zero
  have diagonalA (x : V) : (fderiv ℝ F x) (A x) = 0 := by
    simpa only [map_zero, add_zero, zero_add, vacuum] using balance x 0
  have diagonalD (y : V) : (fderiv ℝ F y) (D y) = 0 := by
    simpa only [map_zero, add_zero, zero_add, vacuum] using balance 0 y
  have crossB (x y : V) : (fderiv ℝ F x) (B y) = -(fderiv ℝ F y) (C x) := by
    have h := balance x y
    rw [map_add, map_add, diagonalA, diagonalD] at h
    linarith
  have crossC (x y : V) : (fderiv ℝ F x) (C y) = -(fderiv ℝ F y) (B x) := by
    have h := crossB y x
    linarith
  constructor
  · intro x z v
    let L : V →L[ℝ] ℝ := fderiv ℝ F (x + z) - fderiv ℝ F x - fderiv ℝ F z
    have hB (y : V) : L (B y) = 0 := by
      simp only [L, ContinuousLinearMap.sub_apply, crossB, map_add]
      ring
    have hC (y : V) : L (C y) = 0 := by
      simp only [L, ContinuousLinearMap.sub_apply, crossC, map_add]
      ring
    have h := annihilator_of_dense_exchange B C coverage L hB hC v
    dsimp [L] at h
    linarith
  · intro r x v
    let L : V →L[ℝ] ℝ := fderiv ℝ F (r • x) - r • fderiv ℝ F x
    have hB (y : V) : L (B y) = 0 := by
      simp only [L, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        crossB, map_smul, smul_eq_mul]
      ring
    have hC (y : V) : L (C y) = 0 := by
      simp only [L, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        crossC, map_smul, smul_eq_mul]
      ring
    have h := annihilator_of_dense_exchange B C coverage L hB hC v
    change (fderiv ℝ F (r • x)) v - r * (fderiv ℝ F x) v = 0 at h
    linarith

/-- Dense operator exchange selects a symmetric positive semidefinite algebraic
bilinear response, including the zero response, and zero third difference. -/
theorem differentiable_balance_selects_bilinear (F : V → ℝ)
    (hF : Differentiable ℝ F) (nonnegative : ∀ x, 0 ≤ F x) (zero : F 0 = 0)
    (A B C D : V →L[ℝ] V) (balance : Balance F A B C D)
    (coverage : DenseRange (fun p : V × V => B p.1 + C p.2)) :
    ∃ K : V →ₗ[ℝ] V →ₗ[ℝ] ℝ,
      (∀ x y, K x y = K y x) ∧ (∀ x, F x = K x x / 2) ∧
      (∀ x, 0 ≤ K x x) ∧
      (∀ x y z, F (x + y + z) - F (x + y) - F (x + z) - F (y + z) +
        F x + F y + F z - F 0 = 0) := by
  obtain ⟨hadd, hsmul⟩ := derivative_linear_in_base F hF nonnegative zero
    A B C D balance coverage
  let G : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    { toFun := fun x => (fderiv ℝ F x).toLinearMap
      map_add' := by intro x z; ext v; exact hadd x z v
      map_smul' := by intro r x; ext v; exact hsmul r x v }
  have representation (x : V) : F x = G x x / 2 := by
    have hd (t : ℝ) := InfinitesimalPairReadoutSelection.hasDerivAt_ray F hF x t
    have hlinear (t : ℝ) :
        deriv (fun s : ℝ => F (s • x)) t = (fderiv ℝ F x) x * t := by
      rw [hd t |>.deriv, hsmul]
      ring
    have h := InfinitesimalReadoutSelection.quadratic_of_linear_derivative
      (fun t : ℝ => F (t • x)) (fun t => (hd t).differentiableAt)
      (by simpa using zero) ((fderiv ℝ F x) x) hlinear 1
    simpa [G] using h
  let K : V →ₗ[ℝ] V →ₗ[ℝ] ℝ := (1 / 2 : ℝ) • (G + G.flip)
  have symmetric (x y : V) : K x y = K y x := by
    change (1 / 2 : ℝ) * (G x y + G y x) = (1 / 2 : ℝ) * (G y x + G x y)
    ring
  have krepr (x : V) : F x = K x x / 2 := by
    rw [representation]
    change G x x / 2 = ((1 / 2 : ℝ) * (G x x + G x x)) / 2
    ring
  refine ⟨K, symmetric, krepr, ?_, ?_⟩
  · intro x
    have h := nonnegative x
    rw [krepr] at h
    linarith
  · exact InfinitesimalPairReadoutSelection.third_difference_of_bilinear
      F K symmetric krepr

/-- Actual vacuum tangents with dense exchange inherit the selection theorem
from complete nonlinear raw conservation and one common attenuation. -/
theorem attenuation_tangent_selects_bilinear
    (F : V → ℝ) (hF : Differentiable ℝ F)
    (nonnegative : ∀ x, 0 ≤ F x) (zero : F 0 = 0)
    (r g : ℝ) (r_pos : 0 < r) (r_lt : r < 1) (g_pos : 0 < g)
    (attenuation : ∀ z, F (r • z) = g * F z)
    (P R : V → V → V) (P_zero : P 0 0 = 0) (R_zero : R 0 0 = 0)
    (A B C D : V →L[ℝ] V)
    (P_tangent : ∀ x y, HasDerivAt (fun t : ℝ => P (t • x) (t • y)) (A x + B y) 0)
    (R_tangent : ∀ x y, HasDerivAt (fun t : ℝ => R (t • x) (t • y)) (C x + D y) 0)
    (conservation : ∀ x y, (fderiv ℝ F x) (P x y) + (fderiv ℝ F y) (R x y) = 0)
    (coverage : DenseRange (fun p : V × V => B p.1 + C p.2)) :
    ∃ K : V →ₗ[ℝ] V →ₗ[ℝ] ℝ,
      (∀ x y, K x y = K y x) ∧ (∀ x, F x = K x x / 2) ∧
      (∀ x, 0 ≤ K x x) ∧
      (∀ x y z, F (x + y + z) - F (x + y) - F (x + z) - F (y + z) +
        F x + F y + F z - F 0 = 0) := by
  apply differentiable_balance_selects_bilinear F hF nonnegative zero A B C D
    _ coverage
  exact AttenuationTangentReadoutSelection.conservation_passes_to_vacuum_tangent
    F hF r g r_pos r_lt g_pos attenuation P R P_zero R_zero _ _
    P_tangent R_tangent conservation

/-- A live response pins the common gain after selection, with no fitted exponent. -/
theorem attenuation_gain_of_bilinear (F : V → ℝ)
    (K : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (representation : ∀ x, F x = K x x / 2)
    (v₀ : V) (positive : 0 < F v₀) (r g : ℝ)
    (attenuation : ∀ z, F (r • z) = g * F z) : g = r ^ 2 := by
  have scaling : F (r • v₀) = r ^ 2 * F v₀ := by
    rw [representation _, representation v₀]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  exact mul_right_cancel₀ (ne_of_gt positive) ((attenuation v₀).symm.trans scaling)

/-- Data-only obligations: supplied bridges are not derived by this theorem. -/
inductive OpenObligation where
  | deriveNativeRealDifferentiableCompletion
  | deriveIndependentlyFixedScalarAndCoherentOperations
  | deriveCommonPhysicalAttenuation
  | deriveCompleteRawConservationAndReferenceCalibration
  | derivePhysicallyAccessibleActualVacuumTangent
  | deriveDenseDirectionalCoverage
  | deriveActualization
  | derivePhaseAndComplexStructure
  | deriveEntangledComposites
  | derivePhysicalScales
  deriving DecidableEq, Repr

/-- No closure or physical-access claim follows from this data-only list. -/
def openObligations : List OpenObligation :=
  [ .deriveNativeRealDifferentiableCompletion,
    .deriveIndependentlyFixedScalarAndCoherentOperations,
    .deriveCommonPhysicalAttenuation,
    .deriveCompleteRawConservationAndReferenceCalibration,
    .derivePhysicallyAccessibleActualVacuumTangent,
    .deriveDenseDirectionalCoverage,
    .deriveActualization,
    .derivePhaseAndComplexStructure,
    .deriveEntangledComposites,
    .derivePhysicalScales ]

end

end IDT.QMClosure.DenseExchangeReadoutSelection
