import Proofs.QMClosure.InfinitesimalPairReadoutSelection
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Conditional selection from attenuation and vacuum tangent conservation

The supplied bridges are a fixed native scalar scaling and coherent preparation,
a real differentiable operational completion, one uniform physical attenuation
with a common response gain, vacuum-linear mixing, and complete raw-response
conservation with reference calibration. The response gain is not assumed to be
quadratic. The fields may be nonlinear away from the vacuum. Their actual ray
derivatives at the pair vacuum, for every pair of directions, are supplied.

The scalar selection specialization requires the SAME scalar coefficients in
ALL internal directions. An arbitrary nonzero operator block is insufficient.
This conditional theorem does not derive its bridges from native primitives,
actualization, phase, composites, physical scales, or full QM.
-/

namespace IDT.QMClosure.AttenuationTangentReadoutSelection

noncomputable section

open Filter Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Differentiate the supplied attenuation identity, without selecting its gain. -/
theorem attenuation_derivative (F : V → ℝ) (hF : Differentiable ℝ F)
    (r g : ℝ) (attenuation : ∀ z, F (r • z) = g * F z) (x v : V) :
    r * (fderiv ℝ F (r • x)) v = g * (fderiv ℝ F x) v := by
  have left := (hF (r • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul r)
  have right := (hF x).hasFDerivAt.const_smul g
  have identity : (fun z => F (r • z)) = (fun z => g • F z) := by
    ext z
    exact attenuation z
  change HasFDerivAt (fun z => F (r • z)) _ x at left
  rw [identity] at left
  have h := congrArg (fun L : V →L[ℝ] ℝ => L v) (left.unique right)
  simpa using h

/-- Iteration uses only the same one-step attenuation, never a fitted exponent. -/
theorem attenuation_iterate (F : V → ℝ) (r g : ℝ)
    (attenuation : ∀ z, F (r • z) = g * F z) (n : ℕ) (z : V) :
    F ((r ^ n) • z) = g ^ n * F z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, attenuation, ih, pow_succ']
    ring

/-- Exact raw conservation passes to any actual directional vacuum tangent.
No continuity of the derivative of F, global field linearity, or flow is used. -/
theorem conservation_passes_to_vacuum_tangent
    (F : V → ℝ) (hF : Differentiable ℝ F)
    (r g : ℝ) (r_pos : 0 < r) (r_lt : r < 1) (g_pos : 0 < g)
    (attenuation : ∀ z, F (r • z) = g * F z)
    (P Q : V → V → V) (P_zero : P 0 0 = 0) (Q_zero : Q 0 0 = 0)
    (L₁ L₂ : V → V → V)
    (P_tangent : ∀ x y, HasDerivAt (fun t : ℝ => P (t • x) (t • y)) (L₁ x y) 0)
    (Q_tangent : ∀ x y, HasDerivAt (fun t : ℝ => Q (t • x) (t • y)) (L₂ x y) 0)
    (conservation : ∀ x y, (fderiv ℝ F x) (P x y) + (fderiv ℝ F y) (Q x y) = 0) :
    ∀ x y, (fderiv ℝ F x) (L₁ x y) + (fderiv ℝ F y) (L₂ x y) = 0 := by
  intro x y
  have seq : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_pow_atTop_nhds_zero_of_lt_one r_pos.le r_lt,
        Eventually.of_forall (fun n => pow_pos r_pos n)⟩
  have p_limit : Tendsto (fun n : ℕ => (r ^ n)⁻¹ • P ((r ^ n) • x) ((r ^ n) • y))
      atTop (𝓝 (L₁ x y)) := by
    simpa [P_zero] using (P_tangent x y).tendsto_slope_zero_right.comp seq
  have q_limit : Tendsto (fun n : ℕ => (r ^ n)⁻¹ • Q ((r ^ n) • x) ((r ^ n) • y))
      atTop (𝓝 (L₂ x y)) := by
    simpa [Q_zero] using (Q_tangent x y).tendsto_slope_zero_right.comp seq
  have normalized (n : ℕ) :
      (fderiv ℝ F x) ((r ^ n)⁻¹ • P ((r ^ n) • x) ((r ^ n) • y)) +
        (fderiv ℝ F y) ((r ^ n)⁻¹ • Q ((r ^ n) • x) ((r ^ n) • y)) = 0 := by
    have scale := attenuation_iterate F r g attenuation n
    have hp := attenuation_derivative F hF (r ^ n) (g ^ n) scale x
      (P ((r ^ n) • x) ((r ^ n) • y))
    have hq := attenuation_derivative F hF (r ^ n) (g ^ n) scale y
      (Q ((r ^ n) • x) ((r ^ n) • y))
    have hc := conservation ((r ^ n) • x) ((r ^ n) • y)
    have sum_zero : (fderiv ℝ F x) (P ((r ^ n) • x) ((r ^ n) • y)) +
        (fderiv ℝ F y) (Q ((r ^ n) • x) ((r ^ n) • y)) = 0 := by
      have product : g ^ n * ((fderiv ℝ F x) (P ((r ^ n) • x) ((r ^ n) • y)) +
          (fderiv ℝ F y) (Q ((r ^ n) • x) ((r ^ n) • y))) = 0 := by
        rw [mul_add, ← hp, ← hq, ← mul_add, hc, mul_zero]
      exact (mul_eq_zero.mp product).resolve_left (pow_ne_zero n (ne_of_gt g_pos))
    simp only [map_smul, smul_eq_mul, ← mul_add, sum_zero, mul_zero]
  have limit := ((fderiv ℝ F x).continuous.tendsto _ |>.comp p_limit).add
    ((fderiv ℝ F y).continuous.tendsto _ |>.comp q_limit)
  exact tendsto_nhds_unique limit (by simpa only [Function.comp_apply, normalized] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))

/-- The scalar vacuum tangent yields the existing universal Balance contract. -/
theorem attenuation_tangent_balance
    (F : V → ℝ) (hF : Differentiable ℝ F)
    (r g : ℝ) (r_pos : 0 < r) (r_lt : r < 1) (g_pos : 0 < g)
    (attenuation : ∀ z, F (r • z) = g * F z)
    (P Q : V → V → V) (P_zero : P 0 0 = 0) (Q_zero : Q 0 0 = 0)
    (a b c d : ℝ)
    (P_tangent : ∀ x y, HasDerivAt (fun t : ℝ => P (t • x) (t • y)) (a • x + b • y) 0)
    (Q_tangent : ∀ x y, HasDerivAt (fun t : ℝ => Q (t • x) (t • y)) (c • x + d • y) 0)
    (conservation : ∀ x y, (fderiv ℝ F x) (P x y) + (fderiv ℝ F y) (Q x y) = 0) :
    InfinitesimalPairReadoutSelection.Balance F a b c d :=
  conservation_passes_to_vacuum_tangent F hF r g r_pos r_lt g_pos attenuation
    P Q P_zero Q_zero _ _ P_tangent Q_tangent conservation

/-- Nonzero scalar mixing selects bilinear response, its attenuation gain, and
zero third additive difference. This remains conditional on all supplied bridges. -/
theorem attenuation_tangent_selects_bilinear
    (F : V → ℝ) (hF : Differentiable ℝ F)
    (nonnegative : ∀ x, 0 ≤ F x) (zero : F 0 = 0)
    (v₀ : V) (positive : 0 < F v₀)
    (r g : ℝ) (r_pos : 0 < r) (r_lt : r < 1) (g_pos : 0 < g)
    (attenuation : ∀ z, F (r • z) = g * F z)
    (P Q : V → V → V) (P_zero : P 0 0 = 0) (Q_zero : Q 0 0 = 0)
    (a b c d : ℝ) (exchange : b ≠ 0 ∨ c ≠ 0)
    (P_tangent : ∀ x y, HasDerivAt (fun t : ℝ => P (t • x) (t • y)) (a • x + b • y) 0)
    (Q_tangent : ∀ x y, HasDerivAt (fun t : ℝ => Q (t • x) (t • y)) (c • x + d • y) 0)
    (conservation : ∀ x y, (fderiv ℝ F x) (P x y) + (fderiv ℝ F y) (Q x y) = 0) :
    a = 0 ∧ d = 0 ∧ c = -b ∧ b ≠ 0 ∧ g = r ^ 2 ∧
      ∃ B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ,
        (∀ x y, B x y = B y x) ∧
        (∀ x, F x = B x x / 2) ∧ (∀ x, 0 ≤ B x x) ∧
        (∀ x y z, F (x + y + z) - F (x + y) - F (x + z) - F (y + z) +
          F x + F y + F z - F 0 = 0) := by
  have balance := attenuation_tangent_balance F hF r g r_pos r_lt g_pos
    attenuation P Q P_zero Q_zero a b c d P_tangent Q_tangent conservation
  obtain ⟨ha, hd, hc, hb, B, symmetric, representation, positive_semidefinite⟩ :=
    InfinitesimalPairReadoutSelection.differentiable_balance_selects_bilinear
      F hF nonnegative zero v₀ positive a b c d exchange balance
  have quadratic_scaling : F (r • v₀) = r ^ 2 * F v₀ := by
    rw [representation _, representation v₀]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have gain : g = r ^ 2 :=
    mul_right_cancel₀ (ne_of_gt positive) ((attenuation v₀).symm.trans quadratic_scaling)
  exact ⟨ha, hd, hc, hb, gain, B, symmetric, representation, positive_semidefinite,
    InfinitesimalPairReadoutSelection.third_difference_of_bilinear F B symmetric representation⟩

/-- Data-only physical/native obligations; this conditional proof discharges
none of their native origin or physical interpretation. -/
inductive OpenObligation where
  | deriveFixedNativeScalarScalingAndCoherentPreparation
  | deriveUniformPhysicalAttenuationAndCommonResponseGain
  | deriveRealDifferentiableOperationalCompletion
  | deriveActualVacuumLinearizationWithUniformScalarMixing
  | deriveCompleteRawConservationAndReferenceCalibration
  | deriveActualization
  | derivePhaseAndComplexStructure
  | deriveEntangledComposites
  | derivePhysicalScales
  deriving DecidableEq, Repr

/-- All listed bridges remain supplied/open, with no claim-status upgrade. -/
def openObligations : List OpenObligation :=
  [ .deriveFixedNativeScalarScalingAndCoherentPreparation,
    .deriveUniformPhysicalAttenuationAndCommonResponseGain,
    .deriveRealDifferentiableOperationalCompletion,
    .deriveActualVacuumLinearizationWithUniformScalarMixing,
    .deriveCompleteRawConservationAndReferenceCalibration,
    .deriveActualization,
    .derivePhaseAndComplexStructure,
    .deriveEntangledComposites,
    .derivePhysicalScales ]

end

end IDT.QMClosure.AttenuationTangentReadoutSelection
