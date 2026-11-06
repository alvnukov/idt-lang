import Proofs.QMClosure.FiniteMixerReadoutSelection

/-!
# Conditional selection of the native Gaussian norm

The cancellation residual carrier and Gaussian serial algebra, unit calibration,
and response multiplicativity are supplied. An additive real embedding and a
symmetric bilinear representation select its squared norm without assuming
phase invariance, a diagonal ansatz, or a native quadratic response formula.

The integrated theorem retains all compatible completion and finite conserving
mixer premises. Their native origin and physical accessibility remain open.
This is a conditional raw-response theorem, not Born actualization, a physical
complex Hilbert space, tensor closure, or a derivation of physical scales.
-/

namespace IDT.QMClosure.NativeGaussianReadoutSelection

noncomputable section
open LocalHistoryReadoutOrderWall Filter Topology

section Algebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Additivity identifies both integer coordinates; no phase law is supplied. -/
theorem additive_coordinates (E : Residual →+ V) (a b : ℤ) :
    E (a, b) = (a : ℝ) • E (1, 0) + (b : ℝ) • E (0, 1) := by
  have coordinates : (a, b) = a • ((1, 0) : Residual) + b • ((0, 1) : Residual) := by
    ext <;> simp
  rw [coordinates, map_add, map_zsmul, map_zsmul,
    Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]

/-- A multiplicative native response represented by any symmetric real
bilinear form is the Gaussian squared norm. Neither positivity nor topology
is assumed; positivity follows from the conclusion. -/
theorem bilinear_native_response_is_norm
    (W : DyadicResponseExtension.Response) (E : Residual →+ V)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (symmetric : ∀ x y, B x y = B y x)
    (representation : ∀ z, W.weight z = B (E z) (E z) / 2) :
    ∀ z : Residual, W.weight z = (quadratic z : ℝ) := by
  have coordinate (a b : ℤ) : W.weight (a, b) =
      (a : ℝ) ^ 2 * (B (E (1, 0)) (E (1, 0)) / 2) +
      (a : ℝ) * (b : ℝ) * B (E (1, 0)) (E (0, 1)) +
      (b : ℝ) ^ 2 * (B (E (0, 1)) (E (0, 1)) / 2) := by
    rw [representation, additive_coordinates]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, symmetric (E (0, 1)) (E (1, 0))]
    ring
  have unit : W.weight (1, 0) = 1 := W.unital
  have negative_unit : W.weight (-1, 0) = 1 := by
    have h := coordinate (-1) 0
    have h₁ := coordinate 1 0
    norm_num at h h₁
    linarith
  have imag_square : W.weight (0, 1) * W.weight (0, 1) = 1 := by
    have h := W.multiplicative (0, 1) (0, 1)
    norm_num [serial] at h
    linarith
  have twice_imag : W.weight (0, 2) = 4 * W.weight (0, 1) := by
    have h := coordinate 0 2
    have h₁ := coordinate 0 1
    norm_num at h h₁
    linarith
  have imag_nonnegative : 0 ≤ W.weight (0, 1) := by
    have h := W.multiplicative (1, 1) (1, 1)
    norm_num [serial] at h
    nlinarith [sq_nonneg (W.weight (1, 1))]
  have imag : W.weight (0, 1) = 1 := by nlinarith
  have first := coordinate 1 0
  have second := coordinate 0 1
  norm_num at first second
  have first_value : B (E (1, 0)) (E (1, 0)) / 2 = 1 := by linarith
  have second_value : B (E (0, 1)) (E (0, 1)) / 2 = 1 := by linarith
  have twice_unit : W.weight (2, 0) = 4 := by
    have h := coordinate 2 0
    norm_num at h
    linarith
  have cross_value : B (E (1, 0)) (E (0, 1)) = 0 := by
    have plus := coordinate 1 1
    have minus := coordinate 1 (-1)
    rw [first_value, second_value] at plus minus
    norm_num at plus minus
    have h := W.multiplicative (1, 1) (1, -1)
    norm_num [serial] at h
    rw [plus, minus, twice_unit] at h
    nlinarith [sq_nonneg (B (E (1, 0)) (E (0, 1)))]
  rintro ⟨a, b⟩
  rw [coordinate, first_value, second_value, cross_value]
  norm_num [quadratic]

end Algebra

section Completion

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The supplied native completion and genuinely mixing finite conserving map
select the native norm. Additivity of the native embedding remains explicit. -/
theorem native_dyadic_finite_mixer_selects_gaussian_norm
    (W : DyadicResponseExtension.Response)
    (doubling_ne : DyadicResponseExtension.doublingValue W ≠ 0)
    (embed : DyadicResponseExtension.Dyadic → V) (dense : DenseRange embed)
    (intertwines : ∀ z, embed (DyadicResponseExtension.half z) = (1 / 2 : ℝ) • embed z)
    (additive_embed : ∀ z w : Residual,
      embed (DyadicResponseExtension.base (z + w)) =
        embed (DyadicResponseExtension.base z) + embed (DyadicResponseExtension.base w))
    (F : V → ℝ) (hF : Differentiable ℝ F)
    (nonnegative : ∀ x, 0 ≤ F x) (zero : F 0 = 0)
    (compatible : ∀ z, F (embed z) = DyadicResponseExtension.extension W doubling_ne z)
    (P Q : V → V → V) (P_zero : P 0 0 = 0) (Q_zero : Q 0 0 = 0)
    (a b c d : ℝ) (mixing : a * b ≠ 0 ∨ c * d ≠ 0)
    (P_tangent : ∀ x y, HasDerivAt (fun t : ℝ => P (t • x) (t • y)) (a • x + b • y) 0)
    (Q_tangent : ∀ x y, HasDerivAt (fun t : ℝ => Q (t • x) (t • y)) (c • x + d • y) 0)
    (conservation : ∀ x y, ∀ᶠ n : ℕ in atTop,
      F (P (((1 / 2 : ℝ) ^ n) • x) (((1 / 2 : ℝ) ^ n) • y)) +
        F (Q (((1 / 2 : ℝ) ^ n) • x) (((1 / 2 : ℝ) ^ n) • y)) =
          F (((1 / 2 : ℝ) ^ n) • x) + F (((1 / 2 : ℝ) ^ n) • y)) :
    ∀ z : Residual, W.weight z = (quadratic z : ℝ) := by
  obtain ⟨_, _, B, symmetric, representation, _⟩ :=
    FiniteMixerReadoutSelection.native_dyadic_finite_mixer_selects_bilinear
      W doubling_ne embed dense intertwines additive_embed F hF nonnegative zero compatible
      P Q P_zero Q_zero a b c d mixing P_tangent Q_tangent conservation
  let E : Residual →+ V :=
    { toFun := fun z => embed (DyadicResponseExtension.base z)
      map_zero' := by
        have h : embed (DyadicResponseExtension.base 0) + 0 =
            embed (DyadicResponseExtension.base 0) + embed (DyadicResponseExtension.base 0) := by
          simpa only [add_zero, zero_add] using additive_embed 0 0
        exact (add_left_cancel h).symm
      map_add' := additive_embed }
  have native_value (z : Residual) : W.weight z = F (E z) :=
    ((compatible _).trans (DyadicResponseExtension.extension_base W doubling_ne z)).symm
  exact bilinear_native_response_is_norm W E B symmetric
    (fun z => (native_value z).trans (representation (E z)))

end Completion

/-- Data-only boundaries; these are research obligations, not derived laws. -/
inductive OpenObligation where
  | deriveCancellationQuotientAndGaussianSerialAlgebra
  | deriveNativeResponseMultiplicativityAndUnitCalibration
  | deriveCompatibleAdditiveRealDifferentiableCompletion
  | deriveAccessibleFiniteConservingMixerWithGenuineMixedVacuumTangent
  | deriveBornActualization
  | derivePhysicalComplexHilbertAndTensorClosure
  | derivePhysicalScales
  deriving DecidableEq, Repr

def openObligations : List OpenObligation :=
  [.deriveCancellationQuotientAndGaussianSerialAlgebra,
   .deriveNativeResponseMultiplicativityAndUnitCalibration,
   .deriveCompatibleAdditiveRealDifferentiableCompletion,
   .deriveAccessibleFiniteConservingMixerWithGenuineMixedVacuumTangent,
   .deriveBornActualization, .derivePhysicalComplexHilbertAndTensorClosure,
   .derivePhysicalScales]

end

end IDT.QMClosure.NativeGaussianReadoutSelection
