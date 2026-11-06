import Proofs.QMClosure.InfinitesimalReadoutSelection
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

namespace IDT.QMClosure.InfinitesimalPairReadoutSelection

noncomputable section

/-!
# Conditional vector response selection from infinitesimal conservation

A real normed operational domain, differentiable response, fixed coherent
addition, identical response in two distinguishable channels, additive total
response, accessible nonzero linear exchange, and conservation of this raw
response uniformly over all states are supplied bridges. The theorem derives
the symmetric positive semidefinite bilinear response; it assumes no pair
kernel, Hessian, inner product, finite dimension, or nonzero dark curvature.

This is a conditional mathematical selection theorem. It derives neither the
physical origin of its bridges nor an IDT-native carrier, Hilbert structure,
Born rule, actualization, tensor composition, full QM, or GR.
-/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A fixed scalar generator conserves the additive raw response on every
pair of operational states. The derivative is the actual Fréchet derivative. -/
def Balance (F : V → ℝ) (a b c d : ℝ) : Prop :=
  ∀ x y, (fderiv ℝ F x) (a • x + b • y) +
    (fderiv ℝ F y) (c • x + d • y) = 0

/-- Chain rule on a supplied real operational ray. -/
theorem hasDerivAt_ray (F : V → ℝ) (hF : Differentiable ℝ F) (v : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (s • v)) ((fderiv ℝ F (t • v)) v) t := by
  simpa only [Function.comp_def, one_smul] using
    (hF (t • v)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const v)

/-- A nonzero exchange first selects the generator and then forces a symmetric
bilinear, positive semidefinite raw response on an arbitrary real normed space. -/
theorem differentiable_balance_selects_bilinear (F : V → ℝ)
    (hF : Differentiable ℝ F) (nonnegative : ∀ x, 0 ≤ F x)
    (zero : F 0 = 0) (v₀ : V) (positive : 0 < F v₀)
    (a b c d : ℝ) (exchange : b ≠ 0 ∨ c ≠ 0)
    (balance : Balance F a b c d) :
    a = 0 ∧ d = 0 ∧ c = -b ∧ b ≠ 0 ∧
      ∃ B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ,
        (∀ x y, B x y = B y x) ∧
        (∀ x, F x = B x x / 2) ∧ (∀ x, 0 ≤ B x x) := by
  have ray_deriv (v : V) (t : ℝ) :
      deriv (fun s : ℝ => F (s • v)) t = (fderiv ℝ F (t • v)) v :=
    (hasDerivAt_ray F hF v t).deriv
  have ray_diff (v : V) : Differentiable ℝ (fun s : ℝ => F (s • v)) :=
    fun t => (hasDerivAt_ray F hF v t).differentiableAt
  have ray_balance :
      InfinitesimalReadoutSelection.Balance (fun t : ℝ => F (t • v₀)) a b c d := by
    intro t s
    rw [ray_deriv, ray_deriv]
    have h := balance (t • v₀) (s • v₀)
    simp only [map_add, map_smul, smul_eq_mul] at h
    nlinarith [h]
  obtain ⟨ha, hd, hc, hb, _⟩ :=
    InfinitesimalReadoutSelection.differentiable_balance_selects_quadratic
      (fun t : ℝ => F (t • v₀)) (ray_diff v₀) (fun t => nonnegative _)
      (by simpa using zero) (by simpa using positive) a b c d exchange ray_balance
  have symm (x y : V) : (fderiv ℝ F x) y = (fderiv ℝ F y) x := by
    have h := balance x y
    rw [ha, hd, hc] at h
    simp only [zero_smul, zero_add, add_zero, map_smul, smul_eq_mul] at h
    have hp : b * ((fderiv ℝ F x) y - (fderiv ℝ F y) x) = 0 := by
      nlinarith [h]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hb)
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    { toFun := fun x => (fderiv ℝ F x).toLinearMap
      map_add' := by
        intro x z
        ext y
        change (fderiv ℝ F (x + z)) y = (fderiv ℝ F x) y + (fderiv ℝ F z) y
        rw [symm (x + z) y, map_add, symm y x, symm y z]
      map_smul' := by
        intro r x
        ext y
        change (fderiv ℝ F (r • x)) y = r * (fderiv ℝ F x) y
        rw [symm (r • x) y, map_smul, symm y x]
        rfl }
  have hquadratic (x : V) : F x = B x x / 2 := by
    have hlinear (t : ℝ) :
        deriv (fun s : ℝ => F (s • x)) t = (fderiv ℝ F x) x * t := by
      rw [ray_deriv, symm (t • x) x, map_smul]
      simp only [smul_eq_mul, mul_comm]
    have h := InfinitesimalReadoutSelection.quadratic_of_linear_derivative
      (fun t : ℝ => F (t • x)) (ray_diff x) (by simpa using zero)
      ((fderiv ℝ F x) x) hlinear 1
    simpa [B] using h
  refine ⟨ha, hd, hc, hb, B, ?_, hquadratic, ?_⟩
  · intro x y
    exact symm x y
  · intro x
    have h := nonnegative x
    rw [hquadratic x] at h
    linarith

/-- The pair expansion follows from a derived bilinear representation; it is
not an assumption of the selection theorem. -/
theorem pair_expansion_of_bilinear (F : V → ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (symmetric : ∀ x y, B x y = B y x)
    (representation : ∀ x, F x = B x x / 2) (x y : V) :
    F (x + y) = F x + F y + B x y := by
  simp only [representation, map_add, LinearMap.add_apply]
  rw [symmetric y x]
  ring

/-- The third additive difference vanishes for supplied coherent addition.
This is a universal mathematical identity, not an experimental assertion. -/
theorem third_difference_of_bilinear (F : V → ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (symmetric : ∀ x y, B x y = B y x)
    (representation : ∀ x, F x = B x x / 2) (x y z : V) :
    F (x + y + z) - F (x + y) - F (x + z) - F (y + z) +
      F x + F y + F z - F 0 = 0 := by
  have hzero : F 0 = 0 := by simpa using representation 0
  rw [pair_expansion_of_bilinear F B symmetric representation (x + y) z,
    pair_expansion_of_bilinear F B symmetric representation x z,
    pair_expansion_of_bilinear F B symmetric representation y z, hzero]
  simp only [map_add, LinearMap.add_apply]
  ring

/-- The conditional selection assumptions imply zero third additive difference
through the derived bilinear representation, without assuming a pair law. -/
theorem differentiable_balance_zero_third_difference (F : V → ℝ)
    (hF : Differentiable ℝ F) (nonnegative : ∀ x, 0 ≤ F x)
    (zero : F 0 = 0) (v₀ : V) (positive : 0 < F v₀)
    (a b c d : ℝ) (exchange : b ≠ 0 ∨ c ≠ 0)
    (balance : Balance F a b c d) (x y z : V) :
    F (x + y + z) - F (x + y) - F (x + z) - F (y + z) +
      F x + F y + F z - F 0 = 0 := by
  obtain ⟨_, _, _, _, B, symmetric, representation, _⟩ :=
    differentiable_balance_selects_bilinear F hF nonnegative zero v₀ positive
      a b c d exchange balance
  exact third_difference_of_bilinear F B symmetric representation x y z

/-- Data-only names of open bridges toward a physical reconstruction. None is
asserted to follow from IDT primitives by the conditional mathematics above. -/
inductive OpenObligation where
  | deriveRealDifferentiableOperationalCompletion
  | deriveMergeCompatibleContinuousExchange
  | deriveDistinguishableChannelAdditivityAndCommonResponse
  | deriveRawResponseConservationWithoutSelectingReadout
  | derivePhaseAndComplexStructure
  | deriveActualization
  | deriveEntangledCompositeNoSignalling
  | derivePhysicalScales
  deriving DecidableEq, Repr

/-- All listed obligations remain open; this list records scope, not proofs,
status upgrades, physical derivations, or evidence of completed primitives. -/
def openObligations : List OpenObligation :=
  [ .deriveRealDifferentiableOperationalCompletion,
    .deriveMergeCompatibleContinuousExchange,
    .deriveDistinguishableChannelAdditivityAndCommonResponse,
    .deriveRawResponseConservationWithoutSelectingReadout,
    .derivePhaseAndComplexStructure,
    .deriveActualization,
    .deriveEntangledCompositeNoSignalling,
    .derivePhysicalScales ]

end

end IDT.QMClosure.InfinitesimalPairReadoutSelection
