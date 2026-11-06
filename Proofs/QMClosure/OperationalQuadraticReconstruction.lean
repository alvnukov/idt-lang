import Proofs.QMClosure.TransparentSwapRoot
import Proofs.QMClosure.PositiveMixerQuadraticReadout
import Proofs.QMClosure.OperationalPhaseMixerWitness

namespace IDT.QMClosure.OperationalQuadraticReconstruction

noncomputable section

/-!
# Quadratic readout from a transparent additive root of exchange

The public universal theorem starts with an additive commutative monoid, one
complete additive two-port operation, diagonal transparency, exact square-swap,
and a nonnegative real vacuum-zero readout conserved on **all** carrier inputs.
Neither an additive group, a phase, a half, scalars nor serial multiplication
is supplied. The operation determines the phase and half by explicit formulas.
Its derived antipodes supply the additive group used internally to apply the
positive-readout theorem; the original addition and zero are preserved.

This is a conditional structural theorem, not a derivation or physical
justification of its supplied operational laws. In particular coherent addition
is not identified here with probabilistic mixing. The separate complex witness
proves consistency and nonzero readout only; it supplies no premise to the
universal reconstruction. No scientific status or full-QM claim is upgraded.
-/

section Monoid
variable {V : Type*} [AddCommMonoid V]

/-- Explicit phase determined by the given complete operation. -/
def phase (T : (V × V) →+ (V × V)) : V →+ V :=
  TransparentSwapRoot.phase (TransparentSwapRoot.portA T)

/-- Explicit genuine half determined by the given complete operation. -/
def half (T : (V × V) →+ (V × V)) : V →+ V :=
  TransparentSwapRoot.half (TransparentSwapRoot.portA T) (TransparentSwapRoot.portB T)

/-- No additive cancellation or inverse is an input to this construction.
The group extends exactly the supplied additive monoid, with inverse `G²`. -/
abbrev groupFromAntipodes (G : V →+ V) (cancel : ∀ x, x + G (G x) = 0) :
    AddCommGroup V :=
  letI : Neg V := ⟨fun x => G (G x)⟩
  { (inferInstance : AddCommMonoid V) with
    neg := fun x => G (G x)
    zsmul := zsmulRec
    neg_add_cancel := fun x => by
      change G (G x) + x = 0
      simpa only [add_comm] using cancel x }

/-- Every conclusion is stated using the original monoid operations. -/
structure Reconstruction (T : (V × V) →+ (V × V)) (W : V → ℝ) : Prop where
  halves : ∀ x, half T x + half T x = x
  fourth : ∀ x, phase T (phase T (phase T (phase T x))) = x
  antipodes : ∀ x, x + phase T (phase T x) = 0
  routing : (T : (V × V) → (V × V)) =
    PhaseMixerCancellation.mixer (phase T) (half T)
  even : ∀ x, W (phase T (phase T x)) = W x
  phase_invariant : ∀ x, W (phase T x) = W x
  half_scaling : ∀ x, W (half T x) = W x / 4
  parallelogram : ∀ x y,
    W (x + y) + W (x + phase T (phase T y)) = 2 * W x + 2 * W y
  mixed_square : ∀ x, W (x + phase T x) = 2 * W x
  third_order_zero : ∀ x y z,
    W (x + y + z) - W (x + y) - W (x + z) - W (y + z) +
      W x + W y + W z = 0

end Monoid

section Group
variable {V : Type*} [AddCommGroup V]

/-- The algebraic Sorkin identity follows universally from evenness and the
parallelogram identity, with no extra three-input conservation assumption. -/
theorem third_order_zero_of_parallelogram (W : V → ℝ)
    (even : ∀ x, W (-x) = W x)
    (parallelogram : ∀ x y, W (x + y) + W (x - y) = 2 * W x + 2 * W y)
    (x y z : V) :
    W (x + y + z) - W (x + y) - W (x + z) - W (y + z) +
      W x + W y + W z = 0 := by
  have h₁ := parallelogram (x + z) y
  have h₂ := parallelogram (y + z) x
  have h₃ := parallelogram (x - y) z
  have h₄ := parallelogram x y
  have e₁ : x + z + y = x + y + z := by abel
  have e₂ : y + z + x = x + y + z := by abel
  have e₃ : x + z - y = x - y + z := by abel
  have e₄ : x - y - z = -(y + z - x) := by abel
  rw [e₁, e₃] at h₁
  rw [e₂] at h₂
  rw [e₄, even] at h₃
  linarith

end Group

section Reconstruction
variable {V : Type*} [AddCommMonoid V]

/-- End-to-end reconstruction: group, phase, genuine half, quadratic readout,
and vanishing third-order interference are conclusions of the listed contract.
Full-domain conservation includes all iterated derived-half refinements. -/
theorem reconstruct_positive_operation
    (T : (V × V) →+ (V × V))
    (transparent : ∀ x, T (x, x) = (x, x))
    (square : ∀ p, T (T p) = p.swap)
    (W : V → ℝ) (vacuum : W 0 = 0) (positive : ∀ x, 0 ≤ W x)
    (conserve : ∀ x y, W (T (x, y)).1 + W (T (x, y)).2 = W x + W y) :
    Reconstruction T W := by
  obtain ⟨r, route⟩ := TransparentSwapRoot.reconstruct_operation T transparent square
  have cancel : ∀ x, x + phase T (phase T x) = 0 := r.cancellation
  letI : AddCommGroup V := groupFromAntipodes (phase T) cancel
  have quarter : ∀ x, phase T (phase T x) = -x := fun _ => rfl
  have route' : ∀ x y, T (x, y) =
      PositiveMixerQuadraticReadout.mixer (phase T) (half T) x y := by
    intro x y
    rw [congrFun route]
    change (half T (x + phase T x) + half T (y + phase T (phase T (phase T y))),
      half T (x + phase T (phase T (phase T x))) + half T (y + phase T y)) =
      (half T (x + phase T x) + half T (y - phase T y),
      half T (x - phase T x) + half T (y + phase T y))
    rw [quarter (phase T x), quarter (phase T y)]
    rfl
  have conserved : PositiveMixerQuadraticReadout.Conserved (phase T) (half T) W := by
    intro x y
    simpa only [route' x y] using conserve x y
  have q := PositiveMixerQuadraticReadout.positive_conserved_readout_is_quadratic
    (phase T) (half T) r.halves quarter W vacuum conserved positive
  exact {
    halves := r.halves
    fourth := r.fourth
    antipodes := cancel
    routing := route
    even := q.even
    phase_invariant := q.phase_invariant
    half_scaling := q.half_scaling
    parallelogram := q.parallelogram
    mixed_square := q.mixed_square
    third_order_zero := third_order_zero_of_parallelogram W q.even q.parallelogram }

end Reconstruction

namespace ConsistencyWitness

open OperationalPhaseMixerReconstruction OperationalPhaseMixerWitness

/-- Complex arithmetic occurs only in this explicit consistency witness. -/
def operation : (ℂ × ℂ) →+ (ℂ × ℂ) where
  toFun := selectedMixer Complex.I OperationalPhaseMixerWitness.half
  map_zero' := by
    simp [selectedMixer, PhaseMixerCancellation.mixer,
      PhaseMixerCancellation.coefficientA, PhaseMixerCancellation.coefficientB,
      OperationalPhaseMixerWitness.half]
  map_add' p q := by
    apply Prod.ext <;>
      simp [selectedMixer, PhaseMixerCancellation.mixer,
        PhaseMixerCancellation.coefficientA, PhaseMixerCancellation.coefficientB,
        OperationalPhaseMixerReconstruction.phase, OperationalPhaseMixerWitness.half] <;>
      ring

theorem transparent (x : ℂ) : operation (x, x) = (x, x) := by
  have h := TransparentSwapRoot.selected_transparent
    (OperationalPhaseMixerReconstruction.phase Complex.I)
    OperationalPhaseMixerWitness.halfHom OperationalPhaseMixerWitness.halves
    OperationalPhaseMixerWitness.cancellation x
  apply Prod.ext
  · exact h
  · change PhaseMixerCancellation.coefficientB
      (OperationalPhaseMixerReconstruction.phase Complex.I)
      OperationalPhaseMixerWitness.half x +
      PhaseMixerCancellation.coefficientA
      (OperationalPhaseMixerReconstruction.phase Complex.I)
      OperationalPhaseMixerWitness.half x = x
    simpa only [add_comm] using h

theorem square (p : ℂ × ℂ) : operation (operation p) = p.swap :=
  PhaseMixerCancellation.mixer_squared_swap
    (OperationalPhaseMixerReconstruction.phase Complex.I)
    OperationalPhaseMixerWitness.halfHom OperationalPhaseMixerWitness.halves
    OperationalPhaseMixerWitness.phase_fourth OperationalPhaseMixerWitness.cancellation p

/-- Simultaneous nonvacuity of every supplied law, with a normalized nonzero
reference. This witness is not an assumption of the universal theorem. -/
theorem entire_contract_nonvacuous :
    (∀ x, operation (x, x) = (x, x)) ∧
    (∀ p, operation (operation p) = p.swap) ∧
    Complex.normSq 0 = 0 ∧
    (∀ x, 0 ≤ Complex.normSq x) ∧
    (∀ x y, Complex.normSq (operation (x, y)).1 +
      Complex.normSq (operation (x, y)).2 = Complex.normSq x + Complex.normSq y) ∧
    (∃ e : ℂ, Complex.normSq e = 1) := by
  exact ⟨transparent, square, Complex.normSq_zero, Complex.normSq_nonneg,
    OperationalPhaseMixerWitness.norm_conservation, 1, Complex.normSq_one⟩

theorem reconstructed_nonzero_model : Reconstruction operation Complex.normSq :=
  reconstruct_positive_operation operation transparent square Complex.normSq
    Complex.normSq_zero Complex.normSq_nonneg OperationalPhaseMixerWitness.norm_conservation

end ConsistencyWitness

/-- The distinction between supplied laws, derived structure and physical
questions remains machine visible without changing any proof-status ledger. -/
inductive BoundaryRole where
  | suppliedAdditiveCoherentMerging
  | suppliedCompleteTwoPortOperation
  | suppliedDiagonalTransparency
  | suppliedExactRootOfSwap
  | suppliedNonnegativeRealVacuumZeroReadout
  | suppliedConservationOnAllCarrierInputs
  | derivedAdditiveGroup
  | derivedPhaseFourthIterateIdentity
  | derivedGenuineHalf
  | derivedQuadraticReadout
  | derivedThirdOrderZero
  | openPhysicalRealization
  | openCoherentSumVersusProbabilisticMixing
  | openNormalizedEventActualization
  | openFullStateCompleteness
  | openHilbertCompletion
  | openDynamics
  | openComposites
  | openPhysicalScales
  | noSerialMultiplicationAssumed
  | noPrimitiveInevitabilityClaim
  | noFullQMOrStatusUpgrade
  deriving DecidableEq, Repr

def boundaryRoles : List BoundaryRole :=
  [.suppliedAdditiveCoherentMerging, .suppliedCompleteTwoPortOperation,
   .suppliedDiagonalTransparency, .suppliedExactRootOfSwap,
   .suppliedNonnegativeRealVacuumZeroReadout, .suppliedConservationOnAllCarrierInputs,
   .derivedAdditiveGroup, .derivedPhaseFourthIterateIdentity, .derivedGenuineHalf,
   .derivedQuadraticReadout, .derivedThirdOrderZero, .openPhysicalRealization,
   .openCoherentSumVersusProbabilisticMixing, .openNormalizedEventActualization,
   .openFullStateCompleteness, .openHilbertCompletion, .openDynamics, .openComposites,
   .openPhysicalScales, .noSerialMultiplicationAssumed, .noPrimitiveInevitabilityClaim,
   .noFullQMOrStatusUpgrade]

end
end IDT.QMClosure.OperationalQuadraticReconstruction
