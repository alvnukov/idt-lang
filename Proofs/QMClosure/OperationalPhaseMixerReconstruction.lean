import Proofs.QMClosure.PhaseMixerCancellation
import Proofs.QMClosure.NativeDyadicMixerSelection

namespace IDT.QMClosure.OperationalPhaseMixerReconstruction

noncomputable section

namespace RawSyntax
export SequentialUndoCancellationBoundary
  (Raw empty e0 e1 e2 e3 merge serial phaseRotate gamma representative
    gamma_representative gamma_surjective gamma_merge gamma_serial gamma_phase)
end RawSyntax
open LocalHistoryReadoutOrderWall DyadicResponseExtension

/-!
# Conditional reconstruction from an actual selected two-port representation

The ambient scalar sector is a commutative semiring, not a supplied Gaussian
carrier or additive group. Commutativity concerns this local scalar sector,
not all physical processes. The quarter-turn, pointwise structural half,
raw sum/phase/serial representation, complete two-output injectivity, real
zero-unital multiplicative response, and raw-input total conservation are
supplied. The exact routing is the previously selected candidate.

Cancellation and the faithful generated integer-pair sector, its quadratic
response, and the response of a structural half are conclusions. The half is
stored as a plain function, but in this unital commutative semiring its genuine
halving law implies half x = half 1 * x and hence additivity. Omitting an
additive-half field does not weaken the mathematical halving premise. No
positivity, topology, differentiability, ambient additive inverses, norm law,
or conservation for arbitrary ambient inputs is assumed. An ambient
sector can contain additional invisible elements: faithfulness below concerns
only the generated residual image. This conditional result does not derive a
physical device, detector actualization, Hilbert states, composites, or QM.
-/

def phase {S : Type*} [CommSemiring S] (u : S) : S →+ S where
  toFun x := u * x
  map_zero' := mul_zero u
  map_add' := mul_add u

def selectedMixer {S : Type*} [CommSemiring S] (u : S) (half : S → S) :=
  PhaseMixerCancellation.mixer (phase u) half

/-- Every field is supplied operational/algebraic data, never a conclusion. -/
structure Contract (S : Type*) [CommSemiring S] where
  u : S
  fourth : u ^ 4 = 1
  half : S → S
  halves : ∀ x, half x + half x = x
  mixer_injective : Function.Injective (selectedMixer u half)
  response : S → ℝ
  response_zero : response 0 = 0
  response_one : response 1 = 1
  response_mul : ∀ x y, response (x * y) = response x * response y
  eval : RawSyntax.Raw → S
  eval_empty : eval RawSyntax.empty = 0
  eval_one : eval RawSyntax.e0 = 1
  eval_merge : ∀ n m, eval (RawSyntax.merge n m) = eval n + eval m
  eval_phase : ∀ n, eval (RawSyntax.phaseRotate n) = u * eval n
  eval_serial : ∀ n m, eval (RawSyntax.serial n m) = eval n * eval m
  conserves : ∀ n m,
    response (selectedMixer u half (eval n, eval m)).1 +
      response (selectedMixer u half (eval n, eval m)).2 =
        response (eval n) + response (eval m)

namespace Contract
variable {S : Type*} [CommSemiring S] (C : Contract S)

theorem phase_fourth (x : S) :
    phase C.u (phase C.u (phase C.u (phase C.u x))) = x := by
  change C.u * (C.u * (C.u * (C.u * x))) = x
  calc
    _ = C.u ^ 4 * x := by ring
    _ = x := by rw [C.fourth, one_mul]

theorem cancellation (x : S) : x + phase C.u (phase C.u x) = 0 :=
  PhaseMixerCancellation.injective_mixer_forces_cancellation
    (phase C.u) C.phase_fourth C.half C.mixer_injective x

theorem unique_factor : ∃! F : Residual → S,
    ∀ n, C.eval n = F (RawSyntax.gamma n) :=
  PhaseMixerCancellation.represented_unique_residual_factor
    (phase C.u) C.phase_fourth C.half C.mixer_injective C.eval C.eval_merge C.eval_phase

def residualEval : Residual → S := C.unique_factor.choose

theorem factor (n : RawSyntax.Raw) : C.eval n = C.residualEval (RawSyntax.gamma n) :=
  C.unique_factor.choose_spec.1 n

theorem factor_unique (F : Residual → S)
    (hF : ∀ n, C.eval n = F (RawSyntax.gamma n)) : F = C.residualEval :=
  C.unique_factor.choose_spec.2 F hF

theorem residual_representative (z : Residual) :
    C.residualEval z = C.eval (RawSyntax.representative z) := by
  rw [C.factor, RawSyntax.gamma_representative]

theorem residual_zero : C.residualEval (0 : Residual) = 0 := by
  have hz : RawSyntax.gamma RawSyntax.empty = (0 : Residual) := rfl
  rw [← hz, ← C.factor, C.eval_empty]

theorem residual_one : C.residualEval unit = 1 := by
  have hz : RawSyntax.gamma RawSyntax.e0 = unit := by decide
  rw [← hz, ← C.factor, C.eval_one]

theorem residual_add (z w : Residual) :
    C.residualEval (z + w) = C.residualEval z + C.residualEval w := by
  obtain ⟨n, rfl⟩ := RawSyntax.gamma_surjective z
  obtain ⟨m, rfl⟩ := RawSyntax.gamma_surjective w
  rw [← C.factor, ← C.factor, ← C.eval_merge, C.factor, RawSyntax.gamma_merge]
  rfl

theorem residual_serial (z w : Residual) :
    C.residualEval (serial z w) = C.residualEval z * C.residualEval w := by
  obtain ⟨n, rfl⟩ := RawSyntax.gamma_surjective z
  obtain ⟨m, rfl⟩ := RawSyntax.gamma_surjective w
  rw [← RawSyntax.gamma_serial, ← C.factor, C.eval_serial, C.factor, C.factor]

theorem residual_double : C.residualEval double = (2 : S) := by
  have hd : double = unit + unit := by decide
  rw [hd, C.residual_add, C.residual_one]
  norm_num

theorem residual_i : C.residualEval NativeDyadicMixerSelection.i = C.u := by
  have hi : RawSyntax.gamma (RawSyntax.phaseRotate RawSyntax.e0) =
      NativeDyadicMixerSelection.i := by decide
  rw [← hi, ← C.factor, C.eval_phase, C.eval_one, mul_one]

theorem residual_ni : C.residualEval NativeDyadicMixerSelection.ni = C.u ^ 3 := by
  have hi : RawSyntax.gamma
      (RawSyntax.phaseRotate (RawSyntax.phaseRotate (RawSyntax.phaseRotate RawSyntax.e0))) =
      NativeDyadicMixerSelection.ni := by decide
  rw [← hi, ← C.factor, C.eval_phase, C.eval_phase, C.eval_phase, C.eval_one]
  ring

theorem residual_p : C.residualEval NativeDyadicMixerSelection.p = 1 + C.u := by
  have hp : NativeDyadicMixerSelection.p = unit + NativeDyadicMixerSelection.i := by decide
  rw [hp, C.residual_add, C.residual_one, C.residual_i]

theorem residual_m : C.residualEval NativeDyadicMixerSelection.m = 1 + C.u ^ 3 := by
  have hm : NativeDyadicMixerSelection.m = unit + NativeDyadicMixerSelection.ni := by decide
  rw [hm, C.residual_add, C.residual_one, C.residual_ni]

def nativeResponse : Response where
  weight z := C.response (C.residualEval z)
  unital := by rw [C.residual_one, C.response_one]
  multiplicative z w := by rw [C.residual_serial, C.response_mul]

/-- Nonzero gain follows from a represented unit and a genuine half of one. -/
theorem response_two_nonzero : C.response (2 : S) ≠ 0 := by
  have hh : (2 : S) * C.half 1 = 1 := by
    simpa only [two_mul] using C.halves 1
  have hr := congrArg C.response hh
  rw [C.response_mul, C.response_one] at hr
  intro hz
  rw [hz, zero_mul] at hr
  norm_num at hr

theorem doubling_nonzero : doublingValue C.nativeResponse ≠ 0 := by
  change C.response (C.residualEval double) ≠ 0
  rw [C.residual_double]
  exact C.response_two_nonzero

theorem doubled_output₁ (z w : Residual) :
    (2 : S) * (selectedMixer C.u C.half (C.residualEval z, C.residualEval w)).1 =
      C.residualEval (NativeDyadicMixerSelection.numerator₁ z w) := by
  rw [NativeDyadicMixerSelection.numerator₁, C.residual_add,
    C.residual_serial, C.residual_serial, C.residual_p, C.residual_m]
  change 2 * (C.half (C.residualEval z + C.u * C.residualEval z) +
    C.half (C.residualEval w + C.u * (C.u * (C.u * C.residualEval w)))) = _
  rw [mul_add, two_mul, two_mul, C.halves, C.halves]
  ring

theorem doubled_output₂ (z w : Residual) :
    (2 : S) * (selectedMixer C.u C.half (C.residualEval z, C.residualEval w)).2 =
      C.residualEval (NativeDyadicMixerSelection.numerator₂ z w) := by
  rw [NativeDyadicMixerSelection.numerator₂, C.residual_add,
    C.residual_serial, C.residual_serial, C.residual_p, C.residual_m]
  change 2 * (C.half (C.residualEval z + C.u * (C.u * (C.u * C.residualEval z))) +
    C.half (C.residualEval w + C.u * C.residualEval w)) = _
  rw [mul_add, two_mul, two_mul, C.halves, C.halves]
  ring

theorem residual_conservation (z w : Residual) :
    C.response (selectedMixer C.u C.half (C.residualEval z, C.residualEval w)).1 +
      C.response (selectedMixer C.u C.half (C.residualEval z, C.residualEval w)).2 =
        C.response (C.residualEval z) + C.response (C.residualEval w) := by
  rw [C.residual_representative z, C.residual_representative w]
  exact C.conserves _ _

/-- Actual doubled outputs, not an assumed fractional readout law, give this. -/
theorem numerator_conservation : NativeDyadicMixerSelection.NumeratorConserves C.nativeResponse := by
  intro z w
  change C.response (C.residualEval (NativeDyadicMixerSelection.numerator₁ z w)) +
    C.response (C.residualEval (NativeDyadicMixerSelection.numerator₂ z w)) =
      C.response (C.residualEval double) *
        (C.response (C.residualEval z) + C.response (C.residualEval w))
  rw [← C.doubled_output₁, ← C.doubled_output₂, C.residual_double,
    C.response_mul, C.response_mul, ← mul_add, C.residual_conservation]

theorem native_conservation : NativeDyadicMixerSelection.Conserves
    C.nativeResponse C.doubling_nonzero :=
  (NativeDyadicMixerSelection.conservation_iff C.nativeResponse C.doubling_nonzero).mpr
    C.numerator_conservation

theorem residual_norm (z : Residual) :
    C.response (C.residualEval z) = (quadratic z : ℝ) :=
  NativeDyadicMixerSelection.native_selection C.nativeResponse C.doubling_nonzero
    (by change C.response (C.residualEval (0 : Residual)) = 0
        rw [C.residual_zero, C.response_zero])
    C.native_conservation z

theorem raw_norm (n : RawSyntax.Raw) :
    C.response (C.eval n) = (quadratic (RawSyntax.gamma n) : ℝ) := by
  rw [C.factor, C.residual_norm]

theorem response_two : C.response (2 : S) = 4 := by
  rw [← C.residual_double, C.residual_norm]
  norm_num [double, quadratic]

theorem half_response (x : S) : C.response (C.half x) = C.response x / 4 := by
  have hh : (2 : S) * C.half x = x := by
    simpa only [two_mul] using C.halves x
  have hr := congrArg C.response hh
  rw [C.response_mul, C.response_two] at hr
  linarith

theorem residual_neg_pair (z : Residual) :
    C.residualEval z + C.residualEval (-z) = 0 := by
  rw [← C.residual_add, add_neg_cancel, C.residual_zero]

/-- Faithfulness is a conclusion for the generated sector, not all of S. -/
theorem residual_injective : Function.Injective C.residualEval := by
  intro z w heq
  have hz : C.residualEval (z - w) = 0 := by
    rw [sub_eq_add_neg, C.residual_add, heq, C.residual_neg_pair]
  have hq := C.residual_norm (z - w)
  rw [hz, C.response_zero] at hq
  have hqi : quadratic (z - w) = 0 := by exact_mod_cast hq.symm
  exact sub_eq_zero.mp ((quadratic_eq_zero_iff _).mp hqi)

/-- One reviewable end-to-end conclusion with all supplied fields in Contract. -/
theorem reconstruction :
    (∀ x, x + phase C.u (phase C.u x) = 0) ∧
    (∃! F : Residual → S, ∀ n, C.eval n = F (RawSyntax.gamma n)) ∧
    (∀ n, C.eval n = C.residualEval (RawSyntax.gamma n)) ∧
    C.residualEval (0 : Residual) = 0 ∧
    C.residualEval unit = 1 ∧
    (∀ z w, C.residualEval (z + w) = C.residualEval z + C.residualEval w) ∧
    (∀ z w, C.residualEval (serial z w) = C.residualEval z * C.residualEval w) ∧
    Function.Injective C.residualEval ∧
    (∀ z, C.response (C.residualEval z) = (quadratic z : ℝ)) ∧
    (∀ n, C.response (C.eval n) = (quadratic (RawSyntax.gamma n) : ℝ)) ∧
    C.response (2 : S) = 4 ∧
    (∀ x, C.response (C.half x) = C.response x / 4) :=
  ⟨C.cancellation, C.unique_factor, C.factor, C.residual_zero, C.residual_one,
    C.residual_add, C.residual_serial, C.residual_injective, C.residual_norm,
    C.raw_norm, C.response_two, C.half_response⟩

end Contract

inductive BoundaryRole where
  | supplied | proved | openBridge | excludedInference
  deriving DecidableEq

def boundaryLedger : List (BoundaryRole × String) :=
  [ (.supplied, "Local commutative scalar semiring, C4 scalar, actual raw sum/phase/serial representation with zero and unit, pointwise genuine structural half."),
    (.supplied, "Exact selected two-port routing, injectivity of the complete two outputs, real zero-unital multiplicative response, and conservation for every pair of raw preparations."),
    (.proved, "Selected routing injectivity forces cancellation and unique native residual descent; response gain at double is nonzero without assuming it."),
    (.proved, "Actual doubled outputs imply native numerator conservation, hence quadratic response, gain four, half-response one quarter, and a faithful generated Gaussian-integer sector."),
    (.openBridge, "Independent operational selection and physical motivation of this exact routing."),
    (.openBridge, "Physical realization of the raw representation, scalar grammar and structural half."),
    (.openBridge, "Complete accessible outputs, passivity and exhaustive raw/reference response coupling."),
    (.openBridge, "Real-valued detector response interpretation and actualization."),
    (.openBridge, "Full state spaces, dynamics, composites and physical scales."),
    (.excludedInference, "No assertion that the whole ambient carrier is Gaussian, complex or Hilbert; invisible extra sectors remain possible."),
    (.excludedInference, "With genuine additive half, injectivity is equivalent to cancellation in the selected routing; native conservation is equivalent to the quadratic response. This is an explicit conditional reconstruction, not weaker equivalent axioms or full QM.") ]

end
end IDT.QMClosure.OperationalPhaseMixerReconstruction
