import Proofs.QMClosure.OperationalPhaseMixerReconstruction
import Mathlib.Data.Complex.Basic

namespace IDT.QMClosure.OperationalPhaseMixerWitness

noncomputable section

open OperationalPhaseMixerReconstruction LocalHistoryReadoutOrderWall

/-!
# Nonvacuity of the entire operational contract

Complex numbers are used only for an explicit consistency model. They are not
an assumption of the reconstruction theorem. The model supplies the routing,
real norm-squared response and actual raw representation and verifies every
Contract field, including injectivity and conservation universally. This
example is not evidence that the physical device or norm response was derived
independently. It does not identify the whole ambient carrier in the theorem.
-/

def gaussian (z : Residual) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

theorem gaussian_zero : gaussian (0 : Residual) = 0 := by simp [gaussian]
theorem gaussian_one : gaussian DyadicResponseExtension.unit = 1 := by
  norm_num [gaussian, DyadicResponseExtension.unit]

theorem gaussian_add (z w : Residual) : gaussian (z + w) = gaussian z + gaussian w := by
  simp only [gaussian, Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

theorem gaussian_serial (z w : Residual) :
    gaussian (serial z w) = gaussian z * gaussian w := by
  apply Complex.ext <;> simp [gaussian, serial]

theorem gaussian_rotate (z : Residual) : gaussian (rotate z) = Complex.I * gaussian z := by
  apply Complex.ext <;> simp [gaussian, rotate]

def eval (n : RawSyntax.Raw) : ℂ := gaussian (RawSyntax.gamma n)

theorem eval_empty : eval RawSyntax.empty = 0 := by
  change gaussian (0 : Residual) = 0
  exact gaussian_zero

theorem eval_one : eval RawSyntax.e0 = 1 := by
  change gaussian DyadicResponseExtension.unit = 1
  exact gaussian_one

theorem eval_merge (n m : RawSyntax.Raw) :
    eval (RawSyntax.merge n m) = eval n + eval m := by
  unfold eval
  rw [RawSyntax.gamma_merge]
  exact gaussian_add _ _

theorem eval_serial (n m : RawSyntax.Raw) :
    eval (RawSyntax.serial n m) = eval n * eval m := by
  unfold eval
  rw [RawSyntax.gamma_serial, gaussian_serial]

theorem eval_phase (n : RawSyntax.Raw) :
    eval (RawSyntax.phaseRotate n) = Complex.I * eval n := by
  unfold eval
  rw [RawSyntax.gamma_phase, gaussian_rotate]

def half (x : ℂ) : ℂ := x / 2

def halfHom : ℂ →+ ℂ where
  toFun := half
  map_zero' := by simp [half]
  map_add' x y := add_div x y 2

theorem halves (x : ℂ) : half x + half x = x := by
  dsimp [half]
  ring

theorem phase_fourth (x : ℂ) : phase Complex.I
    (phase Complex.I (phase Complex.I (phase Complex.I x))) = x := by
  change Complex.I * (Complex.I * (Complex.I * (Complex.I * x))) = x
  simp [← mul_assoc]

theorem cancellation (x : ℂ) : x + phase Complex.I (phase Complex.I x) = 0 := by
  change x + Complex.I * (Complex.I * x) = 0
  simp [← mul_assoc]

theorem mixer_injective : Function.Injective (selectedMixer Complex.I half) :=
  (PhaseMixerCancellation.mixer_bijective_of_cancellation
    (phase Complex.I) halfHom halves phase_fourth cancellation).1

/-- Universal coordinate identity; no reconstruction conclusion is used. -/
theorem norm_conservation (x y : ℂ) :
    Complex.normSq (selectedMixer Complex.I half (x, y)).1 +
      Complex.normSq (selectedMixer Complex.I half (x, y)).2 =
        Complex.normSq x + Complex.normSq y := by
  simp [selectedMixer, PhaseMixerCancellation.mixer,
    PhaseMixerCancellation.coefficientA, PhaseMixerCancellation.coefficientB,
    phase, half, Complex.normSq_apply]
  ring

/-- All supplied assumptions are simultaneously inhabited, including E laws. -/
def model : Contract ℂ where
  u := Complex.I
  fourth := Complex.I_pow_four
  half := half
  halves := halves
  mixer_injective := mixer_injective
  response := Complex.normSq
  response_zero := Complex.normSq_zero
  response_one := Complex.normSq_one
  response_mul := Complex.normSq_mul
  eval := eval
  eval_empty := eval_empty
  eval_one := eval_one
  eval_merge := eval_merge
  eval_phase := eval_phase
  eval_serial := eval_serial
  conserves n m := norm_conservation (eval n) (eval m)

theorem contract_nonempty : Nonempty (Contract ℂ) := ⟨model⟩

/-- A complex-valued identity response conserves a different raw total. -/
theorem identity_response_conserves (x y : ℂ) :
    (selectedMixer Complex.I half (x, y)).1 +
      (selectedMixer Complex.I half (x, y)).2 = x + y := by
  apply Complex.ext <;>
    simp [selectedMixer, PhaseMixerCancellation.mixer,
      PhaseMixerCancellation.coefficientA, PhaseMixerCancellation.coefficientB,
      phase, half] <;> ring

/-- The complex-valued control is zero-unital and multiplicative but sends 2
to 2. The real codomain of Contract is a substantive supplied boundary. -/
theorem complex_identity_control :
    (id : ℂ → ℂ) 0 = 0 ∧ (id : ℂ → ℂ) 1 = 1 ∧
    (∀ x y : ℂ, id (x * y) = id x * id y) ∧
    (∀ x y : ℂ, id (selectedMixer Complex.I half (x, y)).1 +
      id (selectedMixer Complex.I half (x, y)).2 = id x + id y) ∧
    (id (2 : ℂ) ≠ 4) := by
  refine ⟨rfl, rfl, fun _ _ => rfl, identity_response_conserves, ?_⟩
  norm_num

end
end IDT.QMClosure.OperationalPhaseMixerWitness
