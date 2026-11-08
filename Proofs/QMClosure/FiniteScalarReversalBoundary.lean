import Proofs.QMClosure.TransparentSwapRoot
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Finite scalar boundary for reversal descent

TransparentSwapRoot already reconstructs phase, half and cancellation from
the additive operational contract. This finite scalar image satisfies that
contract, but has no additive unital map reversing its reconstructed phase.
Thus equality in an arbitrary scalar image need not be stable under reflected
histories. Reversal descent needs separate justification. Faithful generated
arithmetic is one sufficient route.
-/

namespace IDT.QMClosure.FiniteScalarReversalBoundary

abbrev Scalar := ZMod 5

def a : Scalar := 4
def b : Scalar := 2
def phase : Scalar := 2 * a ^ 2
def half : Scalar := a * b

def forward (p : Scalar × Scalar) : Scalar × Scalar :=
  (a * p.1 + b * p.2, b * p.1 + a * p.2)

def undo (p : Scalar × Scalar) : Scalar × Scalar :=
  (b * p.1 + a * p.2, a * p.1 + b * p.2)

theorem coefficient_laws : a + b = 1 ∧ a * a + b * b = 0 ∧
    a * b + b * a = 1 := by decide

theorem square_swap (p : Scalar × Scalar) : forward (forward p) = (p.2, p.1) := by
  revert p
  decide

theorem diagonal (x : Scalar) : forward (x, x) = (x, x) := by
  revert x
  decide

theorem undo_forward (p : Scalar × Scalar) : undo (forward p) = p := by
  revert p
  decide

theorem forward_undo (p : Scalar × Scalar) : forward (undo p) = p := by
  revert p
  decide

def coefficientA : AddMonoid.End Scalar where
  toFun x := a * x
  map_zero' := mul_zero a
  map_add' x y := mul_add a x y

def coefficientB : AddMonoid.End Scalar where
  toFun x := b * x
  map_zero' := mul_zero b
  map_add' x y := mul_add b x y

theorem forward_additive (p q : Scalar × Scalar) :
    forward (p + q) = forward p + forward q := by
  ext <;> dsimp [forward] <;> ring

/-- The existing general theorem applies to this finite scalar image. -/
theorem reconstructed :
    TransparentSwapRoot.Reconstruction coefficientA coefficientB := by
  apply TransparentSwapRoot.reconstruct
  · intro x
    exact congrArg Prod.fst (diagonal x)
  · intro p
    exact square_swap p

theorem coefficients_nonzero : a ≠ 0 ∧ b ≠ 0 := by decide

theorem coefficients_units : IsUnit a ∧ IsUnit b := by
  constructor
  · exact ⟨⟨a, a, by decide, by decide⟩, rfl⟩
  · exact ⟨⟨b, 3, by decide, by decide⟩, rfl⟩

theorem phase_value : phase = 2 := by decide
theorem phase_square : phase ^ 2 = -1 := by decide
theorem phase_fourth : phase ^ 4 = 1 := by decide
theorem phase_inverse_value : phase ^ 3 = 3 := by decide
theorem phase_inverse : phase * 3 = 1 ∧ 3 * phase = 1 := by decide
theorem half_value : half = 3 := by decide
theorem half_doubles : half + half = 1 := by decide

theorem no_additive_unital_phase_reversal :
    ¬ ∃ J : Scalar →+ Scalar, J 1 = 1 ∧ J phase = phase ^ 3 := by
  rintro ⟨J, hunit, hphase⟩
  have heq : phase = (1 : Scalar) + 1 := by decide
  rw [heq, map_add, hunit] at hphase
  have hbad : (2 : Scalar) = 3 := by simpa only [phase_inverse_value] using hphase
  exact (by decide : (2 : Scalar) ≠ 3) hbad

theorem no_additive_unital_coefficient_swap :
    ¬ ∃ J : Scalar →+ Scalar, J 1 = 1 ∧ J a = b := by
  rintro ⟨J, hunit, hswap⟩
  have ha : a = (1 : Scalar) + 1 + 1 + 1 := by decide
  rw [ha, map_add, map_add, map_add, hunit] at hswap
  exact (by decide : (1 : Scalar) + 1 + 1 + 1 ≠ b) hswap

end IDT.QMClosure.FiniteScalarReversalBoundary
