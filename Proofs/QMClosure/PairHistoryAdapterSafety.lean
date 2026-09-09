import Proofs.QMClosure.PairHistoryMeasureProbe

namespace IDT.QMClosure.PairHistoryAdapterSafety

open scoped BigOperators

/-!
# Native pair-history adapter safety

These algebraic facts use the original integer and Gaussian-integer carriers,
addition, multiplication and weights. They do not add rational amplitudes.
Rationals below are only the codomain of an explicitly normalized, real-valued
projection used to exhibit an unsafe adapter bridge.

The unit-weight phase distinction is a capability observation, not a rejection
of signed primitives with other possible operational realizations. The tensor
counterexample rejects only the proposed real-projection bridge: forgetting the
imaginary pair information before multiplying does not preserve this diagonal
event weight. Neither realization is rejected, and no local generative law,
physical tensor product, probability interpretation, or QM/SM/GR is derived.
-/

theorem signed_scalar_unit_sum_weight_zero_or_four
    (amplitude : ℤ)
    (unitWeight : pairHistoryQuadraticWeight amplitude = 1) :
    pairHistoryQuadraticWeight (1 + amplitude) = 0 ∨
      pairHistoryQuadraticWeight (1 + amplitude) = 4 := by
  rcases signed_scalar_unit_weight_is_only_a_sign amplitude unitWeight with
    positive | negative
  · right
    norm_num [positive, pairHistoryQuadraticWeight]
  · left
    norm_num [negative, pairHistoryQuadraticWeight]

def one : GaussianHistoryAmplitude := ⟨1, 0⟩

def quarterTurn : GaussianHistoryAmplitude := ⟨0, 1⟩

theorem gaussian_quarter_turn_has_midpoint_weight :
    gaussianHistoryWeight quarterTurn = 1 ∧
      gaussianHistoryWeight (gaussianHistoryAdd one quarterTurn) = 2 := by
  norm_num [one, quarterTurn, gaussianHistoryWeight, gaussianHistoryAdd]

/-- The diagonal composite histories are `1 * 1` and `i * i`. -/
def nativeDiagonalAmplitude : GaussianHistoryAmplitude :=
  gaussianHistoryAdd (gaussianHistoryMul one one)
    (gaussianHistoryMul quarterTurn quarterTurn)

theorem gaussian_diagonal_composite_weight_zero :
    gaussianHistoryWeight nativeDiagonalAmplitude = 0 := by
  norm_num [nativeDiagonalAmplitude, one, quarterTurn, gaussianHistoryAdd,
    gaussianHistoryMul, gaussianHistoryWeight]

def histories : Fin 2 → GaussianHistoryAmplitude := ![one, quarterTurn]

/--
For histories `(1, i)`, retain only the real pair term, divided by their total
weight `W(1 + i) = 2`. This is the proposed projection, not a derived readout.
-/
def projectedRealKernel : Matrix (Fin 2) (Fin 2) ℚ := fun left right =>
  (((histories left).re * (histories right).re +
    (histories left).im * (histories right).im : ℤ) : ℚ) / 2

/-- The explicitly imported tensor rule for the projected real matrix. -/
def projectedRealTensor : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℚ :=
  fun left right =>
    projectedRealKernel left.1 right.1 *
      projectedRealKernel left.2 right.2

/-- Sum the tensor entries selected by the diagonal event `{(0,0), (1,1)}`. -/
def projectedDiagonalWeight : ℚ :=
  ∑ left : Fin 2, ∑ right : Fin 2,
    projectedRealTensor (left, left) (right, right)

/-- Use the same supplied total normalization: `W(1 + i)^2 = 4`. -/
def normalizedNativeDiagonalWeight : ℚ :=
  (gaussianHistoryWeight nativeDiagonalAmplitude : ℚ) / 4

theorem gaussian_normalized_native_diagonal_weight_zero :
    normalizedNativeDiagonalWeight = 0 := by
  simp [normalizedNativeDiagonalWeight, gaussian_diagonal_composite_weight_zero]

theorem gaussian_real_projected_tensor_diagonal_weight_half :
    projectedDiagonalWeight = 1 / 2 := by
  norm_num [projectedDiagonalWeight, Fin.sum_univ_two, projectedRealTensor,
    projectedRealKernel, histories, one, quarterTurn]

theorem gaussian_real_projection_fails_diagonal_composite_bridge :
    normalizedNativeDiagonalWeight ≠ projectedDiagonalWeight := by
  rw [gaussian_normalized_native_diagonal_weight_zero,
    gaussian_real_projected_tensor_diagonal_weight_half]
  norm_num

end IDT.QMClosure.PairHistoryAdapterSafety
