import Proofs.QMClosure.RawOperationalHilbert
import Proofs.QMClosure.MixerRecordNaturality

namespace IDT.QMClosure.RawOperationalSeparation

open MedialSwapRoot RawOperationalHilbert
open PositiveMixerQuadraticReadout

noncomputable section

/-!
Raw output tests separate exactly the canonical Hilbert features. All algebra
below is reconstructed on `Carrier d`. The separating reference is quantified
over that closed mathematical carrier; its existence supplies no copying,
normalization, or physical preparation procedure for an unknown input.
-/

variable {V : Type*} (d : Data V)

theorem difference_eq (x y : Data.Carrier d) : d.difference x y = x - y := by
  rfl

/-- The original diagonal, before its mathematical normalization. -/
def diagonal (x : Data.Carrier d) : Data.Carrier d :=
  DiagonalNormalization.diagonal (firstChannel d.operation) x

private def rawLaws : DiagonalNormalization.Laws (firstChannel d.operation) where
  medial := d.medial
  bookend := raw_operation_bookend d.operation d.square

theorem diagonal_involutive (x : Data.Carrier d) : diagonal d (diagonal d x) = x :=
  DiagonalNormalization.diagonal_involutive (rawLaws d) x

theorem diagonal_weight (x : Data.Carrier d) : d.weight (diagonal d x) = d.weight x :=
  DiagonalNormalization.diagonal_preserves_readout d.weight
    (raw_operation_conserves_readout d.operation d.square d.weight d.conserved) x

theorem normalized_transparent (x : Data.Carrier d) :
    d.normalizedOperation (x, x) = (x, x) := by
  letI : Zero V := ⟨d.chosenZero⟩
  exact Prod.ext (d.normalizedLaws.idempotent x) (d.normalizedLaws.idempotent x)

theorem normalized_square (p : Data.Carrier d × Data.Carrier d) :
    d.normalizedOperation (d.normalizedOperation p) = p.swap := by
  letI : Zero V := ⟨d.chosenZero⟩
  exact Prod.ext (d.normalizedLaws.bookend p.1 p.2) (d.normalizedLaws.bookend p.2 p.1)

theorem diagonal_intertwines :
    MixerRecordNaturality.Intertwines d.normalizedOperation d.normalizedOperation
      (diagonal d) := by
  intro x y
  apply Prod.ext
  · exact congrArg (diagonal d)
      (DiagonalNormalization.diagonal_map (rawLaws d) x y)
  · exact congrArg (diagonal d)
      (DiagonalNormalization.diagonal_map (rawLaws d) y x)

/-- The raw diagonal may translate the chosen zero by a null direction. -/
theorem diagonal_distance (x y : Data.Carrier d) :
    d.weight (diagonal d x - diagonal d y) = d.weight (x - y) := by
  obtain ⟨L, affine, _⟩ := (MixerRecordNaturality.affine_classification
    d.normalizedOperation d.normalizedOperation (normalized_transparent d)
    (normalized_square d) (normalized_transparent d) (normalized_square d)
    (diagonal d)).mp (diagonal_intertwines d)
  have hz : d.weight (diagonal d 0) = 0 :=
    (diagonal_weight d 0).trans d.quadratic.zero
  have hL (u : Data.Carrier d) : d.weight (L u) = d.weight u := by
    have h := diagonal_weight d u
    rw [affine u, d.quadratic.null_translate (L u) (diagonal d 0) hz] at h
    exact h
  rw [affine x, affine y]
  have e : L x + diagonal d 0 - (L y + diagonal d 0) = L (x - y) := by
    rw [map_sub]
    abel
  rw [e, hL]

abbrev phase (x : Data.Carrier d) : Data.Carrier d := d.phase.J x

abbrev half : Data.Carrier d →+ Data.Carrier d :=
  OperationalQuadraticReconstruction.half d.normalizedOperation

private theorem phase_eq :
    OperationalQuadraticReconstruction.phase d.normalizedOperation = d.phase.J := rfl

theorem normalized_route (x y : Data.Carrier d) :
    d.normalizedOperation (x, y) = mixer d.phase.J (half d) x y := by
  rw [congrFun d.reconstruction.routing]
  change (half d (x + d.phase.J x) +
      half d (y + d.phase.J (d.phase.J (d.phase.J y))),
    half d (x + d.phase.J (d.phase.J (d.phase.J x))) +
      half d (y + d.phase.J y)) = _
  rw [d.phase.square (d.phase.J y), d.phase.square (d.phase.J x)]
  rfl

private theorem normalized_conserved : Conserved d.phase.J (half d) d.weight := by
  intro x y
  rw [← normalized_route d]
  exact DiagonalNormalization.normalized_conserves_readout d.weight
    (raw_operation_conserves_readout d.operation d.square d.weight d.conserved) x y

theorem coefficients_weight (x : Data.Carrier d) :
    d.weight (coefficientA (V := Data.Carrier d) d.phase.J (half d) x) = d.weight x / 2 ∧
    d.weight (coefficientB (V := Data.Carrier d) d.phase.J (half d) x) = d.weight x / 2 :=
  coefficient_readout (V := Data.Carrier d) d.phase.J (half d) d.reconstruction.halves d.phase.square
    d.weight d.quadratic.zero (normalized_conserved d) d.nonnegative x

def portA : Data.Carrier d →+ Data.Carrier d :=
  TransparentSwapRoot.portA d.normalizedOperation

def portB : Data.Carrier d →+ Data.Carrier d :=
  TransparentSwapRoot.portB d.normalizedOperation

theorem portA_eq (x : Data.Carrier d) :
    portA d x = coefficientA d.phase.J (half d) x := by
  have h := congrArg Prod.fst (normalized_route d x 0)
  simpa [portA, TransparentSwapRoot.portA, mixer, coefficientB] using h

theorem portB_eq (x : Data.Carrier d) :
    portB d x = coefficientB d.phase.J (half d) x := by
  have h := congrArg Prod.fst (normalized_route d 0 x)
  simpa [portB, TransparentSwapRoot.portB, mixer, coefficientA] using h

theorem raw_first (x y : Data.Carrier d) :
    (d.operation (x, y)).1 = diagonal d (portA d x + portB d y) := by
  have h := congrArg (diagonal d) (congrArg Prod.fst (normalized_route d x y))
  change diagonal d (diagonal d ((d.operation (x, y)).1)) = _ at h
  rw [diagonal_involutive] at h
  simpa only [mixer, portA_eq, portB_eq] using h

theorem raw_second (x y : Data.Carrier d) :
    (d.operation (x, y)).2 = diagonal d (portB d x + portA d y) := by
  have h := congrArg Prod.snd (raw_operation_eq_symmetric d.operation d.square (x, y))
  change (d.operation (x, y)).2 = (d.operation (y, x)).1 at h
  rw [h, raw_first d y x, add_comm]

theorem raw_first_left_distance (x y z : Data.Carrier d) :
    d.weight (d.difference (d.operation (x, z)).1 (d.operation (y, z)).1) =
      d.weight (x - y) / 2 := by
  rw [difference_eq d]
  rw [raw_first, raw_first, diagonal_distance]
  have e : portA d x + portB d z - (portA d y + portB d z) = portA d (x - y) := by
    rw [map_sub]
    abel
  rw [e, portA_eq]
  exact (coefficients_weight d (x - y)).1

theorem raw_first_right_distance (x y z : Data.Carrier d) :
    d.weight (d.difference (d.operation (z, x)).1 (d.operation (z, y)).1) =
      d.weight (x - y) / 2 := by
  rw [difference_eq d]
  rw [raw_first, raw_first, diagonal_distance]
  have e : portA d z + portB d x - (portA d z + portB d y) = portB d (x - y) := by
    rw [map_sub]
    abel
  rw [e, portB_eq]
  exact (coefficients_weight d (x - y)).2

theorem raw_second_left_distance (x y z : Data.Carrier d) :
    d.weight (d.difference (d.operation (x, z)).2 (d.operation (y, z)).2) =
      d.weight (x - y) / 2 := by
  rw [difference_eq d]
  rw [raw_second, raw_second, diagonal_distance]
  have e : portB d x + portA d z - (portB d y + portA d z) = portB d (x - y) := by
    rw [map_sub]
    abel
  rw [e, portB_eq]
  exact (coefficients_weight d (x - y)).2

theorem raw_second_right_distance (x y z : Data.Carrier d) :
    d.weight (d.difference (d.operation (z, x)).2 (d.operation (z, y)).2) =
      d.weight (x - y) / 2 := by
  rw [difference_eq d]
  rw [raw_second, raw_second, diagonal_distance]
  have e : portB d z + portA d x - (portB d z + portA d y) = portA d (x - y) := by
    rw [map_sub]
    abel
  rw [e, portA_eq]
  exact (coefficients_weight d (x - y)).1

theorem portB_separating_reference (y : Data.Carrier d) :
    portB d (-d.phase.J y) = -portA d y := by
  rw [portB_eq, portA_eq]
  unfold coefficientA coefficientB
  calc
    _ = half d (-(y + d.phase.J y)) := by
      congr 1
      rw [map_neg, d.phase.square]
      abel
    _ = _ := map_neg (half d) _

/-- A closed-carrier witness; no procedure for producing it is asserted. -/
theorem separating_reference (x y : Data.Carrier d) :
    d.weight (d.operation (x, -d.phase.J y)).1 = d.weight (x - y) / 2 := by
  rw [raw_first, diagonal_weight, portB_separating_reference]
  rw [← sub_eq_add_neg, ← map_sub, portA_eq]
  exact (coefficients_weight d (x - y)).1

theorem feature_eq_iff_raw_tests (x y : V) :
    d.feature x = d.feature y ↔
      ∀ z, d.weight (d.operation (x, z)).1 = d.weight (d.operation (y, z)).1 := by
  rw [d.feature_eq_iff, difference_eq d x y]
  constructor
  · intro h z
    have hn := raw_first_left_distance d x y z
    rw [h, zero_div] at hn
    rw [difference_eq d] at hn
    have ht := d.quadratic.null_translate (d.operation (y, z)).1
      (d.difference (d.operation (x, z)).1 (d.operation (y, z)).1)
      (by rw [difference_eq d]; exact hn)
    convert ht using 1
    congr 1
    rw [difference_eq d]
    have cancel (a b : Data.Carrier d) : a = b + (a - b) := by abel
    exact cancel _ _
  · intro h
    have hh := h (-d.phase.J y)
    rw [separating_reference, separating_reference, sub_self, d.quadratic.zero,
      zero_div] at hh
    linarith

end

end IDT.QMClosure.RawOperationalSeparation
