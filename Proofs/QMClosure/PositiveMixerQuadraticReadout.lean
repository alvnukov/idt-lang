import Proofs.QMClosure.PhaseMixerCancellation
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

namespace IDT.QMClosure.PositiveMixerQuadraticReadout

noncomputable section

/-!
# Positive readout conserved on the complete refined mixer domain

This universal algebraic theorem supplies an additive abelian carrier, genuine
additive halving, a quarter-turn whose square is negation, and nonnegative real
readout vanishing at zero. Conservation is required for **every pair in the
carrier**, including every iterated half refinement, not merely raw histories.
No serial multiplication, weight multiplication, norm law, scalar structure on
the carrier, topology, continuity, or differentiability is assumed. The real
codomain's Archimedean order is used to eliminate an odd readout component.

This does not derive the supplied algebra or full-domain conservation from IDT
primitives. It does not prove state completeness, Hilbert representation,
composite closure, dynamics, actualization, or full QM.
-/

variable {V : Type*} [AddCommGroup V]

def coefficientA (J H : V →+ V) (x : V) : V := H (x + J x)
def coefficientB (J H : V →+ V) (x : V) : V := H (x - J x)
def mixer (J H : V →+ V) (x y : V) : V × V :=
  (coefficientA J H x + coefficientB J H y,
   coefficientB J H x + coefficientA J H y)

variable (J H : V →+ V) (half : ∀ x, H x + H x = x)
variable (quarter : ∀ x, J (J x) = -x)

include quarter in
theorem phase_cube (x : V) : J (J (J x)) = -J x := quarter (J x)

include half in
private theorem double_sum_half (x y : V) :
    (H x + H y) + (H x + H y) = x + y := by
  calc
    _ = (H x + H x) + (H y + H y) := by abel
    _ = x + y := by rw [half, half]

include half in
theorem mixer_centered (s d : V) :
    mixer J H (s + d) (s - d) = (s + J d, s - J d) := by
  apply Prod.ext <;>
    apply PhaseMixerCancellation.doubling_injective H half
  · change (H _ + H _) + (H _ + H _) = _
    rw [double_sum_half H half]
    simp only [map_add, map_sub]
    abel
  · change (H _ + H _) + (H _ + H _) = _
    rw [double_sum_half H half]
    simp only [map_add, map_sub]
    abel

include half quarter in
theorem mixer_square (z x : V) :
    mixer J H (z + x + J x) z = (z + J x, z + x) := by
  apply Prod.ext <;>
    apply PhaseMixerCancellation.doubling_injective H half
  · change (H _ + H _) + (H _ + H _) = _
    rw [double_sum_half H half]
    simp only [map_add, quarter]
    abel
  · change (H _ + H _) + (H _ + H _) = _
    rw [double_sum_half H half]
    simp only [map_add, quarter]
    abel

def Conserved (W : V → ℝ) : Prop :=
  ∀ x y, W (mixer J H x y).1 + W (mixer J H x y).2 = W x + W y

variable (W : V → ℝ) (zero : W 0 = 0) (conserve : Conserved J H W)

include half conserve in
theorem centered_identity (s d : V) :
    W (s + d) + W (s - d) = W (s + J d) + W (s - J d) := by
  have h := conserve (s + d) (s - d)
  rw [mixer_centered J H half] at h
  exact h.symm

include half quarter conserve in
theorem mixed_square_identity (z x : V) :
    W (z + x + J x) + W z = W (z + J x) + W (z + x) := by
  have h := conserve (z + x + J x) z
  rw [mixer_square J H half quarter] at h
  exact h.symm

include half quarter zero conserve in
theorem double_readout (x : V) : W (x + x) = 3 * W x + W (-x) := by
  have hc := centered_identity J H half W conserve x x
  have hm := mixed_square_identity J H half quarter W conserve 0 x
  have hn := mixed_square_identity J H half quarter W conserve (-J x) x
  have h0 := centered_identity J H half W conserve 0 x
  have he : -J x + x + J x = x := by abel
  simp only [zero_add, zero_sub, sub_self, zero] at hc hm h0
  rw [he] at hn
  simp only [neg_add_cancel, zero] at hn
  have he' : -J x + x = x - J x := by abel
  rw [he'] at hn
  linarith

def evenPart (W : V → ℝ) (x : V) : ℝ := (W x + W (-x)) / 2
def oddPart (W : V → ℝ) (x : V) : ℝ := (W x - W (-x)) / 2

include half quarter zero conserve in
theorem part_half_scaling (x : V) :
    evenPart W (H x) = evenPart W x / 4 ∧
      oddPart W (H x) = oddPart W x / 2 := by
  have hp := double_readout J H half quarter W zero conserve (H x)
  have hn := double_readout J H half quarter W zero conserve (-H x)
  have he : -H x + -H x = -x := by rw [← neg_add, half]
  rw [half] at hp
  rw [he, neg_neg] at hn
  constructor <;> dsimp [evenPart, oddPart] <;> linarith

include half quarter zero conserve in
theorem readout_even (positive : ∀ x, 0 ≤ W x) : ∀ x, W (-x) = W x := by
  have bound : ∀ (n : ℕ) (x : V),
      (2 : ℝ) ^ n * |oddPart W x| ≤ evenPart W x := by
    intro n
    induction n with
    | zero =>
        intro x
        simp only [pow_zero, one_mul]
        rw [abs_le]
        constructor <;> dsimp [evenPart, oddPart] <;>
          linarith [positive x, positive (-x)]
    | succ n ih =>
        intro x
        have h := ih (H x)
        obtain ⟨hq, hl⟩ := part_half_scaling J H half quarter W zero conserve x
        rw [hq, hl, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
        rw [pow_succ]
        nlinarith
  intro x
  have hz : oddPart W x = 0 := by
    by_contra hn
    have ha : 0 < |oddPart W x| := abs_pos.mpr hn
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
      (evenPart W x / |oddPart W x|) (by norm_num : (1 : ℝ) < 2)
    have ht := (div_lt_iff₀ ha).mp hn
    have hb := bound n x
    nlinarith
  dsimp [oddPart] at hz
  linarith

include half quarter in
theorem phase_coefficientA (x : V) :
    J (coefficientA J H x) = -coefficientB J H x := by
  dsimp [coefficientA, coefficientB]
  rw [← PhaseMixerCancellation.refinement_commutes H half J]
  rw [map_add, quarter, ← map_neg]
  congr 1
  abel

include half quarter in
theorem mixer_crossed (x y : V) :
    mixer J H x (J y) =
      (coefficientA J H (x + y), coefficientB J H (x - y)) := by
  apply Prod.ext <;>
    apply PhaseMixerCancellation.doubling_injective H half
  · change (H _ + H _) + (H _ + H _) = H _ + H _
    rw [double_sum_half H half, half]
    simp only [map_add, quarter]
    abel
  · change (H _ + H _) + (H _ + H _) = H _ + H _
    rw [double_sum_half H half, half]
    simp only [map_sub, quarter]
    abel

include half quarter zero conserve in
theorem phase_invariant (positive : ∀ x, 0 ≤ W x) (x : V) : W (J x) = W x := by
  have he := readout_even J H half quarter W zero conserve positive
  have hc := centered_identity J H half W conserve 0 x
  simp only [zero_add, zero_sub, he] at hc
  linarith

include half quarter zero conserve in
theorem coefficient_readout (positive : ∀ x, 0 ≤ W x) (x : V) :
    W (coefficientA J H x) = W x / 2 ∧
      W (coefficientB J H x) = W x / 2 := by
  have he := readout_even J H half quarter W zero conserve positive
  have hj := phase_invariant J H half quarter W zero conserve positive
  have hc := conserve x 0
  have hzero : coefficientA J H 0 = 0 ∧ coefficientB J H 0 = 0 := by
    simp [coefficientA, coefficientB]
  change W (coefficientA J H x + coefficientB J H 0) +
    W (coefficientB J H x + coefficientA J H 0) = W x + W 0 at hc
  rw [hzero.1, hzero.2, add_zero, add_zero, zero, add_zero] at hc
  have hp := hj (coefficientA J H x)
  rw [phase_coefficientA J H half quarter, he] at hp
  constructor <;> linarith

include half quarter zero conserve in
theorem parallelogram (positive : ∀ x, 0 ≤ W x) (x y : V) :
    W (x + y) + W (x - y) = 2 * W x + 2 * W y := by
  have hc := conserve x (J y)
  rw [mixer_crossed J H half quarter] at hc
  rw [(coefficient_readout J H half quarter W zero conserve positive (x + y)).1,
    (coefficient_readout J H half quarter W zero conserve positive (x - y)).2,
    phase_invariant J H half quarter W zero conserve positive y] at hc
  linarith

include half quarter zero conserve in
theorem half_scaling (positive : ∀ x, 0 ≤ W x) (x : V) : W (H x) = W x / 4 := by
  have h := (part_half_scaling J H half quarter W zero conserve x).1
  have he := readout_even J H half quarter W zero conserve positive
  simp only [evenPart, he] at h
  linarith

include half quarter zero conserve in
theorem mixed_square (positive : ∀ x, 0 ≤ W x) (x : V) :
    W (x + J x) = 2 * W x := by
  have h := mixed_square_identity J H half quarter W conserve 0 x
  simp only [zero_add, zero, add_zero,
    phase_invariant J H half quarter W zero conserve positive] at h
  linarith

/-- The packed universal conclusion; no finite gate or sampled domain is used. -/
structure QuadraticReadout (J H : V →+ V) (W : V → ℝ) : Prop where
  even : ∀ x, W (-x) = W x
  phase_invariant : ∀ x, W (J x) = W x
  half_scaling : ∀ x, W (H x) = W x / 4
  parallelogram : ∀ x y, W (x + y) + W (x - y) = 2 * W x + 2 * W y
  mixed_square : ∀ x, W (x + J x) = 2 * W x

include half quarter zero conserve in
/-- Positivity kills the additive odd component through all half refinements. -/
theorem positive_conserved_readout_is_quadratic (positive : ∀ x, 0 ≤ W x) :
    QuadraticReadout J H W where
  even := readout_even J H half quarter W zero conserve positive
  phase_invariant := phase_invariant J H half quarter W zero conserve positive
  half_scaling := half_scaling J H half quarter W zero conserve positive
  parallelogram := parallelogram J H half quarter W zero conserve positive
  mixed_square := mixed_square J H half quarter W zero conserve positive

/-- Machine-visible statement of the conditional research boundary. -/
inductive SuppliedBridge where
  | additiveAbelianCarrier
  | additiveGlobalHalving
  | additiveQuarterTurn
  | nonnegativeArchimedeanRealReadout
  | vacuumReadoutZero
  | conservationOnEveryRefinedInput

/-- These obligations are not conclusions of this artifact. -/
inductive OpenObligation where
  | deriveSuppliedAlgebraFromPrimitives
  | justifyFullRefinedDomainConservation
  | stateCompleteness
  | hilbertRepresentation
  | compositeClosure
  | dynamics
  | actualization
  | fullQM

def suppliedBridges : List SuppliedBridge :=
  [.additiveAbelianCarrier, .additiveGlobalHalving, .additiveQuarterTurn,
   .nonnegativeArchimedeanRealReadout, .vacuumReadoutZero,
   .conservationOnEveryRefinedInput]

def openObligations : List OpenObligation :=
  [.deriveSuppliedAlgebraFromPrimitives, .justifyFullRefinedDomainConservation,
   .stateCompleteness, .hilbertRepresentation, .compositeClosure, .dynamics,
   .actualization, .fullQM]

end
end IDT.QMClosure.PositiveMixerQuadraticReadout
