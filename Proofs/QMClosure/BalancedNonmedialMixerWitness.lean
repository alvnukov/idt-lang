import Proofs.QMClosure.BalancedNonmedialMixerCore
import Proofs.QMClosure.RawNetworkMedialWall

/-!
# Exact radical witnesses for the balanced nonmedial mixer

The fixed nonlinear gate has the global properties checked in its core module.
Here exact calculations refute first-channel mediality and distinguish a literal
three-gate raw program from the same syntax interpreted by the scalar native
mixer. The conserved norm readout supplies all six raw-semantic probability
conditions at every finite width.

This is a process/mediality wall, not a failure of the norm readout on its own
raw outputs. The raw prepared-state equality condition differs from the scalar
native one. No physical actualization, no-signalling model, fitted calibration,
or full QM closure is established.
-/

namespace IDT.QMClosure.BalancedNonmedialMixerWitness

noncomputable section
open BalancedNonmedialMixerCore
open MedialSwapRoot MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open WeightFreeRawProbability (evalRaw)

def radical : ℝ := Real.sqrt 2993

theorem radical_positive : 0 < radical := Real.sqrt_pos.mpr (by norm_num)

theorem radical_ne_zero : radical ≠ 0 := ne_of_gt radical_positive

theorem radical_complex_ne_zero : (radical : ℂ) ≠ 0 := by
  exact_mod_cast radical_ne_zero

theorem radical_square : radical ^ 2 = 2993 := Real.sq_sqrt (by norm_num)

private theorem first_coefficient : k (2 + Complex.I) Complex.I = 11 / 6 := by
  norm_num [k, R, Complex.normSq_apply]

private theorem first_phase : q (2 + Complex.I) = (3 + 4 * Complex.I) / 5 := by
  apply Complex.ext <;>
    norm_num [q, Complex.normSq_apply, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.mul_im]

theorem first_turn : turn (2 + Complex.I) Complex.I = -(52 + 17 * Complex.I) / 33 := by
  rw [turn, first_coefficient, frozenTurn, first_phase]
  apply Complex.ext <;>
    norm_num [A, B, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem first_turn_norm : ‖turn (2 + Complex.I) Complex.I‖ = radical / 33 := by
  rw [first_turn]
  rw [← sq_eq_sq₀ (norm_nonneg _)
    (div_nonneg radical_positive.le (by norm_num : (0 : ℝ) ≤ 33))]
  rw [← Complex.normSq_eq_norm_sq]
  norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im, div_pow, radical_square]

theorem first_rotated :
    rotated (2 + Complex.I) Complex.I = -(52 + 17 * Complex.I) / (radical : ℂ) := by
  unfold rotated
  rw [first_turn_norm, first_turn]
  apply Complex.ext <;>
    norm_num [Complex.smul_re, Complex.smul_im, Complex.div_re, Complex.div_im]

private theorem third_coefficient :
    k (1 - Complex.I / 2) (-Complex.I / 2) = 11 / 6 := by
  norm_num [k, R, Complex.normSq_apply, Complex.div_re, Complex.div_im]

private theorem third_phase : q (1 - Complex.I / 2) = (3 - 4 * Complex.I) / 5 := by
  apply Complex.ext <;>
    norm_num [q, Complex.normSq_apply, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.mul_im]

theorem third_turn :
    turn (1 - Complex.I / 2) (-Complex.I / 2) = (52 - 17 * Complex.I) / 66 := by
  rw [turn, third_coefficient, frozenTurn, third_phase]
  apply Complex.ext <;>
    norm_num [A, B, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem third_turn_norm :
    ‖turn (1 - Complex.I / 2) (-Complex.I / 2)‖ = radical / 66 := by
  rw [third_turn]
  rw [← sq_eq_sq₀ (norm_nonneg _)
    (div_nonneg radical_positive.le (by norm_num : (0 : ℝ) ≤ 66))]
  rw [← Complex.normSq_eq_norm_sq]
  norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im, div_pow, radical_square]

theorem third_rotated :
    rotated (1 - Complex.I / 2) (-Complex.I / 2) =
      (52 - 17 * Complex.I) / ((2 * radical : ℝ) : ℂ) := by
  unfold rotated
  rw [third_turn_norm, third_turn]
  apply Complex.ext <;>
    norm_num [norm_div, Complex.smul_re, Complex.smul_im, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.mul_im] <;>
    field_simp [radical_ne_zero] <;> ring

theorem gate_first_selected :
    (gate (1 + Complex.I, 1)).1 =
      1 + Complex.I / 2 - (52 + 17 * Complex.I) / ((2 * radical : ℝ) : ℂ) := by
  change ((1 + Complex.I + 1) +
    rotated (1 + Complex.I + 1) (1 + Complex.I - 1)) / 2 = _
  rw [show (1 + Complex.I + 1 : ℂ) = 2 + Complex.I by ring,
    show (1 + Complex.I - 1 : ℂ) = Complex.I by ring, first_rotated]
  push_cast
  field_simp [radical_complex_ne_zero]
  ring

theorem gate_third_selected :
    (gate ((1 - Complex.I) / 2, 1 / 2)).1 =
      1 / 2 - Complex.I / 4 + (52 - 17 * Complex.I) / ((4 * radical : ℝ) : ℂ) := by
  change (((1 - Complex.I) / 2 + 1 / 2) +
    rotated ((1 - Complex.I) / 2 + 1 / 2) ((1 - Complex.I) / 2 - 1 / 2)) / 2 = _
  rw [show ((1 - Complex.I) / 2 + 1 / 2 : ℂ) = 1 - Complex.I / 2 by ring,
    show ((1 - Complex.I) / 2 - 1 / 2 : ℂ) = -Complex.I / 2 by ring, third_rotated]
  push_cast
  field_simp [radical_complex_ne_zero]
  ring

theorem gate_I_one : gate (Complex.I, 1) = (0, 1 + Complex.I) := by
  have hv : gate (1 + Complex.I, 0) = (Complex.I, 1) := by
    rw [gate_vacuum_right]
    apply Prod.ext <;> apply Complex.ext <;>
      norm_num [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
  have hs := gate_square (1 + Complex.I, 0)
  rw [hv] at hs
  exact hs

theorem gate_one_I : gate (1, Complex.I) = (1 + Complex.I, 0) := by
  have hv : gate (0, 1 + Complex.I) = (1, Complex.I) := by
    rw [gate_vacuum_left]
    apply Prod.ext <;> apply Complex.ext <;>
      norm_num [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
  have hs := gate_square (0, 1 + Complex.I)
  rw [hv] at hs
  exact hs

theorem medial_tuple_left :
    firstChannel gate (firstChannel gate 1 1) (firstChannel gate Complex.I 1) =
      (1 + Complex.I) / 2 := by
  change (gate ((gate (1, 1)).1, (gate (Complex.I, 1)).1)).1 = _
  rw [gate_transparent, gate_I_one, gate_vacuum_right]
  simp

theorem medial_tuple_right :
    firstChannel gate (firstChannel gate 1 Complex.I) (firstChannel gate 1 1) =
      1 + Complex.I / 2 - (52 + 17 * Complex.I) / ((2 * radical : ℝ) : ℂ) := by
  change (gate ((gate (1, Complex.I)).1, (gate (1, 1)).1)).1 = _
  rw [gate_one_I, gate_transparent]
  exact gate_first_selected

theorem medial_tuple_unequal :
    firstChannel gate (firstChannel gate 1 1) (firstChannel gate Complex.I 1) ≠
      firstChannel gate (firstChannel gate 1 Complex.I) (firstChannel gate 1 1) := by
  rw [medial_tuple_left, medial_tuple_right]
  intro h
  have hi := congrArg Complex.im h
  norm_num [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im] at hi
  field_simp [radical_ne_zero] at hi
  nlinarith [radical_positive]

theorem gate_not_medial : ¬RawNetworkMedialWall.FirstChannelMedial gate :=
  fun h => medial_tuple_unequal (h 1 1 Complex.I 1)

/-- The same pair violates flexibility; no equivalence with mediality is asserted. -/
theorem gate_not_flexible :
    ¬∀ x y : ℂ, firstChannel gate (firstChannel gate x y) x =
      firstChannel gate x (firstChannel gate y x) := by
  intro h
  have hd : firstChannel gate (1 : ℂ) 1 = 1 := congrArg Prod.fst (gate_transparent 1)
  apply medial_tuple_unequal
  simpa only [hd] using (h 1 Complex.I).symm

/-- This is only an exact rejection of the quadratical identity at x=z=1,y=i. -/
theorem gate_not_quadratical :
    ¬∀ x y z : ℂ, firstChannel gate (firstChannel gate x y) x =
      firstChannel gate (firstChannel gate z x) (firstChannel gate y z) := by
  intro h
  have hd : firstChannel gate (1 : ℂ) 1 = 1 := congrArg Prod.fst (gate_transparent 1)
  apply medial_tuple_unequal
  simpa only [hd] using (h 1 Complex.I 1).symm

theorem gate_not_rowColumnCommutes : ¬RawNetworkMedialWall.RowColumnCommutes gate :=
  fun h => gate_not_medial (RawNetworkMedialWall.medial_of_rowColumnCommutes gate h)

/-- Six all-width conditions with the nonlinear gate's own literal raw semantics. -/
def rawLaw : RawNetworkMedialWall.RawSemanticsLaw gate (0 : ℂ) 1 :=
  RawNetworkMedialWall.readoutLaw gate 0 1 Complex.normSq
    (by simp) (by simp) Complex.normSq_nonneg gate_conserves

theorem raw_probability_eq_own_normSq {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (i : ι) :
    rawLaw.prob s c i = Complex.normSq (RawNetworkMedialWall.prepared gate 0 1 s c i) := rfl

def pair01 : Native (Fin 3) := .pair 0 1 (by decide)
def pair02 : Native (Fin 3) := .pair 0 2 (by decide)
def pair12 : Native (Fin 3) := .pair 1 2 (by decide)

def twoGatePrefix : Native (Fin 3) := .seq pair01 pair02
def word : Native (Fin 3) := .seq twoGatePrefix pair12

theorem pair01_output :
    RawNetworkMedialWall.prepared gate 0 1 0 pair01 =
      ![(1 + Complex.I) / 2, (1 - Complex.I) / 2, 0] := by
  funext i
  fin_cases i <;>
    simp [RawNetworkMedialWall.prepared, RawNetworkMedialWall.rawSource,
      evalRaw, pair01, gate_vacuum_right,
      show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide]

theorem prefix_output :
    RawNetworkMedialWall.prepared gate 0 1 0 twoGatePrefix =
      ![Complex.I / 2, (1 - Complex.I) / 2, 1 / 2] := by
  change evalRaw gate pair02 (RawNetworkMedialWall.prepared gate 0 1 0 pair01) = _
  rw [pair01_output]
  funext i
  fin_cases i <;>
    simp [pair02, evalRaw,
      show (1 : Fin 3) ≠ 0 by decide,
      show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide,
      gate_vacuum_right] <;>
    apply Complex.ext <;>
    norm_num [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]

theorem word_selected :
    RawNetworkMedialWall.prepared gate 0 1 0 word 1 =
      1 / 2 - Complex.I / 4 + (52 - 17 * Complex.I) / ((4 * radical : ℝ) : ℂ) := by
  change evalRaw gate pair12 (RawNetworkMedialWall.prepared gate 0 1 0 twoGatePrefix) 1 = _
  rw [prefix_output]
  exact gate_third_selected

private theorem word_selected_re :
    (RawNetworkMedialWall.prepared gate 0 1 0 word 1).re = 1 / 2 + 13 / radical := by
  rw [word_selected]
  norm_num [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
  field_simp [radical_ne_zero]
  ring

private theorem word_selected_im :
    (RawNetworkMedialWall.prepared gate 0 1 0 word 1).im = -1 / 4 - 17 / (4 * radical) := by
  rw [word_selected]
  norm_num [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
  field_simp [radical_ne_zero]
  ring

theorem word_selected_normSq :
    Complex.normSq (RawNetworkMedialWall.prepared gate 0 1 0 word 1) =
      3 / 8 + 121 / (8 * radical) := by
  simp only [Complex.normSq_apply, word_selected_re, word_selected_im]
  field_simp [radical_ne_zero]
  nlinarith [radical_square]

theorem word_probability : rawLaw.prob 0 word 1 = 3 / 8 + 121 / (8 * radical) :=
  word_selected_normSq

theorem native_word_selected : word.eval (source 0) 1 = (3 - Complex.I) / 4 := by
  apply Complex.ext <;>
    norm_num [word, twoGatePrefix, pair01, pair02, pair12, Circuit.eval, pairGate, pairReplace,
      source, single, NativeMixerEventConeExclusion.mixer, NativeMixerEventConeExclusion.Raw,
      CompositeProductControls.RawSign.N, CompositeProductControls.RawSign.n_re,
      CompositeProductControls.RawSign.n_im,
      show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
      show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
      Complex.div_re, Complex.div_im]

theorem native_word_normSq : Complex.normSq (word.eval (source 0) 1) = 5 / 8 := by
  rw [native_word_selected]
  norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im]

theorem raw_word_differs_from_native :
    rawLaw.prob 0 word 1 ≠ Complex.normSq (word.eval (source 0) 1) := by
  rw [word_probability, native_word_normSq]
  intro h
  have he : radical = 121 / 2 := by
    field_simp [radical_ne_zero] at h
    linarith
  have hs := radical_square
  rw [he] at hs
  norm_num at hs

end

end IDT.QMClosure.BalancedNonmedialMixerWitness
