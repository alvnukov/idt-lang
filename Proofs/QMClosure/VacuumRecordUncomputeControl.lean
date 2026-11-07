import Proofs.QMClosure.BalancedNonmedialMixerWitness

/-!
# A weak vacuum record/uncompute protocol does not select mediality

The four ports are labelled 00, 01, 10, 11 in that order. Every port is
retained. S splits ports 0 and 2; C swaps ports 2 and 3; R repeats the raw
02 gate three times and then the raw 13 gate three times. R is literal syntax,
not a supplied inverse operation. The permitted output permutation C is also
literal circuit syntax.

The amplitude identities below require only square-swap and agreement with
the native mixer on both one-zero inputs. They assume no mediality, global
homogeneity, linearity, tensor structure, purity, or probability law.

The nonlinear nonmedial gate already has its own conserved norm readout and
six-field raw law. With that supplied law the marked array is uniform, while
the unmarked and uncomputed arrays are point distributions. Thus this
weak protocol does not select the current medial primitive. These are exact
mathematical controls, not physical records, cloning, measurement,
actualization, independent-party availability, or conditioned success.
-/

namespace IDT.QMClosure.VacuumRecordUncomputeControl

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open NativeVacuumProbabilityFamily RawNetworkMedialWall
open WeightFreeRawProbability (evalRaw)

def a : ℂ := (1 + Complex.I) / 2
def b : ℂ := (1 - Complex.I) / 2

def input : Fin 4 → ℂ := rawSource 0 1 0

def S : Native (Fin 4) := .pair 0 2 (by decide)
def C : Native (Fin 4) := .permute (Equiv.swap 2 3)

def threePair (i j : Fin 4) (hij : i ≠ j) : Native (Fin 4) :=
  .seq (.seq (.pair i j hij) (.pair i j hij)) (.pair i j hij)

def R : Native (Fin 4) :=
  .seq (threePair 0 2 (by decide)) (threePair 1 3 (by decide))

def unmarked : Native (Fin 4) := .seq S R
def marked : Native (Fin 4) := .seq (.seq S C) R
def uncomputed : Native (Fin 4) := .seq (.seq (.seq S C) C) R

variable (F : ℂ × ℂ → ℂ × ℂ)

theorem threePair_eval (i j : Fin 4) (hij : i ≠ j) (x : Fin 4 → ℂ) :
    evalRaw F (threePair i j hij) x = fun k =>
      if k = i then (F (F (F (x i, x j)))).1
      else if k = j then (F (F (F (x i, x j)))).2 else x k := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [threePair, evalRaw, Ne.symm hij]
  · by_cases hkj : k = j
    · subst k
      simp [threePair, evalRaw, Ne.symm hij]
    · simp [threePair, evalRaw, hki, hkj]

/-- C is an involution on the entire retained array, for every raw operation. -/
theorem C_involution (x : Fin 4 → ℂ) :
    evalRaw F C (evalRaw F C x) = x := by
  funext i
  simp [C, evalRaw]

variable (hsquare : ∀ p, F (F p) = p.swap)

include hsquare in
/-- The third raw application is derived from square-swap, not postulated. -/
theorem cube (p : ℂ × ℂ) : F (F (F p)) = (F p).swap := hsquare (F p)

include hsquare in
theorem fourth (p : ℂ × ℂ) : F (F (F (F p))) = p := by
  rw [hsquare, hsquare]
  rfl

variable
  (hright : ∀ z, F (z, 0) = NativeMixerEventConeExclusion.mixer (z, 0))
  (hleft : ∀ z, F (0, z) = NativeMixerEventConeExclusion.mixer (0, z))

include hright in
theorem vacuum_right (z : ℂ) : F (z, 0) = (a * z, b * z) := by
  rw [hright]
  apply Prod.ext
  · simpa [a, b, NativeAttenuationCircuit.a, NativeAttenuationCircuit.b] using
      NativeAttenuationCircuit.mixer_fst z 0
  · simpa [a, b, NativeAttenuationCircuit.a, NativeAttenuationCircuit.b] using
      NativeAttenuationCircuit.mixer_snd z 0

include hleft in
theorem vacuum_left (z : ℂ) : F (0, z) = (b * z, a * z) := by
  rw [hleft]
  apply Prod.ext
  · simpa [a, b, NativeAttenuationCircuit.a, NativeAttenuationCircuit.b] using
      NativeAttenuationCircuit.mixer_fst 0 z
  · simpa [a, b, NativeAttenuationCircuit.a, NativeAttenuationCircuit.b] using
      NativeAttenuationCircuit.mixer_snd 0 z

include hsquare hright in
theorem cube_vacuum_right (z : ℂ) : F (F (F (z, 0))) = (b * z, a * z) := by
  rw [cube F hsquare, vacuum_right F hright]
  rfl

include hsquare hleft in
theorem cube_vacuum_left (z : ℂ) : F (F (F (0, z))) = (a * z, b * z) := by
  rw [cube F hsquare, vacuum_left F hleft]
  rfl

include hsquare hright in
/-- Three more literal raw gates undo the split of a one-zero input. -/
theorem cube_after_vacuum (z : ℂ) : F (F (F (a * z, b * z))) = (z, 0) := by
  calc
    _ = F (F (F (F (z, 0)))) := by rw [vacuum_right F hright]
    _ = (z, 0) := fourth F hsquare _

include hsquare hright in
theorem cube_split_unit : F (F (F (a, b))) = (1, 0) := by
  simpa using cube_after_vacuum F hsquare hright 1

include hright in
/-- The actual preparation is the unit-reference basis array at port zero. -/
theorem split_output : prepared F 0 1 (0 : Fin 4) S = ![a, 0, b, 0] := by
  funext i
  fin_cases i <;>
    simp [prepared, rawSource, S, evalRaw, vacuum_right F hright]

include hright in
theorem recorded_output : prepared F 0 1 (0 : Fin 4) (.seq S C) =
    ![a, 0, 0, b] := by
  change evalRaw F C (prepared F 0 1 (0 : Fin 4) S) = _
  rw [split_output F hright]
  funext i
  fin_cases i <;> norm_num [C, evalRaw, Equiv.swap_apply_def, Fin.ext_iff] <;> rfl

include hsquare hright in
theorem R_split_array : evalRaw F R ![a, 0, b, 0] = ![1, 0, 0, 0] := by
  have h02 : evalRaw F (threePair 0 2 (by decide)) ![a, 0, b, 0] =
      ![1, 0, 0, 0] := by
    rw [threePair_eval]
    funext i
    fin_cases i <;> simp [cube_split_unit F hsquare hright]
  change evalRaw F (threePair 1 3 (by decide))
    (evalRaw F (threePair 0 2 (by decide)) ![a, 0, b, 0]) = _
  rw [h02, threePair_eval]
  funext i
  fin_cases i <;> simp [cube_vacuum_right F hsquare hright]

include hsquare hright hleft in
theorem R_recorded_array : evalRaw F R ![a, 0, 0, b] =
    ![1 / 2, 1 / 2, Complex.I / 2, -Complex.I / 2] := by
  have h02 : evalRaw F (threePair 0 2 (by decide)) ![a, 0, 0, b] =
      ![b * a, 0, a * a, b] := by
    rw [threePair_eval]
    funext i
    fin_cases i <;> simp [cube_vacuum_right F hsquare hright]
  change evalRaw F (threePair 1 3 (by decide))
    (evalRaw F (threePair 0 2 (by decide)) ![a, 0, 0, b]) = _
  rw [h02, threePair_eval]
  funext i
  fin_cases i <;> simp [cube_vacuum_left F hsquare hleft] <;>
    apply Complex.ext <;>
    norm_num [a, b, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]

include hsquare hright in
theorem unmarked_output : prepared F 0 1 (0 : Fin 4) unmarked =
    ![1, 0, 0, 0] := by
  change evalRaw F R (prepared F 0 1 (0 : Fin 4) S) = _
  rw [split_output F hright, R_split_array F hsquare hright]

include hsquare hright hleft in
theorem marked_output : prepared F 0 1 (0 : Fin 4) marked =
    ![1 / 2, 1 / 2, Complex.I / 2, -Complex.I / 2] := by
  change evalRaw F R (prepared F 0 1 (0 : Fin 4) (.seq S C)) = _
  rw [recorded_output F hright, R_recorded_array F hsquare hright hleft]

include hsquare hright in
theorem uncomputed_output : prepared F 0 1 (0 : Fin 4) uncomputed =
    ![1, 0, 0, 0] := by
  change evalRaw F R (evalRaw F C (evalRaw F C (evalRaw F S input))) = _
  rw [C_involution]
  exact unmarked_output F hsquare hright

/-! The following readouts use only the already supplied nonlinear gate's law. -/

open BalancedNonmedialMixerCore BalancedNonmedialMixerWitness

theorem balanced_marked_probability (i : Fin 4) :
    rawLaw.prob 0 marked i = 1 / 4 := by
  rw [raw_probability_eq_own_normSq,
    marked_output BalancedNonmedialMixerCore.gate BalancedNonmedialMixerCore.gate_square
      native_vacuum_right native_vacuum_left]
  fin_cases i <;>
    norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im]

theorem balanced_unmarked_probability (i : Fin 4) :
    rawLaw.prob 0 unmarked i = if i = 0 then 1 else 0 := by
  rw [raw_probability_eq_own_normSq,
    unmarked_output BalancedNonmedialMixerCore.gate BalancedNonmedialMixerCore.gate_square
      native_vacuum_right]
  fin_cases i <;> norm_num

theorem balanced_uncomputed_probability (i : Fin 4) :
    rawLaw.prob 0 uncomputed i = if i = 0 then 1 else 0 := by
  rw [raw_probability_eq_own_normSq,
    uncomputed_output BalancedNonmedialMixerCore.gate BalancedNonmedialMixerCore.gate_square
      native_vacuum_right]
  fin_cases i <;> norm_num

/-- The row is precisely the two retained ports labelled 00 and 01. -/
def rowWeight (c : Native (Fin 4)) : ℝ := rawLaw.prob 0 c 0 + rawLaw.prob 0 c 1

theorem balanced_unmarked_row : rowWeight unmarked = 1 := by
  norm_num [rowWeight, balanced_unmarked_probability]

theorem balanced_marked_row : rowWeight marked = 1 / 2 := by
  norm_num [rowWeight, balanced_marked_probability]

theorem balanced_uncomputed_row : rowWeight uncomputed = 1 := by
  norm_num [rowWeight, balanced_uncomputed_probability]

/-- Passing this exact weak protocol is compatible with failure of mediality. -/
theorem protocol_passes_without_mediality :
    (∀ i : Fin 4, rawLaw.prob 0 marked i = 1 / 4) ∧
    rowWeight unmarked = 1 ∧ rowWeight marked = 1 / 2 ∧
    rowWeight uncomputed = 1 ∧ ¬ FirstChannelMedial BalancedNonmedialMixerCore.gate :=
  ⟨balanced_marked_probability, balanced_unmarked_row, balanced_marked_row,
    balanced_uncomputed_row, BalancedNonmedialMixerWitness.gate_not_medial⟩

end
end IDT.QMClosure.VacuumRecordUncomputeControl
