import Proofs.QMClosure.NativeThreeWireResidueProbability
import Proofs.QMClosure.NativeAttenuationCircuit

/-!
# A finite four-wire extension wall for the three-wire residue probability

Two literal four-wire native words prepare exactly the same complex state.
Three explicit probability agreements with vacuum-padded three-wire words,
nonnegativity, normalization, spectator-pair locality, and prepared-state
equivalence are inconsistent. The contradiction needs only these two padded
words; no general circuit-padding or arbitrary-width synthesis theorem is used.

This excludes the stated extension of the specific residue countermodel. It
does not prove uniqueness of the Born rule, a physical readout law, or QM closure.
-/

namespace IDT.QMClosure.NativeThreeWireProbabilityExtensionWall

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

open MixerGeneratedProcessWall NativeMixerEventConeExclusion
open scoped BigOperators

attribute [local simp] Fin.ext_iff

abbrev Native4Circuit := Circuit (ι := Fin 4) mixer

def source4 : Fin 4 → ℂ := Pi.single 0 1
def pair01 : Native4Circuit := .pair 0 1 (by decide)
def pair02 : Native4Circuit := .pair 0 2 (by decide)
def pair03 : Native4Circuit := .pair 0 3 (by decide)
def pair12 : Native4Circuit := .pair 1 2 (by decide)
def pair13 : Native4Circuit := .pair 1 3 (by decide)

def initial : Native4Circuit := .seq pair01 pair02
def middle : Native4Circuit := .seq initial pair03

/-- The suffix touches only ports zero, one, and two. -/
def spectatorSuffix (c : Native4Circuit) : Native4Circuit :=
  .seq (.seq (.seq (.seq c pair12) pair02) pair12) pair02

def leftWord : Native4Circuit := spectatorSuffix middle
def rightWord : Native4Circuit :=
  .seq (.seq (.seq pair01 pair13) pair01) (.permute (Equiv.swap 0 3))

def commonState : Fin 4 → ℂ :=
  ![-Complex.I / 2, (3 + Complex.I) / 4, 0, (1 + Complex.I) / 4]

private theorem swap03_table :
    ∀ i : Fin 4, Equiv.swap 0 3 i = (![3, 1, 2, 0] : Fin 4 → Fin 4) i := by decide

private theorem swap02_table :
    ∀ i : Fin 3, Equiv.swap 0 2 i = (![2, 1, 0] : Fin 3 → Fin 3) i := by decide

theorem left_prepares : leftWord.eval source4 = commonState := by
  ext i
  fin_cases i <;> apply Complex.ext <;>
    norm_num [leftWord, spectatorSuffix, middle, initial, pair01, pair02, pair03,
      pair12, source4, commonState, Circuit.eval, pairGate, pairReplace,
      Pi.single_apply, NativeAttenuationCircuit.mixer_fst, NativeAttenuationCircuit.mixer_snd,
      NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
      NativeThreeWireLocality.a, NativeThreeWireLocality.b,
      NativeMixerInfiniteOrder.a, NativeMixerInfiniteOrder.b,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem right_prepares : rightWord.eval source4 = commonState := by
  ext i
  fin_cases i <;> apply Complex.ext <;>
    norm_num [rightWord, pair01, pair13, source4, commonState, Circuit.eval,
      pairGate, pairReplace, Pi.single_apply, swap03_table,
      NativeAttenuationCircuit.mixer_fst, NativeAttenuationCircuit.mixer_snd,
      NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
      NativeThreeWireLocality.a, NativeThreeWireLocality.b,
      NativeMixerInfiniteOrder.a, NativeMixerInfiniteOrder.b,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem prepared_states_equal : leftWord.eval source4 = rightWord.eval source4 :=
  left_prepares.trans right_prepares.symm

/-- Generic structural premises, separate from the three special probability facts. -/
structure BridgePremises (P : Native4Circuit → Fin 4 → ℝ) : Prop where
  nonnegative : ∀ c i, 0 ≤ P c i
  normalized : ∀ c, ∑ i, P c i = 1
  prepared_eq : ∀ c d, c.eval source4 = d.eval source4 → P c = P d
  spectator_pair : ∀ c (i j s : Fin 4) (hij : i ≠ j),
    s ≠ i → s ≠ j → P (.seq c (.pair i j hij)) s = P c s

/-- The contradiction consumes exactly three imported finite probability values. -/
theorem no_four_wire_law_with_three_facts
    (P : Native4Circuit → Fin 4 → ℝ) (hP : BridgePremises P)
    (h1 : P initial 1 = 1 / 2) (h2 : P initial 2 = 1 / 2)
    (h3 : P rightWord 3 = 1) : False := by
  have hm1 : P middle 1 = 1 / 2 := by
    change P (.seq initial (.pair 0 3 (by decide))) 1 = _
    rw [hP.spectator_pair initial 0 3 1 (by decide) (by decide) (by decide), h1]
  have hm2 : P middle 2 = 1 / 2 := by
    change P (.seq initial (.pair 0 3 (by decide))) 2 = _
    rw [hP.spectator_pair initial 0 3 2 (by decide) (by decide) (by decide), h2]
  have hn : P middle 0 + P middle 1 + P middle 2 + P middle 3 = 1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hP.normalized middle
  have hm3 : P middle 3 = 0 := by
    linarith [hP.nonnegative middle 0, hP.nonnegative middle 3]
  have h12 (c : Native4Circuit) : P (.seq c pair12) 3 = P c 3 :=
    hP.spectator_pair c 1 2 3 (by decide) (by decide) (by decide)
  have h02 (c : Native4Circuit) : P (.seq c pair02) 3 = P c 3 :=
    hP.spectator_pair c 0 2 3 (by decide) (by decide) (by decide)
  have hl3 : P leftWord 3 = 0 := by
    simp only [leftWord, spectatorSuffix, h02, h12, hm3]
  have he : P leftWord 3 = P rightWord 3 :=
    congrFun (hP.prepared_eq leftWord rightWord prepared_states_equal) 3
  linarith

/-! The two concrete three-wire words and their checked scalar probabilities. -/

def initial3 : NativeCircuit := .seq gate01 gate02
def right3 : NativeCircuit :=
  .seq (.seq (.seq gate01 gate12) gate01) (.permute (Equiv.swap 0 2))

def pad012 (v : Fin 3 → ℂ) : Fin 4 → ℂ := ![v 0, v 1, v 2, 0]
def pad013 (v : Fin 3 → ℂ) : Fin 4 → ℂ := ![v 0, v 1, 0, v 2]

/-- The initial four-wire word is the first three-wire word with one vacuum port. -/
theorem initial_is_padded : initial.eval source4 =
    pad012 (initial3.eval NativeThreeWireResidueProbability.source) := by
  ext i
  fin_cases i <;> apply Complex.ext <;>
    norm_num [initial, pair01, pair02, initial3, gate01, gate02, source4,
      pad012, NativeThreeWireResidueProbability.source, Circuit.eval,
      pairGate, pairReplace, Pi.single_apply,
      NativeThreeWireResidueProbability.mixer_linear,
      NativeThreeWireLocality.a, NativeThreeWireLocality.b,
      NativeMixerInfiniteOrder.a, NativeMixerInfiniteOrder.b,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

/-- The short word is the second three-wire word embedded on ports zero, one, three. -/
theorem right_is_padded : rightWord.eval source4 =
    pad013 (right3.eval NativeThreeWireResidueProbability.source) := by
  rw [right_prepares]
  ext i
  fin_cases i <;> apply Complex.ext <;>
    norm_num [-Fin.ext_iff, Matrix.cons_val_two, commonState, right3, gate01, gate12,
      pad013, NativeThreeWireResidueProbability.source, Circuit.eval,
      pairGate, pairReplace, Pi.single_apply, swap02_table,
      show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
      show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
      NativeAttenuationCircuit.mixer_fst, NativeAttenuationCircuit.mixer_snd,
      NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem initial3_probability_one :
    NativeThreeWireResidueProbability.probability initial3 1 = 1 / 2 := by
  have h : NativeThreeWireResidueProbability.qUnits
      (NativeThreeWireResidueProbability.preparedResidue initial3 1) = 1 := by decide
  simp [NativeThreeWireResidueProbability.probability,
    NativeThreeWireResidueProbability.q, h]

theorem initial3_probability_two :
    NativeThreeWireResidueProbability.probability initial3 2 = 1 / 2 := by
  have h : NativeThreeWireResidueProbability.qUnits
      (NativeThreeWireResidueProbability.preparedResidue initial3 2) = 1 := by decide
  simp [NativeThreeWireResidueProbability.probability,
    NativeThreeWireResidueProbability.q, h]

theorem right3_probability_two :
    NativeThreeWireResidueProbability.probability right3 2 = 1 := by
  have h : NativeThreeWireResidueProbability.qUnits
      (NativeThreeWireResidueProbability.preparedResidue right3 2) = 2 := by decide
  simp [NativeThreeWireResidueProbability.probability,
    NativeThreeWireResidueProbability.q, h]

/-- Only these three agreements are required of a proposed vacuum extension. -/
structure FiniteVacuumAgreement (P : Native4Circuit → Fin 4 → ℝ) : Prop where
  initial_one : P initial 1 = NativeThreeWireResidueProbability.probability initial3 1
  initial_two : P initial 2 = NativeThreeWireResidueProbability.probability initial3 2
  right_three : P rightWord 3 = NativeThreeWireResidueProbability.probability right3 2

/-- The specific three-wire law has no extension satisfying these finite premises. -/
theorem no_residue_probability_extension
    (P : Native4Circuit → Fin 4 → ℝ) (hP : BridgePremises P)
    (ha : FiniteVacuumAgreement P) : False :=
  no_four_wire_law_with_three_facts P hP
    (ha.initial_one.trans initial3_probability_one)
    (ha.initial_two.trans initial3_probability_two)
    (ha.right_three.trans right3_probability_two)

/-! A quantitative restriction on every law satisfying the structural premises. -/

def attenuationWord : Native4Circuit := .seq pair01 pair13
def balancedWord : Native4Circuit := .seq (.seq attenuationWord pair02) pair03
def balancedState : Fin 4 → ℂ := ![-1 / 2, 1 / 2, 1 / 2, 1 / 2]

theorem balanced_prepares : balancedWord.eval source4 = balancedState := by
  ext i
  fin_cases i <;> apply Complex.ext <;>
    norm_num [balancedWord, attenuationWord, pair01, pair13, pair02, pair03,
      source4, balancedState, Circuit.eval, pairGate, pairReplace, Pi.single_apply,
      NativeAttenuationCircuit.mixer_fst, NativeAttenuationCircuit.mixer_snd,
      NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

def OutputPermutationCovariance (P : Native4Circuit → Fin 4 → ℝ) : Prop :=
  ∀ c (e : Equiv.Perm (Fin 4)) i, P (.seq c (.permute e)) i = P c (e i)

/-- Equal prepared coordinates have equal probabilities under output covariance. -/
theorem equal_coordinate_probabilities
    (P : Native4Circuit → Fin 4 → ℝ) (hP : BridgePremises P)
    (hperm : OutputPermutationCovariance P) (c : Native4Circuit) (i j : Fin 4)
    (hcoord : c.eval source4 i = c.eval source4 j) : P c i = P c j := by
  have he : (Circuit.seq c (.permute (Equiv.swap i j))).eval source4 = c.eval source4 := by
    ext s
    change c.eval source4 (Equiv.swap i j s) = c.eval source4 s
    by_cases hsi : s = i
    · subst s
      simpa only [Equiv.swap_apply_left] using hcoord.symm
    by_cases hsj : s = j
    · subst s
      simpa only [Equiv.swap_apply_right] using hcoord
    · simp only [Equiv.swap_apply_def, if_neg hsi, if_neg hsj]
  have hstate := congrFun (hP.prepared_eq
    (.seq c (.permute (Equiv.swap i j))) c he) i
  have hcov := hperm c (Equiv.swap i j) i
  rw [Equiv.swap_apply_left] at hcov
  exact hstate.symm.trans hcov

/-- A universal finite bound under the stated premises, without residue calibration. -/
theorem attenuation_probability_bound
    (P : Native4Circuit → Fin 4 → ℝ) (hP : BridgePremises P)
    (hperm : OutputPermutationCovariance P) :
    0 ≤ P attenuationWord 1 ∧ P attenuationWord 1 ≤ 1 / 3 := by
  have h12 : P balancedWord 1 = P balancedWord 2 :=
    equal_coordinate_probabilities P hP hperm balancedWord 1 2
      (by rw [balanced_prepares]; rfl)
  have h13 : P balancedWord 1 = P balancedWord 3 :=
    equal_coordinate_probabilities P hP hperm balancedWord 1 3
      (by rw [balanced_prepares]; rfl)
  have hkeep : P balancedWord 1 = P attenuationWord 1 := by
    change P (.seq (.seq attenuationWord (.pair 0 2 (by decide)))
      (.pair 0 3 (by decide))) 1 = _
    rw [hP.spectator_pair _ 0 3 1 (by decide) (by decide) (by decide),
      hP.spectator_pair _ 0 2 1 (by decide) (by decide) (by decide)]
  have hn : P balancedWord 0 + P balancedWord 1 +
      P balancedWord 2 + P balancedWord 3 = 1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hP.normalized balancedWord
  exact ⟨hP.nonnegative attenuationWord 1,
    by linarith [hP.nonnegative balancedWord 0]⟩

end
end IDT.QMClosure.NativeThreeWireProbabilityExtensionWall
