import Proofs.QMClosure.NativeSingleSourceReferenceWall
import Proofs.QMClosure.NativeProbabilityUniqueness

/-!
# Exact scalar separation by two native reference settings

The algebraic core has no probability-law premise. Two fixed references, `1`
and `i/2`, recover the real coordinate and half the imaginary coordinate by
signed differences of unrenormalized output squared norms. The four selected
weights are not a normalized distribution on the selected ports.

Every realized setting retains one actual circuit, two distinct ports, its
literal marked source, and the full ancillary array. The settings are separate
recipes; no common history across settings or processing of an independently
supplied unknown token is asserted. The references use existing preparation
lemmas, and complex coordinates are the existing scalar coefficient semantics.

The probability corollary requires a supplied native `Law`. A contrast is a
signed difference of two event probabilities, not a negative event probability.
No physical reference availability, arbitrary-carrier tomography, minimality,
finite-resolution or noise guarantee, actualization, or full-QM claim follows.
-/

namespace IDT.QMClosure.NativeReferenceSeparation

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open NativeGaussianResponse NativeCoherentBranchDilation

def sumOutput (z t : ℂ) : ℂ := (z + t) / 2

def differenceOutput (z t : ℂ) : ℂ := Complex.I * (z - t) / 2

def settingWeights (z t : ℂ) : ℝ × ℝ :=
  (Complex.normSq (sumOutput z t), Complex.normSq (differenceOutput z t))

/-- No conditioning or renormalization of the selected pair is performed. -/
def contrast (z t : ℂ) : ℝ := (settingWeights z t).1 - (settingWeights z t).2

theorem contrast_identity (z t : ℂ) : contrast z t = (z * star t).re := by
  norm_num [contrast, settingWeights, sumOutput, differenceOutput,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]
  ring

theorem contrast_unit (z : ℂ) : contrast z 1 = z.re := by
  simpa using contrast_identity z 1

theorem contrast_quadrature (z : ℂ) :
    contrast z (Complex.I / 2) = z.im / 2 := by
  rw [contrast_identity]
  norm_num [Complex.mul_re, Complex.div_re, Complex.div_im]
  ring

/-- Two contrasts, each obtained from two weights of one setting. -/
def profile (z : ℂ) : ℝ × ℝ := (contrast z 1, contrast z (Complex.I / 2))

theorem profile_coordinates (z : ℂ) : profile z = (z.re, z.im / 2) := by
  simp only [profile, contrast_unit, contrast_quadrature]

theorem profile_injective : Function.Injective profile := by
  intro z w h
  rw [profile_coordinates, profile_coordinates] at h
  have hr := congrArg Prod.fst h
  have hi := congrArg Prod.snd h
  change z.re = w.re at hr
  change z.im / 2 = w.im / 2 at hi
  apply Complex.ext
  · exact hr
  · linarith

theorem profile_eq_iff (z w : ℂ) : profile z = profile w ↔ z = w :=
  ⟨fun h => profile_injective h, fun h => congrArg profile h⟩

def fourWeightProfile (z : ℂ) : (ℝ × ℝ) × (ℝ × ℝ) :=
  (settingWeights z 1, settingWeights z (Complex.I / 2))

theorem fourWeightProfile_eq_iff (z w : ℂ) :
    fourWeightProfile z = fourWeightProfile w ↔ z = w := by
  constructor
  · intro h
    apply profile_injective
    exact congrArg (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      (p.1.1 - p.1.2, p.2.1 - p.2.2)) h
  · intro h
    exact congrArg fourWeightProfile h

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A pair certificate retains a single entire native circuit and its distinct
ports. It is stronger than two unrelated scalar reachability assertions. -/
structure PairedSetting (s : ι) (e reference : Event ι) where
  baseLevel : ℕ
  circuit : Native (Tower ι (baseLevel + 1))
  sumPort : Tower ι (baseLevel + 1)
  differencePort : Tower ι (baseLevel + 1)
  distinct : sumPort ≠ differencePort
  sum_amplitude :
    circuit.eval (source (sourceAt s (baseLevel + 1))) sumPort =
      sumOutput (amplitude s e) (amplitude s reference)
  difference_amplitude :
    circuit.eval (source (sourceAt s (baseLevel + 1))) differencePort =
      differenceOutput (amplitude s e) (amplitude s reference)

/-- Witness selection uses the existing exact recipe theorem, with no search
over circuits by output amplitude and no probability law. -/
theorem pairedSetting_exists (s : ι) (e reference : Event ι) :
    Nonempty (PairedSetting s e reference) := by
  obtain ⟨n, c, i, j, hij, hs, hd⟩ :=
    NativeSingleSourceReferenceWall.aligned_sum_difference s e reference
  exact ⟨⟨n, c, i, j, hij, hs, hd⟩⟩

def pairedSetting (s : ι) (e reference : Event ι) : PairedSetting s e reference :=
  Classical.choice (pairedSetting_exists s e reference)

def PairedSetting.sumEvent {s : ι} {e reference : Event ι}
    (p : PairedSetting s e reference) : Event ι :=
  ⟨p.baseLevel + 1, p.circuit, p.sumPort⟩

def PairedSetting.differenceEvent {s : ι} {e reference : Event ι}
    (p : PairedSetting s e reference) : Event ι :=
  ⟨p.baseLevel + 1, p.circuit, p.differencePort⟩

def PairedSetting.weights {s : ι} {e reference : Event ι}
    (p : PairedSetting s e reference) : ℝ × ℝ :=
  (Complex.normSq (p.circuit.eval (source (sourceAt s (p.baseLevel + 1))) p.sumPort),
    Complex.normSq
      (p.circuit.eval (source (sourceAt s (p.baseLevel + 1))) p.differencePort))

omit [Fintype ι] in
theorem PairedSetting.weights_eq {s : ι} {e reference : Event ι}
    (p : PairedSetting s e reference) :
    p.weights = settingWeights (amplitude s e) (amplitude s reference) := by
  simp only [PairedSetting.weights, p.sum_amplitude, p.difference_amplitude,
    settingWeights]

omit [Fintype ι] in
theorem PairedSetting.contrast_eq {s : ι} {e reference : Event ι}
    (p : PairedSetting s e reference) :
    p.weights.1 - p.weights.2 = (amplitude s e * star (amplitude s reference)).re := by
  rw [p.weights_eq]
  exact contrast_identity _ _

def unitReference (s : ι) : Event ι := baseEvent .identity s

omit [Fintype ι] in
theorem unitReference_amplitude (s : ι) : amplitude s (unitReference s) = 1 := by
  change (source (sourceAt s 0)) (sourceAt s 0) = 1
  simp [source, single]

def quadratureReference (s : ι) : Event ι := rotateHalfEvent (unitReference s)

theorem quadratureReference_amplitude (s : ι) :
    amplitude s (quadratureReference s) = Complex.I / 2 := by
  rw [quadratureReference, rotateHalfEvent_amplitude, unitReference_amplitude, mul_one]

/-- These are two separate actual settings, retaining four selected weights in
total. The certificate does not identify their histories. -/
structure Experiment (s : ι) (e : Event ι) where
  unit : PairedSetting s e (unitReference s)
  quadrature : PairedSetting s e (quadratureReference s)

def experiment (s : ι) (e : Event ι) : Experiment s e :=
  ⟨pairedSetting s e (unitReference s), pairedSetting s e (quadratureReference s)⟩

def Experiment.weights {s : ι} {e : Event ι} (x : Experiment s e) :
    (ℝ × ℝ) × (ℝ × ℝ) := (x.unit.weights, x.quadrature.weights)

theorem Experiment.weights_eq {s : ι} {e : Event ι} (x : Experiment s e) :
    x.weights = fourWeightProfile (amplitude s e) := by
  simp only [Experiment.weights, PairedSetting.weights_eq,
    unitReference_amplitude, quadratureReference_amplitude, fourWeightProfile]

/-- Exact scalar equality, for actual events over the same marked source. -/
theorem experiment_weights_eq_iff (s : ι) (e f : Event ι)
    (x : Experiment s e) (y : Experiment s f) :
    x.weights = y.weights ↔ amplitude s e = amplitude s f := by
  rw [x.weights_eq, y.weights_eq, fourWeightProfile_eq_iff]

/-! ## Separate supplied-law probability transfer -/

def PairedSetting.probabilityContrast {s : ι} {e reference : Event ι}
    (p : PairedSetting s e reference) (L : Law) : ℝ :=
  L.prob (sourceAt s (p.baseLevel + 1)) p.circuit p.sumPort -
    L.prob (sourceAt s (p.baseLevel + 1)) p.circuit p.differencePort

theorem PairedSetting.probabilityContrast_eq {s : ι} {e reference : Event ι}
    (p : PairedSetting s e reference) (L : Law) :
    p.probabilityContrast L =
      (amplitude s e * star (amplitude s reference)).re := by
  unfold PairedSetting.probabilityContrast
  rw [NativeProbabilityUniqueness.native_probability_eq_normSq L _ p.circuit p.sumPort,
    NativeProbabilityUniqueness.native_probability_eq_normSq L _ p.circuit p.differencePort,
    p.sum_amplitude, p.difference_amplitude]
  exact contrast_identity _ _

def Experiment.probabilityProfile {s : ι} {e : Event ι}
    (x : Experiment s e) (L : Law) : ℝ × ℝ :=
  (x.unit.probabilityContrast L, x.quadrature.probabilityContrast L)

theorem Experiment.probabilityProfile_eq {s : ι} {e : Event ι}
    (x : Experiment s e) (L : Law) :
    x.probabilityProfile L = profile (amplitude s e) := by
  simp only [Experiment.probabilityProfile, PairedSetting.probabilityContrast_eq,
    unitReference_amplitude, quadratureReference_amplitude,
    profile, contrast_identity]

theorem experiment_probabilityProfile_eq_iff (L : Law) (s : ι) (e f : Event ι)
    (x : Experiment s e) (y : Experiment s f) :
    x.probabilityProfile L = y.probabilityProfile L ↔ amplitude s e = amplitude s f := by
  rw [x.probabilityProfile_eq L, y.probabilityProfile_eq L, profile_eq_iff]

/-! ## Actual reachable negative controls -/

/-- Both controls come from the same duplicated identity circuit at level one. -/
def positiveControl (s : ι) : Event ι := ⟨1, duplicate .identity, .inl s⟩

def negativeControl (s : ι) : Event ι := ⟨1, duplicate .identity, .inr s⟩

theorem positiveControl_amplitude (s : ι) :
    amplitude s (positiveControl s) = NativeAttenuationCircuit.a := by
  simpa [positiveControl, amplitude, sourceAt, Circuit.eval, source, single] using
    (duplicate_amplitudes s (.identity : Native ι) s).1

theorem negativeControl_amplitude (s : ι) :
    amplitude s (negativeControl s) = NativeAttenuationCircuit.b := by
  simpa [negativeControl, amplitude, sourceAt, Circuit.eval, source, single] using
    (duplicate_amplitudes s (.identity : Native ι) s).2

theorem control_values_distinct : NativeAttenuationCircuit.a ≠ NativeAttenuationCircuit.b := by
  intro h
  have hi := congrArg Complex.im h
  norm_num [NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
    Complex.div_re, Complex.div_im] at hi

theorem control_weight_profiles :
    fourWeightProfile NativeAttenuationCircuit.a = ((5/8, 1/8), (5/16, 1/16)) ∧
    fourWeightProfile NativeAttenuationCircuit.b = ((5/8, 1/8), (1/16, 5/16)) := by
  norm_num [fourWeightProfile, settingWeights, sumOutput, differenceOutput,
    NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

/-- An actual same-source pair of recipes defeats the single unit setting. -/
theorem actual_unit_setting_not_separating (s : ι) :
    amplitude s (positiveControl s) ≠ amplitude s (negativeControl s) ∧
    settingWeights (amplitude s (positiveControl s)) 1 =
      settingWeights (amplitude s (negativeControl s)) 1 := by
  rw [positiveControl_amplitude, negativeControl_amplitude]
  refine ⟨control_values_distinct, ?_⟩
  have ha := congrArg Prod.fst control_weight_profiles.1
  have hb := congrArg Prod.fst control_weight_profiles.2
  exact ha.trans hb.symm

def halfControl (s : ι) : Event ι := halfEvent (unitReference s)

def quarterControl (s : ι) : Event ι := halfEvent (halfControl s)

theorem halfControl_amplitude (s : ι) : amplitude s (halfControl s) = (1/2 : ℂ) := by
  rw [halfControl, halfEvent_amplitude, unitReference_amplitude]

theorem quarterControl_amplitude (s : ι) : amplitude s (quarterControl s) = (1/4 : ℂ) := by
  rw [quarterControl, halfEvent_amplitude, halfControl_amplitude]
  norm_num

/-- Exact-zero observations deliberately discard all nonzero magnitudes. -/
def zeroSetting (z t : ℂ) : Bool × Bool :=
  (decide (sumOutput z t = 0), decide (differenceOutput z t = 0))

def zeroProfile (z : ℂ) : (Bool × Bool) × (Bool × Bool) :=
  (zeroSetting z 1, zeroSetting z (Complex.I / 2))

theorem zeroProfile_false_iff (z : ℂ) :
    zeroProfile z = ((false, false), (false, false)) ↔
      (sumOutput z 1 ≠ 0 ∧ differenceOutput z 1 ≠ 0) ∧
      (sumOutput z (Complex.I / 2) ≠ 0 ∧ differenceOutput z (Complex.I / 2) ≠ 0) := by
  simp [zeroProfile, zeroSetting]

theorem half_quarter_zero_profiles :
    zeroProfile (1/2 : ℂ) = ((false, false), (false, false)) ∧
    zeroProfile (1/4 : ℂ) = ((false, false), (false, false)) := by
  norm_num [zeroProfile, zeroSetting, sumOutput, differenceOutput, Complex.ext_iff,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

/-- Distinct actual recipes have the same exact-zero signature. Every selected
test output is nonzero, although the full weight profile separates them. -/
theorem actual_zero_profile_not_separating (s : ι) :
    amplitude s (halfControl s) ≠ amplitude s (quarterControl s) ∧
    zeroProfile (amplitude s (halfControl s)) =
      zeroProfile (amplitude s (quarterControl s)) ∧
    ((sumOutput (amplitude s (halfControl s)) 1 ≠ 0 ∧
      differenceOutput (amplitude s (halfControl s)) 1 ≠ 0) ∧
      (sumOutput (amplitude s (halfControl s)) (Complex.I / 2) ≠ 0 ∧
      differenceOutput (amplitude s (halfControl s)) (Complex.I / 2) ≠ 0)) ∧
    ((sumOutput (amplitude s (quarterControl s)) 1 ≠ 0 ∧
      differenceOutput (amplitude s (quarterControl s)) 1 ≠ 0) ∧
      (sumOutput (amplitude s (quarterControl s)) (Complex.I / 2) ≠ 0 ∧
      differenceOutput (amplitude s (quarterControl s)) (Complex.I / 2) ≠ 0)) := by
  rw [halfControl_amplitude, quarterControl_amplitude]
  refine ⟨?_, half_quarter_zero_profiles.1.trans half_quarter_zero_profiles.2.symm,
    (zeroProfile_false_iff _).mp half_quarter_zero_profiles.1,
    (zeroProfile_false_iff _).mp half_quarter_zero_profiles.2⟩
  intro h
  have hr := congrArg Complex.re h
  norm_num [Complex.div_re, Complex.div_im] at hr

end
end IDT.QMClosure.NativeReferenceSeparation
