import Proofs.QMClosure.ResponseSignatureControls
import Proofs.QMClosure.NativeReferenceSeparation
import Proofs.QMClosure.NativeRecipeContextRealization

/-!
# Recipe observation boundaries for supplied Boolean signatures

This is a mathematical supplied scalar model with an ideal exact Boolean
signature. Arbitrary fixed references in full response contexts are distinct
from actual finite same-source recipes. A point test outside the unit disk
separates the full raw scalar carrier contextually, yet is false on every
finite native basis output, including every compiled recipe and ancillary
output. This countermodel retains a supplied six-field probability law.

In contrast, the zero test with all recipe-indexed comparison settings separates
recipe amplitudes. Each comparison retains an actual full circuit with distinct
sum and difference ports. It constructs a program from known supplied recipes;
it is not a processor for independently supplied unknown tokens or free copying.

Neither result asserts physical reference or detector availability, finite
precision robustness, actualization, or QM closure. The negative result concerns
universal arbitrary-signature recipe completeness, not a physical no-go theorem.
The existing fixed-four zero-test nonseparation result is unchanged; there is no
minimality claim.
-/

namespace IDT.QMClosure.NativeRecipeObservationBoundary

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open ResponseContextQuotient OperationalContextQuotient
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open NativeGaussianResponse NativeRecipeContextRealization
open NativeMixerEventConeExclusion (mixer)
open NativeAttenuationCircuit (a b mixer_fst)

def pointTest (q z : ℂ) : Bool := by
  classical
  exact decide (z = q)

@[simp] theorem pointTest_eq_true_iff (q z : ℂ) :
    pointTest q z = true ↔ z = q := by
  classical
  simp [pointTest]

@[simp] theorem pointTest_self (q : ℂ) : pointTest q q = true := by
  simp [pointTest]

/-- For fixed q and comparison x, the reference is fixed; y occurs once. -/
def pointReference (q x : ℂ) : ℂ := (1 + Complex.I) * q - Complex.I * x

theorem first_point_reference (q x y : ℂ) :
    (mixer (y, pointReference q x)).1 = q + a * (y - x) := by
  rw [mixer_fst]
  apply Complex.ext <;>
    norm_num [pointReference, a, b, Complex.div_re, Complex.div_im] <;> ring

/-- Every point test, not only the zero test, has separating full contexts. -/
theorem point_responseEq_iff_eq (q x y : ℂ) :
    ResponseEq mixer (pointTest q) x y ↔ x = y := by
  constructor
  · intro h
    have ht := h (.left .first .hole (pointReference q x))
    change pointTest q (mixer (x, pointReference q x)).1 =
      pointTest q (mixer (y, pointReference q x)).1 at ht
    rw [first_point_reference, first_point_reference, sub_self, mul_zero,
      add_zero, pointTest_self] at ht
    have hz : q + a * (y - x) = q := (pointTest_eq_true_iff _ _).mp ht.symm
    have hz' : a * (y - x) = 0 := by
      have hh := congrArg (fun z : ℂ => z - q) hz
      simpa only [add_sub_cancel_left, sub_self] using hh
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hz').resolve_left
      ResponseSignatureControls.native_a_ne_zero)).symm
  · rintro rfl
    intro _
    rfl

def pointData (q : ℂ) : Data ℂ Bool where
  chosenZero := 0
  operation := mixer
  signature := pointTest q
  square p := by
    constructor
    · apply (point_responseEq_iff_eq q _ _).mpr
      exact congrArg Prod.fst (NativeMixerEventConeExclusion.mixer_square p)
    · apply (point_responseEq_iff_eq q _ _).mpr
      exact congrArg Prod.snd (NativeMixerEventConeExclusion.mixer_square p)
  medial w x y z := (point_responseEq_iff_eq q _ _).mpr
    (ResponseSignatureControls.native_medial w x y z)

theorem point_observedTransparent (q : ℂ) : ObservedTransparent (pointData q) := by
  intro x
  apply (point_responseEq_iff_eq q _ _).mpr
  exact congrArg Prod.fst (NativeMixerEventConeExclusion.mixer_transparent x)

theorem point_classOf_injective (q : ℂ) : Function.Injective (pointData q).classOf := by
  intro x y h
  exact (point_responseEq_iff_eq q x y).mp (Quotient.exact h)

theorem point_quotient_infinite (q : ℂ) : Infinite (pointData q).Space := by
  refine ⟨fun hfinite => ?_⟩
  letI : Finite (pointData q).Space := hfinite
  exact (Finite.of_injective (pointData q).classOf (point_classOf_injective q)).false

/-! ## All six law fields and the identical probability field -/

theorem point_prepared (q : ℂ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) :
    ResponseNativeProbabilitySelection.prepared (pointData q) 1 s c =
      c.eval (source s) := by
  unfold ResponseNativeProbabilitySelection.prepared
  change WeightFreeRawProbability.evalRaw mixer c (source s) = _
  exact ResponseSignatureControls.evalRaw_native c (source s)

def pointLawOfScalar (q : ℂ) (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law (pointData q) 1 where
  prob := L.prob
  nonnegative := L.nonnegative
  normalized := L.normalized
  prepared_eq s c e h := by
    apply L.prepared_eq s c e
    have hraw : ResponseNativeProbabilitySelection.prepared (pointData q) 1 s c =
        ResponseNativeProbabilitySelection.prepared (pointData q) 1 s e := by
      funext i
      exact (point_responseEq_iff_eq q _ _).mp (h i)
    simpa only [point_prepared] using hraw
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

theorem pointLawOfScalar_probability (q : ℂ) (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob ℂ Bool (pointData q) 1
      (pointLawOfScalar q L) = @NativeVacuumProbabilityFamily.Law.prob L := rfl

/-- Separate consistency witness; separation has no canonical-law premise. -/
def canonicalPointLaw (q : ℂ) := pointLawOfScalar q NativeVacuumProbabilityFamily.canonicalLaw

theorem point_law_nonempty (q : ℂ) :
    Nonempty (ResponseNativeProbabilitySelection.Law (pointData q) 1) :=
  ⟨canonicalPointLaw q⟩

/-! ## Every actual finite basis output stays in the unit disk -/

theorem pointTest_false_of_normSq_le_one (q z : ℂ)
    (hq : 1 < Complex.normSq q) (hz : Complex.normSq z ≤ 1) :
    pointTest q z = false := by
  have hne : z ≠ q := by
    intro h
    rw [h] at hz
    linarith
  classical
  simp [pointTest, hne]

theorem native_output_pointTest_false (q : ℂ) (hq : 1 < Complex.normSq q)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι) :
    pointTest q (c.eval (source s) i) = false :=
  pointTest_false_of_normSq_le_one q _ hq
    (NativeSingleSourceReferenceWall.output_normSq_le_one s c i)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem event_pointTest_false (q : ℂ) (hq : 1 < Complex.normSq q)
    (s : ι) (e : Event ι) : pointTest q (amplitude s e) = false :=
  native_output_pointTest_false q hq (sourceAt s e.level) e.circuit e.port

theorem realization_pointTest_false (q : ℂ) (hq : 1 < Complex.normSq q)
    (s : ι) (C : Context (Event ι)) (e E : Event ι) (_h : Realizes s C e E) :
    pointTest q (amplitude s E) = false := event_pointTest_false q hq s E

theorem realize_pointTest_false (q : ℂ) (hq : 1 < Complex.normSq q)
    (s : ι) (C : Context (Event ι)) (e : Event ι) :
    pointTest q (amplitude s (realize s C e)) = false :=
  event_pointTest_false q hq s (realize s C e)

/-- Includes both marked ports and every retained ancillary output. -/
theorem pairedSetting_all_outputs_false (q : ℂ) (hq : 1 < Complex.normSq q)
    (s : ι) (e r : Event ι) (p : NativeReferenceSeparation.PairedSetting s e r)
    (k : Tower ι (p.baseLevel + 1)) :
    pointTest q (p.circuit.eval (source (sourceAt s (p.baseLevel + 1))) k) = false :=
  native_output_pointTest_false q hq _ p.circuit k

/-- Only observations of the actual attenuated compiler outputs are compared. -/
def RecipeObservationEq (q : ℂ) (s : ι) (e f : Event ι) : Prop :=
  ∀ C : Context (Event ι),
    pointTest q (amplitude s (realize s C e)) =
      pointTest q (amplitude s (realize s C f))

theorem outside_point_all_recipe_observations_equal (q : ℂ)
    (hq : 1 < Complex.normSq q) (s : ι) (e f : Event ι) :
    RecipeObservationEq q s e f := by
  intro C
  rw [realize_pointTest_false q hq, realize_pointTest_false q hq]

theorem half_quarter_amplitudes_distinct (s : ι) :
    amplitude s (NativeReferenceSeparation.halfControl s) ≠
      amplitude s (NativeReferenceSeparation.quarterControl s) := by
  rw [NativeReferenceSeparation.halfControl_amplitude,
    NativeReferenceSeparation.quarterControl_amplitude]
  intro h
  have hr := congrArg Complex.re h
  norm_num [Complex.div_re, Complex.div_im] at hr

theorem half_quarter_not_responseEq (q : ℂ) (s : ι) :
    ¬ ResponseEq mixer (pointTest q)
      (amplitude s (NativeReferenceSeparation.halfControl s))
      (amplitude s (NativeReferenceSeparation.quarterControl s)) := by
  intro h
  exact half_quarter_amplitudes_distinct s ((point_responseEq_iff_eq q _ _).mp h)

theorem point_two_normSq : Complex.normSq (2 : ℂ) = 4 := by norm_num

/-- An actual pair of recipes defeats universal arbitrary-signature recipe
completeness even with transparent data and a supplied law consistency witness. -/
theorem arbitrary_signature_recipe_completeness_fails (s : ι) :
    ObservedTransparent (pointData 2) ∧
    Nonempty (ResponseNativeProbabilitySelection.Law (pointData 2) 1) ∧
    RecipeObservationEq 2 s (NativeReferenceSeparation.halfControl s)
      (NativeReferenceSeparation.quarterControl s) ∧
    ¬ ResponseEq mixer (pointTest 2)
      (amplitude s (NativeReferenceSeparation.halfControl s))
      (amplitude s (NativeReferenceSeparation.quarterControl s)) := by
  refine ⟨point_observedTransparent 2, point_law_nonempty 2, ?_,
    half_quarter_not_responseEq 2 s⟩
  exact outside_point_all_recipe_observations_equal 2
    (by rw [point_two_normSq]; norm_num) s _ _

theorem point_two_unit_reference : pointReference 2 1 = 2 + Complex.I := by
  unfold pointReference
  ring

theorem point_two_unit_reference_normSq : Complex.normSq (pointReference 2 1) = 5 := by
  rw [point_two_unit_reference]
  norm_num [Complex.normSq_apply]

/-- The arbitrary comparison reference used by the full-context proof need
not be a reachable unit-source recipe, even at arbitrary finite width. -/
theorem point_two_unit_reference_not_reachable :
    ¬ NativeSingleSourceReferenceWall.ScalarReachable (pointReference 2 1) := by
  intro h
  have hb := NativeSingleSourceReferenceWall.scalarReachable_normSq_le_one h
  rw [point_two_unit_reference_normSq] at hb
  norm_num at hb

/-! ## Positive companion: all recipe-indexed exact-zero comparisons -/

def zeroComparison (s : ι) (e r : Event ι) : Bool :=
  ResponseSignatureControls.zeroTest
    (amplitude s (NativeReferenceSeparation.pairedSetting s e r).differenceEvent)

theorem zeroComparison_true_iff (s : ι) (e r : Event ι) :
    zeroComparison s e r = true ↔ amplitude s e = amplitude s r := by
  unfold zeroComparison
  rw [ResponseSignatureControls.zeroTest_eq_true_iff]
  change (NativeReferenceSeparation.pairedSetting s e r).circuit.eval
    (source (sourceAt s ((NativeReferenceSeparation.pairedSetting s e r).baseLevel + 1)))
    (NativeReferenceSeparation.pairedSetting s e r).differencePort = 0 ↔ _
  rw [(NativeReferenceSeparation.pairedSetting s e r).difference_amplitude]
  simp [NativeReferenceSeparation.differenceOutput, div_eq_zero_iff,
    mul_eq_zero, sub_eq_zero, Complex.I_ne_zero]

theorem zeroComparison_eq_decide (s : ι) (e r : Event ι) :
    zeroComparison s e r = decide (amplitude s e = amplitude s r) := by
  classical
  cases hb : zeroComparison s e r with
  | false =>
    have hne : amplitude s e ≠ amplitude s r := by
      intro h
      have ht := (zeroComparison_true_iff s e r).mpr h
      rw [hb] at ht
      contradiction
    simp [hne]
  | true =>
    have he := (zeroComparison_true_iff s e r).mp hb
    simp [he]

/-- The reference recipe e itself suffices for the forward implication. -/
theorem all_zeroComparisons_eq_iff (s : ι) (e f : Event ι) :
    (∀ r : Event ι, zeroComparison s e r = zeroComparison s f r) ↔
      amplitude s e = amplitude s f := by
  constructor
  · intro h
    have he : zeroComparison s e e = true := (zeroComparison_true_iff s e e).mpr rfl
    have hf : zeroComparison s f e = true := (h e).symm.trans he
    exact ((zeroComparison_true_iff s f e).mp hf).symm
  · intro h r
    simp only [zeroComparison_eq_decide, h]

/-- Retained circuit witness: no amplitude search or scalar-only reference
substitution is used to assert realizability of the zero comparison. -/
theorem zeroComparison_retained_circuit (s : ι) (e r : Event ι) :
    ∃ n : ℕ, ∃ c : Native (Tower ι (n + 1)), ∃ i j : Tower ι (n + 1),
      i ≠ j ∧
      c.eval (source (sourceAt s (n + 1))) i =
        NativeReferenceSeparation.sumOutput (amplitude s e) (amplitude s r) ∧
      c.eval (source (sourceAt s (n + 1))) j =
        NativeReferenceSeparation.differenceOutput (amplitude s e) (amplitude s r) ∧
      zeroComparison s e r = ResponseSignatureControls.zeroTest
        (c.eval (source (sourceAt s (n + 1))) j) := by
  let p := NativeReferenceSeparation.pairedSetting s e r
  exact ⟨p.baseLevel, p.circuit, p.sumPort, p.differencePort,
    p.distinct, p.sum_amplitude, p.difference_amplitude, rfl⟩

end
end IDT.QMClosure.NativeRecipeObservationBoundary
