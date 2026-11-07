import Proofs.QMClosure.NativeRecipeObservationBoundary
import Proofs.QMClosure.ResponseRecipeComparison

/-!
# Full recipe-profile separation without comparator-vacuum soundness

The supplied mathematical scalar model uses the ideal Boolean signature
`z = 0 or z = t`, with t nonzero. Full arbitrary-reference response equivalence
is literal equality. All reference-recipe comparison profiles also separate
recipe amplitudes, although an individual comparison can have the vacuum
signature without being response-equivalent to vacuum.

The comparison recipes retain their full native circuits and ancillary outputs;
they are constructed from known supplied recipes, not independently supplied
unknown tokens or freely copied physical states. The positive profile result
quantifies over all reference recipes and supplies no fixed universal finite
battery, detector minimality, physical reference/detector availability,
finite-precision robustness, actualization, or QM closure.
-/

namespace IDT.QMClosure.NativeTwoPointObservationControl

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open ResponseContextQuotient OperationalContextQuotient
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily NativeGaussianResponse
open NativeMixerEventConeExclusion (mixer)
open NativeAttenuationCircuit (a)
open NativeRecipeObservationBoundary (first_point_reference pointReference)
open ResponseRecipeContextReflection (originalEvent)
open ResponseRecipeComparison (comparisonEvent responseProfile ComparatorVacuumSound)

def twoPointTest (t z : ℂ) : Bool := by
  classical
  exact decide (z = 0 ∨ z = t)

@[simp] theorem twoPointTest_true_iff (t z : ℂ) :
    twoPointTest t z = true ↔ z = 0 ∨ z = t := by
  classical
  simp [twoPointTest]

@[simp] theorem twoPointTest_zero (t : ℂ) : twoPointTest t 0 = true := by
  simp [twoPointTest]

@[simp] theorem twoPointTest_self (t : ℂ) : twoPointTest t t = true := by
  simp [twoPointTest]

/-- The first context detects displacement from x unless it equals t. A second
context then compares the true response at t with the false response at 2t. -/
theorem twoPoint_responseEq_iff_eq (t : ℂ) (ht : t ≠ 0) (x y : ℂ) :
    ResponseEq mixer (twoPointTest t) x y ↔ x = y := by
  constructor
  · intro h
    have hc := h (.left .first .hole (pointReference 0 x))
    change twoPointTest t (mixer (x, pointReference 0 x)).1 =
      twoPointTest t (mixer (y, pointReference 0 x)).1 at hc
    rw [first_point_reference, first_point_reference, sub_self, mul_zero,
      add_zero, zero_add, twoPointTest_zero] at hc
    have hd := (twoPointTest_true_iff t (a * (y - x))).mp hc.symm
    have hz : a * (y - x) = 0 := by
      rcases hd with hz | hd
      · exact hz
      · have hc' := h (.left .first .hole (pointReference t x))
        change twoPointTest t (mixer (x, pointReference t x)).1 =
          twoPointTest t (mixer (y, pointReference t x)).1 at hc'
        rw [first_point_reference, first_point_reference, sub_self, mul_zero,
          add_zero, twoPointTest_self, hd] at hc'
        have htwice := (twoPointTest_true_iff t (t + t)).mp hc'.symm
        have htzero : t = 0 := by
          rcases htwice with hzero | heq
          · have hmul : (2 : ℂ) * t = 0 := by linear_combination hzero
            exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)
          · linear_combination heq
        exact False.elim (ht htzero)
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
      ResponseSignatureControls.native_a_ne_zero)).symm
  · rintro rfl
    intro _
    rfl

/-- Exact native structural laws imply the observed laws, independently of t. -/
def data (t : ℂ) : Data ℂ Bool where
  chosenZero := 0
  operation := mixer
  signature := twoPointTest t
  square p := by
    constructor
    · intro c
      exact congrArg (fun z => twoPointTest t (c.eval mixer z))
        (congrArg Prod.fst (NativeMixerEventConeExclusion.mixer_square p))
    · intro c
      exact congrArg (fun z => twoPointTest t (c.eval mixer z))
        (congrArg Prod.snd (NativeMixerEventConeExclusion.mixer_square p))
  medial w x y z := by
    intro c
    exact congrArg (fun u => twoPointTest t (c.eval mixer u))
      (ResponseSignatureControls.native_medial w x y z)

theorem observedTransparent (t : ℂ) : ObservedTransparent (data t) := by
  intro x c
  exact congrArg (fun z => twoPointTest t (c.eval mixer z))
    (congrArg Prod.fst (NativeMixerEventConeExclusion.mixer_transparent x))

theorem scalar_prepared (t : ℂ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) :
    ResponseNativeProbabilitySelection.prepared (data t) 1 s c = c.eval (source s) := by
  unfold ResponseNativeProbabilitySelection.prepared
  change WeightFreeRawProbability.evalRaw mixer c (source s) = _
  exact ResponseSignatureControls.evalRaw_native c (source s)

def lawOfScalar (t : ℂ) (ht : t ≠ 0) (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law (data t) 1 where
  prob := L.prob
  nonnegative := L.nonnegative
  normalized := L.normalized
  prepared_eq s c e h := by
    apply L.prepared_eq s c e
    have hraw : ResponseNativeProbabilitySelection.prepared (data t) 1 s c =
        ResponseNativeProbabilitySelection.prepared (data t) 1 s e := by
      funext i
      exact (twoPoint_responseEq_iff_eq t ht _ _).mp (h i)
    simpa only [scalar_prepared] using hraw
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

theorem lawOfScalar_probability (t : ℂ) (ht : t ≠ 0)
    (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob ℂ Bool (data t) 1 (lawOfScalar t ht L) =
      @NativeVacuumProbabilityFamily.Law.prob L := rfl

/-- This witness is separate from the contextual and recipe separation proofs. -/
def canonicalLaw (t : ℂ) (ht : t ≠ 0) :=
  lawOfScalar t ht NativeVacuumProbabilityFamily.canonicalLaw

theorem law_nonempty (t : ℂ) (ht : t ≠ 0) :
    Nonempty (ResponseNativeProbabilitySelection.Law (data t) 1) :=
  ⟨canonicalLaw t ht⟩

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem originalEvent_scalar (t : ℂ) (s : ι) (e : Event ι) :
    originalEvent (data t) 1 s e = amplitude s e := by
  unfold originalEvent
  rw [scalar_prepared]
  rfl

theorem comparisonEvent_amplitude (s : ι) (e r : Event ι) :
    amplitude s (comparisonEvent s e r) =
      Complex.I * (amplitude s e - amplitude s r) / 2 :=
  (NativeReferenceSeparation.pairedSetting s e r).difference_amplitude

theorem profile_value (t : ℂ) (s : ι) (e r : Event ι) :
    responseProfile (data t) 1 s e r =
      twoPointTest t (Complex.I * (amplitude s e - amplitude s r) / 2) := by
  change twoPointTest t (originalEvent (data t) 1 s (comparisonEvent s e r)) = _
  rw [originalEvent_scalar, comparisonEvent_amplitude]

theorem signed_membership_forces_zero (t δ : ℂ) (ht : t ≠ 0)
    (hp : δ = 0 ∨ δ = t) (hm : -δ = 0 ∨ -δ = t) : δ = 0 := by
  rcases hp with hzero | heq
  · exact hzero
  · rcases hm with hzero | hneg
    · exact neg_eq_zero.mp hzero
    · have hsum : (2 : ℂ) * t = 0 := by linear_combination -heq - hneg
      have htzero : t = 0 := (mul_eq_zero.mp hsum).resolve_left (by norm_num)
      exact False.elim (ht htzero)

/-- All reference-recipe profiles separate, without comparator soundness.
The two reference recipes e and f are enough for this implication for this
particular pair; no fixed universal finite reference battery is supplied. -/
theorem profile_eq_iff_amplitude_eq (t : ℂ) (ht : t ≠ 0)
    (s : ι) (e f : Event ι) :
    responseProfile (data t) 1 s e = responseProfile (data t) 1 s f ↔
      amplitude s e = amplitude s f := by
  constructor
  · intro h
    let δ : ℂ := Complex.I * (amplitude s e - amplitude s f) / 2
    have he := congrFun h e
    rw [profile_value, profile_value] at he
    simp only [sub_self, mul_zero, zero_div, twoPointTest_zero] at he
    have hflip : Complex.I * (amplitude s f - amplitude s e) / 2 = -δ := by
      dsimp only [δ]
      ring
    rw [hflip] at he
    have hf := congrFun h f
    rw [profile_value, profile_value] at hf
    simp only [sub_self, mul_zero, zero_div, twoPointTest_zero] at hf
    have hp : δ = 0 ∨ δ = t := (twoPointTest_true_iff t δ).mp hf
    have hm : -δ = 0 ∨ -δ = t := (twoPointTest_true_iff t (-δ)).mp he.symm
    have hz := signed_membership_forces_zero t δ ht hp hm
    have hz' : Complex.I * (amplitude s e - amplitude s f) / 2 = 0 := hz
    simpa [div_eq_zero_iff, mul_eq_zero, sub_eq_zero, Complex.I_ne_zero] using hz'
  · intro h
    funext r
    rw [profile_value, profile_value, h]

theorem profile_eq_iff_responseEq (t : ℂ) (ht : t ≠ 0)
    (s : ι) (e f : Event ι) :
    responseProfile (data t) 1 s e = responseProfile (data t) 1 s f ↔
      ResponseEq (data t).operation (data t).signature
        (originalEvent (data t) 1 s e) (originalEvent (data t) 1 s f) := by
  rw [profile_eq_iff_amplitude_eq t ht, originalEvent_scalar, originalEvent_scalar]
  exact (twoPoint_responseEq_iff_eq t ht _ _).symm

/-! ## An actual comparator with vacuum signature but nonvacuum response class -/

def controlPoint : ℂ := Complex.I / 8

theorem controlPoint_ne_zero : controlPoint ≠ 0 := by
  norm_num [controlPoint]

theorem half_quarter_comparison_amplitude (s : ι) :
    amplitude s (comparisonEvent s (NativeReferenceSeparation.halfControl s)
      (NativeReferenceSeparation.quarterControl s)) = controlPoint := by
  rw [comparisonEvent_amplitude, NativeReferenceSeparation.halfControl_amplitude,
    NativeReferenceSeparation.quarterControl_amplitude]
  unfold controlPoint
  ring

theorem controlPoint_vacuum_signature :
    twoPointTest controlPoint controlPoint = twoPointTest controlPoint 0 := by simp

theorem controlPoint_not_responseEq_vacuum :
    ¬ ResponseEq mixer (twoPointTest controlPoint) controlPoint 0 := by
  intro h
  exact controlPoint_ne_zero
    ((twoPoint_responseEq_iff_eq controlPoint controlPoint_ne_zero _ _).mp h)

theorem not_comparatorVacuumSound (s : ι) :
    ¬ ComparatorVacuumSound (data controlPoint) 1 s := by
  intro h
  let e := NativeReferenceSeparation.halfControl s
  let f := NativeReferenceSeparation.quarterControl s
  have hsignature :
      (data controlPoint).signature (originalEvent (data controlPoint) 1 s
        (comparisonEvent s e f)) = (data controlPoint).signature (data controlPoint).chosenZero := by
    change twoPointTest controlPoint
      (originalEvent (data controlPoint) 1 s (comparisonEvent s e f)) =
        twoPointTest controlPoint 0
    rw [originalEvent_scalar]
    change twoPointTest controlPoint (amplitude s (comparisonEvent s
      (NativeReferenceSeparation.halfControl s) (NativeReferenceSeparation.quarterControl s))) = _
    rw [half_quarter_comparison_amplitude]
    exact controlPoint_vacuum_signature
  have hresponse := h e f hsignature
  apply controlPoint_not_responseEq_vacuum
  change ResponseEq mixer (twoPointTest controlPoint)
    (originalEvent (data controlPoint) 1 s (comparisonEvent s e f)) 0 at hresponse
  rw [originalEvent_scalar] at hresponse
  change ResponseEq mixer (twoPointTest controlPoint)
    (amplitude s (comparisonEvent s (NativeReferenceSeparation.halfControl s)
      (NativeReferenceSeparation.quarterControl s))) 0 at hresponse
  rw [half_quarter_comparison_amplitude] at hresponse
  exact hresponse

/-- The sufficient comparator-soundness condition is not necessary for this
supplied signature's full recipe-profile separation. All six law fields remain
simultaneously satisfiable, independently of the separation proof. -/
theorem separating_profiles_without_comparatorSoundness (s : ι) :
    ObservedTransparent (data controlPoint) ∧
    Nonempty (ResponseNativeProbabilitySelection.Law (data controlPoint) 1) ∧
    (∀ e f : Event ι,
      responseProfile (data controlPoint) 1 s e = responseProfile (data controlPoint) 1 s f ↔
      ResponseEq (data controlPoint).operation (data controlPoint).signature
        (originalEvent (data controlPoint) 1 s e) (originalEvent (data controlPoint) 1 s f)) ∧
    ¬ ComparatorVacuumSound (data controlPoint) 1 s :=
  ⟨observedTransparent controlPoint, law_nonempty controlPoint controlPoint_ne_zero,
    profile_eq_iff_responseEq controlPoint controlPoint_ne_zero s,
    not_comparatorVacuumSound s⟩

end
end IDT.QMClosure.NativeTwoPointObservationControl
