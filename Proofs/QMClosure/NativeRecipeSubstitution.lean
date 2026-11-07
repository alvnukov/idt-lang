import Proofs.QMClosure.NativeRecipeContextRealization

/-!
# Attenuation-accounted substitution of actual same-source recipes

The outer references, as well as the inserted hole recipe, must have the
inner context's dyadic scale. Corrected substitution equates selected scalar
and normalized raw outputs. The circuits, levels, ancillary arrays and histories
may differ. Each recipe is finite; arbitrary finite vacuum extensions are
permitted without a capacity, efficiency or noise-robustness claim.

Raw transfer applies to any chosen reference, including null and finite-order
references, through existing scalar/raw coefficient correlation. It requires no
infinite-order, positive-weight or probability-law premise. It concerns only
the normalized operation; original-gate interpretation needs its evaluator
bridge. Scalar inequality need not imply raw inequality for a null reference.

Algebraic attenuation accounting supplies no native amplification, unattenuated
copying, unknown-token processor, arbitrary-signature reflection, physical
reference availability, legal physical-history composition, actualization or
QM closure. The probability corollary separately retains a supplied native Law.
-/

namespace IDT.QMClosure.NativeRecipeSubstitution

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open NativeGaussianResponse NativeRecipeContextRealization
open OperationalContextQuotient
open NativeMixerEventConeExclusion (mixer)
open NativeAttenuationCircuit (a b mixer_fst)
open ReferenceOccurrenceCompilation (referenceCount)

theorem referenceCount_plug {A : Type*} (C D : Context A) :
    referenceCount (C.plug D) = referenceCount C + referenceCount D := by
  induction C with
  | hole => simp [Context.plug, referenceCount]
  | left o C r ih =>
    simp [Context.plug, referenceCount, ih, Nat.add_comm,
      Nat.add_left_comm]
  | right o r C ih =>
    simp [Context.plug, referenceCount, ih, Nat.add_comm,
      Nat.add_left_comm]

theorem mapRefs_comp {A B X : Type*} (f : A → B) (g : B → X)
    (C : Context A) :
    mapRefs g (mapRefs f C) = mapRefs (g ∘ f) C := by
  induction C with
  | hole => rfl
  | left o C r ih => simp only [mapRefs, ih, Function.comp_def]
  | right o r C ih => simp only [mapRefs, ih, Function.comp_def]

theorem mapRefs_plug {A B : Type*} (f : A → B) (C D : Context A) :
    mapRefs f (C.plug D) = (mapRefs f C).plug (mapRefs f D) := by
  induction C with
  | hole => rfl
  | left o C r ih => simp only [mapRefs, Context.plug, ih]
  | right o r C ih => simp only [mapRefs, Context.plug, ih]

/-- Joint scaling includes every reference occurrence and the hole. No
homogeneity claim for an arbitrary raw operation is used. -/
theorem context_eval_div (C : Context ℂ) (x q : ℂ) :
    Context.eval mixer (mapRefs (fun z => z / q) C) (x / q) =
      Context.eval mixer C x / q := by
  induction C with
  | hole => rfl
  | left o C r ih =>
    simp only [mapRefs, Context.eval, ih, mixer_select_div]
  | right o r C ih =>
    simp only [mapRefs, Context.eval, ih, mixer_select_div]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Repeated literal native real-half attenuation, retaining whole recipes. -/
def dampEvent : ℕ → Event ι → Event ι
  | 0, e => e
  | k + 1, e => halfEvent (dampEvent k e)

theorem dampEvent_amplitude (s : ι) (k : ℕ) (e : Event ι) :
    amplitude s (dampEvent k e) = amplitude s e / (2 : ℂ)^k := by
  induction k with
  | zero => simp only [dampEvent, pow_zero, div_one]
  | succ k ih =>
    rw [dampEvent, halfEvent_amplitude, ih, div_div, pow_succ]

theorem mapRefs_amplitude_damp (s : ι) (k : ℕ) (C : Context (Event ι)) :
    mapRefs (amplitude s) (mapRefs (dampEvent k) C) =
      mapRefs (fun z => z / (2 : ℂ)^k) (mapRefs (amplitude s) C) := by
  induction C with
  | hole => rfl
  | left o C r ih => simp only [mapRefs, ih, dampEvent_amplitude]
  | right o r C ih => simp only [mapRefs, ih, dampEvent_amplitude]

omit [Fintype ι] in
theorem idealAmplitude_plug (s : ι) (C D : Context (Event ι)) (e : Event ι) :
    idealAmplitude s (C.plug D) e =
      Context.eval mixer (mapRefs (amplitude s) C) (idealAmplitude s D e) := by
  simp only [idealAmplitude, mapRefs_plug, Context.eval_plug]

/-- The explicit amplitude equation of the existing chosen finite witness. -/
theorem realize_amplitude (s : ι) (C : Context (Event ι)) (e : Event ι) :
    amplitude s (realize s C e) =
      idealAmplitude s C e / (2 : ℂ)^referenceCount C :=
  realize_spec s C e

theorem damped_outer_ideal (s : ι) (C D : Context (Event ι)) (e : Event ι) :
    idealAmplitude s (mapRefs (dampEvent (referenceCount D)) C)
        (realize s D e) =
      idealAmplitude s (C.plug D) e / (2 : ℂ)^referenceCount D := by
  change Context.eval mixer
      (mapRefs (amplitude s) (mapRefs (dampEvent (referenceCount D)) C))
      (amplitude s (realize s D e)) = _
  rw [mapRefs_amplitude_damp, realize_amplitude, context_eval_div,
    ← idealAmplitude_plug s C D e]

/-- Corrected nesting and direct substitution have the identical total
attenuation exponent. Only the selected amplitudes are compared. -/
theorem corrected_realization_amplitude (s : ι)
    (C D : Context (Event ι)) (e : Event ι) :
    amplitude s
        (realize s (mapRefs (dampEvent (referenceCount D)) C) (realize s D e)) =
      idealAmplitude s (C.plug D) e /
        (2 : ℂ)^(referenceCount C + referenceCount D) := by
  rw [realize_amplitude, referenceCount_mapRefs, damped_outer_ideal,
    div_div, pow_add,
    mul_comm ((2 : ℂ)^referenceCount D) ((2 : ℂ)^referenceCount C)]

theorem plugged_realization_amplitude (s : ι)
    (C D : Context (Event ι)) (e : Event ι) :
    amplitude s (realize s (C.plug D) e) =
      idealAmplitude s (C.plug D) e /
        (2 : ℂ)^(referenceCount C + referenceCount D) := by
  rw [realize_amplitude, referenceCount_plug]

theorem corrected_substitution_amplitude (s : ι)
    (C D : Context (Event ι)) (e : Event ι) :
    amplitude s
        (realize s (mapRefs (dampEvent (referenceCount D)) C) (realize s D e)) =
      amplitude s (realize s (C.plug D) e) := by
  rw [corrected_realization_amplitude, plugged_realization_amplitude]

/-- The same scalar certificate determines both normalized raw outputs.
The reference may be null or finite order; scalar faithfulness is not used. -/
theorem corrected_substitution_raw {V : Type*}
    (r : WeightFreeRawProbability.RawOperationalData V) (v : r.Carrier)
    (s : ι) (C D : Context (Event ι)) (e : Event ι) :
    rawEvent r v s
        (realize s (mapRefs (dampEvent (referenceCount D)) C) (realize s D e)) =
      rawEvent r v s (realize s (C.plug D) e) := by
  have h := rawEvent_related r v s
    (realize s (mapRefs (dampEvent (referenceCount D)) C) (realize s D e))
  rw [corrected_substitution_amplitude s C D e] at h
  exact RawNativeDyadicSemantics.related_raw_unique r.zeroWeightData v h
    (rawEvent_related r v s (realize s (C.plug D) e))

/-- Only this corollary adds the supplied native probability-family Law;
it does not assert equality of complete prepared arrays. -/
theorem corrected_substitution_probability (L : NativeVacuumProbabilityFamily.Law)
    (s : ι) (C D : Context (Event ι)) (e : Event ι) :
    probability L s
        (realize s (mapRefs (dampEvent (referenceCount D)) C) (realize s D e)) =
      probability L s (realize s (C.plug D) e) := by
  simp only [probability, NativeProbabilityUniqueness.native_probability_eq_normSq]
  exact congrArg Complex.normSq (corrected_substitution_amplitude s C D e)

/-! ## Actual positive-count countercontrol to naive recipe substitution -/

def unitRecipe (s : ι) : Event ι := baseEvent .identity s

omit [Fintype ι] in
theorem unitRecipe_amplitude (s : ι) : amplitude s (unitRecipe s) = 1 := by
  change (source (sourceAt s 0)) (sourceAt s 0) = 1
  simp [source, single]

def unitContext (s : ι) : Context (Event ι) := .left .first .hole (unitRecipe s)

omit [Fintype ι] [DecidableEq ι] in
theorem unitContext_referenceCount (s : ι) : referenceCount (unitContext s) = 1 := rfl

omit [Fintype ι] in
theorem unitContext_ideal (s : ι) (e : Event ι) :
    idealAmplitude s (unitContext s) e = (mixer (amplitude s e, 1)).1 := by
  simp only [idealAmplitude, unitContext, mapRefs, Context.eval, select,
    unitRecipe_amplitude]

theorem unitContext_realize_amplitude (s : ι) (e : Event ι) :
    amplitude s (realize s (unitContext s) e) =
      (mixer (amplitude s e, 1)).1 / 2 := by
  rw [realize_amplitude, unitContext_ideal, unitContext_referenceCount, pow_one]

theorem unitContext_on_unit_amplitude (s : ι) :
    amplitude s (realize s (unitContext s) (unitRecipe s)) = (1 : ℂ) / 2 := by
  rw [unitContext_realize_amplitude, unitRecipe_amplitude, mixer_fst]
  dsimp only [a, b]
  ring

theorem naive_unit_substitution_amplitude (s : ι) :
    amplitude s
        (realize s (unitContext s) (realize s (unitContext s) (unitRecipe s))) =
      (3 - Complex.I) / 8 := by
  rw [unitContext_realize_amplitude, unitContext_on_unit_amplitude, mixer_fst]
  dsimp only [a, b]
  ring

omit [Fintype ι] in
theorem plugged_unit_ideal (s : ι) :
    idealAmplitude s ((unitContext s).plug (unitContext s)) (unitRecipe s) = 1 := by
  rw [idealAmplitude_plug]
  change (mixer ((mixer (amplitude s (unitRecipe s),
    amplitude s (unitRecipe s))).1, amplitude s (unitRecipe s))).1 = 1
  simp only [unitRecipe_amplitude, mixer_fst, a, b]
  ring

theorem plugged_unit_substitution_amplitude (s : ι) :
    amplitude s
        (realize s ((unitContext s).plug (unitContext s)) (unitRecipe s)) =
      (1 : ℂ) / 4 := by
  rw [plugged_realization_amplitude, plugged_unit_ideal, unitContext_referenceCount]
  norm_num

theorem corrected_unit_substitution_amplitude (s : ι) :
    amplitude s
        (realize s (mapRefs (dampEvent (referenceCount (unitContext s))) (unitContext s))
          (realize s (unitContext s) (unitRecipe s))) = (1 : ℂ) / 4 := by
  rw [corrected_substitution_amplitude]
  exact plugged_unit_substitution_amplitude s

theorem naive_unit_substitution_normSq (s : ι) :
    Complex.normSq (amplitude s
      (realize s (unitContext s) (realize s (unitContext s) (unitRecipe s)))) =
      (5 : ℝ) / 32 := by
  rw [naive_unit_substitution_amplitude]
  norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im]

theorem plugged_unit_substitution_normSq (s : ι) :
    Complex.normSq (amplitude s
      (realize s ((unitContext s).plug (unitContext s)) (unitRecipe s))) =
      (1 : ℝ) / 16 := by
  rw [plugged_unit_substitution_amplitude]
  norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im]

/-- One concrete failure, with both reference counts positive. This makes
neither a universal failure assertion nor any raw-inequality assertion. -/
theorem naive_unit_substitution_fails (s : ι) :
    0 < referenceCount (unitContext s) ∧
      Complex.normSq (amplitude s
        (realize s (unitContext s) (realize s (unitContext s) (unitRecipe s)))) ≠
        Complex.normSq (amplitude s
          (realize s ((unitContext s).plug (unitContext s)) (unitRecipe s))) := by
  rw [unitContext_referenceCount, naive_unit_substitution_normSq,
    plugged_unit_substitution_normSq]
  norm_num

end

end IDT.QMClosure.NativeRecipeSubstitution
