import Proofs.QMClosure.ReferenceOccurrenceCompilation
import Proofs.QMClosure.NativeSingleSourceReferenceWall
import Proofs.QMClosure.NativeProbabilityUniqueness

/-!
# Finite same-source recipe contexts, with accounted attenuation

References and the hole are actual event recipes in one canonical doubling
tower above a fixed finite wire type and marked source. The construction keeps
whole circuits and every ancillary output. It realizes the selected ideal
context amplitude divided by two once per reference occurrence, using no
probability law. It supplies neither arbitrary references nor fresh
unattenuated copies. Every constructed circuit is finite; arbitrary finite
vacuum extensions are permitted, without a capacity or efficiency claim.

The separate raw transfer concerns normalized raw evaluation and an arbitrary
chosen source reference v, including null or finite-order v; context references
remain source-generated recipes. The zero-weight adapter carries no readout
information. Original-gate interpretation needs its evaluator bridge.
Raw equality does not recover scalar equality: a null reference can collapse
coefficients. Injectivity of reconstructed half is algebraic and supplies no
native amplification or physical removal of attenuation.

Whole finite contexts are compiled. Naively composing independently compiled
contexts need not preserve this accounting: outer references need alignment
and damping. Exact equality and inequality reflection supply no uniform
finite-resolution or noise robustness. No unknown-token processing, raw
signature reflection, physical source/control availability, actualization,
Hilbert premise, or full-QM conclusion is asserted.
-/

namespace IDT.QMClosure.NativeRecipeContextRealization

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

open MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open NativeGaussianResponse NativeCoherentBranchDilation
open NativeScalarAmplitudeSufficiency OperationalContextQuotient
open NativeMixerEventConeExclusion (mixer)
open NativeAttenuationCircuit (a b mixer_fst mixer_snd)
open ReferenceOccurrenceCompilation (referenceCount)

/-- Structural replacement of references; the unique hole is unchanged. -/
def mapRefs {A B : Type*} (f : A → B) : Context A → Context B
  | .hole => .hole
  | .left o c r => .left o (mapRefs f c) (f r)
  | .right o r c => .right o (f r) (mapRefs f c)

theorem referenceCount_mapRefs {A B : Type*} (f : A → B) (C : Context A) :
    referenceCount (mapRefs f C) = referenceCount C := by
  induction C with
  | hole => rfl
  | left o c r ih => simpa only [mapRefs, referenceCount] using congrArg Nat.succ ih
  | right o r c ih => simpa only [mapRefs, referenceCount] using congrArg Nat.succ ih

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The existing comparison word, including both untouched ancillary blocks.
This is a new interface to that word, not a new comparison construction. -/
theorem comparison_blocks (s : ι) (c d : Native ι) :
    (comparison c d).eval (source (.inl (.inl s))) =
      Sum.elim
        (Sum.elim (fun i => a^2 * source s i) (fun i => c.eval (source s) i / 2))
        (Sum.elim (fun i => d.eval (source s) i / 2) (fun i => b^2 * source s i)) := by
  funext w
  rcases w with (i | i) | (i | i)
  · simp only [comparison, dilation_amplitude_left, Circuit.eval,
      AddMonoidHom.id_apply, Sum.elim_inl]
    ring
  · simp only [comparison, dilation_amplitude_left, dilation_amplitude_right,
      Sum.elim_inl, Sum.elim_inr]
    rw [← mul_assoc, a_mul_b]
    ring
  · simp only [comparison, dilation_amplitude_left, dilation_amplitude_right,
      Sum.elim_inl, Sum.elim_inr]
    rw [← mul_assoc, mul_comm b a, a_mul_b]
    ring
  · simp only [comparison, dilation_amplitude_right, Circuit.eval,
      AddMonoidHom.id_apply, Sum.elim_inr]
    ring

theorem comparison_middle_left (s : ι) (c d : Native ι) (i : ι) :
    (comparison c d).eval (source (.inl (.inl s))) (.inl (.inr i)) =
      c.eval (source s) i / 2 := by
  rw [comparison_blocks]
  rfl

theorem comparison_middle_right (s : ι) (c d : Native ι) (j : ι) :
    (comparison c d).eval (source (.inl (.inl s))) (.inr (.inl j)) =
      d.eval (source s) j / 2 := by
  rw [comparison_blocks]
  rfl

theorem mixer_select_div (o : Output) (z w q : ℂ) :
    select o (mixer (z/q, w/q)) = select o (mixer (z,w)) / q := by
  cases o <;> simp only [select, mixer_fst, mixer_snd] <;> ring

/-- Continue the existing comparison on its two distinct middle ports. -/
def halvedMixerCircuit (c d : Native ι) (i j : ι) :
    Native ((ι ⊕ ι) ⊕ (ι ⊕ ι)) :=
  .seq (comparison c d) (.pair (.inl (.inr i)) (.inr (.inl j)) (by simp))

theorem halvedMixer_amplitudes (s : ι) (c d : Native ι) (i j : ι) :
    (halvedMixerCircuit c d i j).eval (source (.inl (.inl s))) (.inl (.inr i)) =
      (mixer (c.eval (source s) i, d.eval (source s) j)).1 / 2 ∧
    (halvedMixerCircuit c d i j).eval (source (.inl (.inl s))) (.inr (.inl j)) =
      (mixer (c.eval (source s) i, d.eval (source s) j)).2 / 2 := by
  constructor <;>
    simp [halvedMixerCircuit, Circuit.eval, pairGate, pairReplace,
      comparison_middle_left, comparison_middle_right, mixer_fst, mixer_snd] <;> ring

/-- Both mixer outputs belong to one actual circuit, on distinct ports. The
other ports remain part of this complete native circuit's output array. -/
theorem exists_halved_mixer (s : ι) (e f : Event ι) :
    ∃ n : ℕ, ∃ c : Native (Tower ι (n+2)), ∃ i j : Tower ι (n+2),
      i ≠ j ∧
      c.eval (source (sourceAt s (n+2))) i =
        (mixer (amplitude s e, amplitude s f)).1 / 2 ∧
      c.eval (source (sourceAt s (n+2))) j =
        (mixer (amplitude s e, amplitude s f)).2 / 2 := by
  obtain ⟨n, c, d, i, j, hc, hd, _, _⟩ := exists_common_level s e f
  refine ⟨n, halvedMixerCircuit c d i j, .inl (.inr i), .inr (.inl j),
    by simp, ?_, ?_⟩
  · simpa only [sourceAt, hc, hd] using
      (halvedMixer_amplitudes (sourceAt s n) c d i j).1
  · simpa only [sourceAt, hc, hd] using
      (halvedMixer_amplitudes (sourceAt s n) c d i j).2

theorem exists_selected_halved_mixer (s : ι) (o : Output) (e f : Event ι) :
    ∃ E : Event ι,
      amplitude s E = select o (mixer (amplitude s e, amplitude s f)) / 2 := by
  obtain ⟨n, c, i, j, _, hi, hj⟩ := exists_halved_mixer s e f
  refine ⟨⟨n+2, c, select o (i,j)⟩, ?_⟩
  cases o with
  | first => exact hi
  | second => exact hj

def idealAmplitude (s : ι) (C : Context (Event ι)) (e : Event ι) : ℂ :=
  Context.eval mixer (mapRefs (amplitude s) C) (amplitude s e)

def Realizes (s : ι) (C : Context (Event ι)) (e E : Event ι) : Prop :=
  amplitude s E = idealAmplitude s C e / (2 : ℂ)^referenceCount C

/-- Law-free finite recipe realization. Each new reference is damped to the
child's scale before the next literal middle-port mixer gate. -/
theorem exists_realization (s : ι) (C : Context (Event ι)) (e : Event ι) :
    ∃ E : Event ι, Realizes s C e E := by
  induction C with
  | hole => exact ⟨e, by simp [Realizes, idealAmplitude, mapRefs, Context.eval,
      referenceCount]⟩
  | left o C r ih =>
    obtain ⟨E, hE⟩ := ih
    obtain ⟨R, hR, _⟩ := exists_damping s r (referenceCount C)
    obtain ⟨F, hF⟩ := exists_selected_halved_mixer s o E R
    refine ⟨F, ?_⟩
    change amplitude s E = idealAmplitude s C e / (2 : ℂ)^referenceCount C at hE
    change amplitude s F =
      select o (mixer (idealAmplitude s C e, amplitude s r)) /
        (2 : ℂ)^(referenceCount C + 1)
    rw [hF, hE, hR, mixer_select_div, div_div, pow_succ]
  | right o r C ih =>
    obtain ⟨E, hE⟩ := ih
    obtain ⟨R, hR, _⟩ := exists_damping s r (referenceCount C)
    obtain ⟨F, hF⟩ := exists_selected_halved_mixer s o R E
    refine ⟨F, ?_⟩
    change amplitude s E = idealAmplitude s C e / (2 : ℂ)^referenceCount C at hE
    change amplitude s F =
      select o (mixer (amplitude s r, idealAmplitude s C e)) /
        (2 : ℂ)^(referenceCount C + 1)
    rw [hF, hE, hR, mixer_select_div, div_div, pow_succ]

/-- A choice of proved finite recipe witnesses, not an amplitude search. -/
def realize (s : ι) (C : Context (Event ι)) (e : Event ι) : Event ι :=
  Classical.choose (exists_realization s C e)

theorem realize_spec (s : ι) (C : Context (Event ι)) (e : Event ι) :
    Realizes s C e (realize s C e) := Classical.choose_spec (exists_realization s C e)

omit [Fintype ι] in
theorem realization_normSq (s : ι) (C : Context (Event ι)) (e E : Event ι)
    (h : Realizes s C e E) :
    Complex.normSq (amplitude s E) =
      Complex.normSq (idealAmplitude s C e) / (4 : ℝ)^referenceCount C := by
  rw [h, Complex.normSq_div, map_pow]
  norm_num

private theorem div_same_iff {K : Type*} [Field K] {x y q : K} (hq : q ≠ 0) :
    x/q = y/q ↔ x = y := by
  constructor
  · intro h
    exact mul_right_cancel₀ hq ((div_eq_div_iff hq hq).mp h)
  · intro h
    rw [h]

omit [Fintype ι] in
theorem realization_amplitude_eq_iff (s : ι) (C : Context (Event ι))
    (e f E F : Event ι) (hE : Realizes s C e E) (hF : Realizes s C f F) :
    amplitude s E = amplitude s F ↔ idealAmplitude s C e = idealAmplitude s C f := by
  rw [hE, hF]
  exact div_same_iff (pow_ne_zero _ (by norm_num))

omit [Fintype ι] in
theorem realization_amplitude_ne_iff (s : ι) (C : Context (Event ι))
    (e f E F : Event ι) (hE : Realizes s C e E) (hF : Realizes s C f F) :
    amplitude s E ≠ amplitude s F ↔ idealAmplitude s C e ≠ idealAmplitude s C f :=
  not_congr (realization_amplitude_eq_iff s C e f E F hE hF)

omit [Fintype ι] in
theorem realization_normSq_eq_iff (s : ι) (C : Context (Event ι))
    (e f E F : Event ι) (hE : Realizes s C e E) (hF : Realizes s C f F) :
    Complex.normSq (amplitude s E) = Complex.normSq (amplitude s F) ↔
      Complex.normSq (idealAmplitude s C e) = Complex.normSq (idealAmplitude s C f) := by
  rw [realization_normSq s C e E hE, realization_normSq s C f F hF]
  exact div_same_iff (pow_ne_zero _ (by norm_num))

omit [Fintype ι] in
theorem realization_normSq_ne_iff (s : ι) (C : Context (Event ι))
    (e f E F : Event ι) (hE : Realizes s C e E) (hF : Realizes s C f F) :
    Complex.normSq (amplitude s E) ≠ Complex.normSq (amplitude s F) ↔
      Complex.normSq (idealAmplitude s C e) ≠ Complex.normSq (idealAmplitude s C f) :=
  not_congr (realization_normSq_eq_iff s C e f E F hE hF)

/-- Only this corollary adds a probability-family premise. -/
theorem realization_probability (L : NativeVacuumProbabilityFamily.Law)
    (s : ι) (C : Context (Event ι)) (e E : Event ι) (h : Realizes s C e E) :
    probability L s E =
      Complex.normSq (idealAmplitude s C e) / (4 : ℝ)^referenceCount C := by
  change L.prob (NativeGaussianResponse.sourceAt s E.level) E.circuit E.port = _
  rw [NativeProbabilityUniqueness.native_probability_eq_normSq]
  exact realization_normSq s C e E h

section Raw

open RawOperationalHilbert RawNativeDyadicSemantics

variable {V : Type*} (r : WeightFreeRawProbability.RawOperationalData V)
  (v : r.Carrier)

/-- Literal normalized raw evaluation of the supplied full event recipe. -/
def rawEvent (s : ι) (e : Event ι) : r.Carrier :=
  WeightFreeRawProbability.prepared r v (sourceAt s e.level) e.circuit e.port

omit [Fintype ι] in
theorem rawEvent_related (s : ι) (e : Event ι) :
    Related r.zeroWeightData v (amplitude s e) (rawEvent r v s e) := by
  have h := native_output_related r.zeroWeightData v
    (sourceAt s e.level) e.circuit e.port
  change Related r.zeroWeightData v (amplitude s e)
    (RawNativeProbabilitySelection.rawPrepared r.zeroWeightData v
      (sourceAt s e.level) e.circuit e.port) at h
  rw [WeightFreeRawProbability.rawPrepared_eq_prepared] at h
  exact h

def rawIdealContext (s : ι) (C : Context (Event ι)) (e : Event ι) : r.Carrier :=
  Context.eval r.normalizedOperation (mapRefs (rawEvent r v s) C) (rawEvent r v s e)

omit [Fintype ι] in
/-- Context induction preserves exact scalar/raw coefficient correlation;
neither positive weight nor infinite additive order is assumed. -/
theorem idealContext_related (s : ι) (C : Context (Event ι)) (e : Event ι) :
    Related r.zeroWeightData v (idealAmplitude s C e) (rawIdealContext r v s C e) := by
  induction C with
  | hole => exact rawEvent_related r v s e
  | left o C ref ih =>
    have h := related_mixer r.zeroWeightData v ih (rawEvent_related r v s ref)
    cases o with
    | first => exact h.1
    | second => exact h.2
  | right o ref C ih =>
    have h := related_mixer r.zeroWeightData v (rawEvent_related r v s ref) ih
    cases o with
    | first => exact h.1
    | second => exact h.2

theorem related_halfPower {z : ℂ} {x : r.Carrier}
    (h : Related r.zeroWeightData v z x) (n : ℕ) :
    Related r.zeroWeightData v (z/(2 : ℂ)^n) (halfPower r.zeroWeightData n x) := by
  induction n with
  | zero => simpa only [pow_zero, div_one, halfPower, AddMonoidHom.id_apply] using h
  | succ n ih =>
    simpa only [div_div, pow_succ, halfPower, AddMonoidHom.comp_apply] using
      related_half r.zeroWeightData v ih

omit [Fintype ι] in
/-- Every scalar witness with the proved amplitude formula has this raw
semantics, including witnesses chosen by any other construction. -/
theorem raw_realization_of_scalar (s : ι) (C : Context (Event ι)) (e E : Event ι)
    (h : Realizes s C e E) :
    rawEvent r v s E =
      halfPower r.zeroWeightData (referenceCount C) (rawIdealContext r v s C e) := by
  have hE := rawEvent_related r v s E
  rw [h] at hE
  exact related_raw_unique r.zeroWeightData v hE
    (related_halfPower r v (idealContext_related r v s C e) (referenceCount C))

/-- One actual recipe simultaneously realizes the scalar and normalized raw
context, for any reference, including a null or finite-order reference. -/
theorem exists_correlated_realization (s : ι) (C : Context (Event ι)) (e : Event ι) :
    ∃ E : Event ι, Realizes s C e E ∧ rawEvent r v s E =
      halfPower r.zeroWeightData (referenceCount C) (rawIdealContext r v s C e) := by
  obtain ⟨E, hE⟩ := exists_realization s C e
  exact ⟨E, hE, raw_realization_of_scalar r v s C e E hE⟩

/-- Reconstructed dyadic damping is injective on the entire raw carrier.
This is not a realizable native amplification circuit. -/
theorem halfPower_injective (n : ℕ) :
    Function.Injective (halfPower r.zeroWeightData n) := by
  have recover (x : r.Carrier) :
      (2 : ℕ)^n • halfPower r.zeroWeightData n x = x := by
    rw [← map_nsmul, halfPower_two_pow]
  intro x y h
  calc
    x = (2 : ℕ)^n • halfPower r.zeroWeightData n x := (recover x).symm
    _ = (2 : ℕ)^n • halfPower r.zeroWeightData n y := congrArg (fun t => (2 : ℕ)^n • t) h
    _ = y := recover y

omit [Fintype ι] in
theorem raw_realization_eq_iff (s : ι) (C : Context (Event ι))
    (e f E F : Event ι) (hE : Realizes s C e E) (hF : Realizes s C f F) :
    rawEvent r v s E = rawEvent r v s F ↔
      rawIdealContext r v s C e = rawIdealContext r v s C f := by
  rw [raw_realization_of_scalar r v s C e E hE,
    raw_realization_of_scalar r v s C f F hF]
  constructor
  · intro h
    exact halfPower_injective r (referenceCount C) h
  · exact congrArg (halfPower r.zeroWeightData (referenceCount C))

omit [Fintype ι] in
theorem raw_realization_ne_iff (s : ι) (C : Context (Event ι))
    (e f E F : Event ι) (hE : Realizes s C e E) (hF : Realizes s C f F) :
    rawEvent r v s E ≠ rawEvent r v s F ↔
      rawIdealContext r v s C e ≠ rawIdealContext r v s C f :=
  not_congr (raw_realization_eq_iff r v s C e f E F hE hF)

end Raw
end

end IDT.QMClosure.NativeRecipeContextRealization
