import Proofs.QMClosure.ResponseNativeProbabilitySelection
import Proofs.QMClosure.NativeVacuumProbabilityFamily
import Mathlib.Data.Fintype.EquivFin

/-!
# Controls for arbitrary response signatures

A finite contextual quotient cannot support the strengthened all-width law
under observed transparency: a law requires an infinite-order contextual
reference. A constant signature has a singleton contextual quotient and hence
has no such law, for any supplied raw operation.

Finiteness here concerns response-equivalence classes of raw coherent
preparations. It is not finite Hilbert dimension, finite detector labels, or
finitely many hidden states in an arbitrary stochastic model: distributions
over those states may form an infinite preparation carrier. No general
finite-memory classical-physics impossibility result is asserted.

Finite response alphabet is a different condition. In the supplied native
complex model, a Boolean exact-zero test and arbitrary fixed references
distinguish every complex state. Its contextual quotient is therefore infinite.
Every supplied scalar native probability law transports with the same field;
the existing canonical law supplies one separate consistency witness.

These are mathematical controls, not a derivation of complex states or of the
native gate. The Boolean signature is an ideal exact algebraic test, not an
asserted physically available detector or a preassigned actual outcome for
incompatible measurements. Arbitrary reference contexts are explicit. No
finite-precision robustness, preparation availability, detector dynamics,
actualization, or full QM conclusion is asserted. The generic response contract
has no weight field; the concrete canonical probability witness is supplied.
Independent scientific provenance of a supplied signature remains a requirement
outside the `Data` type; these constructions do not certify that provenance.
-/

namespace IDT.QMClosure.ResponseSignatureControls

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open ResponseContextQuotient
open OperationalContextQuotient (Context Output select)
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open WeightFreeRawProbability (evalRaw)

variable {V Ω : Type*}

/-! ## Finiteness applies to the contextual quotient, not the signature alphabet -/

theorem finite_quotient_no_law (d : Data V Ω) (v : V)
    (transparent : ObservedTransparent d) [Finite d.Space] :
    ¬ Nonempty (ResponseNativeProbabilitySelection.Law d v) := by
  rintro ⟨L⟩
  let G := d.quotientData.Carrier
  letI : AddCommGroup G := d.quotientData.zeroWeightData.derivedGroup
  letI : Finite G := by change Finite d.Space; infer_instance
  let vG : G := d.classOf v
  have hi : ∀ n : ℤ, n • vG = 0 → n = 0 :=
    ResponseNativeProbabilitySelection.reference_infiniteOrder L transparent
  have hinj : Function.Injective (fun n : ℤ => n • vG) := by
    intro n m hnm
    change n • vG = m • vG at hnm
    apply sub_eq_zero.mp
    apply hi (n - m)
    rw [sub_zsmul, hnm, add_neg_cancel]
  exact (Finite.of_injective (fun n : ℤ => n • vG) hinj).false

theorem law_implies_infinite_quotient (d : Data V Ω) (v : V)
    (transparent : ObservedTransparent d)
    (L : ResponseNativeProbabilitySelection.Law d v) : Infinite d.Space := by
  refine ⟨fun hfinite => ?_⟩
  letI : Finite d.Space := hfinite
  exact finite_quotient_no_law d v transparent ⟨L⟩

/-- The identity signature separates states already in the hole context.
This lemma alone makes no statement about equivalence of probability contracts. -/
theorem identity_responseEq_iff_eq (T : V × V → V × V) (x y : V) :
    ResponseEq T id x y ↔ x = y := by
  constructor
  · intro h
    exact h .hole
  · rintro rfl
    intro c
    rfl

/-! ## Constant responses collapse every raw state -/

def constantData (T : V × V → V × V) (z : V) (o : Ω) : Data V Ω where
  chosenZero := z
  operation := T
  signature := fun _ => o
  square _ := ⟨fun _ => rfl, fun _ => rfl⟩
  medial _ _ _ _ _ := rfl

theorem constant_responseEq (T : V × V → V × V) (z : V) (o : Ω) (x y : V) :
    ResponseEq (constantData T z o).operation (constantData T z o).signature x y :=
  fun _ => rfl

theorem constant_observedTransparent (T : V × V → V × V) (z : V) (o : Ω) :
    ObservedTransparent (constantData T z o) := fun _ _ => rfl

theorem constant_quotient_subsingleton (T : V × V → V × V) (z : V) (o : Ω) :
    Subsingleton (constantData T z o).Space := by
  constructor
  intro x y
  induction x using Quotient.inductionOn with
  | _ x =>
    induction y using Quotient.inductionOn with
    | _ y => exact Quotient.sound (constant_responseEq T z o x y)

theorem constant_quotient_singleton (T : V × V → V × V) (z : V) (o : Ω) :
    ∃ x : (constantData T z o).Space, ∀ y, y = x := by
  letI := constant_quotient_subsingleton T z o
  exact ⟨(constantData T z o).classOf z, fun _ => Subsingleton.elim _ _⟩

theorem constant_no_law (T : V × V → V × V) (z : V) (o : Ω) (v : V) :
    ¬ Nonempty (ResponseNativeProbabilitySelection.Law (constantData T z o) v) := by
  letI := constant_quotient_subsingleton T z o
  exact finite_quotient_no_law (constantData T z o) v (constant_observedTransparent T z o)

/-! ## A finite exact-response alphabet with an infinite contextual quotient -/

def zeroTest (z : ℂ) : Bool := by
  classical
  exact decide (z = 0)

@[simp] theorem zeroTest_eq_true_iff (z : ℂ) : zeroTest z = true ↔ z = 0 := by
  classical
  simp [zeroTest]

@[simp] theorem zeroTest_zero : zeroTest 0 = true := by simp [zeroTest]

theorem native_a_ne_zero : NativeAttenuationCircuit.a ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  norm_num [NativeAttenuationCircuit.a, Complex.div_re, Complex.div_im] at hr

/-- For each fixed comparison state x, the reference is fixed at −i*x.
The variable input y occurs exactly once in this native one-hole experiment. -/
theorem native_first_cancel_reference (x y : ℂ) :
    (NativeMixerEventConeExclusion.mixer (y, -Complex.I * x)).1 =
      NativeAttenuationCircuit.a * (y - x) := by
  rw [NativeAttenuationCircuit.mixer_fst]
  apply Complex.ext <;>
    norm_num [NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
      Complex.div_re, Complex.div_im] <;> ring

theorem native_responseEq_iff_eq (x y : ℂ) :
    ResponseEq NativeMixerEventConeExclusion.mixer zeroTest x y ↔ x = y := by
  constructor
  · intro h
    have ht := h (.left .first .hole (-Complex.I * x))
    change zeroTest (NativeMixerEventConeExclusion.mixer (x, -Complex.I * x)).1 =
      zeroTest (NativeMixerEventConeExclusion.mixer (y, -Complex.I * x)).1 at ht
    rw [native_first_cancel_reference, native_first_cancel_reference,
      sub_self, mul_zero, zeroTest_zero] at ht
    have hz : NativeAttenuationCircuit.a * (y - x) = 0 :=
      (zeroTest_eq_true_iff _).mp ht.symm
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left native_a_ne_zero)).symm
  · rintro rfl
    intro c
    rfl

theorem native_medial (a b c d : ℂ) :
    MedialSwapRoot.firstChannel NativeMixerEventConeExclusion.mixer
      (MedialSwapRoot.firstChannel NativeMixerEventConeExclusion.mixer a b)
      (MedialSwapRoot.firstChannel NativeMixerEventConeExclusion.mixer c d) =
    MedialSwapRoot.firstChannel NativeMixerEventConeExclusion.mixer
      (MedialSwapRoot.firstChannel NativeMixerEventConeExclusion.mixer a c)
      (MedialSwapRoot.firstChannel NativeMixerEventConeExclusion.mixer b d) := by
  simp only [MedialSwapRoot.firstChannel, NativeAttenuationCircuit.mixer_fst]
  ring

def nativeData : Data ℂ Bool where
  chosenZero := 0
  operation := NativeMixerEventConeExclusion.mixer
  signature := zeroTest
  square p := by
    constructor
    · apply (native_responseEq_iff_eq _ _).mpr
      exact congrArg Prod.fst (NativeMixerEventConeExclusion.mixer_square p)
    · apply (native_responseEq_iff_eq _ _).mpr
      exact congrArg Prod.snd (NativeMixerEventConeExclusion.mixer_square p)
  medial a b c d := (native_responseEq_iff_eq _ _).mpr (native_medial a b c d)

theorem native_observedTransparent : ObservedTransparent nativeData := by
  intro x
  apply (native_responseEq_iff_eq _ _).mpr
  exact congrArg Prod.fst (NativeMixerEventConeExclusion.mixer_transparent x)

theorem native_classOf_injective : Function.Injective nativeData.classOf := by
  intro x y h
  apply (native_responseEq_iff_eq x y).mp
  exact Quotient.exact h

theorem native_quotient_infinite : Infinite nativeData.Space := by
  refine ⟨fun hfinite => ?_⟩
  letI : Finite nativeData.Space := hfinite
  exact (Finite.of_injective nativeData.classOf native_classOf_injective).false

theorem finite_alphabet_infinite_quotient : Finite Bool ∧ Infinite nativeData.Space :=
  ⟨inferInstance, native_quotient_infinite⟩

/-! ## Transport any supplied native scalar probability law without changing it -/

theorem evalRaw_native {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Native ι) (x : ι → ℂ) :
    evalRaw NativeMixerEventConeExclusion.mixer c x = c.eval x := by
  induction c generalizing x with
  | identity => rfl
  | pair i j hij => rfl
  | permute e => rfl
  | seq c e hc he =>
    simp only [evalRaw, Circuit.eval, AddMonoidHom.comp_apply, hc, he]

theorem native_prepared {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) :
    ResponseNativeProbabilitySelection.prepared nativeData 1 s c = c.eval (source s) := by
  unfold ResponseNativeProbabilitySelection.prepared
  change evalRaw NativeMixerEventConeExclusion.mixer c (source s) = _
  exact evalRaw_native c (source s)

def nativeLawOfScalar (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law nativeData 1 where
  prob := L.prob
  nonnegative := L.nonnegative
  normalized := L.normalized
  prepared_eq s c e h := by
    apply L.prepared_eq s c e
    have hraw : ResponseNativeProbabilitySelection.prepared nativeData 1 s c =
        ResponseNativeProbabilitySelection.prepared nativeData 1 s e := by
      funext i
      exact (native_responseEq_iff_eq _ _).mp (h i)
    simpa only [native_prepared] using hraw
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

theorem nativeLawOfScalar_probability (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob ℂ Bool nativeData 1 (nativeLawOfScalar L) =
      @NativeVacuumProbabilityFamily.Law.prob L := rfl

/-- A separate supplied-model consistency witness, not a premise used by the
generic response probability-selection theorem. -/
def nativeLaw : ResponseNativeProbabilitySelection.Law nativeData 1 :=
  nativeLawOfScalar NativeVacuumProbabilityFamily.canonicalLaw

theorem native_law_nonempty :
    Nonempty (ResponseNativeProbabilitySelection.Law nativeData 1) := ⟨nativeLaw⟩

theorem native_reference_infiniteOrder :
    ResponseNativeProbabilitySelection.ReferenceInfiniteOrder nativeData 1 :=
  ResponseNativeProbabilitySelection.reference_infiniteOrder nativeLaw native_observedTransparent

end

end IDT.QMClosure.ResponseSignatureControls
