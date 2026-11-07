import Proofs.QMClosure.NativeRecipeContextRealization
import Proofs.QMClosure.ResponseSourceLocalProbability

/-!
# Original response-context reflection for finite same-source recipes

Two source-local full-context diagonal premises identify the original raw
recipe semantics with the normalized quotient semantics. References inside
the compiled ideal context are source-generated recipes. The outer ResponseEq
still quantifies over every original finite context with arbitrary raw references.

Realizes is the existing syntactic compiler certificate; its scalar expression
does not supply complex coordinates on the original raw carrier. No probability
law, numerical signature, positive weight, infinite-order reference or Hilbert
premise is added. Statements concern selected event values and contextual
equivalence, not equality of full arrays or histories. Injective algebraic
halving supplies no native amplification or physical outcome actualization.
-/

namespace IDT.QMClosure.ResponseRecipeContextReflection

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open OperationalContextQuotient ResponseContextQuotient
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open NativeGaussianResponse NativeRecipeContextRealization
open ResponseSourceLocalProbability SourceLocalOriginalSemantics
open ReferenceOccurrenceCompilation (referenceCount)
open RawNativeDyadicSemantics (halfPower)

variable {V Ω : Type*}
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def originalEvent (d : Data V Ω) (v : V) (s : ι) (e : Event ι) : V :=
  ResponseNativeProbabilitySelection.prepared d v (sourceAt s e.level) e.circuit e.port

def idealOriginalContext (d : Data V Ω) (v : V) (s : ι)
    (C : Context (Event ι)) (e : Event ι) : V :=
  Context.eval d.operation (mapRefs (originalEvent d v s) C) (originalEvent d v s e)

/-- Original quotient classes commute with arbitrary original contexts; no
source-local premise is needed for this structural quotient statement. -/
theorem context_eval_class (d : Data V Ω) (C : Context V) (x : V) :
    d.classOf (C.eval d.operation x) =
      (mapRefs d.classOf C).eval d.quotientOperation (d.classOf x) := by
  induction C with
  | hole => rfl
  | left o C r ih =>
    change d.classOf (select o (d.operation (C.eval d.operation x, r))) =
      select o (d.quotientOperation
        ((mapRefs d.classOf C).eval d.quotientOperation (d.classOf x), d.classOf r))
    rw [← ih]
    cases o <;> rfl
  | right o r C ih =>
    change d.classOf (select o (d.operation (r, C.eval d.operation x))) =
      select o (d.quotientOperation
        (d.classOf r, (mapRefs d.classOf C).eval d.quotientOperation (d.classOf x)))
    rw [← ih]
    cases o <;> rfl

theorem mapRefs_comp {A B D : Type*} (f : A → B) (h : B → D) (C : Context A) :
    mapRefs h (mapRefs f C) = mapRefs (h ∘ f) C := by
  induction C with
  | hole => rfl
  | left o C r ih => simp only [mapRefs, ih, Function.comp_apply]
  | right o r C ih => simp only [mapRefs, ih, Function.comp_apply]

omit [Fintype ι] in
theorem originalEvent_class (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (s : ι) (e : Event ι) :
    d.classOf (originalEvent d v s e) = rawEvent d.quotientData (d.classOf v) s e := by
  have h := congrFun (ResponseSourceLocalProbability.originalPrepared_eq_class d v
    (sourceAt s e.level) e.circuit) e.port
  have hn := SourceLocalOriginalSemantics.originalPrepared_eq_prepared
    d.quotientData (d.classOf v)
    ((diagonalFixed_iff_quotient_fixed d d.chosenZero).mp hz)
    ((diagonalFixed_iff_quotient_fixed d v).mp hv)
    (sourceAt s e.level) e.circuit
  exact h.symm.trans (congrFun hn e.port)

omit [Fintype ι] in
/-- Fixedness of event values follows from fixedness of the complete basis
input array and preservation by the original evaluator. -/
theorem rawEvent_fixed (r : WeightFreeRawProbability.RawOperationalData V) (v : V)
    (hz : g r r.chosenZero = r.chosenZero) (hv : g r v = v)
    (s : ι) (e : Event ι) :
    g r (rawEvent r v s e) = rawEvent r v s e := by
  unfold rawEvent
  have heq := congrFun (originalPrepared_eq_prepared r v hz hv
    (sourceAt s e.level) e.circuit) e.port
  have hfixed : g r (WeightFreeRawProbability.originalPrepared r v
      (sourceAt s e.level) e.circuit e.port) =
      WeightFreeRawProbability.originalPrepared r v (sourceAt s e.level) e.circuit e.port :=
    evalRaw_fixed r e.circuit
      (WeightFreeRawProbability.basisInput r v (sourceAt s e.level))
      (basisInput_fixed r v hz hv (sourceAt s e.level)) e.port
  exact (congrArg (g r) heq.symm).trans (hfixed.trans heq)

theorem originalEvent_class_fixed (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (s : ι) (e : Event ι) :
    g d.quotientData (d.classOf (originalEvent d v s e)) =
      d.classOf (originalEvent d v s e) := by
  rw [originalEvent_class d v hz hv]
  exact rawEvent_fixed d.quotientData (d.classOf v)
    ((diagonalFixed_iff_quotient_fixed d d.chosenZero).mp hz)
    ((diagonalFixed_iff_quotient_fixed d v).mp hv) s e

theorem selected_output_fixed (r : WeightFreeRawProbability.RawOperationalData V)
    (o : Output) (x y : V) (hx : g r x = x) (hy : g r y = y) :
    g r (select o (r.operation (x, y))) = select o (r.operation (x, y)) := by
  have hp : G r (x, y) = (x, y) := Prod.ext hx hy
  have h := operation_G r (x, y)
  rw [hp] at h
  cases o with
  | first => exact (congrArg Prod.fst h).symm
  | second => exact (congrArg Prod.snd h).symm

theorem context_eval_fixed (r : WeightFreeRawProbability.RawOperationalData V)
    {A : Type*} (f : A → V) (hf : ∀ a, g r (f a) = f a)
    (C : Context A) (x : V) (hx : g r x = x) :
    g r ((mapRefs f C).eval r.operation x) = (mapRefs f C).eval r.operation x := by
  induction C with
  | hole => exact hx
  | left o C ref ih => exact selected_output_fixed r o _ _ ih (hf ref)
  | right o ref C ih => exact selected_output_fixed r o _ _ (hf ref) ih

/-- Original and normalized contexts agree whenever each supplied reference
and the hole value are diagonal-fixed. This asserts no availability of g. -/
theorem context_eval_eq_normalized (r : WeightFreeRawProbability.RawOperationalData V)
    {A : Type*} (f : A → V) (hf : ∀ a, g r (f a) = f a)
    (C : Context A) (x : V) (hx : g r x = x) :
    (mapRefs f C).eval r.operation x = (mapRefs f C).eval r.normalizedOperation x := by
  induction C with
  | hole => rfl
  | left o C ref ih =>
    change select o (r.operation ((mapRefs f C).eval r.operation x, f ref)) =
      select o (r.normalizedOperation ((mapRefs f C).eval r.normalizedOperation x, f ref))
    rw [← ih]
    exact congrArg (select o) ((gate_eq_iff r _ _).mpr
      ⟨context_eval_fixed r f hf C x hx, hf ref⟩).symm
  | right o ref C ih =>
    change select o (r.operation (f ref, (mapRefs f C).eval r.operation x)) =
      select o (r.normalizedOperation (f ref, (mapRefs f C).eval r.normalizedOperation x))
    rw [← ih]
    exact congrArg (select o) ((gate_eq_iff r _ _).mpr
      ⟨hf ref, context_eval_fixed r f hf C x hx⟩).symm

theorem idealOriginalContext_class (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (s : ι) (C : Context (Event ι)) (e : Event ι) :
    d.classOf (idealOriginalContext d v s C e) =
      rawIdealContext d.quotientData (d.classOf v) s C e := by
  unfold idealOriginalContext
  rw [context_eval_class, mapRefs_comp]
  have hf : (d.classOf ∘ originalEvent d v s) =
      rawEvent d.quotientData (d.classOf v) s := by
    funext a
    exact originalEvent_class d v hz hv s a
  rw [hf, originalEvent_class d v hz hv]
  exact context_eval_eq_normalized d.quotientData
    (rawEvent d.quotientData (d.classOf v) s)
    (rawEvent_fixed d.quotientData (d.classOf v)
      ((diagonalFixed_iff_quotient_fixed d d.chosenZero).mp hz)
      ((diagonalFixed_iff_quotient_fixed d v).mp hv) s)
    C (rawEvent d.quotientData (d.classOf v) s e)
    (rawEvent_fixed d.quotientData (d.classOf v)
      ((diagonalFixed_iff_quotient_fixed d d.chosenZero).mp hz)
      ((diagonalFixed_iff_quotient_fixed d v).mp hv) s e)

/-- Every existing compiler witness has the stated original quotient value. -/
theorem original_realization_class (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (s : ι) (C : Context (Event ι)) (e E : Event ι) (hE : Realizes s C e E) :
    d.classOf (originalEvent d v s E) =
      halfPower d.quotientData.zeroWeightData (referenceCount C)
        (d.classOf (idealOriginalContext d v s C e)) := by
  rw [originalEvent_class d v hz hv, idealOriginalContext_class d v hz hv]
  exact raw_realization_of_scalar d.quotientData (d.classOf v) s C e E hE

/-- Same C on both sides: equal attenuation cancels injectively in the
quotient. Outer equivalence still uses every arbitrary-reference raw context. -/
theorem realization_responseEq_iff (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (s : ι) (C : Context (Event ι)) (e f E F : Event ι)
    (hE : Realizes s C e E) (hF : Realizes s C f F) :
    ResponseEq d.operation d.signature (originalEvent d v s E) (originalEvent d v s F) ↔
      ResponseEq d.operation d.signature
        (idealOriginalContext d v s C e) (idealOriginalContext d v s C f) := by
  rw [← d.classOf_eq_iff_responseEq, ← d.classOf_eq_iff_responseEq]
  rw [originalEvent_class d v hz hv, originalEvent_class d v hz hv,
    idealOriginalContext_class d v hz hv, idealOriginalContext_class d v hz hv]
  exact raw_realization_eq_iff d.quotientData (d.classOf v) s C e f E F hE hF

theorem realization_not_responseEq_iff (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (s : ι) (C : Context (Event ι)) (e f E F : Event ι)
    (hE : Realizes s C e E) (hF : Realizes s C f F) :
    ¬ ResponseEq d.operation d.signature (originalEvent d v s E) (originalEvent d v s F) ↔
      ¬ ResponseEq d.operation d.signature
        (idealOriginalContext d v s C e) (idealOriginalContext d v s C f) :=
  not_congr (realization_responseEq_iff d v hz hv s C e f E F hE hF)

theorem realize_responseEq_iff (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (s : ι) (C : Context (Event ι)) (e f : Event ι) :
    ResponseEq d.operation d.signature
      (originalEvent d v s (realize s C e)) (originalEvent d v s (realize s C f)) ↔
      ResponseEq d.operation d.signature
        (idealOriginalContext d v s C e) (idealOriginalContext d v s C f) :=
  realization_responseEq_iff d v hz hv s C e f _ _
    (realize_spec s C e) (realize_spec s C f)

end
end IDT.QMClosure.ResponseRecipeContextReflection
