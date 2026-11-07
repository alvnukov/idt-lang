import Proofs.QMClosure.OperationalContextQuotient
import Proofs.QMClosure.WeightFreeRawProbability

/-!
# Contextual equivalence for an arbitrary supplied response signature

The raw input supplies a chosen zero, an operation, and a signature `V → Ω`.
The codomain is arbitrary: no real weight, positivity, conservation, norm,
inner product, or Hilbert feature is part of this input contract. The existing
one-hole `Context` and `plug` grammar is reused unchanged, with all of its
arbitrary fixed references and finite nestings.

Response equivalence means equality of the supplied signature in every such
context. Both-output, both-slot congruence follows from context composition.
Observed square-swap and first-channel mediality therefore descend to exact
laws on contextual classes, yielding `WeightFreeRawProbability.RawOperationalData`.
The existing weight-free proof facade internally uses a constant-zero weight;
that adapter supplies no observational or probabilistic information.

An additional first-output observed diagonal-transparency premise yields full
quotient transparency. Only with this premise is the canonical normalized
quotient gate identified with the quotient of the original raw gate.

The signature may encode structural or statistical response data; its provenance
must be specified independently of the desired probability conclusion. Even a
Boolean signature does not assign actual outcomes to every incompatible
measurement context. A supplied map is not automatically a physically
available deterministic measurement outcome. Universal observed laws remain
supplied; arbitrary-reference quantification does not establish physical
availability. Detector dynamics, outcome actualization, and full QM closure are
not established.
-/

namespace IDT.QMClosure.ResponseContextQuotient

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open OperationalContextQuotient
open NativeVacuumProbabilityFamily

variable {V : Type*} {Ω : Type*}

/-- Equality of an arbitrary supplied signature in every stated response context. -/
def ResponseEq (T : (V × V) → V × V) (o : V → Ω) (x y : V) : Prop :=
  ∀ c : Context V, o (c.eval T x) = o (c.eval T y)

def responseSetoid (T : (V × V) → V × V) (o : V → Ω) : Setoid V where
  r := ResponseEq T o
  iseqv := ⟨fun _ _ => rfl, fun h c => (h c).symm, fun h k c => (h c).trans (k c)⟩

theorem signature_eq {T : (V × V) → V × V} {o : V → Ω} {x y : V}
    (h : ResponseEq T o x y) : o x = o y := h .hole

theorem left_congr {T : (V × V) → V × V} {o : V → Ω} {x y : V}
    (h : ResponseEq T o x y) (s : Output) (r : V) :
    ResponseEq T o (select s (T (x, r))) (select s (T (y, r))) := by
  intro c
  simpa only [Context.eval_plug, Context.eval] using h (c.plug (.left s .hole r))

theorem right_congr {T : (V × V) → V × V} {o : V → Ω} {x y : V}
    (h : ResponseEq T o x y) (s : Output) (r : V) :
    ResponseEq T o (select s (T (r, x))) (select s (T (r, y))) := by
  intro c
  simpa only [Context.eval_plug, Context.eval] using h (c.plug (.right s r .hole))

theorem output_congr {T : (V × V) → V × V} {o : V → Ω} {x x' y y' : V}
    (hx : ResponseEq T o x x') (hy : ResponseEq T o y y') (s : Output) :
    ResponseEq T o (select s (T (x, y))) (select s (T (x', y'))) := by
  intro c
  exact (left_congr hx s y c).trans (right_congr hy s x' c)

/-- Every signature-preserving relation stable under both outputs in both slots
is contained in response-context equivalence. -/
theorem relation_le_responseEq (T : (V × V) → V × V) (o : V → Ω)
    (R : V → V → Prop)
    (signature_preserving : ∀ x y, R x y → o x = o y)
    (left_stable : ∀ s x y r, R x y → R (select s (T (x, r))) (select s (T (y, r))))
    (right_stable : ∀ s x y r, R x y → R (select s (T (r, x))) (select s (T (r, y))))
    {x y : V} (h : R x y) : ResponseEq T o x y := by
  intro c
  apply signature_preserving
  induction c with
  | hole => exact h
  | left s c r ih => exact left_stable s _ _ r ih
  | right s r c ih => exact right_stable s _ _ r ih

/-- The raw contract has no readout weight or scalar structure. Its structural
laws are supplied only up to response-context equivalence. -/
structure Data (V : Type*) (Ω : Type*) where
  chosenZero : V
  operation : (V × V) → V × V
  signature : V → Ω
  square : ∀ p,
    ResponseEq operation signature (operation (operation p)).1 p.2 ∧
    ResponseEq operation signature (operation (operation p)).2 p.1
  medial : ∀ a b c d,
    ResponseEq operation signature
      (MedialSwapRoot.firstChannel operation
        (MedialSwapRoot.firstChannel operation a b) (MedialSwapRoot.firstChannel operation c d))
      (MedialSwapRoot.firstChannel operation
        (MedialSwapRoot.firstChannel operation a c) (MedialSwapRoot.firstChannel operation b d))

namespace Data

variable (d : Data V Ω)

abbrev Space := Quotient (responseSetoid d.operation d.signature)

def classOf (x : V) : Space d := Quotient.mk _ x

theorem classOf_eq_iff_responseEq (x y : V) :
    d.classOf x = d.classOf y ↔ ResponseEq d.operation d.signature x y :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- The original signature itself descends; no probability meaning is assigned. -/
def quotientSignature (x : Space d) : Ω :=
  Quotient.liftOn x d.signature (fun _ _ h => signature_eq h)

@[simp] theorem quotientSignature_class (x : V) :
    d.quotientSignature (d.classOf x) = d.signature x := rfl

def quotientOutput (s : Output) (x y : Space d) : Space d :=
  Quotient.liftOn₂ x y (fun a b => d.classOf (select s (d.operation (a, b))))
    (fun _ _ _ _ hx hy => Quotient.sound (output_congr hx hy s))

def quotientOperation (p : Space d × Space d) : Space d × Space d :=
  (d.quotientOutput .first p.1 p.2, d.quotientOutput .second p.1 p.2)

@[simp] theorem quotientOutput_class (s : Output) (x y : V) :
    d.quotientOutput s (d.classOf x) (d.classOf y) =
      d.classOf (select s (d.operation (x, y))) := rfl

@[simp] theorem quotientOperation_class (x y : V) :
    d.quotientOperation (d.classOf x, d.classOf y) =
      (d.classOf (d.operation (x, y)).1, d.classOf (d.operation (x, y)).2) := rfl

theorem quotient_square (p : Space d × Space d) :
    d.quotientOperation (d.quotientOperation p) = p.swap := by
  rcases p with ⟨x, y⟩
  induction x using Quotient.inductionOn with | _ x =>
    induction y using Quotient.inductionOn with | _ y =>
      apply Prod.ext
      · exact Quotient.sound (d.square (x, y)).1
      · exact Quotient.sound (d.square (x, y)).2

theorem quotient_medial (a b c e : Space d) :
    MedialSwapRoot.firstChannel d.quotientOperation
      (MedialSwapRoot.firstChannel d.quotientOperation a b)
      (MedialSwapRoot.firstChannel d.quotientOperation c e) =
    MedialSwapRoot.firstChannel d.quotientOperation
      (MedialSwapRoot.firstChannel d.quotientOperation a c)
      (MedialSwapRoot.firstChannel d.quotientOperation b e) := by
  induction a using Quotient.inductionOn with | _ a =>
    induction b using Quotient.inductionOn with | _ b =>
      induction c using Quotient.inductionOn with | _ c =>
        induction e using Quotient.inductionOn with | _ e =>
          exact Quotient.sound (d.medial a b c e)

/-- Exact weight-free operational data on the response-context quotient. -/
def quotientData : WeightFreeRawProbability.RawOperationalData (Space d) where
  chosenZero := d.classOf d.chosenZero
  operation := d.quotientOperation
  square := d.quotient_square
  medial := d.quotient_medial

end Data

/-- Only first-output diagonal transparency is supplied; square-swap supplies
the corresponding quotient statement for the second output. -/
def ObservedTransparent (d : Data V Ω) : Prop :=
  ∀ x, ResponseEq d.operation d.signature (d.operation (x, x)).1 x

theorem quotient_transparent (d : Data V Ω) (transparent : ObservedTransparent d)
    (x : d.Space) : d.quotientOperation (x, x) = (x, x) := by
  have hfirst : (d.quotientOperation (x, x)).1 = x := by
    induction x using Quotient.inductionOn with
    | _ x => exact Quotient.sound (transparent x)
  calc
    d.quotientOperation (x, x) =
        (MedialSwapRoot.firstChannel d.quotientOperation x x,
          MedialSwapRoot.firstChannel d.quotientOperation x x) :=
      MedialSwapRoot.raw_operation_eq_symmetric d.quotientOperation d.quotient_square (x, x)
    _ = (x, x) := Prod.ext hfirst hfirst

/-- Transparency identifies normalization with the original descended gate. -/
theorem quotient_normalizedOperation_eq (d : Data V Ω)
    (transparent : ObservedTransparent d) :
    d.quotientData.normalizedOperation = d.quotientOperation :=
  WeightFreeRawProbability.normalizedOperation_eq_original d.quotientData
    (quotient_transparent d transparent)

/-- Actual original-gate evaluation commutes with passage to response classes. -/
theorem evalRaw_class (d : Data V Ω) {ι : Type} [DecidableEq ι]
    (c : Native ι) (x : ι → V) :
    WeightFreeRawProbability.evalRaw d.quotientOperation c (fun i => d.classOf (x i)) =
      fun i => d.classOf (WeightFreeRawProbability.evalRaw d.operation c x i) := by
  induction c generalizing x with
  | identity => rfl
  | pair i j hij =>
    funext k
    by_cases hki : k = i
    · simp [WeightFreeRawProbability.evalRaw, hki]
    · by_cases hkj : k = j
      · simp [WeightFreeRawProbability.evalRaw, hkj, hij.symm]
      · simp [WeightFreeRawProbability.evalRaw, hki, hkj]
  | permute e => rfl
  | seq c e hc he =>
    simp only [WeightFreeRawProbability.evalRaw, hc, he]

/-- The normalized quotient evaluator denotes classes of the original raw words
only under the explicit observed-transparency premise. -/
theorem normalized_evalRaw_class (d : Data V Ω) (transparent : ObservedTransparent d)
    {ι : Type} [DecidableEq ι] (c : Native ι) (x : ι → V) :
    WeightFreeRawProbability.evalRaw d.quotientData.normalizedOperation c
        (fun i => d.classOf (x i)) =
      fun i => d.classOf (WeightFreeRawProbability.evalRaw d.operation c x i) := by
  rw [quotient_normalizedOperation_eq d transparent]
  exact evalRaw_class d c x

end

end IDT.QMClosure.ResponseContextQuotient
