import Proofs.QMClosure.RawOperationalHilbert
import Proofs.QMClosure.RawOperationalSeparation

namespace IDT.QMClosure.OperationalContextQuotient

noncomputable section

/-- Which of the two outputs is retained by a one-hole experiment. -/
inductive Output where
  | first
  | second
  deriving DecidableEq, Repr

def select {V : Type*} : Output → V × V → V
  | .first, p => p.1
  | .second, p => p.2

/-- A single occurrence of the hole, with arbitrary fixed references. Neither
constructor copies its variable input. Nesting permits all finite contexts. -/
inductive Context (V : Type*) where
  | hole
  | left (output : Output) (inner : Context V) (reference : V)
  | right (output : Output) (reference : V) (inner : Context V)

namespace Context

variable {V : Type*}

def eval (T : (V × V) → V × V) : Context V → V → V
  | .hole, x => x
  | .left s c r, x => select s (T (eval T c x, r))
  | .right s r c, x => select s (T (r, eval T c x))

/-- Substitute a one-hole context for the unique hole of another. -/
def plug : Context V → Context V → Context V
  | .hole, d => d
  | .left s c r, d => .left s (plug c d) r
  | .right s r c, d => .right s r (plug c d)

theorem eval_plug (T : (V × V) → V × V) (c d : Context V) (x : V) :
    eval T (plug c d) x = eval T c (eval T d x) := by
  induction c with
  | hole => rfl
  | left s c r ih => simp only [plug, eval, ih]
  | right s r c ih => simp only [plug, eval, ih]

end Context

variable {V : Type*}

/-- Universal future-context equivalence. This quantifies over all fixed
references and finite one-hole experiments, rather than a finite test suite. -/
def ObservationalEq (T : (V × V) → V × V) (W : V → ℝ) (x y : V) : Prop :=
  ∀ c : Context V, W (c.eval T x) = W (c.eval T y)

def observationalSetoid (T : (V × V) → V × V) (W : V → ℝ) : Setoid V where
  r := ObservationalEq T W
  iseqv := ⟨fun _ _ => rfl, fun h c => (h c).symm, fun h k c => (h c).trans (k c)⟩

theorem weight_eq {T : (V × V) → V × V} {W : V → ℝ} {x y : V}
    (h : ObservationalEq T W x y) : W x = W y := h .hole

theorem left_congr {T : (V × V) → V × V} {W : V → ℝ} {x y : V}
    (h : ObservationalEq T W x y) (s : Output) (r : V) :
    ObservationalEq T W (select s (T (x, r))) (select s (T (y, r))) := by
  intro c
  simpa only [Context.eval_plug, Context.eval] using h (c.plug (.left s .hole r))

theorem right_congr {T : (V × V) → V × V} {W : V → ℝ} {x y : V}
    (h : ObservationalEq T W x y) (s : Output) (r : V) :
    ObservationalEq T W (select s (T (r, x))) (select s (T (r, y))) := by
  intro c
  simpa only [Context.eval_plug, Context.eval] using h (c.plug (.right s r .hole))

theorem output_congr {T : (V × V) → V × V} {W : V → ℝ} {x x' y y' : V}
    (hx : ObservationalEq T W x x') (hy : ObservationalEq T W y y') (s : Output) :
    ObservationalEq T W (select s (T (x, y))) (select s (T (x', y'))) := by
  intro c
  exact (left_congr hx s y c).trans (right_congr hy s x' c)

/-- Any weight-preserving relation stable under both outputs in both slots
is contained in contextual equivalence. Even equivalence of R is unnecessary. -/
theorem relation_le_observationalEq (T : (V × V) → V × V) (W : V → ℝ)
    (R : V → V → Prop)
    (weight_preserving : ∀ x y, R x y → W x = W y)
    (left_stable : ∀ s x y r, R x y → R (select s (T (x, r))) (select s (T (y, r))))
    (right_stable : ∀ s x y r, R x y → R (select s (T (r, x))) (select s (T (r, y))))
    {x y : V} (h : R x y) : ObservationalEq T W x y := by
  intro c
  apply weight_preserving
  induction c with
  | hole => exact h
  | left s c r ih => exact left_stable s _ _ r ih
  | right s r c ih => exact right_stable s _ _ r ih

/-- The raw laws are only observational square-swap and first-channel
mediality. Positivity and exact total conservation remain universal premises. -/
structure ObservedData (V : Type*) where
  chosenZero : V
  operation : (V × V) → V × V
  weight : V → ℝ
  vacuum : weight chosenZero = 0
  nonnegative : ∀ x, 0 ≤ weight x
  conserved : ∀ x y,
    weight (operation (x, y)).1 + weight (operation (x, y)).2 = weight x + weight y
  square : ∀ p,
    ObservationalEq operation weight (operation (operation p)).1 p.2 ∧
    ObservationalEq operation weight (operation (operation p)).2 p.1
  medial : ∀ a b c d,
    ObservationalEq operation weight
      (MedialSwapRoot.firstChannel operation
        (MedialSwapRoot.firstChannel operation a b) (MedialSwapRoot.firstChannel operation c d))
      (MedialSwapRoot.firstChannel operation
        (MedialSwapRoot.firstChannel operation a c) (MedialSwapRoot.firstChannel operation b d))

namespace ObservedData

variable (d : ObservedData V)

abbrev Space := Quotient (observationalSetoid d.operation d.weight)

def classOf (x : V) : Space d := Quotient.mk _ x

def quotientWeight (x : Space d) : ℝ :=
  Quotient.liftOn x d.weight (fun _ _ h => weight_eq h)

def quotientOutput (s : Output) (x y : Space d) : Space d :=
  Quotient.liftOn₂ x y (fun a b => d.classOf (select s (d.operation (a, b))))
    (fun _ _ _ _ hx hy => Quotient.sound (output_congr hx hy s))

def quotientOperation (p : Space d × Space d) : Space d × Space d :=
  (d.quotientOutput .first p.1 p.2, d.quotientOutput .second p.1 p.2)

@[simp] theorem quotientWeight_class (x : V) : d.quotientWeight (d.classOf x) = d.weight x := rfl

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

/-- Congruence is derived above from context composition, never supplied as a
bridge premise. The descended operation has exact structural equations. -/
def quotientData : RawOperationalHilbert.Data (Space d) where
  chosenZero := d.classOf d.chosenZero
  operation := d.quotientOperation
  square := d.quotient_square
  medial := d.quotient_medial
  weight := d.quotientWeight
  vacuum := d.vacuum
  nonnegative x := by
    induction x using Quotient.inductionOn with | _ x => exact d.nonnegative x
  conserved x y := by
    induction x using Quotient.inductionOn with | _ x =>
      induction y using Quotient.inductionOn with | _ y => exact d.conserved x y

/-- The complete complex inner product space is a constructed output. -/
abbrev Hilbert := d.quotientData.Hilbert

/-- A feature map from the original raw carrier, without raw carrier algebra. -/
def feature (x : V) : Hilbert d := d.quotientData.feature (d.classOf x)

theorem norm_feature_sq (x : V) : ‖d.feature x‖ ^ 2 = d.weight x :=
  d.quotientData.norm_feature_sq (d.classOf x)

theorem feature_zero : d.feature d.chosenZero = 0 := d.quotientData.feature_zero

/-- Contextual equivalence descends through the quotient feature. -/
theorem feature_eq_of_observationalEq {x y : V}
    (h : ObservationalEq d.operation d.weight x y) : d.feature x = d.feature y :=
  congrArg d.quotientData.feature (Quotient.sound h)

theorem feature_left_stable (s : Output) {x y : V} (r : V)
    (h : d.feature x = d.feature y) :
    d.feature (select s (d.operation (x, r))) =
      d.feature (select s (d.operation (y, r))) := by
  have hn := (d.quotientData.feature_eq_iff (d.classOf x) (d.classOf y)).mp h
  rw [RawOperationalSeparation.difference_eq] at hn
  cases s with
  | first =>
    apply (d.quotientData.feature_eq_iff _ _).mpr
    change d.quotientData.weight (d.quotientData.difference
      (d.quotientData.operation (d.classOf x, d.classOf r)).1
      (d.quotientData.operation (d.classOf y, d.classOf r)).1) = 0
    rw [RawOperationalSeparation.raw_first_left_distance, hn, zero_div]
  | second =>
    apply (d.quotientData.feature_eq_iff _ _).mpr
    change d.quotientData.weight (d.quotientData.difference
      (d.quotientData.operation (d.classOf x, d.classOf r)).2
      (d.quotientData.operation (d.classOf y, d.classOf r)).2) = 0
    rw [RawOperationalSeparation.raw_second_left_distance, hn, zero_div]

theorem feature_right_stable (s : Output) {x y : V} (r : V)
    (h : d.feature x = d.feature y) :
    d.feature (select s (d.operation (r, x))) =
      d.feature (select s (d.operation (r, y))) := by
  have hn := (d.quotientData.feature_eq_iff (d.classOf x) (d.classOf y)).mp h
  rw [RawOperationalSeparation.difference_eq] at hn
  cases s with
  | first =>
    apply (d.quotientData.feature_eq_iff _ _).mpr
    change d.quotientData.weight (d.quotientData.difference
      (d.quotientData.operation (d.classOf r, d.classOf x)).1
      (d.quotientData.operation (d.classOf r, d.classOf y)).1) = 0
    rw [RawOperationalSeparation.raw_first_right_distance, hn, zero_div]
  | second =>
    apply (d.quotientData.feature_eq_iff _ _).mpr
    change d.quotientData.weight (d.quotientData.difference
      (d.quotientData.operation (d.classOf r, d.classOf x)).2
      (d.quotientData.operation (d.classOf r, d.classOf y)).2) = 0
    rw [RawOperationalSeparation.raw_second_right_distance, hn, zero_div]

/-- Constructed feature equality is exactly equivalence in all contexts of
the stated grammar. Universal observed laws and references remain premises. -/
theorem feature_eq_iff_observationalEq (x y : V) :
    d.feature x = d.feature y ↔ ObservationalEq d.operation d.weight x y := by
  constructor
  · intro h
    apply relation_le_observationalEq d.operation d.weight
      (fun a b => d.feature a = d.feature b) _ _ _ h
    · intro a b hab
      rw [← d.norm_feature_sq a, ← d.norm_feature_sq b, hab]
    · intro s a b r hab; exact d.feature_left_stable s r hab
    · intro s a b r hab; exact d.feature_right_stable s r hab
  · exact d.feature_eq_of_observationalEq

/-- All original native references suffice. Choosing representatives proves
surjectivity of reference quantification, not a physical control procedure. -/
theorem feature_eq_iff_single_tests (x y : V) :
    d.feature x = d.feature y ↔
      ∀ z, d.weight (d.operation (x, z)).1 = d.weight (d.operation (y, z)).1 := by
  constructor
  · intro h z
    exact (RawOperationalSeparation.feature_eq_iff_raw_tests d.quotientData
      (d.classOf x) (d.classOf y)).mp h (d.classOf z)
  · intro h
    apply (RawOperationalSeparation.feature_eq_iff_raw_tests d.quotientData
      (d.classOf x) (d.classOf y)).mpr
    intro z
    induction z using Quotient.inductionOn with | _ z => exact h z

theorem observationalEq_iff_single_tests (x y : V) :
    ObservationalEq d.operation d.weight x y ↔
      ∀ z, d.weight (d.operation (x, z)).1 = d.weight (d.operation (y, z)).1 := by
  rw [← d.feature_eq_iff_observationalEq, d.feature_eq_iff_single_tests]

theorem quotient_feature_injective : Function.Injective d.quotientData.feature := by
  intro x y
  induction x using Quotient.inductionOn with | _ x =>
    induction y using Quotient.inductionOn with | _ y =>
      intro h
      exact Quotient.sound ((d.feature_eq_iff_observationalEq x y).mp h)

theorem denseRange_feature : DenseRange d.feature := by
  have hr : Set.range d.feature = Set.range d.quotientData.feature := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨d.classOf x, rfl⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := Quotient.exists_rep x
      exact ⟨y, congrArg d.quotientData.feature hy⟩
  change Dense (Set.range d.feature)
  rw [hr]
  exact d.quotientData.denseRange_feature

end ObservedData

/-- Universal laws remain supplied and mathematical reconstruction does not
establish availability, copying, actualization, or physical closure. -/
inductive BoundaryRole where
  | suppliedAllContextsAndAllReferences
  | noCopyingInOneHoleContextGrammar
  | derivedBothOutputBothSlotCongruence
  | suppliedObservationalSquareAndMedialLaws
  | suppliedGlobalPositiveConservedRealReadout
  | exactQuotientLawsAndConstructedHilbertOutput
  | noRawAlgebraScalarsOrTopologyPremise
  | provedFeatureEqualityExactlyMatchesContextualEquivalence
  | singleOutputAllNativeReferenceTestsSuffice
  | quotientFeatureInjectiveWithDenseImage
  | doesNotDeriveContextFirstPrimitiveBase
  | doesNotProveEventsAvailabilityCopyingOrFullQM
  | noManifestStatusUpgrade
  deriving DecidableEq, Repr

end

end IDT.QMClosure.OperationalContextQuotient
