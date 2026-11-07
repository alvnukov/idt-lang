import Proofs.QMClosure.ResponseNativeProbabilitySelection
import Proofs.QMClosure.SourceLocalOriginalSemantics

/-!
# Source-local probability transport on full response-context classes

Original quotient semantics requires no transparency. The later normalized
transport uses full contextual diagonal equality only at the supplied zero and
source, retaining globally observed square-swap and mediality. All six supplied
law fields and the entire probability field are preserved. Conditional selection
and a separate existence criterion do not supply an unconditional probability witness.

Contexts retain arbitrary fixed raw references at every finite nesting. The
term-defined quotient diagonal is not an available physical unary operation;
diagonal terms do not supply free copies, controls, measurements, actualization,
or full QM closure.
-/

namespace IDT.QMClosure.ResponseSourceLocalProbability

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open ResponseContextQuotient
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily

variable {V : Type*} {Ω : Type*}

theorem originalPrepared_eq_class (d : Data V Ω) (v : V)
    {ι : Type} [DecidableEq ι] (s : ι) (c : Native ι) :
    WeightFreeRawProbability.originalPrepared d.quotientData (d.classOf v) s c =
      fun i => d.classOf (ResponseNativeProbabilitySelection.prepared d v s c i) := by
  unfold WeightFreeRawProbability.originalPrepared ResponseNativeProbabilitySelection.prepared
  have hsource : WeightFreeRawProbability.basisInput d.quotientData (d.classOf v) s =
      fun i => d.classOf (ResponseNativeProbabilitySelection.basisInput d v s i) := by
    funext i
    by_cases hi : i = s <;>
      simp [WeightFreeRawProbability.basisInput,
        ResponseNativeProbabilitySelection.basisInput, hi, Data.quotientData]
  rw [hsource]
  exact evalRaw_class d c (ResponseNativeProbabilitySelection.basisInput d v s)

/-- Equality of whole original quotient arrays is exactly pointwise full
contextual equivalence, including all ancillary wires. -/
theorem responseEq_iff_originalPrepared_eq (d : Data V Ω) (v : V)
    {ι : Type} [DecidableEq ι] (s : ι) (c e : Native ι) :
    (∀ i, ResponseEq d.operation d.signature
      (ResponseNativeProbabilitySelection.prepared d v s c i)
      (ResponseNativeProbabilitySelection.prepared d v s e i)) ↔
    WeightFreeRawProbability.originalPrepared d.quotientData (d.classOf v) s c =
      WeightFreeRawProbability.originalPrepared d.quotientData (d.classOf v) s e := by
  rw [originalPrepared_eq_class, originalPrepared_eq_class]
  constructor
  · intro h
    funext i
    exact (d.classOf_eq_iff_responseEq _ _).mpr (h i)
  · intro h i
    exact (d.classOf_eq_iff_responseEq _ _).mp (congrFun h i)

abbrev OriginalLaw (d : Data V Ω) (v : V) :=
  SourceLocalOriginalSemantics.GenericOriginalLaw d.quotientData (d.classOf v)

def toOriginalLaw (d : Data V Ω) (v : V)
    (L : ResponseNativeProbabilitySelection.Law d v) : OriginalLaw d v where
  prob := L.prob
  nonnegative := L.nonnegative
  normalized := L.normalized
  prepared_eq s c e h :=
    L.prepared_eq s c e ((responseEq_iff_originalPrepared_eq d v s c e).mpr h)
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

def fromOriginalLaw (d : Data V Ω) (v : V)
    (L : OriginalLaw d v) : ResponseNativeProbabilitySelection.Law d v where
  prob := L.prob
  nonnegative := L.nonnegative
  normalized := L.normalized
  prepared_eq s c e h :=
    L.prepared_eq s c e ((responseEq_iff_originalPrepared_eq d v s c e).mp h)
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

/-- No transparency premise occurs in this equivalence. -/
def originalLawEquiv (d : Data V Ω) (v : V) :
    ResponseNativeProbabilitySelection.Law d v ≃ OriginalLaw d v where
  toFun := toOriginalLaw d v
  invFun := fromOriginalLaw d v
  left_inv L := by cases L; rfl
  right_inv L := by cases L; rfl

theorem toOriginalLaw_probability (d : Data V Ω) (v : V)
    (L : ResponseNativeProbabilitySelection.Law d v) :
    @SourceLocalOriginalSemantics.GenericOriginalLaw.prob _ d.quotientData (d.classOf v)
      (toOriginalLaw d v L) = @ResponseNativeProbabilitySelection.Law.prob V Ω d v L := rfl

theorem fromOriginalLaw_probability (d : Data V Ω) (v : V) (L : OriginalLaw d v) :
    @ResponseNativeProbabilitySelection.Law.prob V Ω d v (fromOriginalLaw d v L) =
      @SourceLocalOriginalSemantics.GenericOriginalLaw.prob _ d.quotientData (d.classOf v) L := rfl

/-- Full contextual equality, not equality of the uncontextualized signature. -/
def DiagonalFixed (d : Data V Ω) (x : V) : Prop :=
  ResponseEq d.operation d.signature (d.operation (x, x)).1 x

theorem diagonalFixed_iff_quotient_fixed (d : Data V Ω) (x : V) :
    DiagonalFixed d x ↔
      SourceLocalOriginalSemantics.g d.quotientData (d.classOf x) = d.classOf x := by
  change ResponseEq d.operation d.signature (d.operation (x, x)).1 x ↔
    d.classOf (d.operation (x, x)).1 = d.classOf x
  exact (d.classOf_eq_iff_responseEq _ _).symm

theorem observedTransparent_diagonalFixed (d : Data V Ω)
    (h : ObservedTransparent d) (x : V) : DiagonalFixed d x := h x

theorem observedTransparent_source_local (d : Data V Ω) (v : V)
    (h : ObservedTransparent d) : DiagonalFixed d d.chosenZero ∧ DiagonalFixed d v :=
  ⟨h d.chosenZero, h v⟩

def normalizedLawEquiv (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v) :
    ResponseNativeProbabilitySelection.Law d v ≃
      WeightFreeRawProbability.Law d.quotientData (d.classOf v) :=
  (originalLawEquiv d v).trans
    (SourceLocalOriginalSemantics.lawEquiv d.quotientData (d.classOf v)
      ((diagonalFixed_iff_quotient_fixed d d.chosenZero).mp hz)
      ((diagonalFixed_iff_quotient_fixed d v).mp hv))

theorem normalizedLawEquiv_probability (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (L : ResponseNativeProbabilitySelection.Law d v) :
    @RawNativeProbabilitySelection.RawLaw.prob _ d.quotientData.zeroWeightData (d.classOf v)
      (normalizedLawEquiv d v hz hv L) =
      @ResponseNativeProbabilitySelection.Law.prob V Ω d v L := rfl

theorem normalizedLawEquiv_symm_probability (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (L : WeightFreeRawProbability.Law d.quotientData (d.classOf v)) :
    @ResponseNativeProbabilitySelection.Law.prob V Ω d v
      ((normalizedLawEquiv d v hz hv).symm L) =
      @RawNativeProbabilitySelection.RawLaw.prob _ d.quotientData.zeroWeightData (d.classOf v) L := rfl

/-- The supplied law is a premise; no witness or infinite-order premise is added. -/
theorem probability_eq_normSq (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (L : ResponseNativeProbabilitySelection.Law d v)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι) :
    L.prob s c i = Complex.normSq (c.eval (source s) i) :=
  WeightFreeRawProbability.probability_eq_normSq d.quotientData (d.classOf v)
    (normalizedLawEquiv d v hz hv L) s c i

theorem probability_fields_equal (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v)
    (L M : ResponseNativeProbabilitySelection.Law d v) :
    @ResponseNativeProbabilitySelection.Law.prob V Ω d v L =
      @ResponseNativeProbabilitySelection.Law.prob V Ω d v M := by
  funext α instF instD s c i
  exact (probability_eq_normSq d v hz hv L s c i).trans
    (probability_eq_normSq d v hz hv M s c i).symm

/-- Separate existence boundary; the two fixed classes alone do not give a law. -/
theorem law_nonempty_iff_reference_infiniteOrder (d : Data V Ω) (v : V)
    (hz : DiagonalFixed d d.chosenZero) (hv : DiagonalFixed d v) :
    Nonempty (ResponseNativeProbabilitySelection.Law d v) ↔
      WeightFreeRawProbability.ReferenceInfiniteOrder d.quotientData (d.classOf v) := by
  have he : Nonempty (ResponseNativeProbabilitySelection.Law d v) ↔
      Nonempty (WeightFreeRawProbability.Law d.quotientData (d.classOf v)) :=
    ⟨fun ⟨L⟩ => ⟨normalizedLawEquiv d v hz hv L⟩,
      fun ⟨L⟩ => ⟨(normalizedLawEquiv d v hz hv).symm L⟩⟩
  exact he.trans
    (WeightFreeRawProbability.law_nonempty_iff_reference_infiniteOrder
      d.quotientData (d.classOf v))

namespace Controls

abbrev PairCarrier := SourceLocalOriginalSemantics.Controls.PairCarrier

theorem identity_responseEq_iff (T : (PairCarrier × PairCarrier) → PairCarrier × PairCarrier)
    (x y : PairCarrier) : ResponseEq T (fun a => a) x y ↔ x = y := by
  constructor
  · exact signature_eq
  · intro h
    subst y
    intro c
    rfl

/-- Identity signature makes full contextual equivalence literal equality;
the operation and both global laws remain the original decorated gate. -/
def data : Data PairCarrier PairCarrier where
  chosenZero := SourceLocalOriginalSemantics.Controls.fixedData.chosenZero
  operation := SourceLocalOriginalSemantics.Controls.fixedData.operation
  signature := fun x => x
  square p := by
    constructor
    · apply (identity_responseEq_iff _ _ _).mpr
      exact congrArg Prod.fst (SourceLocalOriginalSemantics.Controls.fixedData.square p)
    · apply (identity_responseEq_iff _ _ _).mpr
      exact congrArg Prod.snd (SourceLocalOriginalSemantics.Controls.fixedData.square p)
  medial a b c d :=
    (identity_responseEq_iff _ _ _).mpr
      (SourceLocalOriginalSemantics.Controls.fixedData.medial a b c d)

def fixedSource : PairCarrier := SourceLocalOriginalSemantics.Controls.fixedSource

theorem zero_fixed : DiagonalFixed data data.chosenZero := by
  apply (identity_responseEq_iff _ _ _).mpr
  change SourceLocalOriginalSemantics.g
    SourceLocalOriginalSemantics.Controls.fixedData
    SourceLocalOriginalSemantics.Controls.fixedData.chosenZero =
      SourceLocalOriginalSemantics.Controls.fixedData.chosenZero
  exact SourceLocalOriginalSemantics.Controls.fixedData_zero_fixed

theorem source_fixed : DiagonalFixed data fixedSource := by
  apply (identity_responseEq_iff _ _ _).mpr
  change SourceLocalOriginalSemantics.g
    SourceLocalOriginalSemantics.Controls.fixedData
    SourceLocalOriginalSemantics.Controls.fixedSource =
      SourceLocalOriginalSemantics.Controls.fixedSource
  exact SourceLocalOriginalSemantics.Controls.fixedData_source_fixed

theorem not_globally_transparent : ¬ ObservedTransparent data := by
  intro h
  have hp := (identity_responseEq_iff _ _ _).mp (h (0, 1))
  change (OriginalGateProbabilityWall.operation ((0, 1), (0, 1))).1 = (0, 1) at hp
  rw [OriginalGateProbabilityWall.operation_diagonal] at hp
  have hm := congrArg Prod.snd hp
  norm_num [OriginalGateProbabilityWall.diagonal] at hm

/-- Strictness of sufficient hypotheses; no necessity claim for uniqueness. -/
theorem source_local_without_global :
    DiagonalFixed data data.chosenZero ∧ DiagonalFixed data fixedSource ∧
      ¬ ObservedTransparent data :=
  ⟨zero_fixed, source_fixed, not_globally_transparent⟩

end Controls
end
end IDT.QMClosure.ResponseSourceLocalProbability
