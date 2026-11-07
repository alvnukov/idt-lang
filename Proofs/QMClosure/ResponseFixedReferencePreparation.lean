import Proofs.QMClosure.RawFixedReferencePreparation
import Proofs.QMClosure.FixedReferenceProgramCompilation
import Proofs.QMClosure.ResponseSourceLocalProbability
import Proofs.QMClosure.ResponseAllocatedUniversalPeriodBridge

/-!
# Explicit fixed-reference preparation on response-context classes

The raw nested first-channel term retracts onto diagonal-fixed response classes.
Only contextual fixedness is asserted: the supplied raw laws need not hold as
literal state equalities. The preparation uses three supplied copies and retains
all three circuit outputs; it does not copy an unknown source or discard garbage.

Rebasing uses the actual selected raw outputs for the chosen zero and source.
Both source-local fixedness premises follow, but the preparation has changed.
No preservation of an old law, calibration, source information, or noncollapse
is established here.
The six-field probability law remains supplied, with a separate infinite-order
existence criterion on the rebased quotient and source. Full QM is not derived.
-/

namespace IDT.QMClosure.ResponseFixedReferencePreparation

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open ResponseContextQuotient ResponseSourceLocalProbability
open MedialSwapRoot MixerGeneratedProcessWall NativeVacuumProbabilityFamily

variable {V : Type*} {Ω : Type*}

/-- A raw term, with no literal raw fixedness conclusion. -/
def rawRetract (d : Data V Ω) (x : V) : V :=
  RawFixedReferencePreparation.retract (firstChannel d.operation) x

/-- The raw term commutes with passage to full response-context classes. -/
theorem class_rawRetract (d : Data V Ω) (x : V) :
    d.classOf (rawRetract d x) =
      RawFixedReferencePreparation.rawRetract d.quotientData (d.classOf x) := rfl

/-- Every prepared class is fixed; equality is quantified over all contexts. -/
theorem rawRetract_diagonalFixed (d : Data V Ω) (x : V) :
    DiagonalFixed d (rawRetract d x) := by
  apply (diagonalFixed_iff_quotient_fixed d _).mpr
  rw [class_rawRetract]
  exact RawFixedReferencePreparation.g_rawRetract_fixed d.quotientData (d.classOf x)

/-- Preparation retracts an already fixed class, without claiming raw equality. -/
theorem rawRetract_responseEq_of_diagonalFixed (d : Data V Ω) (x : V)
    (hx : DiagonalFixed d x) :
    ResponseEq d.operation d.signature (rawRetract d x) x := by
  apply (d.classOf_eq_iff_responseEq _ _).mp
  rw [class_rawRetract]
  exact RawFixedReferencePreparation.rawRetract_eq_self_of_fixed d.quotientData
    (d.classOf x) ((diagonalFixed_iff_quotient_fixed d x).mp hx)

/-- Repeating preparation changes no response-context class. -/
theorem rawRetract_responseEq_idempotent (d : Data V Ω) (x : V) :
    ResponseEq d.operation d.signature (rawRetract d (rawRetract d x))
      (rawRetract d x) :=
  rawRetract_responseEq_of_diagonalFixed d _ (rawRetract_diagonalFixed d x)

/-- All three outputs of the actual original-operation word are retained. -/
def rawCircuitOutputs (d : Data V Ω) (x : V) : Fin 3 → V :=
  WeightFreeRawProbability.evalRaw d.operation
    RawFixedReferencePreparation.fixedReferenceWord (fun _ => x)

/-- The actual selected raw output, rather than a quotient representative choice. -/
def preparedReference (d : Data V Ω) (x : V) : V := rawCircuitOutputs d x 2

/-- Full-array class transport keeps both unselected outputs visible. -/
theorem rawCircuitOutputs_class (d : Data V Ω) (x : V) :
    (fun i => d.classOf (rawCircuitOutputs d x i)) =
      ![d.classOf (firstChannel d.operation (firstChannel d.operation x x) x),
        d.classOf (firstChannel d.operation (firstChannel d.operation x x)
          (firstChannel d.operation x (firstChannel d.operation x x))),
        d.classOf (rawRetract d x)] := by
  change (fun i => d.classOf (WeightFreeRawProbability.evalRaw d.operation
    RawFixedReferencePreparation.fixedReferenceWord (fun _ => x) i)) = _
  rw [← evalRaw_class d RawFixedReferencePreparation.fixedReferenceWord (fun _ => x)]
  exact RawFixedReferencePreparation.evalRaw_fixedReferenceWord d.quotientData (d.classOf x)

/-- Only contextual equality identifies the actual selected output with the term. -/
theorem class_preparedReference (d : Data V Ω) (x : V) :
    d.classOf (preparedReference d x) = d.classOf (rawRetract d x) := by
  calc
    d.classOf (preparedReference d x) =
        WeightFreeRawProbability.evalRaw d.quotientOperation
          RawFixedReferencePreparation.fixedReferenceWord (fun _ => d.classOf x) 2 :=
      (congrFun (evalRaw_class d RawFixedReferencePreparation.fixedReferenceWord
        (fun _ => x)) 2).symm
    _ = RawFixedReferencePreparation.rawRetract d.quotientData (d.classOf x) :=
      RawFixedReferencePreparation.evalRaw_fixedReferenceWord_selected
        d.quotientData (d.classOf x)
    _ = d.classOf (rawRetract d x) := (class_rawRetract d x).symm

theorem preparedReference_responseEq (d : Data V Ω) (x : V) :
    ResponseEq d.operation d.signature (preparedReference d x) (rawRetract d x) :=
  (d.classOf_eq_iff_responseEq _ _).mp (class_preparedReference d x)

theorem preparedReference_diagonalFixed (d : Data V Ω) (x : V) :
    DiagonalFixed d (preparedReference d x) := by
  apply (diagonalFixed_iff_quotient_fixed d _).mpr
  rw [class_preparedReference]
  exact (diagonalFixed_iff_quotient_fixed d _).mp (rawRetract_diagonalFixed d x)

/-- The same raw operation, signature and observed laws, with an actually prepared zero. -/
def rebased (d : Data V Ω) : Data V Ω :=
  { d with chosenZero := preparedReference d d.chosenZero }

/-- The actual changed source preparation; no injectivity or information claim. -/
def processedSource (d : Data V Ω) (v : V) : V := preparedReference d v

theorem rebased_zero_diagonalFixed (d : Data V Ω) :
    DiagonalFixed (rebased d) (rebased d).chosenZero :=
  preparedReference_diagonalFixed d d.chosenZero

theorem processedSource_diagonalFixed (d : Data V Ω) (v : V) :
    DiagonalFixed (rebased d) (processedSource d v) :=
  preparedReference_diagonalFixed d v

/-- Both old fixedness premises are discharged for the changed preparation. -/
theorem rebased_source_local (d : Data V Ω) (v : V) :
    DiagonalFixed (rebased d) (rebased d).chosenZero ∧
      DiagonalFixed (rebased d) (processedSource d v) :=
  ⟨rebased_zero_diagonalFixed d, processedSource_diagonalFixed d v⟩

/-- Compiler preparation is the same actual original-operation selected value. -/
theorem compiler_preparedValue_eq (d : Data V Ω) (x : V) :
    FixedReferenceProgramCompilation.preparedValue d.operation x = preparedReference d x := rfl

/-- Exact selected raw semantics for arbitrary tagged programs. The compiler
retains all garbage outputs and triples each supplied input allocation. -/
theorem compile_eval_rebased (d : Data V Ω) {S : Type*} (stock : S → V)
    (p : AllocatedPreparation.Program S) :
    AllocatedPreparation.eval d.operation d.chosenZero stock
        (FixedReferenceProgramCompilation.compile p) =
      AllocatedPreparation.eval (rebased d).operation (rebased d).chosenZero
        (fun s => preparedReference d (stock s)) p :=
  FixedReferenceProgramCompilation.compile_eval d.operation d.chosenZero stock p

/-- Literal raw-value equality with the changed preparation, not a law transport. -/
theorem compile_rawValue (d : Data V Ω) (v : V)
    (p : NativeAllocatedSourceArithmetic.ScalarProgram) :
    ResponseAllocatedFaithfulness.rawValue d v (FixedReferenceProgramCompilation.compile p) =
      ResponseAllocatedFaithfulness.rawValue (rebased d) (processedSource d v) p :=
  compile_eval_rebased d (fun _ : Unit => v) p

/-- Reference iteration toward a compiled recipe is literally the rebased step. -/
theorem rawReferenceStep_rebased (d : Data V Ω) (v : V)
    (r : NativeAllocatedSourceArithmetic.ScalarProgram) :
    ResponseAllocatedStableBridge.rawReferenceStep (rebased d) (processedSource d v) r =
      ResponseAllocatedStableBridge.rawReferenceStep d v
        (FixedReferenceProgramCompilation.compile r) := by
  funext x
  change (d.operation
      (x, ResponseAllocatedFaithfulness.rawValue (rebased d) (processedSource d v) r)).1 =
    (d.operation
      (x, ResponseAllocatedFaithfulness.rawValue d v
        (FixedReferenceProgramCompilation.compile r))).1
  rw [compile_rawValue]

/-- The original raw predicate restricted to the compiler image. No surjectivity,
noncollapse, or arbitrary-original-program separation is asserted. -/
def CompiledNoCommonPositivePeriod (d : Data V Ω) (v : V) : Prop :=
  ∀ L : ℕ, 0 < L → ∃ r p : NativeAllocatedSourceArithmetic.ScalarProgram,
    d.signature
        ((ResponseAllocatedStableBridge.rawReferenceStep d v
          (FixedReferenceProgramCompilation.compile r))^[L]
          (ResponseAllocatedFaithfulness.rawValue d v
            (FixedReferenceProgramCompilation.compile p))) ≠
      d.signature (ResponseAllocatedFaithfulness.rawValue d v
        (FixedReferenceProgramCompilation.compile p))

/-- Exact all-positive-length predicate transfer on the compiler image only. -/
theorem compiledNoCommonPositivePeriod_iff (d : Data V Ω) (v : V) :
    CompiledNoCommonPositivePeriod d v ↔
      ResponseAllocatedUniversalPeriodBridge.RawNoCommonPositivePeriod
        (rebased d) (processedSource d v) := by
  unfold CompiledNoCommonPositivePeriod
    ResponseAllocatedUniversalPeriodBridge.RawNoCommonPositivePeriod
  simp only [← rawReferenceStep_rebased, compile_rawValue]
  rfl

/-- The rebased six-field law is still an explicit premise. -/
theorem probability_eq_normSq (d : Data V Ω) (v : V)
    (L : ResponseNativeProbabilitySelection.Law (rebased d) (processedSource d v))
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι) :
    L.prob s c i = Complex.normSq (c.eval (source s) i) :=
  ResponseSourceLocalProbability.probability_eq_normSq (rebased d) (processedSource d v)
    (rebased_zero_diagonalFixed d) (processedSource_diagonalFixed d v) L s c i

/-- Uniqueness of the probability field, conditional on supplied rebased laws. -/
theorem probability_fields_equal (d : Data V Ω) (v : V)
    (L M : ResponseNativeProbabilitySelection.Law (rebased d) (processedSource d v)) :
    @ResponseNativeProbabilitySelection.Law.prob V Ω (rebased d) (processedSource d v) L =
      @ResponseNativeProbabilitySelection.Law.prob V Ω (rebased d) (processedSource d v) M :=
  ResponseSourceLocalProbability.probability_fields_equal (rebased d) (processedSource d v)
    (rebased_zero_diagonalFixed d) (processedSource_diagonalFixed d v) L M

/-- Separate existence criterion for the rebased quotient and processed source. -/
theorem law_nonempty_iff_reference_infiniteOrder (d : Data V Ω) (v : V) :
    Nonempty (ResponseNativeProbabilitySelection.Law (rebased d) (processedSource d v)) ↔
      WeightFreeRawProbability.ReferenceInfiniteOrder (rebased d).quotientData
        ((rebased d).classOf (processedSource d v)) :=
  ResponseSourceLocalProbability.law_nonempty_iff_reference_infiniteOrder
    (rebased d) (processedSource d v)
    (rebased_zero_diagonalFixed d) (processedSource_diagonalFixed d v)

/-- A sufficient rebased law still requires the rebased no-common-period
witness and a supplied scalar law; no witness is transferred from old data. -/
def lawOfScalarOfRawNoCommonPositivePeriod (d : Data V Ω) (v : V)
    (h : ResponseAllocatedUniversalPeriodBridge.RawNoCommonPositivePeriod
      (rebased d) (processedSource d v))
    (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law (rebased d) (processedSource d v) :=
  ResponseAllocatedUniversalPeriodBridge.lawOfScalarOfRawNoCommonPositivePeriod
    (rebased d) (processedSource d v)
    (rebased_zero_diagonalFixed d) (processedSource_diagonalFixed d v) h L

/-- The supplied scalar law's entire polymorphic probability field is preserved. -/
theorem lawOfScalarOfRawNoCommonPositivePeriod_probability (d : Data V Ω) (v : V)
    (h : ResponseAllocatedUniversalPeriodBridge.RawNoCommonPositivePeriod
      (rebased d) (processedSource d v))
    (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob V Ω (rebased d) (processedSource d v)
        (lawOfScalarOfRawNoCommonPositivePeriod d v h L) =
      @NativeVacuumProbabilityFamily.Law.prob L := rfl

/-- The compiled raw separation predicate suffices for a rebased law with a
supplied scalar probability field. The enlarged three-source inputs and
nonvacuum garbage do not inherit this rebased single-basis probability law. -/
def lawOfScalarOfCompiledNoCommonPositivePeriod (d : Data V Ω) (v : V)
    (h : CompiledNoCommonPositivePeriod d v) (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law (rebased d) (processedSource d v) :=
  lawOfScalarOfRawNoCommonPositivePeriod d v
    ((compiledNoCommonPositivePeriod_iff d v).mp h) L

/-- Whole-field preservation concerns the supplied scalar law and rebased law;
it assigns no probability to the enlarged compiled experiment. -/
theorem lawOfScalarOfCompiledNoCommonPositivePeriod_probability (d : Data V Ω) (v : V)
    (h : CompiledNoCommonPositivePeriod d v) (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob V Ω (rebased d) (processedSource d v)
        (lawOfScalarOfCompiledNoCommonPositivePeriod d v h L) =
      @NativeVacuumProbabilityFamily.Law.prob L := rfl

end
end IDT.QMClosure.ResponseFixedReferencePreparation
