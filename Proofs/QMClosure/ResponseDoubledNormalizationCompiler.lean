import Proofs.QMClosure.RawDoubledNormalizationCompiler
import Proofs.QMClosure.ResponseNativeProbabilitySelection

/-!
# Logical readout for doubled original-operation encodings

Every logical input position supplies two copies of its original raw input.
The raw compiler executes four original gates per logical pair and retains both
rails. Observed-only structural laws give a whole-array class identity; literal
equality of the actual raw rails is not asserted. The chosen zero and source
remain the original supplied values. Known double inputs and physical common-frame
availability remain supplied; unknown-state copying is not derived.

The new six-field law has logical Native words and logical outcome labels.
Normalization sums over logical labels, never over physical rails. Prepared
consistency uses coordinatewise full response-context equivalence of all encoded
outputs, which is not a joint-detector equivalence. The other five conditions
remain supplied logical conditions. Spectator locality concerns a complete
four-gate macro and logical permutations act on both rails. Vacuum extension
supplies two original-zero inputs per added logical position. Its layout
((ι ⊕ κ) ⊕ (ι ⊕ κ)) is not literal padding of ι ⊕ ι without rearrangement.

The contract supplies no rail probability, rail sum, marginal, conditioning,
postselection, joint law, or raw padding/detector theorem. It does not transfer
a law to uncoded original single-basis experiments. Partial macros, arbitrary
single-rail gates and larger mixed-control grammars remain outside the contract;
the mixed-control probability wall is unchanged. No actual outcome or QM
derivation is established.
-/

namespace IDT.QMClosure.ResponseDoubledNormalizationCompiler

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open ResponseContextQuotient
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open scoped BigOperators

variable {V : Type*} {Ω : Type*}

/-- Passing to classes commutes with the explicit two-rail input array. -/
theorem class_duplicate (d : Data V Ω) {ι : Type} (x : ι → V) :
    (fun w => d.classOf (RawDoubledNormalizationCompiler.duplicate x w)) =
      RawDoubledNormalizationCompiler.duplicate (fun i => d.classOf (x i)) := by
  funext w
  cases w <;> rfl

/-- The whole actual raw doubled array represents two copies of the normalized
quotient evaluation. No literal raw-rail equality is claimed. -/
theorem evalRaw_compileWord_class (d : Data V Ω) {ι : Type} [DecidableEq ι]
    (c : Native ι) (x : ι → V) :
    (fun w => d.classOf (WeightFreeRawProbability.evalRaw d.operation
      (RawDoubledNormalizationCompiler.compileWord c)
      (RawDoubledNormalizationCompiler.duplicate x) w)) =
      RawDoubledNormalizationCompiler.duplicate
        (WeightFreeRawProbability.evalRaw d.quotientData.normalizedOperation c
          (fun i => d.classOf (x i))) := by
  rw [← evalRaw_class d (RawDoubledNormalizationCompiler.compileWord c)
    (RawDoubledNormalizationCompiler.duplicate x), class_duplicate]
  exact RawDoubledNormalizationCompiler.evalRaw_compileWord_rawData d.quotientData c
    (fun i => d.classOf (x i))

/-- Actual original-operation preparation on two supplied copies of every old
basis input. Both output rails are retained; the old zero/source are unchanged. -/
def encodedPrepared (d : Data V Ω) (v : V) {ι : Type} [DecidableEq ι]
    (s : ι) (c : Native ι) : ι ⊕ ι → V :=
  WeightFreeRawProbability.evalRaw d.operation
    (RawDoubledNormalizationCompiler.compileWord c)
    (RawDoubledNormalizationCompiler.duplicate
      (ResponseNativeProbabilitySelection.basisInput d v s))

/-- Full-array normalized quotient semantics, without fixedness or rebasing. -/
theorem encodedPrepared_class (d : Data V Ω) (v : V)
    {ι : Type} [DecidableEq ι] (s : ι) (c : Native ι) :
    (fun w => d.classOf (encodedPrepared d v s c w)) =
      RawDoubledNormalizationCompiler.duplicate
        (WeightFreeRawProbability.prepared d.quotientData (d.classOf v) s c) := by
  unfold encodedPrepared
  rw [evalRaw_compileWord_class]
  have hsource :
      (fun i => d.classOf (ResponseNativeProbabilitySelection.basisInput d v s i)) =
        WeightFreeRawProbability.basisInput d.quotientData (d.classOf v) s := by
    funext i
    by_cases hi : i = s <;>
      simp [ResponseNativeProbabilitySelection.basisInput,
        WeightFreeRawProbability.basisInput, Data.quotientData, hi]
  rw [hsource]
  rfl

/-- Equivalence concerns every encoded coordinate and all response contexts;
it assigns no joint-detector meaning to coordinatewise equivalence. -/
theorem responseEq_iff_prepared_eq (d : Data V Ω) (v : V)
    {ι : Type} [DecidableEq ι] (s : ι) (c e : Native ι) :
    (∀ w, ResponseEq d.operation d.signature
      (encodedPrepared d v s c w) (encodedPrepared d v s e w)) ↔
    WeightFreeRawProbability.prepared d.quotientData (d.classOf v) s c =
      WeightFreeRawProbability.prepared d.quotientData (d.classOf v) s e := by
  constructor
  · intro h
    apply RawDoubledNormalizationCompiler.duplicate_injective
    change RawDoubledNormalizationCompiler.duplicate
        (WeightFreeRawProbability.prepared d.quotientData (d.classOf v) s c) =
      RawDoubledNormalizationCompiler.duplicate
        (WeightFreeRawProbability.prepared d.quotientData (d.classOf v) s e)
    rw [← encodedPrepared_class d v s c, ← encodedPrepared_class d v s e]
    funext w
    exact (d.classOf_eq_iff_responseEq _ _).mpr (h w)
  · intro h w
    apply (d.classOf_eq_iff_responseEq _ _).mp
    have hall : (fun w => d.classOf (encodedPrepared d v s c w)) =
        (fun w => d.classOf (encodedPrepared d v s e w)) := by
      rw [encodedPrepared_class d v s c, encodedPrepared_class d v s e, h]
    exact congrFun hall w

/-- A new logical readout contract. Its probabilities have logical outcome
indices only; the six fields do not supply a physical-rail probability law. -/
structure CompiledLaw (d : Data V Ω) (v : V) where
  prob : {ι : Type} → [Fintype ι] → [DecidableEq ι] → ι → Native ι → ι → ℝ
  nonnegative : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) i,
    0 ≤ prob s c i
  normalized : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι),
    ∑ i, prob s c i = 1
  prepared_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c e : Native ι),
    (∀ w, ResponseEq d.operation d.signature
      (encodedPrepared d v s c w) (encodedPrepared d v s e w)) →
    prob s c = prob s e
  output_perm : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (e : Equiv.Perm ι) i,
    prob s (.seq c (.permute e)) i = prob s c (e i)
  spectator_pair : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (i j k : ι) (hij : i ≠ j),
    k ≠ i → k ≠ j → prob s (.seq c (.pair i j hij)) k = prob s c k
  vacuum : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (s : ι) (c : Native ι) i,
    prob (.inl s) (padCircuit κ c) (.inl i) = prob s c i

/-- All probability values and the five unchanged logical conditions are copied. -/
def toQuotientLaw (d : Data V Ω) (v : V) (L : CompiledLaw d v) :
    WeightFreeRawProbability.Law d.quotientData (d.classOf v) where
  prob := L.prob
  nonnegative := L.nonnegative
  normalized := L.normalized
  prepared_eq s c e h := by
    apply L.prepared_eq s c e
    apply (responseEq_iff_prepared_eq d v s c e).mpr
    simpa only [WeightFreeRawProbability.rawPrepared_eq_prepared] using h
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

/-- The inverse supplies a logical encoded contract, never an uncoded raw law. -/
def fromQuotientLaw (d : Data V Ω) (v : V)
    (L : WeightFreeRawProbability.Law d.quotientData (d.classOf v)) : CompiledLaw d v where
  prob := L.prob
  nonnegative := L.nonnegative
  normalized := L.normalized
  prepared_eq s c e h :=
    WeightFreeRawProbability.prepared_eq_probabilities d.quotientData (d.classOf v)
      L s c e ((responseEq_iff_prepared_eq d v s c e).mp h)
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

def quotientLawEquiv (d : Data V Ω) (v : V) :
    CompiledLaw d v ≃ WeightFreeRawProbability.Law d.quotientData (d.classOf v) where
  toFun := toQuotientLaw d v
  invFun := fromQuotientLaw d v
  left_inv L := by cases L; rfl
  right_inv L := by cases L; rfl

/-- Forward equivalence preserves the entire polymorphic logical field. -/
theorem toQuotientLaw_probability (d : Data V Ω) (v : V) (L : CompiledLaw d v) :
    @RawNativeProbabilitySelection.RawLaw.prob _ d.quotientData.zeroWeightData (d.classOf v)
      (toQuotientLaw d v L) = @CompiledLaw.prob V Ω d v L := rfl

/-- Inverse equivalence preserves the entire polymorphic logical field. -/
theorem fromQuotientLaw_probability (d : Data V Ω) (v : V)
    (L : WeightFreeRawProbability.Law d.quotientData (d.classOf v)) :
    @CompiledLaw.prob V Ω d v (fromQuotientLaw d v L) =
      @RawNativeProbabilitySelection.RawLaw.prob _ d.quotientData.zeroWeightData
        (d.classOf v) L := rfl

/-- Conditional selection for supplied logical laws; no rail readout is inferred. -/
theorem probability_eq_normSq (d : Data V Ω) (v : V) (L : CompiledLaw d v)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι) :
    L.prob s c i = Complex.normSq (c.eval (source s) i) :=
  WeightFreeRawProbability.probability_eq_normSq d.quotientData (d.classOf v)
    (toQuotientLaw d v L) s c i

theorem probability_fields_equal (d : Data V Ω) (v : V) (L M : CompiledLaw d v) :
    @CompiledLaw.prob V Ω d v L = @CompiledLaw.prob V Ω d v M := by
  funext α instF instD s c i
  exact (probability_eq_normSq d v L s c i).trans
    (probability_eq_normSq d v M s c i).symm

/-- Separate existence criterion on the original quotient and original source. -/
theorem law_nonempty_iff_reference_infiniteOrder (d : Data V Ω) (v : V) :
    Nonempty (CompiledLaw d v) ↔
      WeightFreeRawProbability.ReferenceInfiniteOrder d.quotientData (d.classOf v) := by
  have he : Nonempty (CompiledLaw d v) ↔
      Nonempty (WeightFreeRawProbability.Law d.quotientData (d.classOf v)) :=
    ⟨fun ⟨L⟩ => ⟨toQuotientLaw d v L⟩, fun ⟨L⟩ => ⟨fromQuotientLaw d v L⟩⟩
  exact he.trans
    (WeightFreeRawProbability.law_nonempty_iff_reference_infiniteOrder
      d.quotientData (d.classOf v))

end
end IDT.QMClosure.ResponseDoubledNormalizationCompiler
