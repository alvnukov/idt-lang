import Proofs.QMClosure.ResponseContextQuotient

/-!
# Conditional probability selection on response-context classes

`prepared` evaluates native circuit words using the original operation on the
original raw carrier. `Law` supplies six all-width probability conditions;
prepared-state consistency uses pointwise response-context equivalence. The
supplied signature is independent data, not a probability field chosen by this
construction and not an asserted deterministic detector outcome.

Native words describe coherent preparations from a chosen reference and raw
vacua, not arbitrary physical states, operations, or independently unknown rays.
The coherent-preparation ray interface remains open.

Under first-output observed diagonal transparency, the actual raw preparations
descend to the existing normalized weight-free quotient preparations. Both law
adapters retain the identical supplied probability field. They form an
equivalence of contracts, so conditional selection and uniqueness transfer
without a law-existence witness or an infinite-order premise.

A separate theorem characterizes existence exactly by infinite additive order
of the contextual reference in the reconstructed quotient group. This criterion
uses the same explicit transparency premise. It is distinct from the older
weighted observational contract's positivity criterion, which does not require
transparency. Finite signature codomain and finite contextual quotient are not
interchangeable assumptions.

All-width real-valued probabilities and their six conditions remain supplied.
Observed structural laws and observed transparency are not derived from a
context-first primitive base. The grammar does not establish arbitrary-reference
availability. This route does not establish detector dynamics, event
availability, physical outcomes, Born actualization, or full QM closure.
-/

namespace IDT.QMClosure.ResponseNativeProbabilitySelection

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open ResponseContextQuotient
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open scoped BigOperators

variable {V : Type*} {Ω : Type*}

/-- A chosen reference on one wire and the supplied raw zero on the others. -/
def basisInput (d : Data V Ω) (v : V) {ι : Type} [DecidableEq ι]
    (s : ι) : ι → V := fun i => if i = s then v else d.chosenZero

/-- Original raw-gate semantics, without supplying algebra on the raw carrier. -/
def prepared (d : Data V Ω) (v : V) {ι : Type} [DecidableEq ι]
    (s : ι) (c : Native ι) : ι → V :=
  WeightFreeRawProbability.evalRaw d.operation c (basisInput d v s)

/-- Six supplied conditions at every finite width. Only prepared consistency
uses response-context equivalence instead of literal raw-array equality. -/
structure Law (d : Data V Ω) (v : V) where
  prob : {ι : Type} → [Fintype ι] → [DecidableEq ι] → ι → Native ι → ι → ℝ
  nonnegative : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) i,
    0 ≤ prob s c i
  normalized : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι),
    ∑ i, prob s c i = 1
  prepared_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c e : Native ι),
    (∀ i, ResponseEq d.operation d.signature (prepared d v s c i) (prepared d v s e i)) →
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

/-- The existing normalized quotient preparation denotes classes of the actual
original raw preparation, under the explicit observed-transparency premise. -/
theorem prepared_eq_class (d : Data V Ω) (transparent : ObservedTransparent d)
    (v : V) {ι : Type} [DecidableEq ι] (s : ι) (c : Native ι) :
    WeightFreeRawProbability.prepared d.quotientData (d.classOf v) s c =
      fun i => d.classOf (prepared d v s c i) := by
  unfold WeightFreeRawProbability.prepared prepared
  rw [quotient_normalizedOperation_eq d transparent]
  have hsource : WeightFreeRawProbability.basisInput d.quotientData (d.classOf v) s =
      fun i => d.classOf (basisInput d v s i) := by
    funext i
    by_cases hi : i = s <;>
      simp [WeightFreeRawProbability.basisInput, basisInput, hi, Data.quotientData]
  rw [hsource]
  exact evalRaw_class d c (basisInput d v s)

variable {d : Data V Ω} {v : V}

/-- Transport the same supplied field to the checked quotient contract. -/
def Law.toQuotientLaw (L : Law d v) (transparent : ObservedTransparent d) :
    WeightFreeRawProbability.Law d.quotientData (d.classOf v) where
  prob := L.prob
  nonnegative := L.nonnegative
  normalized := L.normalized
  prepared_eq s c e h := by
    apply L.prepared_eq s c e
    intro i
    have hi : d.classOf (prepared d v s c i) = d.classOf (prepared d v s e i) := by
      simpa only [WeightFreeRawProbability.rawPrepared_eq_prepared,
        prepared_eq_class d transparent v] using congrFun h i
    exact Quotient.exact hi
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

/-- The inverse transport also retains the entire supplied probability field. -/
def fromQuotientLaw (d : Data V Ω) (v : V) (transparent : ObservedTransparent d)
    (L : WeightFreeRawProbability.Law d.quotientData (d.classOf v)) : Law d v where
  prob := L.prob
  nonnegative := L.nonnegative
  normalized := L.normalized
  prepared_eq s c e h := by
    apply WeightFreeRawProbability.prepared_eq_probabilities d.quotientData (d.classOf v) L s c e
    simp only [prepared_eq_class d transparent v]
    funext i
    exact Quotient.sound (h i)
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

/-- The contracts are equivalent, rather than merely sharing a selected witness. -/
def quotientLawEquiv (d : Data V Ω) (v : V) (transparent : ObservedTransparent d) :
    Law d v ≃ WeightFreeRawProbability.Law d.quotientData (d.classOf v) where
  toFun L := L.toQuotientLaw transparent
  invFun := fromQuotientLaw d v transparent
  left_inv L := by cases L; rfl
  right_inv L := by cases L; rfl

/-- Forward transport preserves the polymorphic probability field definitionally. -/
theorem Law.toQuotientLaw_probability (L : Law d v) (transparent : ObservedTransparent d) :
    @RawNativeProbabilitySelection.RawLaw.prob _ d.quotientData.zeroWeightData (d.classOf v)
      (L.toQuotientLaw transparent) = @Law.prob V Ω d v L := rfl

/-- Inverse transport preserves the polymorphic probability field definitionally. -/
theorem fromQuotientLaw_probability (d : Data V Ω) (v : V) (transparent : ObservedTransparent d)
    (L : WeightFreeRawProbability.Law d.quotientData (d.classOf v)) :
    @Law.prob V Ω d v (fromQuotientLaw d v transparent L) =
      @RawNativeProbabilitySelection.RawLaw.prob _ d.quotientData.zeroWeightData (d.classOf v) L := rfl

/-- Conditional selection uses the supplied law, without a consistency witness
or an infinite-reference-order assumption. -/
theorem probability_eq_normSq (L : Law d v) (transparent : ObservedTransparent d)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι) :
    L.prob s c i = Complex.normSq (c.eval (source s) i) :=
  WeightFreeRawProbability.probability_eq_normSq d.quotientData (d.classOf v)
    (L.toQuotientLaw transparent) s c i

/-- Uniqueness compares supplied laws and does not assert their existence. -/
theorem probabilities_equal (L M : Law d v) (transparent : ObservedTransparent d)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι) :
    L.prob s c i = M.prob s c i :=
  (probability_eq_normSq L transparent s c i).trans
    (probability_eq_normSq M transparent s c i).symm

theorem probability_fields_equal (L M : Law d v) (transparent : ObservedTransparent d) :
    @Law.prob V Ω d v L = @Law.prob V Ω d v M := by
  funext α instF instD s c i
  exact probabilities_equal L M transparent s c i

/-- Infinite additive order is required only of the chosen contextual reference,
in the reconstructed quotient group, not of the whole raw carrier. -/
abbrev ReferenceInfiniteOrder (d : Data V Ω) (v : V) : Prop :=
  WeightFreeRawProbability.ReferenceInfiniteOrder d.quotientData (d.classOf v)

/-- Exact existence transport, under the same observed-transparency premise. -/
theorem law_nonempty_iff_quotientLaw (d : Data V Ω) (v : V)
    (transparent : ObservedTransparent d) :
    Nonempty (Law d v) ↔
      Nonempty (WeightFreeRawProbability.Law d.quotientData (d.classOf v)) := by
  constructor
  · rintro ⟨L⟩
    exact ⟨L.toQuotientLaw transparent⟩
  · rintro ⟨L⟩
    exact ⟨fromQuotientLaw d v transparent L⟩

/-- A separate exact existence boundary. Transparency remains explicit here;
this theorem does not replace the older weighted positivity criterion. -/
theorem law_nonempty_iff_reference_infiniteOrder (d : Data V Ω) (v : V)
    (transparent : ObservedTransparent d) :
    Nonempty (Law d v) ↔ ReferenceInfiniteOrder d v :=
  (law_nonempty_iff_quotientLaw d v transparent).trans
    (WeightFreeRawProbability.law_nonempty_iff_reference_infiniteOrder
      d.quotientData (d.classOf v))

theorem reference_infiniteOrder (L : Law d v) (transparent : ObservedTransparent d) :
    ReferenceInfiniteOrder d v :=
  (law_nonempty_iff_reference_infiniteOrder d v transparent).mp ⟨L⟩

end

end IDT.QMClosure.ResponseNativeProbabilitySelection
