import Proofs.QMClosure.WeightFreeRawProbability
import Proofs.QMClosure.NativePreparationNaturality
import Proofs.QMClosure.OriginalGateProbabilityWall

/-!
# Source-local agreement of original and normalized native semantics

Global square-swap and first-channel mediality are retained on every raw input.
Only the earlier global diagonal-transparency premise is weakened: the chosen
zero and one source reference are fixed by the term-defined diagonal g.
The resulting agreement concerns full arrays, including every ancillary wire.

No weight, Hilbert structure, infinite reference order or probability law is
supplied to the array core. The probability results retain all six supplied
law fields. Their existence criterion remains conditional; a nonzero or
infinite-order g-fixed source is not derived. For example g=-Id can leave only
zero fixed. The mathematical unary g is not an available native operation;
the expression T(v,v) does not supply two freely prepared copies of v.

No all-carrier transparency, arbitrary raw references, physical gate or source
availability, actualization, or full QM closure is established.
-/

namespace IDT.QMClosure.SourceLocalOriginalSemantics

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open MedialSwapRoot WeightFreeRawProbability
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open scoped BigOperators

variable {V : Type*}

/-- The full global raw laws; no chosen-zero or reference condition is used. -/
def rawLaws (r : RawOperationalData V) :
    DiagonalNormalization.Laws (firstChannel r.operation) where
  medial := r.medial
  bookend := raw_operation_bookend r.operation r.square

def g (r : RawOperationalData V) : V → V :=
  DiagonalNormalization.diagonal (firstChannel r.operation)

def G (r : RawOperationalData V) : V × V → V × V := Prod.map (g r) (g r)

theorem g_involutive (r : RawOperationalData V) (x : V) : g r (g r x) = x :=
  DiagonalNormalization.diagonal_involutive (rawLaws r) x

theorem g_map (r : RawOperationalData V) (x y : V) :
    g r (firstChannel r.operation x y) =
      firstChannel r.operation (g r x) (g r y) :=
  DiagonalNormalization.diagonal_map (rawLaws r) x y

theorem operation_injective (r : RawOperationalData V) :
    Function.Injective r.operation := by
  intro p q h
  have hs := congrArg r.operation h
  rw [r.square, r.square] at hs
  have hss := congrArg Prod.swap hs
  simpa using hss

theorem normalized_eq_after (r : RawOperationalData V) (p : V × V) :
    r.normalizedOperation p = G r (r.operation p) := by
  rw [raw_operation_eq_symmetric r.operation r.square p]
  rfl

theorem operation_G (r : RawOperationalData V) (p : V × V) :
    r.operation (G r p) = G r (r.operation p) := by
  rw [raw_operation_eq_symmetric r.operation r.square (G r p),
    raw_operation_eq_symmetric r.operation r.square p]
  apply Prod.ext
  · exact (g_map r p.1 p.2).symm
  · exact (g_map r p.2 p.1).symm

theorem normalized_eq_before (r : RawOperationalData V) (p : V × V) :
    r.normalizedOperation p = r.operation (G r p) :=
  (normalized_eq_after r p).trans (operation_G r p).symm

/-- Exact pairwise agreement is equivalent to both input points being fixed. -/
theorem gate_eq_iff (r : RawOperationalData V) (x y : V) :
    r.normalizedOperation (x, y) = r.operation (x, y) ↔
      g r x = x ∧ g r y = y := by
  rw [normalized_eq_before]
  constructor
  · intro h
    have hp := operation_injective r h
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · rintro ⟨hx, hy⟩
    change r.operation (g r x, g r y) = r.operation (x, y)
    rw [hx, hy]

/-- Fixed points are preserved on arbitrary arrays; no Fintype premise. -/
theorem evalRaw_fixed (r : RawOperationalData V) {ι : Type} [DecidableEq ι]
    (c : Native ι) (x : ι → V) (hx : ∀ i, g r (x i) = x i) :
    ∀ i, g r (evalRaw r.operation c x i) = evalRaw r.operation c x i := by
  have hcov : NativePreparationNaturality.MapsOperation r.operation r.operation (g r) := by
    intro a b
    exact (operation_G r (a, b)).symm
  have h := NativePreparationNaturality.evalRaw_covariance
    r.operation r.operation (g r) hcov c x
  have hinput : g r ∘ x = x := funext hx
  rw [hinput] at h
  intro i
  exact (congrFun h i).symm

/-- Full-array equality on every pointwise fixed input, not a selected-port
or probability statement. All circuit intermediates remain fixed. -/
theorem evalRaw_eq_on_fixed (r : RawOperationalData V) {ι : Type} [DecidableEq ι]
    (c : Native ι) (x : ι → V) (hx : ∀ i, g r (x i) = x i) :
    evalRaw r.operation c x = evalRaw r.normalizedOperation c x := by
  induction c generalizing x with
  | identity => rfl
  | pair i j hij =>
    have hp := (gate_eq_iff r (x i) (x j)).mpr ⟨hx i, hx j⟩
    funext k
    simp only [evalRaw, hp]
  | permute e => rfl
  | seq c d hc hd =>
    calc
      evalRaw r.operation d (evalRaw r.operation c x) =
          evalRaw r.normalizedOperation d (evalRaw r.operation c x) :=
        hd _ (evalRaw_fixed r c x hx)
      _ = evalRaw r.normalizedOperation d (evalRaw r.normalizedOperation c x) :=
        congrArg (evalRaw r.normalizedOperation d) (hc x hx)

theorem basisInput_fixed (r : RawOperationalData V) (v : V)
    (hz : g r r.chosenZero = r.chosenZero) (hv : g r v = v)
    {ι : Type} [DecidableEq ι] (s : ι) :
    ∀ i, g r (basisInput r v s i) = basisInput r v s i := by
  intro i
  by_cases h : i = s
  · simp [basisInput, h, hv]
  · simp [basisInput, h, hz]

theorem originalPrepared_eq_prepared (r : RawOperationalData V) (v : V)
    (hz : g r r.chosenZero = r.chosenZero) (hv : g r v = v)
    {ι : Type} [DecidableEq ι] (s : ι) (c : Native ι) :
    originalPrepared r v s c = prepared r v s c :=
  evalRaw_eq_on_fixed r c (basisInput r v s) (basisInput_fixed r v hz hv s)

def twoPortWord : Native (Fin 2) := .pair 0 1 (by decide)

def OnePairAgreement (r : RawOperationalData V) (v : V) : Prop :=
  originalPrepared r v (0 : Fin 2) twoPortWord = prepared r v (0 : Fin 2) twoPortWord

def FullAgreement (r : RawOperationalData V) (v : V) : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι),
    originalPrepared r v s c = prepared r v s c

/-- One full two-port array already detects both structural premises. -/
theorem fixed_iff_onePairAgreement (r : RawOperationalData V) (v : V) :
    (g r r.chosenZero = r.chosenZero ∧ g r v = v) ↔ OnePairAgreement r v := by
  constructor
  · rintro ⟨hz, hv⟩
    exact originalPrepared_eq_prepared r v hz hv 0 twoPortWord
  · intro h
    have hp : r.normalizedOperation (v, r.chosenZero) = r.operation (v, r.chosenZero) := by
      apply Prod.ext
      · have h0 := congrFun h (0 : Fin 2)
        simpa [OnePairAgreement, originalPrepared, prepared, twoPortWord,
          evalRaw, basisInput] using h0.symm
      · have h1 := congrFun h (1 : Fin 2)
        simpa [OnePairAgreement, originalPrepared, prepared, twoPortWord,
          evalRaw, basisInput] using h1.symm
    have hf := (gate_eq_iff r v r.chosenZero).mp hp
    exact ⟨hf.2, hf.1⟩

theorem fixed_iff_fullAgreement (r : RawOperationalData V) (v : V) :
    (g r r.chosenZero = r.chosenZero ∧ g r v = v) ↔ FullAgreement r v := by
  constructor
  · rintro ⟨hz, hv⟩ ι instF instD s c
    exact originalPrepared_eq_prepared r v hz hv s c
  · intro h
    exact (fixed_iff_onePairAgreement r v).mpr (h (0 : Fin 2) twoPortWord)

theorem onePairAgreement_iff_fullAgreement (r : RawOperationalData V) (v : V) :
    OnePairAgreement r v ↔ FullAgreement r v :=
  (fixed_iff_onePairAgreement r v).symm.trans (fixed_iff_fullAgreement r v)

/-! ## The same six supplied fields on original semantics -/

/-- Same Native syntax and six-field contract. Only prepared_eq changes its
literal-array semantics; no extra probability premise is added. -/
structure GenericOriginalLaw (r : RawOperationalData V) (v : V) where
  prob : {ι : Type} → [Fintype ι] → [DecidableEq ι] → ι → Native ι → ι → ℝ
  nonnegative : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) i,
    0 ≤ prob s c i
  normalized : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι),
    ∑ i, prob s c i = 1
  prepared_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c d : Native ι),
    originalPrepared r v s c = originalPrepared r v s d → prob s c = prob s d
  output_perm : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (e : Equiv.Perm ι) i,
    prob s (.seq c (.permute e)) i = prob s c (e i)
  spectator_pair : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (i j k : ι) (hij : i ≠ j),
    k ≠ i → k ≠ j → prob s (.seq c (.pair i j hij)) k = prob s c k
  vacuum : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (s : ι) (c : Native ι) i,
    prob (.inl s) (padCircuit κ c) (.inl i) = prob s c i

def toNormalizedLaw (r : RawOperationalData V) (v : V)
    (hz : g r r.chosenZero = r.chosenZero) (hv : g r v = v)
    (L : GenericOriginalLaw r v) : WeightFreeRawProbability.Law r v where
  prob := L.prob
  nonnegative := L.nonnegative
  normalized := L.normalized
  prepared_eq s c d h := by
    apply L.prepared_eq s c d
    rw [originalPrepared_eq_prepared r v hz hv, originalPrepared_eq_prepared r v hz hv]
    simpa only [rawPrepared_eq_prepared] using h
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

def toOriginalLaw (r : RawOperationalData V) (v : V)
    (hz : g r r.chosenZero = r.chosenZero) (hv : g r v = v)
    (L : WeightFreeRawProbability.Law r v) : GenericOriginalLaw r v where
  prob := L.prob
  nonnegative := L.nonnegative
  normalized := L.normalized
  prepared_eq s c d h := by
    apply L.prepared_eq s c d
    rw [originalPrepared_eq_prepared r v hz hv, originalPrepared_eq_prepared r v hz hv] at h
    simpa only [rawPrepared_eq_prepared] using h
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

def lawEquiv (r : RawOperationalData V) (v : V)
    (hz : g r r.chosenZero = r.chosenZero) (hv : g r v = v) :
    GenericOriginalLaw r v ≃ WeightFreeRawProbability.Law r v where
  toFun := toNormalizedLaw r v hz hv
  invFun := toOriginalLaw r v hz hv
  left_inv L := by cases L; rfl
  right_inv L := by cases L; rfl

/-- Equality of entire polymorphic probability fields, not only one event. -/
theorem toNormalizedLaw_probability (r : RawOperationalData V) (v : V)
    (hz : g r r.chosenZero = r.chosenZero) (hv : g r v = v)
    (L : GenericOriginalLaw r v) :
    @RawNativeProbabilitySelection.RawLaw.prob V r.zeroWeightData v
      (toNormalizedLaw r v hz hv L) = @GenericOriginalLaw.prob V r v L := rfl

theorem toOriginalLaw_probability (r : RawOperationalData V) (v : V)
    (hz : g r r.chosenZero = r.chosenZero) (hv : g r v = v)
    (L : WeightFreeRawProbability.Law r v) :
    @GenericOriginalLaw.prob V r v (toOriginalLaw r v hz hv L) =
      @RawNativeProbabilitySelection.RawLaw.prob V r.zeroWeightData v L := rfl

theorem probability_eq_normSq (r : RawOperationalData V) (v : V)
    (hz : g r r.chosenZero = r.chosenZero) (hv : g r v = v)
    (L : GenericOriginalLaw r v) {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (i : ι) :
    L.prob s c i = Complex.normSq (c.eval (source s) i) :=
  WeightFreeRawProbability.probability_eq_normSq r v (toNormalizedLaw r v hz hv L) s c i

theorem probability_fields_equal (r : RawOperationalData V) (v : V)
    (hz : g r r.chosenZero = r.chosenZero) (hv : g r v = v)
    (L M : GenericOriginalLaw r v) :
    @GenericOriginalLaw.prob V r v L = @GenericOriginalLaw.prob V r v M :=
  WeightFreeRawProbability.probability_fields_equal r v
    (toNormalizedLaw r v hz hv L) (toNormalizedLaw r v hz hv M)

/-- The fixed-point premises do not themselves construct a probability law.
Their necessity here is asserted only for full-array semantic agreement. -/
theorem law_nonempty_iff_reference_infiniteOrder (r : RawOperationalData V) (v : V)
    (hz : g r r.chosenZero = r.chosenZero) (hv : g r v = v) :
    Nonempty (GenericOriginalLaw r v) ↔ ReferenceInfiniteOrder r v := by
  have he : Nonempty (GenericOriginalLaw r v) ↔ Nonempty (WeightFreeRawProbability.Law r v) :=
    ⟨fun ⟨L⟩ => ⟨(lawEquiv r v hz hv) L⟩,
      fun ⟨L⟩ => ⟨(lawEquiv r v hz hv).symm L⟩⟩
  exact he.trans (WeightFreeRawProbability.law_nonempty_iff_reference_infiniteOrder r v)

/-! ## Explicit controls from the existing decorated original operation -/

namespace Controls

abbrev PairCarrier := OriginalGateProbabilityWall.V

def fixedData : RawOperationalData PairCarrier :=
  RawOperationalData.ofWeighted OriginalGateProbabilityWall.rawData

def vacuumMovedData : RawOperationalData PairCarrier where
  chosenZero := (0, 1)
  operation := OriginalGateProbabilityWall.operation
  square := OriginalGateProbabilityWall.operation_square
  medial := OriginalGateProbabilityWall.operation_medial

def fixedSource : PairCarrier := (1, 0)

theorem g_fixedData (x : PairCarrier) :
    g fixedData x = (x.1, -x.2) :=
  congrArg Prod.fst (OriginalGateProbabilityWall.operation_diagonal x)

theorem g_vacuumMovedData (x : PairCarrier) :
    g vacuumMovedData x = (x.1, -x.2) :=
  congrArg Prod.fst (OriginalGateProbabilityWall.operation_diagonal x)

theorem fixedData_zero_fixed : g fixedData fixedData.chosenZero = fixedData.chosenZero := by
  rw [g_fixedData]
  simp [fixedData, RawOperationalData.ofWeighted, OriginalGateProbabilityWall.rawData]

theorem fixedData_source_fixed : g fixedData fixedSource = fixedSource := by
  rw [g_fixedData]
  simp [fixedSource]

theorem fixedData_fullAgreement : FullAgreement fixedData fixedSource :=
  (fixed_iff_fullAgreement fixedData fixedSource).mp
    ⟨fixedData_zero_fixed, fixedData_source_fixed⟩

/-- The source-local premises are strictly weaker than global transparency. -/
theorem fixedData_not_globally_transparent :
    ¬ (∀ x, fixedData.operation (x, x) = (x, x)) := by
  intro h
  have hp := h (0, 1)
  change OriginalGateProbabilityWall.operation ((0, 1), (0, 1)) = ((0, 1), (0, 1)) at hp
  rw [OriginalGateProbabilityWall.operation_diagonal] at hp
  have hm := congrArg (fun p : PairCarrier × PairCarrier => p.1.2) hp
  norm_num [OriginalGateProbabilityWall.diagonal] at hm

/-- The existing nonuniqueness source lies outside the new transfer premises. -/
theorem mixed_source_not_fixed :
    g fixedData OriginalGateProbabilityWall.reference ≠ OriginalGateProbabilityWall.reference := by
  rw [g_fixedData]
  intro h
  have hm := congrArg Prod.snd h
  norm_num [OriginalGateProbabilityWall.reference] at hm

theorem vacuumMovedData_source_fixed : g vacuumMovedData fixedSource = fixedSource := by
  rw [g_vacuumMovedData]
  simp [fixedSource]

theorem vacuumMovedData_zero_not_fixed :
    g vacuumMovedData vacuumMovedData.chosenZero ≠ vacuumMovedData.chosenZero := by
  rw [g_vacuumMovedData]
  intro h
  have hm := congrArg Prod.snd h
  norm_num [vacuumMovedData] at hm

/-- Fixing the source alone cannot replace fixing the chosen vacuum. -/
theorem vacuumMovedData_onePair_disagrees :
    originalPrepared vacuumMovedData fixedSource (0 : Fin 2) twoPortWord ≠
      prepared vacuumMovedData fixedSource (0 : Fin 2) twoPortWord := by
  intro h
  exact vacuumMovedData_zero_not_fixed
    ((fixed_iff_onePairAgreement vacuumMovedData fixedSource).mpr h).1

end Controls

end
end IDT.QMClosure.SourceLocalOriginalSemantics
