namespace IDT.QMClosure

/-!
Mechanical draft artifacts for finite readout obligations.

These lemmas use a deliberately weak encoding: finite readout weights are
natural numbers, context totals are list sums, exclusive composition is list
append, coarse-graining is supplied as an explicit equality of totals, and
operational equivalence is supplied as equality of weights.

They do not prove the Born rule and do not prove that IDT readouts must reduce
to this encoding. They only provide checkable finite scaffolds for later proof
cards.
-/

abbrev Weight := Nat
abbrev FiniteReadout := List Weight

def contextTotal (readout : FiniteReadout) : Weight :=
  readout.sum

def exclusiveJoin (left right : FiniteReadout) : FiniteReadout :=
  left ++ right

def coarseGrainingPreservesTotal (fine coarse : FiniteReadout) : Prop :=
  contextTotal fine = contextTotal coarse

def operationallyEquivalentWeight (left right : Weight) : Prop :=
  left = right

def EventWeight (event : Type) := event -> Weight

def RespectsOperationalEquivalence {event : Type}
    (equivalent : event -> event -> Prop)
    (weight : EventWeight event) : Prop :=
  forall left right, equivalent left right -> weight left = weight right

theorem context_normalization_total_is_sum (readout : FiniteReadout) :
    contextTotal readout = readout.sum := by
  rfl

theorem exclusivity_additivity_for_append (left right : FiniteReadout) :
    contextTotal (exclusiveJoin left right) = contextTotal left + contextTotal right := by
  simp [contextTotal, exclusiveJoin, List.sum_append]

theorem coarse_graining_total_stable
    (fine coarse : FiniteReadout)
    (preserves : coarseGrainingPreservesTotal fine coarse) :
    contextTotal fine = contextTotal coarse := by
  exact preserves

theorem operational_equivalence_preserves_weight
    (left right : Weight)
    (equivalent : operationallyEquivalentWeight left right) :
    left = right := by
  exact equivalent

theorem operational_equivalence_respecting_weight_function_preserves_weight {event : Type}
    (equivalent : event -> event -> Prop)
    (weight : EventWeight event)
    (respects : RespectsOperationalEquivalence equivalent weight)
    (left right : event)
    (equivalent_events : equivalent left right) :
    weight left = weight right := by
  exact respects left right equivalent_events

structure StableFiniteReadout where
  weights : FiniteReadout
  positive_total : contextTotal weights > 0

def normalizationDenominator (readout : StableFiniteReadout) : Weight :=
  contextTotal readout.weights

theorem stable_finite_readout_has_positive_denominator
    (readout : StableFiniteReadout) :
    normalizationDenominator readout > 0 := by
  exact readout.positive_total

theorem stable_finite_readout_denominator_is_total
    (readout : StableFiniteReadout) :
    normalizationDenominator readout = contextTotal readout.weights := by
  rfl

structure NormalizedWeight where
  numerator : Weight
  denominator : Weight
  denominator_positive : denominator > 0

def normalizeWeight (readout : StableFiniteReadout) (weight : Weight) : NormalizedWeight :=
  {
    numerator := weight,
    denominator := normalizationDenominator readout,
    denominator_positive := stable_finite_readout_has_positive_denominator readout
  }

def normalizedReadout (readout : StableFiniteReadout) : List NormalizedWeight :=
  readout.weights.map (normalizeWeight readout)

theorem normalized_readout_length_matches
    (readout : StableFiniteReadout) :
    (normalizedReadout readout).length = readout.weights.length := by
  simp [normalizedReadout]

theorem normalized_readout_common_denominator
    (readout : StableFiniteReadout) :
    forall normalized,
      normalized ∈ normalizedReadout readout ->
        normalized.denominator = normalizationDenominator readout := by
  intro normalized member
  simp [normalizedReadout, normalizeWeight] at member
  rcases member with ⟨_weight, _weight_member, normalized_eq⟩
  rw [← normalized_eq]

def flattenReadoutBlocks : List FiniteReadout -> FiniteReadout
  | [] => []
  | block :: rest => block ++ flattenReadoutBlocks rest

def coarseGrainBlocks : List FiniteReadout -> FiniteReadout
  | [] => []
  | block :: rest => contextTotal block :: coarseGrainBlocks rest

theorem coarse_grain_blocks_preserve_total
    (blocks : List FiniteReadout) :
    contextTotal (flattenReadoutBlocks blocks) = contextTotal (coarseGrainBlocks blocks) := by
  induction blocks with
  | nil => rfl
  | cons block rest induction_hypothesis =>
      calc
        contextTotal (flattenReadoutBlocks (block :: rest))
            = contextTotal block + contextTotal (flattenReadoutBlocks rest) := by
              simp [flattenReadoutBlocks, contextTotal, List.sum_append]
        _ = contextTotal block + contextTotal (coarseGrainBlocks rest) := by
              rw [induction_hypothesis]
        _ = contextTotal (coarseGrainBlocks (block :: rest)) := by
              simp [coarseGrainBlocks, contextTotal]

end IDT.QMClosure
