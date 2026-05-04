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

end IDT.QMClosure
