import Proofs.QMClosure.B1PrimitiveBase

namespace IDT
namespace QMClosure

/-!
# Rank-three wall for the B1 primitive base

`Proofs/MetaLang/V8QmResearchTaskLedger.lean` records
`b1_primitive_base_has_no_known_lean_inhabitant`. This file supplies one, and
it is a negative control in the style of `CGSCSemanticContentWall`,
`CGSCTypedDecorativeWall` and `CGSCGroundedToyWall`.

Those three walls exhibited degenerate inhabitants carried by `Bool`.
`UniversalPrimitiveSourceKernel` answered them with `AtLeastThree` rank
conditions and proved the `Bool` witnesses fail (`bool_has_no_at_least_three`).
The open question is whether that step added physical content or only excluded
two-element carriers.

The witness below settles it. Every carrier is `Fin 3`, every `CheckedProp` is
`True`, every relation is `· = 0`, and the reversible context map is the
transposition of `0` and `1`. Nothing here refers to probability, amplitude,
ordering, composition, or any quantity. It satisfies the whole of
`BoundPrimitiveGeneratedBase` and therefore the whole of `B1PrimitiveBase`.

So the rank-three step excluded `Bool` and nothing else, and the constraints
accumulated along the chain are satisfied by three distinct points with
arbitrary non-empty, non-total relations between them.
-/

/-- Every `CheckedProp` slot in this witness carries `True`. -/
def rankThreeChecked : CheckedProp :=
  {
    statement := True,
    proof := True.intro
  }

/-- Every B0 slot carries `True` as well; the wall assumes nothing about B0. -/
def rankThreeB0CandidateBase : B0CandidateBase :=
  {
    finiteGeneration := rankThreeChecked,
    facticizableSeparation := rankThreeChecked,
    importBoundary := rankThreeChecked,
    noPrimitiveGlobalSection := rankThreeChecked,
    noHilbertPrimitive := rankThreeChecked,
    noBornPrimitive := rankThreeChecked,
    noUnitaryPrimitive := rankThreeChecked,
    noTensorPrimitive := rankThreeChecked,
    noStonePrimitive := rankThreeChecked,
    noSpectralPrimitive := rankThreeChecked
  }

/-- Transposition of `0` and `1`, fixing `2`. Its own inverse. -/
def rankThreeSwap : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 0
  | 2 => 2

/--
A fully degenerate inhabitant of the latest primitive-generated base. Carriers
are `Fin 3`; relations are `· = 0`; boundaries are witnessed by picking a second
point.
-/
def rankThreeBoundPrimitiveGeneratedBase : BoundPrimitiveGeneratedBase where
  b0 := rankThreeB0CandidateBase
  primitiveGeneratedScope := rankThreeChecked
  admissibleContextUniverse := rankThreeChecked
  ContextWitness := Fin 3
  FactWitness := Fin 3
  BlockWitness := Fin 3
  RouteWitness := Fin 3
  RefinementWitness := Fin 3
  StateWitness := Fin 3
  GeneratorWitness := Fin 3
  LocalFactWitness := Fin 3
  contextLeft := 0
  contextRight := 1
  contextThird := 2
  contextLeftNeRight := by decide
  contextLeftNeThird := by decide
  contextRightNeThird := by decide
  factWitness := 0
  blockWitness := 0
  blockedBlockWitness := 1
  exposedIn := fun block _ => block = 0
  exposedWitness := by decide
  exposureBoundary := by decide
  routeWitness := 0
  routeBoundaryWitness := 1
  forwardContext := rankThreeSwap
  backwardContext := rankThreeSwap
  roundTripLeft := by decide
  roundTripRight := by decide
  nontrivialForward := by decide
  refinementWitness := 0
  stateLeft := 0
  stateRight := 1
  stateLeftNeRight := by decide
  compactBound := 1
  compactBoundPositive := by decide
  generatorWitness := 0
  generatorBoundaryWitness := 1
  generates := fun generator _ => generator = 0
  generationWitness := by decide
  generationBoundary := by decide
  localFactLeft := 0
  localFactRight := 1
  localFactThird := 2
  localFactLeftNeRight := by decide
  localFactLeftNeThird := by decide
  localFactRightNeThird := by decide
  witnessesJoint := fun _ localFact => localFact = 0
  witnessedJointFact := by decide
  witnessBoundary := by decide

/-- The recorded open item: the B1 base does have a Lean inhabitant. -/
def rankThreeB1PrimitiveBase : B1PrimitiveBase where
  bound := rankThreeBoundPrimitiveGeneratedBase
  successorBasePromoted := rankThreeChecked
  noFreeAdmissibilityBoundary := rankThreeChecked
  noTargetImportBoundary := rankThreeChecked

/--
The degenerate witness clears the rank conditions that killed the `Bool` walls,
because `Fin 3` has three distinct points and that is all those conditions ask.
-/
theorem rank_three_witness_has_universal_exposed_rank :
    AtLeastThree
      (b1PrimitiveGeneratedUniversalSourceKernel
        rankThreeB1PrimitiveBase).grounded.exposed.Context :=
  (b1PrimitiveGeneratedUniversalSourceKernel
    rankThreeB1PrimitiveBase).exposedContextRank

/--
The point of the file. The full-QM obligation bundle is derivable from a base
whose entire content is three distinct points and relations defined by `· = 0`.
Whatever that bundle certifies, it is not physical content of the base.
-/
theorem rank_three_witness_yields_full_qm_obligation_bundle :
    FullQMObligationBundle
      (b1PrimitiveGeneratedCGSCPackageClosure rankThreeB1PrimitiveBase) :=
  b1_primitive_base_yields_full_qm_obligation_bundle rankThreeB1PrimitiveBase

/-- The import guards are likewise carried by the degenerate witness. -/
theorem rank_three_witness_yields_import_guards :
    (b1PrimitiveGeneratedCGSCPackageClosure
        rankThreeB1PrimitiveBase).finiteExposed.noSpectralImport.statement
      ∧ (b1PrimitiveGeneratedCGSCPackageClosure
        rankThreeB1PrimitiveBase).finiteExposed.noBornImport.statement
      ∧ (b1PrimitiveGeneratedCGSCPackageClosure
        rankThreeB1PrimitiveBase).finiteExposed.noHilbertImport.statement
      ∧ (b1PrimitiveGeneratedCGSCPackageClosure
        rankThreeB1PrimitiveBase).routeCoherence.noUnitaryImport.statement
      ∧ (b1PrimitiveGeneratedCGSCPackageClosure
        rankThreeB1PrimitiveBase).routeCoherence.noStoneImport.statement
      ∧ (b1PrimitiveGeneratedCGSCPackageClosure
        rankThreeB1PrimitiveBase).routeCoherence.noGeneratorImport.statement
      ∧ (b1PrimitiveGeneratedCGSCPackageClosure
        rankThreeB1PrimitiveBase).compositeClosure.noTensorImport.statement
      ∧ (b1PrimitiveGeneratedCGSCPackageClosure
        rankThreeB1PrimitiveBase).compositeClosure.noBornImport.statement
      ∧ (b1PrimitiveGeneratedCGSCPackageClosure
        rankThreeB1PrimitiveBase).compositeClosure.noHilbertImport.statement :=
  b1_primitive_base_yields_import_guards rankThreeB1PrimitiveBase

inductive RankThreeWallFinding where
  | b1PrimitiveBaseIsInhabited
  | rankConditionsExcludeOnlyTwoElementCarriers
  | fullQmObligationBundleFollowsFromThreeArbitraryPoints
  | chainAddsFieldsWithoutAddingExclusion
  deriving DecidableEq, Repr

def rankThreeWallFindings : List RankThreeWallFinding :=
  [ .b1PrimitiveBaseIsInhabited,
    .rankConditionsExcludeOnlyTwoElementCarriers,
    .fullQmObligationBundleFollowsFromThreeArbitraryPoints,
    .chainAddsFieldsWithoutAddingExclusion ]

theorem rank_three_wall_records_four_findings :
    rankThreeWallFindings.length = 4 := by
  rfl

def rankThreeWallClaimBoundary : String :=
  "Negative control only. It exhibits a degenerate inhabitant of B1PrimitiveBase over Fin 3 and shows the AtLeastThree step excluded Bool alone; it does not refute the context-first programme, and it derives nothing about quantum mechanics."

end QMClosure
end IDT
