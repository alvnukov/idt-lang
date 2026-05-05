import Proofs.QMClosure.PrimitiveGeneratedAdmissibilityWall

namespace IDT
namespace QMClosure

structure BoundPrimitiveGeneratedBase where
  b0 : B0CandidateBase
  primitiveGeneratedScope : CheckedProp
  admissibleContextUniverse : CheckedProp
  ContextWitness : Type
  FactWitness : Type
  BlockWitness : Type
  RouteWitness : Type
  RefinementWitness : Type
  StateWitness : Type
  GeneratorWitness : Type
  LocalFactWitness : Type
  contextLeft : ContextWitness
  contextRight : ContextWitness
  contextThird : ContextWitness
  contextLeftNeRight : contextLeft ≠ contextRight
  contextLeftNeThird : contextLeft ≠ contextThird
  contextRightNeThird : contextRight ≠ contextThird
  factWitness : FactWitness
  blockWitness : BlockWitness
  blockedBlockWitness : BlockWitness
  exposedIn : BlockWitness → ContextWitness → Prop
  exposedWitness : exposedIn blockWitness contextLeft
  exposureBoundary : ¬ exposedIn blockedBlockWitness contextLeft
  routeWitness : RouteWitness
  routeBoundaryWitness : RouteWitness
  forwardContext : ContextWitness → ContextWitness
  backwardContext : ContextWitness → ContextWitness
  roundTripLeft : backwardContext (forwardContext contextLeft) = contextLeft
  roundTripRight : forwardContext (backwardContext contextRight) = contextRight
  nontrivialForward : forwardContext contextLeft = contextRight
  refinementWitness : RefinementWitness
  stateLeft : StateWitness
  stateRight : StateWitness
  stateLeftNeRight : stateLeft ≠ stateRight
  compactBound : Nat
  compactBoundPositive : compactBound > 0
  generatorWitness : GeneratorWitness
  generatorBoundaryWitness : GeneratorWitness
  generates : GeneratorWitness → RouteWitness → Prop
  generationWitness : generates generatorWitness routeWitness
  generationBoundary : ¬ generates generatorBoundaryWitness routeBoundaryWitness
  localFactLeft : LocalFactWitness
  localFactRight : LocalFactWitness
  localFactThird : LocalFactWitness
  localFactLeftNeRight : localFactLeft ≠ localFactRight
  localFactLeftNeThird : localFactLeft ≠ localFactThird
  localFactRightNeThird : localFactRight ≠ localFactThird
  witnessesJoint : ContextWitness × ContextWitness → LocalFactWitness → Prop
  witnessedJointFact : witnessesJoint (contextLeft, contextRight) localFactLeft
  witnessBoundary : ¬ witnessesJoint (contextLeft, contextRight) localFactRight

inductive BoundSourceAtom (base : BoundPrimitiveGeneratedBase) where
  | context : base.ContextWitness → BoundSourceAtom base
  | fact : base.FactWitness → BoundSourceAtom base
  | block : base.BlockWitness → BoundSourceAtom base
  | route : base.RouteWitness → BoundSourceAtom base
  | refinement : base.RefinementWitness → BoundSourceAtom base
  | state : base.StateWitness → BoundSourceAtom base
  | generator : base.GeneratorWitness → BoundSourceAtom base
  | localFact : base.LocalFactWitness → BoundSourceAtom base

def boundIsContext {base : BoundPrimitiveGeneratedBase} :
    BoundSourceAtom base → Prop
  | BoundSourceAtom.context _ => True
  | _ => False

def boundIsFact {base : BoundPrimitiveGeneratedBase} :
    BoundSourceAtom base → Prop
  | BoundSourceAtom.fact _ => True
  | _ => False

def boundIsBlock {base : BoundPrimitiveGeneratedBase} :
    BoundSourceAtom base → Prop
  | BoundSourceAtom.block _ => True
  | _ => False

def boundIsRoute {base : BoundPrimitiveGeneratedBase} :
    BoundSourceAtom base → Prop
  | BoundSourceAtom.route _ => True
  | _ => False

def boundIsRefinement {base : BoundPrimitiveGeneratedBase} :
    BoundSourceAtom base → Prop
  | BoundSourceAtom.refinement _ => True
  | _ => False

def boundIsState {base : BoundPrimitiveGeneratedBase} :
    BoundSourceAtom base → Prop
  | BoundSourceAtom.state _ => True
  | _ => False

def boundIsGenerator {base : BoundPrimitiveGeneratedBase} :
    BoundSourceAtom base → Prop
  | BoundSourceAtom.generator _ => True
  | _ => False

def boundIsLocalFact {base : BoundPrimitiveGeneratedBase} :
    BoundSourceAtom base → Prop
  | BoundSourceAtom.localFact _ => True
  | _ => False

def boundContextAtomNe {base : BoundPrimitiveGeneratedBase}
    {left right : base.ContextWitness}
    (notEqual : left ≠ right) :
    (BoundSourceAtom.context left : BoundSourceAtom base) ≠ BoundSourceAtom.context right := by
  intro equality
  cases equality
  exact notEqual rfl

def boundStateAtomNe {base : BoundPrimitiveGeneratedBase}
    {left right : base.StateWitness}
    (notEqual : left ≠ right) :
    (BoundSourceAtom.state left : BoundSourceAtom base) ≠ BoundSourceAtom.state right := by
  intro equality
  cases equality
  exact notEqual rfl

def boundLocalFactAtomNe {base : BoundPrimitiveGeneratedBase}
    {left right : base.LocalFactWitness}
    (notEqual : left ≠ right) :
    (BoundSourceAtom.localFact left : BoundSourceAtom base) ≠ BoundSourceAtom.localFact right := by
  intro equality
  cases equality
  exact notEqual rfl

def boundExposedIn (base : BoundPrimitiveGeneratedBase) :
    BoundSourceAtom base → BoundSourceAtom base → Prop
  | BoundSourceAtom.block block, BoundSourceAtom.context context =>
      base.exposedIn block context
  | _, _ => False

def boundForwardContextAtom (base : BoundPrimitiveGeneratedBase) :
    BoundSourceAtom base → BoundSourceAtom base
  | BoundSourceAtom.context context =>
      BoundSourceAtom.context (base.forwardContext context)
  | atom => atom

def boundBackwardContextAtom (base : BoundPrimitiveGeneratedBase) :
    BoundSourceAtom base → BoundSourceAtom base
  | BoundSourceAtom.context context =>
      BoundSourceAtom.context (base.backwardContext context)
  | atom => atom

theorem boundForwardContextAtomClosed (base : BoundPrimitiveGeneratedBase) :
    ∀ atom : BoundSourceAtom base,
      boundIsContext atom → boundIsContext (boundForwardContextAtom base atom) := by
  intro atom witness
  cases atom <;> simp [boundIsContext, boundForwardContextAtom] at witness ⊢

theorem boundBackwardContextAtomClosed (base : BoundPrimitiveGeneratedBase) :
    ∀ atom : BoundSourceAtom base,
      boundIsContext atom → boundIsContext (boundBackwardContextAtom base atom) := by
  intro atom witness
  cases atom <;> simp [boundIsContext, boundBackwardContextAtom] at witness ⊢

def boundGenerates (base : BoundPrimitiveGeneratedBase) :
    BoundSourceAtom base → BoundSourceAtom base → Prop
  | BoundSourceAtom.generator generator, BoundSourceAtom.route route =>
      base.generates generator route
  | _, _ => False

def boundWitnessesJoint (base : BoundPrimitiveGeneratedBase) :
    BoundSourceAtom base × BoundSourceAtom base → BoundSourceAtom base → Prop
  | (BoundSourceAtom.context left, BoundSourceAtom.context right),
      BoundSourceAtom.localFact localFact =>
      base.witnessesJoint (left, right) localFact
  | _, _ => False

def boundPrimitiveGeneratedAdmissibility
    (base : BoundPrimitiveGeneratedBase) :
    PrimitiveGeneratedAdmissibility :=
  {
    Atom := BoundSourceAtom base,
    b0 := base.b0,
    primitiveGeneratedScope := base.primitiveGeneratedScope,
    admissibleContextUniverse := base.admissibleContextUniverse,
    isContext := boundIsContext,
    isFact := boundIsFact,
    isBlock := boundIsBlock,
    isRoute := boundIsRoute,
    isRefinement := boundIsRefinement,
    isState := boundIsState,
    isGenerator := boundIsGenerator,
    isLocalFact := boundIsLocalFact,
    contextLeft := BoundSourceAtom.context base.contextLeft,
    contextRight := BoundSourceAtom.context base.contextRight,
    contextThird := BoundSourceAtom.context base.contextThird,
    contextLeftIsContext := trivial,
    contextRightIsContext := trivial,
    contextThirdIsContext := trivial,
    contextLeftNeRight := boundContextAtomNe base.contextLeftNeRight,
    contextLeftNeThird := boundContextAtomNe base.contextLeftNeThird,
    contextRightNeThird := boundContextAtomNe base.contextRightNeThird,
    factWitness := BoundSourceAtom.fact base.factWitness,
    factWitnessIsFact := trivial,
    blockWitness := BoundSourceAtom.block base.blockWitness,
    blockWitnessIsBlock := trivial,
    blockedBlockWitness := BoundSourceAtom.block base.blockedBlockWitness,
    blockedBlockWitnessIsBlock := trivial,
    exposedIn := boundExposedIn base,
    exposedWitness := base.exposedWitness,
    exposureBoundary := base.exposureBoundary,
    routeWitness := BoundSourceAtom.route base.routeWitness,
    routeWitnessIsRoute := trivial,
    forwardContext := boundForwardContextAtom base,
    backwardContext := boundBackwardContextAtom base,
    forwardContextClosed := boundForwardContextAtomClosed base,
    backwardContextClosed := boundBackwardContextAtomClosed base,
    roundTripLeft := congrArg BoundSourceAtom.context base.roundTripLeft,
    roundTripRight := congrArg BoundSourceAtom.context base.roundTripRight,
    nontrivialForward := congrArg BoundSourceAtom.context base.nontrivialForward,
    refinementWitness := BoundSourceAtom.refinement base.refinementWitness,
    refinementWitnessIsRefinement := trivial,
    stateLeft := BoundSourceAtom.state base.stateLeft,
    stateRight := BoundSourceAtom.state base.stateRight,
    stateLeftIsState := trivial,
    stateRightIsState := trivial,
    stateLeftNeRight := boundStateAtomNe base.stateLeftNeRight,
    compactBound := base.compactBound,
    compactBoundPositive := base.compactBoundPositive,
    generatorWitness := BoundSourceAtom.generator base.generatorWitness,
    generatorWitnessIsGenerator := trivial,
    generatorBoundaryWitness := BoundSourceAtom.generator base.generatorBoundaryWitness,
    generatorBoundaryWitnessIsGenerator := trivial,
    routeBoundaryWitness := BoundSourceAtom.route base.routeBoundaryWitness,
    routeBoundaryWitnessIsRoute := trivial,
    generates := boundGenerates base,
    generationWitness := base.generationWitness,
    generationBoundary := base.generationBoundary,
    localFactLeft := BoundSourceAtom.localFact base.localFactLeft,
    localFactRight := BoundSourceAtom.localFact base.localFactRight,
    localFactThird := BoundSourceAtom.localFact base.localFactThird,
    localFactLeftIsLocalFact := trivial,
    localFactRightIsLocalFact := trivial,
    localFactThirdIsLocalFact := trivial,
    localFactLeftNeRight := boundLocalFactAtomNe base.localFactLeftNeRight,
    localFactLeftNeThird := boundLocalFactAtomNe base.localFactLeftNeThird,
    localFactRightNeThird := boundLocalFactAtomNe base.localFactRightNeThird,
    witnessesJoint := boundWitnessesJoint base,
    witnessedJointFact := base.witnessedJointFact,
    witnessBoundary := base.witnessBoundary
  }

theorem bound_admissibility_context_atoms_are_generated
    (base : BoundPrimitiveGeneratedBase) :
    ∀ atom : (boundPrimitiveGeneratedAdmissibility base).Atom,
      (boundPrimitiveGeneratedAdmissibility base).isContext atom ↔
        ∃ context : base.ContextWitness, atom = BoundSourceAtom.context context := by
  intro atom
  cases atom <;> simp [boundPrimitiveGeneratedAdmissibility, boundIsContext]

theorem bound_admissibility_role_atoms_are_constructor_generated
    (base : BoundPrimitiveGeneratedBase) :
    (∀ atom : (boundPrimitiveGeneratedAdmissibility base).Atom,
      (boundPrimitiveGeneratedAdmissibility base).isContext atom ↔
        ∃ context : base.ContextWitness, atom = BoundSourceAtom.context context)
      ∧ (∀ atom : (boundPrimitiveGeneratedAdmissibility base).Atom,
        (boundPrimitiveGeneratedAdmissibility base).isFact atom ↔
          ∃ fact : base.FactWitness, atom = BoundSourceAtom.fact fact)
      ∧ (∀ atom : (boundPrimitiveGeneratedAdmissibility base).Atom,
        (boundPrimitiveGeneratedAdmissibility base).isRoute atom ↔
          ∃ route : base.RouteWitness, atom = BoundSourceAtom.route route)
      ∧ (∀ atom : (boundPrimitiveGeneratedAdmissibility base).Atom,
        (boundPrimitiveGeneratedAdmissibility base).isGenerator atom ↔
          ∃ generator : base.GeneratorWitness, atom = BoundSourceAtom.generator generator)
      ∧ (∀ atom : (boundPrimitiveGeneratedAdmissibility base).Atom,
        (boundPrimitiveGeneratedAdmissibility base).isLocalFact atom ↔
          ∃ localFact : base.LocalFactWitness, atom = BoundSourceAtom.localFact localFact) := by
  constructor
  · exact bound_admissibility_context_atoms_are_generated base
  constructor
  · intro atom
    cases atom <;> simp [boundPrimitiveGeneratedAdmissibility, boundIsFact]
  constructor
  · intro atom
    cases atom <;> simp [boundPrimitiveGeneratedAdmissibility, boundIsRoute]
  constructor
  · intro atom
    cases atom <;> simp [boundPrimitiveGeneratedAdmissibility, boundIsGenerator]
  · intro atom
    cases atom <;> simp [boundPrimitiveGeneratedAdmissibility, boundIsLocalFact]

def boundPrimitiveGeneratedUniversalSourceKernel
    (base : BoundPrimitiveGeneratedBase) :
    UniversalPrimitiveSourceKernel :=
  primitiveGeneratedUniversalSourceKernel
    (boundPrimitiveGeneratedAdmissibility base)

theorem bound_primitive_generated_base_yields_full_qm_obligation_bundle
    (base : BoundPrimitiveGeneratedBase) :
    FullQMObligationBundle
      (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (boundPrimitiveGeneratedUniversalSourceKernel base))) :=
  primitive_generated_admissibility_yields_full_qm_obligation_bundle
    (boundPrimitiveGeneratedAdmissibility base)

theorem bound_primitive_generated_base_yields_import_guards
    (base : BoundPrimitiveGeneratedBase) :
    (groundedSemanticExtensionBaseToCGSCPackageClosure
      (universalPrimitiveSourceKernelToGrounded
        (boundPrimitiveGeneratedUniversalSourceKernel base))).finiteExposed.noSpectralImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (boundPrimitiveGeneratedUniversalSourceKernel base))).finiteExposed.noBornImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (boundPrimitiveGeneratedUniversalSourceKernel base))).finiteExposed.noHilbertImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (boundPrimitiveGeneratedUniversalSourceKernel base))).routeCoherence.noUnitaryImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (boundPrimitiveGeneratedUniversalSourceKernel base))).routeCoherence.noStoneImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (boundPrimitiveGeneratedUniversalSourceKernel base))).routeCoherence.noGeneratorImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (boundPrimitiveGeneratedUniversalSourceKernel base))).compositeClosure.noTensorImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (boundPrimitiveGeneratedUniversalSourceKernel base))).compositeClosure.noBornImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded
          (boundPrimitiveGeneratedUniversalSourceKernel base))).compositeClosure.noHilbertImport.statement :=
  primitive_generated_admissibility_yields_import_guards
    (boundPrimitiveGeneratedAdmissibility base)

end QMClosure
end IDT
