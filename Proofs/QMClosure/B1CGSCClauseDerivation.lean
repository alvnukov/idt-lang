import Proofs.QMClosure.CGSCStructuralTargetKernel

namespace IDT
namespace QMClosure

def b1FiniteGenerationSource (base : B1PrimitiveBase) : Prop :=
  base.bound.b0.finiteGeneration.statement
    ∧ base.bound.primitiveGeneratedScope.statement
    ∧ base.bound.admissibleContextUniverse.statement

def b1FacticizableSeparationSource (base : B1PrimitiveBase) : Prop :=
  base.bound.b0.facticizableSeparation.statement
    ∧ base.bound.exposedIn base.bound.blockWitness base.bound.contextLeft

def b1ExposedContextDecompositionSource (base : B1PrimitiveBase) : Prop :=
  completeExposedSource
    (primitiveCompleteExposedContextPartitionGround
      (b1PrimitiveGeneratedAdmissibility base))

def b1ReversibleRouteClosureSource (base : B1PrimitiveBase) : Prop :=
  reversibleSource
    (primitiveReversibleContextAutomorphismClosureGround
      (b1PrimitiveGeneratedAdmissibility base))

def b1CoherentRefinementFlowSource (base : B1PrimitiveBase) : Prop :=
  refinementSource
      (primitiveCoherentRefinementCompactnessGround
        (b1PrimitiveGeneratedAdmissibility base))
    ∧ generatorSource
      (primitiveGeneratorBookkeepingWithoutStoneGround
        (b1PrimitiveGeneratedAdmissibility base))

def b1CompositeRouteGenerationSource (base : B1PrimitiveBase) : Prop :=
  productSource
      (primitiveProductContextGenerationClosureGround
        (b1PrimitiveGeneratedAdmissibility base))
    ∧ noHiddenJointSource
      (primitiveNoHiddenJointOnlyGenerationGround
        (b1PrimitiveGeneratedAdmissibility base))

def b1ImportBoundarySource (base : B1PrimitiveBase) : Prop :=
  base.noTargetImportBoundary.statement
    ∧ base.bound.b0.importBoundary.statement
    ∧ base.bound.b0.noHilbertPrimitive.statement
    ∧ base.bound.b0.noBornPrimitive.statement
    ∧ base.bound.b0.noUnitaryPrimitive.statement
    ∧ base.bound.b0.noTensorPrimitive.statement
    ∧ base.bound.b0.noStonePrimitive.statement
    ∧ base.bound.b0.noSpectralPrimitive.statement

def b1FiniteGenerationClause (base : B1PrimitiveBase) : CheckedProp :=
  {
    statement := b1FiniteGenerationSource base,
    proof :=
      And.intro
        base.bound.b0.finiteGeneration.proof
        (And.intro
          base.bound.primitiveGeneratedScope.proof
          base.bound.admissibleContextUniverse.proof)
  }

def b1FacticizableSeparationClause (base : B1PrimitiveBase) : CheckedProp :=
  {
    statement := b1FacticizableSeparationSource base,
    proof :=
      And.intro
        base.bound.b0.facticizableSeparation.proof
        base.bound.exposedWitness
  }

def b1ExposedContextDecompositionClause
    (base : B1PrimitiveBase) :
    CheckedProp :=
  {
    statement := b1ExposedContextDecompositionSource base,
    proof :=
      completeExposedSourceProof
        (primitiveCompleteExposedContextPartitionGround
          (b1PrimitiveGeneratedAdmissibility base))
  }

def b1ReversibleRouteClosureClause
    (base : B1PrimitiveBase) :
    CheckedProp :=
  {
    statement := b1ReversibleRouteClosureSource base,
    proof :=
      reversibleSourceProof
        (primitiveReversibleContextAutomorphismClosureGround
          (b1PrimitiveGeneratedAdmissibility base))
  }

def b1CoherentRefinementFlowClause
    (base : B1PrimitiveBase) :
    CheckedProp :=
  {
    statement := b1CoherentRefinementFlowSource base,
    proof :=
      And.intro
        (refinementSourceProof
          (primitiveCoherentRefinementCompactnessGround
            (b1PrimitiveGeneratedAdmissibility base)))
        (generatorSourceProof
          (primitiveGeneratorBookkeepingWithoutStoneGround
            (b1PrimitiveGeneratedAdmissibility base)))
  }

def b1CompositeRouteGenerationClause
    (base : B1PrimitiveBase) :
    CheckedProp :=
  {
    statement := b1CompositeRouteGenerationSource base,
    proof :=
      And.intro
        (productSourceProof
          (primitiveProductContextGenerationClosureGround
            (b1PrimitiveGeneratedAdmissibility base)))
        (noHiddenJointSourceProof
          (primitiveNoHiddenJointOnlyGenerationGround
            (b1PrimitiveGeneratedAdmissibility base)))
  }

def b1ImportBoundaryClause (base : B1PrimitiveBase) : CheckedProp :=
  {
    statement := b1ImportBoundarySource base,
    proof :=
      And.intro
        base.noTargetImportBoundary.proof
        (And.intro
          base.bound.b0.importBoundary.proof
          (And.intro
            base.bound.b0.noHilbertPrimitive.proof
            (And.intro
              base.bound.b0.noBornPrimitive.proof
              (And.intro
                base.bound.b0.noUnitaryPrimitive.proof
                (And.intro
                  base.bound.b0.noTensorPrimitive.proof
                  (And.intro
                    base.bound.b0.noStonePrimitive.proof
                    base.bound.b0.noSpectralPrimitive.proof))))))
  }

def b1ContextGeneratedStableClosureClauses
    (base : B1PrimitiveBase) :
    ContextGeneratedStableClosureClauses :=
  {
    finiteGeneration := b1FiniteGenerationClause base,
    facticizableSeparation := b1FacticizableSeparationClause base,
    exposedContextDecomposition := b1ExposedContextDecompositionClause base,
    reversibleRouteClosure := b1ReversibleRouteClosureClause base,
    coherentRefinementFlow := b1CoherentRefinementFlowClause base,
    compositeRouteGeneration := b1CompositeRouteGenerationClause base,
    importBoundary := b1ImportBoundaryClause base
  }

def b1AllCGSCClausesDerivedSource (base : B1PrimitiveBase) : Prop :=
  (b1ContextGeneratedStableClosureClauses base).finiteGeneration.statement
    ∧ (b1ContextGeneratedStableClosureClauses base).facticizableSeparation.statement
    ∧ (b1ContextGeneratedStableClosureClauses base).exposedContextDecomposition.statement
    ∧ (b1ContextGeneratedStableClosureClauses base).reversibleRouteClosure.statement
    ∧ (b1ContextGeneratedStableClosureClauses base).coherentRefinementFlow.statement
    ∧ (b1ContextGeneratedStableClosureClauses base).compositeRouteGeneration.statement
    ∧ (b1ContextGeneratedStableClosureClauses base).importBoundary.statement

def b1AllCGSCClausesDerived (base : B1PrimitiveBase) : CheckedProp :=
  {
    statement := b1AllCGSCClausesDerivedSource base,
    proof :=
      And.intro
        (b1ContextGeneratedStableClosureClauses base).finiteGeneration.proof
        (And.intro
          (b1ContextGeneratedStableClosureClauses base).facticizableSeparation.proof
          (And.intro
            (b1ContextGeneratedStableClosureClauses base).exposedContextDecomposition.proof
            (And.intro
              (b1ContextGeneratedStableClosureClauses base).reversibleRouteClosure.proof
              (And.intro
                (b1ContextGeneratedStableClosureClauses base).coherentRefinementFlow.proof
                (And.intro
                  (b1ContextGeneratedStableClosureClauses base).compositeRouteGeneration.proof
                  (b1ContextGeneratedStableClosureClauses base).importBoundary.proof)))))
  }

def b1ContextGeneratedStableClosureDerivationRules
    (base : B1PrimitiveBase) :
    ContextGeneratedStableClosureDerivationRules
      base
      (b1ContextGeneratedStableClosureClauses base) :=
  {
    nonunitalStableDistinguishability := fun _ _ _ =>
      (b1PrimitiveBaseToFullQMSemanticKernel base).residualProjective.nonunitalStableDistinguishability.proof,
    spectralDecomposition := fun _ _ _ =>
      (b1PrimitiveBaseToFullQMSemanticKernel base).representation.spectralDecomposition.proof,
    richDclReversibleSymmetry := fun _ _ _ =>
      (b1PrimitiveBaseToFullQMSemanticKernel base).representation.richDclReversibleSymmetry.proof,
    continuousInheritanceFamily := fun _ _ _ =>
      (b1PrimitiveBaseToFullQMSemanticKernel base).dynamics.continuousInheritanceFamily.proof,
    generatorClosure := fun _ _ =>
      (b1PrimitiveBaseToFullQMSemanticKernel base).dynamics.generatorClosure.proof,
    entanglementClosure := fun _ _ _ _ =>
      (b1PrimitiveBaseToFullQMSemanticKernel base).composite.entanglementClosure.proof
  }

def b1ContextGeneratedStableClosureRoute
    (base : B1PrimitiveBase) :
    ContextGeneratedStableClosureFromB1 :=
  {
    base := base,
    clauses := b1ContextGeneratedStableClosureClauses base,
    clausesDerivedFromB1 := b1AllCGSCClausesDerived base,
    derivationRules := b1ContextGeneratedStableClosureDerivationRules base
  }

theorem b1_derives_all_cgsc_clause_sources
    (base : B1PrimitiveBase) :
    b1AllCGSCClausesDerivedSource base :=
  by
    change (b1AllCGSCClausesDerived base).statement
    exact (b1AllCGSCClausesDerived base).proof

theorem b1_cgsc_clause_sources_share_one_atom_universe
    (base : B1PrimitiveBase) :
    (primitiveGeneratedGroundedSemanticExtensionBase
        (b1PrimitiveGeneratedAdmissibility base)).exposed.Context =
        (b1PrimitiveGeneratedAdmissibility base).Context
      ∧ (primitiveGeneratedGroundedSemanticExtensionBase
        (b1PrimitiveGeneratedAdmissibility base)).reversible.Context =
        (b1PrimitiveGeneratedAdmissibility base).Context
      ∧ (primitiveGeneratedGroundedSemanticExtensionBase
        (b1PrimitiveGeneratedAdmissibility base)).product.LocalContext =
        (b1PrimitiveGeneratedAdmissibility base).Context
      ∧ (primitiveGeneratedGroundedSemanticExtensionBase
        (b1PrimitiveGeneratedAdmissibility base)).noHiddenJoint.LocalFact =
        (b1PrimitiveGeneratedAdmissibility base).LocalFact :=
  primitive_generated_source_slots_share_one_atom_universe
    (b1PrimitiveGeneratedAdmissibility base)

theorem b1_cgsc_clause_derivation_closes_six_blockers
    (base : B1PrimitiveBase) :
    (contextGeneratedStableClosureFromB1SemanticKernel
        (b1ContextGeneratedStableClosureRoute base)).residualProjective.nonunitalStableDistinguishability.statement
      ∧ (contextGeneratedStableClosureFromB1SemanticKernel
        (b1ContextGeneratedStableClosureRoute base)).representation.spectralDecomposition.statement
      ∧ (contextGeneratedStableClosureFromB1SemanticKernel
        (b1ContextGeneratedStableClosureRoute base)).representation.richDclReversibleSymmetry.statement
      ∧ (contextGeneratedStableClosureFromB1SemanticKernel
        (b1ContextGeneratedStableClosureRoute base)).dynamics.continuousInheritanceFamily.statement
      ∧ (contextGeneratedStableClosureFromB1SemanticKernel
        (b1ContextGeneratedStableClosureRoute base)).dynamics.generatorClosure.statement
      ∧ (contextGeneratedStableClosureFromB1SemanticKernel
        (b1ContextGeneratedStableClosureRoute base)).composite.entanglementClosure.statement :=
  cgsc_structural_target_kernel_closes_six_blockers
    base
    (b1ContextGeneratedStableClosureClauses base)
    (b1ContextGeneratedStableClosureDerivationRules base)

theorem b1_cgsc_clause_derivation_yields_full_qm_obligation_bundle
    (base : B1PrimitiveBase) :
    FullQMObligationBundle
      (semanticKernelToPackageClosure
        (contextGeneratedStableClosureFromB1SemanticKernel
          (b1ContextGeneratedStableClosureRoute base))) :=
  context_generated_stable_closure_from_b1_yields_full_qm_obligation_bundle
    (b1ContextGeneratedStableClosureRoute base)

theorem b1_cgsc_clause_derivation_preserves_import_boundaries
    (base : B1PrimitiveBase) :
    (semanticKernelToPackageClosure
      (contextGeneratedStableClosureFromB1SemanticKernel
        (b1ContextGeneratedStableClosureRoute base))).finiteExposed.noSpectralImport.statement
      ∧ (semanticKernelToPackageClosure
        (contextGeneratedStableClosureFromB1SemanticKernel
          (b1ContextGeneratedStableClosureRoute base))).finiteExposed.noBornImport.statement
      ∧ (semanticKernelToPackageClosure
        (contextGeneratedStableClosureFromB1SemanticKernel
          (b1ContextGeneratedStableClosureRoute base))).finiteExposed.noHilbertImport.statement
      ∧ (semanticKernelToPackageClosure
        (contextGeneratedStableClosureFromB1SemanticKernel
          (b1ContextGeneratedStableClosureRoute base))).routeCoherence.noUnitaryImport.statement
      ∧ (semanticKernelToPackageClosure
        (contextGeneratedStableClosureFromB1SemanticKernel
          (b1ContextGeneratedStableClosureRoute base))).routeCoherence.noStoneImport.statement
      ∧ (semanticKernelToPackageClosure
        (contextGeneratedStableClosureFromB1SemanticKernel
          (b1ContextGeneratedStableClosureRoute base))).routeCoherence.noGeneratorImport.statement
      ∧ (semanticKernelToPackageClosure
        (contextGeneratedStableClosureFromB1SemanticKernel
          (b1ContextGeneratedStableClosureRoute base))).compositeClosure.noTensorImport.statement
      ∧ (semanticKernelToPackageClosure
        (contextGeneratedStableClosureFromB1SemanticKernel
          (b1ContextGeneratedStableClosureRoute base))).compositeClosure.noBornImport.statement
      ∧ (semanticKernelToPackageClosure
        (contextGeneratedStableClosureFromB1SemanticKernel
          (b1ContextGeneratedStableClosureRoute base))).compositeClosure.noHilbertImport.statement :=
  context_generated_stable_closure_from_b1_preserves_import_boundaries
    (b1ContextGeneratedStableClosureRoute base)

end QMClosure
end IDT
