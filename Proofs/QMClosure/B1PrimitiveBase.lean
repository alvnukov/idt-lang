import Proofs.QMClosure.BoundPrimitiveGeneratedBase

namespace IDT
namespace QMClosure

structure B1PrimitiveBase where
  bound : BoundPrimitiveGeneratedBase
  successorBasePromoted : CheckedProp
  noFreeAdmissibilityBoundary : CheckedProp
  noTargetImportBoundary : CheckedProp

def b1ToBoundPrimitiveGeneratedBase
    (base : B1PrimitiveBase) :
    BoundPrimitiveGeneratedBase :=
  base.bound

def b1PrimitiveGeneratedAdmissibility
    (base : B1PrimitiveBase) :
    PrimitiveGeneratedAdmissibility :=
  boundPrimitiveGeneratedAdmissibility
    (b1ToBoundPrimitiveGeneratedBase base)

def b1PrimitiveGeneratedUniversalSourceKernel
    (base : B1PrimitiveBase) :
    UniversalPrimitiveSourceKernel :=
  boundPrimitiveGeneratedUniversalSourceKernel
    (b1ToBoundPrimitiveGeneratedBase base)

def b1PrimitiveGeneratedCGSCPackageClosure
    (base : B1PrimitiveBase) :
    CGSCPackageClosure :=
  groundedSemanticExtensionBaseToCGSCPackageClosure
    (universalPrimitiveSourceKernelToGrounded
      (b1PrimitiveGeneratedUniversalSourceKernel base))

theorem b1_primitive_base_constructor_binds_admissibility
    (base : B1PrimitiveBase) :
    (∀ atom : (b1PrimitiveGeneratedAdmissibility base).Atom,
      (b1PrimitiveGeneratedAdmissibility base).isContext atom ↔
        ∃ context : base.bound.ContextWitness,
          atom = BoundSourceAtom.context context)
      ∧ (∀ atom : (b1PrimitiveGeneratedAdmissibility base).Atom,
        (b1PrimitiveGeneratedAdmissibility base).isFact atom ↔
          ∃ fact : base.bound.FactWitness,
            atom = BoundSourceAtom.fact fact)
      ∧ (∀ atom : (b1PrimitiveGeneratedAdmissibility base).Atom,
        (b1PrimitiveGeneratedAdmissibility base).isRoute atom ↔
          ∃ route : base.bound.RouteWitness,
            atom = BoundSourceAtom.route route)
      ∧ (∀ atom : (b1PrimitiveGeneratedAdmissibility base).Atom,
        (b1PrimitiveGeneratedAdmissibility base).isGenerator atom ↔
          ∃ generator : base.bound.GeneratorWitness,
            atom = BoundSourceAtom.generator generator)
      ∧ (∀ atom : (b1PrimitiveGeneratedAdmissibility base).Atom,
        (b1PrimitiveGeneratedAdmissibility base).isLocalFact atom ↔
          ∃ localFact : base.bound.LocalFactWitness,
            atom = BoundSourceAtom.localFact localFact) :=
  bound_admissibility_role_atoms_are_constructor_generated
    (b1ToBoundPrimitiveGeneratedBase base)

theorem b1_primitive_base_promotes_successor_boundaries
    (base : B1PrimitiveBase) :
    base.successorBasePromoted.statement
      ∧ base.noFreeAdmissibilityBoundary.statement
      ∧ base.noTargetImportBoundary.statement
      ∧ base.bound.primitiveGeneratedScope.statement
      ∧ base.bound.admissibleContextUniverse.statement :=
  And.intro
    base.successorBasePromoted.proof
    (And.intro
      base.noFreeAdmissibilityBoundary.proof
      (And.intro
        base.noTargetImportBoundary.proof
        (And.intro
          base.bound.primitiveGeneratedScope.proof
          base.bound.admissibleContextUniverse.proof)))

theorem b1_primitive_base_yields_full_qm_obligation_bundle
    (base : B1PrimitiveBase) :
    FullQMObligationBundle
      (b1PrimitiveGeneratedCGSCPackageClosure base) :=
  bound_primitive_generated_base_yields_full_qm_obligation_bundle
    (b1ToBoundPrimitiveGeneratedBase base)

theorem b1_primitive_base_yields_import_guards
    (base : B1PrimitiveBase) :
    (b1PrimitiveGeneratedCGSCPackageClosure base).finiteExposed.noSpectralImport.statement
      ∧ (b1PrimitiveGeneratedCGSCPackageClosure base).finiteExposed.noBornImport.statement
      ∧ (b1PrimitiveGeneratedCGSCPackageClosure base).finiteExposed.noHilbertImport.statement
      ∧ (b1PrimitiveGeneratedCGSCPackageClosure base).routeCoherence.noUnitaryImport.statement
      ∧ (b1PrimitiveGeneratedCGSCPackageClosure base).routeCoherence.noStoneImport.statement
      ∧ (b1PrimitiveGeneratedCGSCPackageClosure base).routeCoherence.noGeneratorImport.statement
      ∧ (b1PrimitiveGeneratedCGSCPackageClosure base).compositeClosure.noTensorImport.statement
      ∧ (b1PrimitiveGeneratedCGSCPackageClosure base).compositeClosure.noBornImport.statement
      ∧ (b1PrimitiveGeneratedCGSCPackageClosure base).compositeClosure.noHilbertImport.statement :=
  bound_primitive_generated_base_yields_import_guards
    (b1ToBoundPrimitiveGeneratedBase base)

end QMClosure
end IDT
