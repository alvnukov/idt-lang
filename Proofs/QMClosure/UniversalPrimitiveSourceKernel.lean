import Proofs.QMClosure.CGSCGroundedToyWall

namespace IDT
namespace QMClosure

def AtLeastThree (alpha : Type) : Prop :=
  ∃ first : alpha, ∃ second : alpha, ∃ third : alpha,
    first ≠ second ∧ first ≠ third ∧ second ≠ third

theorem bool_has_no_at_least_three : ¬ AtLeastThree Bool := by
  intro witness
  rcases witness with
    ⟨first, second, third, firstNeSecond, firstNeThird, secondNeThird⟩
  cases first <;>
    cases second <;>
    cases third <;>
    simp at firstNeSecond firstNeThird secondNeThird

structure UniversalPrimitiveSourceKernel where
  grounded : GroundedCGSCSemanticExtensionBase
  primitiveGeneratedScope : CheckedProp
  admissibleContextUniverse : CheckedProp
  exposedContextRank : AtLeastThree grounded.exposed.Context
  reversibleContextRank : AtLeastThree grounded.reversible.Context
  localProductContextRank : AtLeastThree grounded.product.LocalContext
  localFactRank : AtLeastThree grounded.noHiddenJoint.LocalFact

def universalPrimitiveSourceKernelToGrounded
    (kernel : UniversalPrimitiveSourceKernel) :
    GroundedCGSCSemanticExtensionBase :=
  kernel.grounded

theorem universal_primitive_source_kernel_yields_full_qm_obligation_bundle
    (kernel : UniversalPrimitiveSourceKernel) :
    FullQMObligationBundle
      (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded kernel)) :=
  grounded_semantic_sources_yield_full_qm_obligation_bundle
    (universalPrimitiveSourceKernelToGrounded kernel)

theorem universal_primitive_source_kernel_yields_import_guards
    (kernel : UniversalPrimitiveSourceKernel) :
    (groundedSemanticExtensionBaseToCGSCPackageClosure
      (universalPrimitiveSourceKernelToGrounded kernel)).finiteExposed.noSpectralImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded kernel)).finiteExposed.noBornImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded kernel)).finiteExposed.noHilbertImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded kernel)).routeCoherence.noUnitaryImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded kernel)).routeCoherence.noStoneImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded kernel)).routeCoherence.noGeneratorImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded kernel)).compositeClosure.noTensorImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded kernel)).compositeClosure.noBornImport.statement
      ∧ (groundedSemanticExtensionBaseToCGSCPackageClosure
        (universalPrimitiveSourceKernelToGrounded kernel)).compositeClosure.noHilbertImport.statement :=
  grounded_semantic_sources_yield_full_qm_import_guards
    (universalPrimitiveSourceKernelToGrounded kernel)

theorem toy_grounded_kernel_has_no_universal_exposed_rank :
    ¬ AtLeastThree toyGroundedCGSCSemanticExtensionBase.exposed.Context :=
  bool_has_no_at_least_three

theorem toy_grounded_kernel_has_no_universal_reversible_rank :
    ¬ AtLeastThree toyGroundedCGSCSemanticExtensionBase.reversible.Context :=
  bool_has_no_at_least_three

theorem toy_grounded_kernel_has_no_universal_product_rank :
    ¬ AtLeastThree toyGroundedCGSCSemanticExtensionBase.product.LocalContext :=
  bool_has_no_at_least_three

theorem toy_grounded_kernel_has_no_universal_local_fact_rank :
    ¬ AtLeastThree toyGroundedCGSCSemanticExtensionBase.noHiddenJoint.LocalFact :=
  bool_has_no_at_least_three

end QMClosure
end IDT
