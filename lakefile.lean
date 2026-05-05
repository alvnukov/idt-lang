import Lake
open Lake DSL

package IDTProofs where

lean_lib Proofs where
  roots := #[
    `Proofs.IDTCore,
    `Proofs.QMClosure.CGSCPackageClosure,
    `Proofs.QMClosure.CGSCPrimitiveBridge,
    `Proofs.QMClosure.CGSCSemanticContentWall,
    `Proofs.QMClosure.CGSCTypedSemanticExtensions,
    `Proofs.QMClosure.CGSCTypedDecorativeWall,
    `Proofs.QMClosure.CGSCGroundedSemanticExtensions,
    `Proofs.QMClosure.FullQMAssemblyFromGroundedSources,
    `Proofs.QMClosure.CGSCGroundedToyWall,
    `Proofs.QMClosure.UniversalPrimitiveSourceKernel,
    `Proofs.QMClosure.UniversalPrimitiveToyWall,
    `Proofs.QMClosure.PrimitiveGeneratedSourceKernel,
    `Proofs.QMClosure.PrimitiveGeneratedAdmissibilityWall,
    `Proofs.QMClosure.BoundPrimitiveGeneratedBase,
    `Proofs.QMClosure.B1PrimitiveBase,
    `Proofs.QMClosure.QMSemanticKernelRoute,
    `Proofs.QMClosure.ProjectionScaffoldsDraft,
    `Proofs.QMClosure.ReadoutScaffoldsDraft,
    `Proofs.QMClosure.InheritanceScaffoldsDraft,
    `Proofs.QMClosure.CompositeScaffoldsDraft,
    `Proofs.QMClosure.MonoidalAssociativityDraft,
    `Proofs.QMClosure.ProjectiveLimitScaffoldDraft,
    `Proofs.QMClosure.BoundaryScaffoldsDraft,
    `Proofs.QMClosure.QMSemanticContentScaffoldBundle,
    `Proofs.QMClosure.CGSCStructuralTargetKernel,
    `Proofs.QMClosure.B1CGSCClauseDerivation,
    `Proofs.QMClosure.BornWallSeparation
  ]
