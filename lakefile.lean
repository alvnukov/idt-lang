import Lake
open Lake DSL

package IDTProofs where

lean_lib Proofs where
  roots := #[
    `Proofs.IDTCore,
    `Proofs.MetaLang.V8VerificationLanguage,
    `Proofs.MetaLang.V8ContextFirstPrimitiveBase,
    `Proofs.MetaLang.V8TheoremCardLedger,
    `Proofs.MetaLang.V8CurrentStatusSnapshot,
    `Proofs.MetaLang.V8ExternalCheckerBoundary,
    `Proofs.MetaLang.V8StatusTransitionPolicy,
    `Proofs.MetaLang.V8DependencyGraphPolicy,
    `Proofs.MetaLang.V8StoppedResearchFrontier,
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
    `Proofs.QMClosure.BornWallSeparation,
    `Proofs.QMClosure.SchrodingerGeneratorLogic,
    `Proofs.QMClosure.S2BornProofSearch,
    `Proofs.QMClosure.PrimitiveBoundaryQMChain,
    `Proofs.QMClosure.ConstructiveWitnessPrimitiveBase,
    `Proofs.QMClosure.BornHilbertUniversalClosure,
    `Proofs.QMClosure.FullQMSectorClosure
  ]
