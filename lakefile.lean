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
    `Proofs.QMClosure.UniversalPrimitiveToyWall
  ]
