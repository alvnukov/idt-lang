import Proofs.QMClosure.ThreeSourceDistributiveSwapRoot
import Proofs.QMClosure.RawPlanePhaseLocalTheory
import Proofs.QMClosure.RawSparseQuarticControl

namespace IDT.QMClosure.ThreeSourceExchangeReadoutBoundary

/-!
The exact two-preparation language and three-value exchange have distinct
boundaries. One existing operation satisfies every native-valid collection in
that language and fails exchange. Another satisfies full exchange with a
nonnegative quartic readout, while failing conservation and the sparse law.
These are supplied controls, with no claim of physical availability. Repeated
preparation values in four-wire networks require preparation replay.
-/

open ThreeSourceDistributiveSwapRoot

theorem actual_not_restrictedExchange :
    ¬ RestrictedExchange RawPlanePhaseControl.operation := by
  intro hexchange
  have hlaws := (restrictedExchange_iff_laws RawPlanePhaseControl.operation
    RawPlanePhaseControl.contract.transparent RawPlanePhaseControl.contract.square).mp hexchange
  have hmedial : ∀ a b c d,
      RawSparseConservationSelection.m RawPlanePhaseControl.contract
        (RawSparseConservationSelection.m RawPlanePhaseControl.contract a b)
        (RawSparseConservationSelection.m RawPlanePhaseControl.contract c d) =
      RawSparseConservationSelection.m RawPlanePhaseControl.contract
        (RawSparseConservationSelection.m RawPlanePhaseControl.contract a c)
        (RawSparseConservationSelection.m RawPlanePhaseControl.contract b d) := medial hlaws
  apply RawPlanePhaseSparseWall.constructed_not_observed_medial
  intro a b c d
  rw [hmedial]
  intro context
  rfl

/-- The statement is restricted to the existing exact quantifier-free syntax. -/
theorem native_valid_collection_exchange_countermodel
    (Γ : Set RawPlanePhaseLocalTheory.QuantifierfreeFormula2)
    (hΓ : ∀ formula ∈ Γ, RawPlanePhaseLocalTheory.nativeValid formula) :
    (∀ formula ∈ Γ, RawPlanePhaseLocalTheory.actualValid formula) ∧
      RawPlanePhaseLocalTheory.ActualCountermodelProperties ∧
      ¬ RestrictedExchange RawPlanePhaseControl.operation := by
  obtain ⟨hvalid, hproperties⟩ :=
    RawPlanePhaseLocalTheory.native_valid_collection_countermodel Γ hΓ
  exact ⟨hvalid, hproperties, actual_not_restrictedExchange⟩

theorem quartic_laws :
    Laws (MedialSwapRoot.firstChannel RawSparseQuarticControl.contract.operation) :=
  ofMedialSwapRootLaws (MedialSwapRoot.laws_of_complete_operation
    RawSparseQuarticControl.contract.operation RawSparseQuarticControl.contract.transparent
    RawSparseQuarticControl.contract.square RawSparseQuarticControl.first_channel_medial)

/-- Even full preparation exchange leaves the scalar readout unconstrained. -/
theorem quartic_exchange_readout_boundary :
    RestrictedExchange RawSparseQuarticControl.contract.operation ∧
      CompleteExchange RawSparseQuarticControl.contract.operation ∧
      (∀ z, 0 ≤ RawSparseQuarticControl.contract.weight z) ∧
      ¬ RawSparseConservationSelection.PairConserved RawSparseQuarticControl.contract ∧
      ¬ RawSparseConservationSelection.SparseMarginalLaw RawSparseQuarticControl.contract := by
  have hrestricted := (restrictedExchange_iff_laws
    RawSparseQuarticControl.contract.operation RawSparseQuarticControl.contract.transparent
    RawSparseQuarticControl.contract.square).mpr quartic_laws
  exact ⟨hrestricted, (restrictedExchange_iff_completeExchange
    RawSparseQuarticControl.contract.operation RawSparseQuarticControl.contract.transparent
    RawSparseQuarticControl.contract.square).mp hrestricted,
    RawSparseQuarticControl.nonnegative, RawSparseQuarticControl.not_pair_conserved,
    RawSparseQuarticControl.not_sparse_law⟩

end IDT.QMClosure.ThreeSourceExchangeReadoutBoundary
