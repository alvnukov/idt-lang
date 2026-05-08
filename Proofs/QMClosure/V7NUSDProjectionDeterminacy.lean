import Proofs.QMClosure.V7PrimitiveCandidateStack

namespace IDT
namespace QMClosure

/-!
V7 NUSD and finite-projection-determinacy recovery.

This module records the v7 distinction between finite route compactness and the
weaker finite projection determinacy route. It is a proof-ledger boundary, not a
first-principles derivation of the Hilbert/Born/QM package.
-/

structure V7NoUnwitnessedStableDifference where
  stableDifferenceRequiresWitnessRoute : Prop
  explicitLossAccountingForUnwitnessedDifference : Prop
  belowBornRule : Prop
  belowHilbertCarrier : Prop

def V7NoUnwitnessedStableDifferenceAccepted
    (nusd : V7NoUnwitnessedStableDifference) : Prop :=
  nusd.stableDifferenceRequiresWitnessRoute
    ∧ nusd.explicitLossAccountingForUnwitnessedDifference
    ∧ nusd.belowBornRule
    ∧ nusd.belowHilbertCarrier

structure V7FiniteRouteCompactness where
  globalFiniteRouteBasis : Prop
  noInfiniteResidualTower : Prop

def V7FiniteRouteCompactnessAccepted
    (frc : V7FiniteRouteCompactness) : Prop :=
  frc.globalFiniteRouteBasis ∧ frc.noInfiniteResidualTower

structure V7FiniteProjectionDeterminacy where
  finiteRouteGeneratedProjectionAgreement : Prop
  noPhysicalDistinctionAfterProjectionAgreement : Prop
  allowsInfiniteTowersWithPointwiseWitnesses : Prop

def V7FiniteProjectionDeterminacyAccepted
    (fpd : V7FiniteProjectionDeterminacy) : Prop :=
  fpd.finiteRouteGeneratedProjectionAgreement
    ∧ fpd.noPhysicalDistinctionAfterProjectionAgreement
    ∧ fpd.allowsInfiniteTowersWithPointwiseWitnesses

structure V7NUSDToFPDRoute where
  nusd : V7NoUnwitnessedStableDifference
  finiteContextGeneration : Prop
  operationalClosure : Prop
  finiteProjectionDeterminacy : V7FiniteProjectionDeterminacy

def V7NUSDToFPDRouteClosed (route : V7NUSDToFPDRoute) : Prop :=
  V7NoUnwitnessedStableDifferenceAccepted route.nusd
    ∧ route.finiteContextGeneration
    ∧ route.operationalClosure
    ∧ V7FiniteProjectionDeterminacyAccepted
        route.finiteProjectionDeterminacy

def v7RecoveredNUSD : V7NoUnwitnessedStableDifference :=
  {
    stableDifferenceRequiresWitnessRoute := True,
    explicitLossAccountingForUnwitnessedDifference := True,
    belowBornRule := True,
    belowHilbertCarrier := True
  }

def v7RecoveredFPD : V7FiniteProjectionDeterminacy :=
  {
    finiteRouteGeneratedProjectionAgreement := True,
    noPhysicalDistinctionAfterProjectionAgreement := True,
    allowsInfiniteTowersWithPointwiseWitnesses := True
  }

def v7RecoveredNUSDToFPDRoute : V7NUSDToFPDRoute :=
  {
    nusd := v7RecoveredNUSD,
    finiteContextGeneration := True,
    operationalClosure := True,
    finiteProjectionDeterminacy := v7RecoveredFPD
  }

def v7RejectedFRCAsPrimitive : V7FiniteRouteCompactness :=
  {
    globalFiniteRouteBasis := False,
    noInfiniteResidualTower := False
  }

theorem v7_nusd_recovered_as_below_born_and_hilbert :
    V7NoUnwitnessedStableDifferenceAccepted v7RecoveredNUSD :=
  And.intro trivial <|
    And.intro trivial <|
      And.intro trivial trivial

theorem v7_fpd_recovered_without_global_frc_primitive :
    V7FiniteProjectionDeterminacyAccepted v7RecoveredFPD
      ∧ ¬ V7FiniteRouteCompactnessAccepted v7RejectedFRCAsPrimitive :=
  And.intro
    (And.intro trivial <| And.intro trivial trivial)
    (by
      intro frc
      exact frc.left)

theorem v7_nusd_plus_finite_context_generation_routes_to_fpd :
    V7NUSDToFPDRouteClosed v7RecoveredNUSDToFPDRoute :=
  And.intro v7_nusd_recovered_as_below_born_and_hilbert <|
    And.intro trivial <|
      And.intro trivial (And.intro trivial <| And.intro trivial trivial)

structure V7FiniteSectorCarrierRoute where
  finiteSectorRepresentation : Prop
  finiteProjectionDeterminacy : Prop
  projectiveConsistency : Prop
  carrierFrontierExhaustion : Prop

def V7FiniteSectorCarrierRouteClosed
    (route : V7FiniteSectorCarrierRoute) : Prop :=
  route.finiteSectorRepresentation
    ∧ route.finiteProjectionDeterminacy
    ∧ route.projectiveConsistency
    ∧ route.carrierFrontierExhaustion

def v7RecoveredCarrierRouteFrontier : V7FiniteSectorCarrierRoute :=
  {
    finiteSectorRepresentation := True,
    finiteProjectionDeterminacy := True,
    projectiveConsistency := False,
    carrierFrontierExhaustion := False
  }

theorem v7_carrier_frontier_still_requires_projective_consistency :
    ¬ V7FiniteSectorCarrierRouteClosed v7RecoveredCarrierRouteFrontier :=
  by
    intro closed
    exact closed.right.right.left

theorem v7_fpd_is_weaker_than_global_frc_in_recovered_ledger :
    V7FiniteProjectionDeterminacyAccepted v7RecoveredFPD
      ∧ ¬ V7FiniteRouteCompactnessAccepted v7RejectedFRCAsPrimitive :=
  v7_fpd_recovered_without_global_frc_primitive

end QMClosure
end IDT
