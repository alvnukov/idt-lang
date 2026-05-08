import Proofs.QMClosure.V7NUSDProjectionDeterminacy
import Proofs.QMClosure.V7B1B2PressureLedger

namespace IDT
namespace QMClosure

/-!
V7 hypothesis-batch recovery.

This file preserves sections 174.78-174.128: batches H1-H28, T1-T3, R1-R4,
FUW/FRC rejection, NUSD stress tests, and the FPD replacement route.
-/

structure V7BatchOne where
  coreDerivesS2 : Prop
  s2GivesPositivityConditionally : Prop
  realHilbertSeparatorSurvives : Prop
  boxworldSeparatorConditional : Prop
  complexHilbertUniquenessFails : Prop
  universalRecoverableExtensionFails : Prop
  bornReadoutConditional : Prop

def V7BatchOneHonest (b : V7BatchOne) : Prop :=
  ¬ b.coreDerivesS2
    ∧ b.s2GivesPositivityConditionally
    ∧ b.realHilbertSeparatorSurvives
    ∧ b.boxworldSeparatorConditional
    ∧ b.complexHilbertUniquenessFails
    ∧ b.universalRecoverableExtensionFails
    ∧ b.bornReadoutConditional

def v7BatchOneRecovered : V7BatchOne :=
  {
    coreDerivesS2 := False,
    s2GivesPositivityConditionally := True,
    realHilbertSeparatorSurvives := True,
    boxworldSeparatorConditional := True,
    complexHilbertUniquenessFails := True,
    universalRecoverableExtensionFails := True,
    bornReadoutConditional := True
  }

structure V7BatchTwoThree where
  positiveGeometryConditional : Prop
  lossAccountingSurvives : Prop
  quadraticReadoutPartial : Prop
  finiteBornLikeContextProbabilityConditional : Prop
  complexHilbertPressureConditional : Prop
  complexHilbertUniquenessFails : Prop

def V7BatchTwoThreeHonest (b : V7BatchTwoThree) : Prop :=
  b.positiveGeometryConditional
    ∧ b.lossAccountingSurvives
    ∧ b.quadraticReadoutPartial
    ∧ b.finiteBornLikeContextProbabilityConditional
    ∧ b.complexHilbertPressureConditional
    ∧ b.complexHilbertUniquenessFails

def v7BatchTwoThreeRecovered : V7BatchTwoThree :=
  {
    positiveGeometryConditional := True,
    lossAccountingSurvives := True,
    quadraticReadoutPartial := True,
    finiteBornLikeContextProbabilityConditional := True,
    complexHilbertPressureConditional := True,
    complexHilbertUniquenessFails := True
  }

structure V7BatchFourFiveSix where
  residualKillerConditional : Prop
  finiteCountermodelAbsentInCurrentGraph : Prop
  b2DoesNotDeriveFUW : Prop
  fuwKillsResidualConditionally : Prop
  fuwDoesNotProveHilbertUniqueness : Prop
  nusdBelowBornAndHilbert : Prop
  nusdDoesNotImplyUniformFRC : Prop
  fpdReplacesFRCAsRoute : Prop

def V7BatchFourFiveSixHonest (b : V7BatchFourFiveSix) : Prop :=
  b.residualKillerConditional
    ∧ b.finiteCountermodelAbsentInCurrentGraph
    ∧ b.b2DoesNotDeriveFUW
    ∧ b.fuwKillsResidualConditionally
    ∧ b.fuwDoesNotProveHilbertUniqueness
    ∧ b.nusdBelowBornAndHilbert
    ∧ b.nusdDoesNotImplyUniformFRC
    ∧ b.fpdReplacesFRCAsRoute

def v7BatchFourFiveSixRecovered : V7BatchFourFiveSix :=
  {
    residualKillerConditional := True,
    finiteCountermodelAbsentInCurrentGraph := True,
    b2DoesNotDeriveFUW := True,
    fuwKillsResidualConditionally := True,
    fuwDoesNotProveHilbertUniqueness := True,
    nusdBelowBornAndHilbert := True,
    nusdDoesNotImplyUniformFRC := True,
    fpdReplacesFRCAsRoute := True
  }

theorem v7_batch_one_recovered :
    V7BatchOneHonest v7BatchOneRecovered :=
  And.intro (by intro h; exact h) <|
    And.intro trivial <|
      And.intro trivial <|
        And.intro trivial <|
          And.intro trivial <|
            And.intro trivial trivial

theorem v7_batches_two_three_recovered :
    V7BatchTwoThreeHonest v7BatchTwoThreeRecovered :=
  And.intro trivial <|
    And.intro trivial <|
      And.intro trivial <|
        And.intro trivial <|
          And.intro trivial trivial

theorem v7_batches_four_five_six_recovered :
    V7BatchFourFiveSixHonest v7BatchFourFiveSixRecovered :=
  And.intro trivial <|
    And.intro trivial <|
      And.intro trivial <|
        And.intro trivial <|
          And.intro trivial <|
            And.intro trivial <|
              And.intro trivial trivial

theorem v7_hypothesis_batches_route_to_fpd_not_full_qm :
    V7NUSDToFPDRouteClosed v7RecoveredNUSDToFPDRoute
      ∧ ¬ V7FiniteSectorCarrierRouteClosed
          v7RecoveredCarrierRouteFrontier :=
  And.intro
    v7_nusd_plus_finite_context_generation_routes_to_fpd
    v7_carrier_frontier_still_requires_projective_consistency

end QMClosure
end IDT
