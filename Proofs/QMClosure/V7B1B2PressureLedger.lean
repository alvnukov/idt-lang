import Proofs.QMClosure.V7PrimitiveCandidateStack

namespace IDT
namespace QMClosure

/-!
V7 B1/B2 pressure-ledger recovery.

This file preserves sections 174.33-174.77 of the v7 research note: the move
from B0 to B1/B1'/B2, strong-positivity pressure, real/boxworld separator
pressure, and the final survivor-base verdict. It is a status ledger, not a
proof that complex Hilbert space or the Born rule follows.
-/

structure V7B1BasePressure where
  finiteFacticizationStability : Prop
  orientedCycleComposition : Prop
  operationalClosureOfD : Prop
  secondOrderFacticizationNeeded : Prop
  strongPositivityPressure : Prop
  provesComplexHilbert : Prop
  provesBornRule : Prop

def V7B1BasePressureHonest (p : V7B1BasePressure) : Prop :=
  p.finiteFacticizationStability
    ∧ p.orientedCycleComposition
    ∧ p.operationalClosureOfD
    ∧ p.secondOrderFacticizationNeeded
    ∧ p.strongPositivityPressure
    ∧ ¬ p.provesComplexHilbert
    ∧ ¬ p.provesBornRule

def v7RecoveredB1Pressure : V7B1BasePressure :=
  {
    finiteFacticizationStability := True,
    orientedCycleComposition := True,
    operationalClosureOfD := True,
    secondOrderFacticizationNeeded := True,
    strongPositivityPressure := True,
    provesComplexHilbert := False,
    provesBornRule := False
  }

structure V7B1SeparatorPressure where
  realHilbertHiddenOrientationRejected : Prop
  boxworldClosureStress : Prop
  genericGPTResidualStillOpen : Prop
  representationClassificationMissing : Prop

def V7B1SeparatorPressureAccepted
    (p : V7B1SeparatorPressure) : Prop :=
  p.realHilbertHiddenOrientationRejected
    ∧ p.boxworldClosureStress
    ∧ p.genericGPTResidualStillOpen
    ∧ p.representationClassificationMissing

def v7RecoveredB1SeparatorPressure : V7B1SeparatorPressure :=
  {
    realHilbertHiddenOrientationRejected := True,
    boxworldClosureStress := True,
    genericGPTResidualStillOpen := True,
    representationClassificationMissing := True
  }

structure V7B2SurvivorBase where
  core : V7CorePrimitiveStack
  noSilentLossAccounting : Prop
  qmSectorNeedsS2 : Prop
  gravitySectorNeedsSourceResponse : Prop
  scaleProjectionDisciplineBoundary : Prop
  provesPurification : Prop
  provesHilbertUniqueness : Prop

def V7B2SurvivorBaseHonest (b : V7B2SurvivorBase) : Prop :=
  V7CorePrimitiveStackClosed b.core
    ∧ b.noSilentLossAccounting
    ∧ b.qmSectorNeedsS2
    ∧ b.gravitySectorNeedsSourceResponse
    ∧ b.scaleProjectionDisciplineBoundary
    ∧ ¬ b.provesPurification
    ∧ ¬ b.provesHilbertUniqueness

def v7RecoveredB2SurvivorBase : V7B2SurvivorBase :=
  {
    core := v7RecoveredCorePrimitiveStack,
    noSilentLossAccounting := True,
    qmSectorNeedsS2 := True,
    gravitySectorNeedsSourceResponse := True,
    scaleProjectionDisciplineBoundary := True,
    provesPurification := False,
    provesHilbertUniqueness := False
  }

theorem v7_b1_pressure_preserved_without_qm_upgrade :
    V7B1BasePressureHonest v7RecoveredB1Pressure :=
  And.intro trivial <|
    And.intro trivial <|
      And.intro trivial <|
        And.intro trivial <|
          And.intro trivial <|
            And.intro (by intro h; exact h) (by intro h; exact h)

theorem v7_b1_separator_pressure_preserved :
    V7B1SeparatorPressureAccepted v7RecoveredB1SeparatorPressure :=
  And.intro trivial <|
    And.intro trivial <|
      And.intro trivial trivial

theorem v7_b2_survivor_base_preserved_without_purification_or_uniqueness :
    V7B2SurvivorBaseHonest v7RecoveredB2SurvivorBase :=
  And.intro v7_core_primitive_stack_contains_dcl_f_q_l <|
    And.intro trivial <|
      And.intro trivial <|
        And.intro trivial <|
          And.intro trivial <|
            And.intro (by intro h; exact h) (by intro h; exact h)

end QMClosure
end IDT
