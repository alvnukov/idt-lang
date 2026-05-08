import Proofs.QMClosure.SchrodingerGeneratorLogic

namespace IDT
namespace QMClosure

/-!
V7 Schrodinger/dynamics route recovery.

V7 separated the frequency-generator route from the physical energy/action
scale. This module preserves the full v7 obligation split and connects it to
the existing action-scale-free Schrodinger generator artifact.
-/

structure V7DynamicsRouteInputs where
  reversibleDclAutomorphism : Prop
  overlapPreservation : Prop
  projectiveAction : Prop
  continuousInheritanceFamily : Prop
  generatorClosure : Prop
  phaseOrientation : Prop
  normalizedTransitionReadout : Prop
  noUnitaryImport : Prop
  noStoneImport : Prop
  noGeneratorImport : Prop

def V7DynamicsRouteClosed
    (inputs : V7DynamicsRouteInputs) : Prop :=
  inputs.reversibleDclAutomorphism
    ∧ inputs.overlapPreservation
    ∧ inputs.projectiveAction
    ∧ inputs.continuousInheritanceFamily
    ∧ inputs.generatorClosure
    ∧ inputs.phaseOrientation
    ∧ inputs.normalizedTransitionReadout
    ∧ inputs.noUnitaryImport
    ∧ inputs.noStoneImport
    ∧ inputs.noGeneratorImport

def v7DynamicsRouteToFrequencySchrodingerStatus
    (inputs : V7DynamicsRouteInputs) :
    FrequencySchrodingerLogicStatus :=
  {
    phaseOrientation := inputs.phaseOrientation,
    normalizedTransitionReadout := inputs.normalizedTransitionReadout,
    reversibleDclAutomorphism := inputs.reversibleDclAutomorphism,
    overlapPreservingProjectiveAction :=
      inputs.overlapPreservation ∧ inputs.projectiveAction,
    continuousInheritanceFlow := inputs.continuousInheritanceFamily,
    closedFrequencyGenerator := inputs.generatorClosure,
    noTargetDynamicsImports :=
      inputs.noUnitaryImport
        ∧ inputs.noStoneImport
        ∧ inputs.noGeneratorImport
  }

theorem v7_dynamics_route_closes_frequency_schrodinger_logic
    (inputs : V7DynamicsRouteInputs) :
    V7DynamicsRouteClosed inputs →
      FrequencySchrodingerLogicClosed
        (v7DynamicsRouteToFrequencySchrodingerStatus inputs) := by
  intro closed
  rcases closed with
    ⟨automorphism, overlap, projective, continuity, generator,
      phase, transition, noUnitary, noStone, noGenerator⟩
  exact And.intro phase
    (And.intro transition
      (And.intro automorphism
        (And.intro
          (And.intro overlap projective)
          (And.intro continuity
            (And.intro generator
              (And.intro noUnitary
                (And.intro noStone noGenerator)))))))

theorem v7_dynamics_route_requires_continuity
    (inputs : V7DynamicsRouteInputs) :
    V7DynamicsRouteClosed inputs →
      inputs.continuousInheritanceFamily :=
  fun closed => closed.right.right.right.left

theorem v7_dynamics_route_requires_generator_closure
    (inputs : V7DynamicsRouteInputs) :
    V7DynamicsRouteClosed inputs →
      inputs.generatorClosure :=
  fun closed => closed.right.right.right.right.left

def v7FiniteUnitaryGatesOnlyDynamics : V7DynamicsRouteInputs :=
  {
    reversibleDclAutomorphism := True,
    overlapPreservation := True,
    projectiveAction := True,
    continuousInheritanceFamily := False,
    generatorClosure := False,
    phaseOrientation := True,
    normalizedTransitionReadout := True,
    noUnitaryImport := True,
    noStoneImport := True,
    noGeneratorImport := True
  }

theorem v7_finite_unitary_gates_only_do_not_close_dynamics_route :
    ¬ V7DynamicsRouteClosed v7FiniteUnitaryGatesOnlyDynamics := by
  intro closed
  exact closed.right.right.right.left

def v7ContinuityWithoutGeneratorDynamics : V7DynamicsRouteInputs :=
  {
    reversibleDclAutomorphism := True,
    overlapPreservation := True,
    projectiveAction := True,
    continuousInheritanceFamily := True,
    generatorClosure := False,
    phaseOrientation := True,
    normalizedTransitionReadout := True,
    noUnitaryImport := True,
    noStoneImport := True,
    noGeneratorImport := True
  }

theorem v7_continuity_without_generator_does_not_close_dynamics_route :
    ¬ V7DynamicsRouteClosed v7ContinuityWithoutGeneratorDynamics := by
  intro closed
  exact closed.right.right.right.right.left

end QMClosure
end IDT
