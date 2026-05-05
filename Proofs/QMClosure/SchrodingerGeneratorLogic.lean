import Proofs.QMClosure.CGSCPackageClosure
import Proofs.QMClosure.PrimitiveBoundaryQMChain

namespace IDT
namespace QMClosure

/-!
Action-scale-free Schrodinger generator logic.

This file does not state the physical energy-form equation. It isolates the
frequency-generator logic:

  phase orientation
  + normalized transition readout
  + reversible D_cl dynamics
  + overlap-preserving projective action
  + continuous inheritance flow
  + closed frequency generator
  + no target dynamics import

The intended mathematical projection is the frequency form
`i d_t psi = Omega psi`. The physical energy/action scale is deliberately
outside this artifact.
-/

structure FrequencySchrodingerLogicStatus where
  phaseOrientation : Prop
  normalizedTransitionReadout : Prop
  reversibleDclAutomorphism : Prop
  overlapPreservingProjectiveAction : Prop
  continuousInheritanceFlow : Prop
  closedFrequencyGenerator : Prop
  noTargetDynamicsImports : Prop

def FrequencySchrodingerLogicClosed
    (status : FrequencySchrodingerLogicStatus) : Prop :=
  status.phaseOrientation
    ∧ status.normalizedTransitionReadout
    ∧ status.reversibleDclAutomorphism
    ∧ status.overlapPreservingProjectiveAction
    ∧ status.continuousInheritanceFlow
    ∧ status.closedFrequencyGenerator
    ∧ status.noTargetDynamicsImports

def frequencySchrodingerLogicFromPackageAndBoundary
    (pkg : CGSCPackageClosure)
    (boundary : PrimitiveBoundaryCandidate) :
    FrequencySchrodingerLogicStatus :=
  {
    phaseOrientation := boundary.phaseBundleJ,
    normalizedTransitionReadout := boundary.normalizedOverlapUniqueness,
    reversibleDclAutomorphism :=
      pkg.routeCoherence.dclAutomorphismDynamics.statement,
    overlapPreservingProjectiveAction :=
      pkg.routeCoherence.overlapPreservationDynamics.statement
        ∧ pkg.routeCoherence.projectiveAction.statement,
    continuousInheritanceFlow :=
      pkg.routeCoherence.continuousInheritanceFamily.statement,
    closedFrequencyGenerator :=
      pkg.routeCoherence.generatorClosure.statement,
    noTargetDynamicsImports :=
      boundary.noTargetImports
        ∧ pkg.routeCoherence.noUnitaryImport.statement
        ∧ pkg.routeCoherence.noStoneImport.statement
        ∧ pkg.routeCoherence.noGeneratorImport.statement
  }

theorem package_and_boundary_close_frequency_schrodinger_logic
    (pkg : CGSCPackageClosure)
    (boundary : PrimitiveBoundaryCandidate) :
    PrimitiveBoundarySuppliesFiniteChainInputs boundary →
      FrequencySchrodingerLogicClosed
        (frequencySchrodingerLogicFromPackageAndBoundary pkg boundary) := by
  intro boundaryInputs
  rcases boundaryInputs with
    ⟨_b1, noTarget, _additiveKernel, normalizedOverlap, phaseJ⟩
  exact ⟨
    phaseJ,
    normalizedOverlap,
    pkg.routeCoherence.dclAutomorphismDynamics.proof,
    ⟨
      pkg.routeCoherence.overlapPreservationDynamics.proof,
      pkg.routeCoherence.projectiveAction.proof
    ⟩,
    pkg.routeCoherence.continuousInheritanceFamily.proof,
    pkg.routeCoherence.generatorClosure.proof,
    ⟨
      noTarget,
      pkg.routeCoherence.noUnitaryImport.proof,
      pkg.routeCoherence.noStoneImport.proof,
      pkg.routeCoherence.noGeneratorImport.proof
    ⟩
  ⟩

theorem frequency_schrodinger_logic_requires_phase_orientation
    (status : FrequencySchrodingerLogicStatus) :
    FrequencySchrodingerLogicClosed status → status.phaseOrientation :=
  fun closed => closed.left

theorem frequency_schrodinger_logic_requires_normalized_transition_readout
    (status : FrequencySchrodingerLogicStatus) :
    FrequencySchrodingerLogicClosed status →
      status.normalizedTransitionReadout :=
  fun closed => closed.right.left

theorem frequency_schrodinger_logic_requires_reversible_dcl_automorphism
    (status : FrequencySchrodingerLogicStatus) :
    FrequencySchrodingerLogicClosed status →
      status.reversibleDclAutomorphism :=
  fun closed => closed.right.right.left

theorem frequency_schrodinger_logic_requires_overlap_projective_action
    (status : FrequencySchrodingerLogicStatus) :
    FrequencySchrodingerLogicClosed status →
      status.overlapPreservingProjectiveAction :=
  fun closed => closed.right.right.right.left

theorem frequency_schrodinger_logic_requires_continuous_flow
    (status : FrequencySchrodingerLogicStatus) :
    FrequencySchrodingerLogicClosed status →
      status.continuousInheritanceFlow :=
  fun closed => closed.right.right.right.right.left

theorem frequency_schrodinger_logic_requires_closed_generator
    (status : FrequencySchrodingerLogicStatus) :
    FrequencySchrodingerLogicClosed status →
      status.closedFrequencyGenerator :=
  fun closed => closed.right.right.right.right.right.left

theorem frequency_schrodinger_logic_requires_no_target_dynamics_imports
    (status : FrequencySchrodingerLogicStatus) :
    FrequencySchrodingerLogicClosed status →
      status.noTargetDynamicsImports :=
  fun closed => closed.right.right.right.right.right.right

theorem missing_phase_orientation_blocks_frequency_schrodinger_logic
    (status : FrequencySchrodingerLogicStatus) :
    ¬ status.phaseOrientation → ¬ FrequencySchrodingerLogicClosed status :=
  fun missing closed =>
    missing (frequency_schrodinger_logic_requires_phase_orientation status closed)

theorem missing_normalized_transition_readout_blocks_frequency_schrodinger_logic
    (status : FrequencySchrodingerLogicStatus) :
    ¬ status.normalizedTransitionReadout →
      ¬ FrequencySchrodingerLogicClosed status :=
  fun missing closed =>
    missing
      (frequency_schrodinger_logic_requires_normalized_transition_readout
        status
        closed)

theorem missing_continuous_flow_blocks_frequency_schrodinger_logic
    (status : FrequencySchrodingerLogicStatus) :
    ¬ status.continuousInheritanceFlow →
      ¬ FrequencySchrodingerLogicClosed status :=
  fun missing closed =>
    missing (frequency_schrodinger_logic_requires_continuous_flow status closed)

theorem missing_closed_generator_blocks_frequency_schrodinger_logic
    (status : FrequencySchrodingerLogicStatus) :
    ¬ status.closedFrequencyGenerator →
      ¬ FrequencySchrodingerLogicClosed status :=
  fun missing closed =>
    missing
      (frequency_schrodinger_logic_requires_closed_generator status closed)

end QMClosure
end IDT
