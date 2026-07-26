import Mathlib

namespace IDT.QMClosure

/-!
# Oriented relational-process countermodel

This probe strengthens the bare typed-rewrite test.  It grants the candidate
the algebraic structure expected from oriented boundaries:

* identity and associative sequential composition;
* orientation reversal as an involutive dagger;
* parallel composition on product boundaries, with interchange;
* states, effects, and discard as processes from/to the empty boundary `Unit`.

Finite relations realize all of this structure, but their scalars have only two
extensional values.  Moreover, without a law coupling process scalars to
operational probabilities, the same process skeleton can be paired with the
normalized no-signalling PR readout and reaches CHSH four.

Thus oriented process structure is a plausible substrate ingredient, but is not
a sufficient primitive base.  The probe does not test an enriched causal OPT
that also derives a positive monoidal scalar/readout map and universal
reversible purification.
-/

def processProbeBitXor (left right : Bool) : Bool :=
  if left then !right else right

def processProbeParity (aliceSetting bobSetting : Bool) : Bool :=
  aliceSetting && bobSetting

def processProbeOutcomeSign (outcome : Bool) : ℚ :=
  if outcome then -1 else 1

structure ProcessProbeNoSignallingBox where
  weight : Bool → Bool → Bool → Bool → ℚ
  weightNonnegative : ∀ x y a b, 0 ≤ weight x y a b
  normalized : ∀ x y,
    weight x y false false + weight x y false true +
      weight x y true false + weight x y true true = 1
  aliceMarginalIndependent : ∀ x a y₀ y₁,
    weight x y₀ a false + weight x y₀ a true =
      weight x y₁ a false + weight x y₁ a true
  bobMarginalIndependent : ∀ y b x₀ x₁,
    weight x₀ y false b + weight x₀ y true b =
      weight x₁ y false b + weight x₁ y true b

def ProcessProbeNoSignallingBox.correlation
    (box : ProcessProbeNoSignallingBox) (x y : Bool) : ℚ :=
  box.weight x y false false * processProbeOutcomeSign false *
      processProbeOutcomeSign false +
    box.weight x y false true * processProbeOutcomeSign false *
      processProbeOutcomeSign true +
    box.weight x y true false * processProbeOutcomeSign true *
      processProbeOutcomeSign false +
    box.weight x y true true * processProbeOutcomeSign true *
      processProbeOutcomeSign true

def ProcessProbeNoSignallingBox.chsh
    (box : ProcessProbeNoSignallingBox) : ℚ :=
  box.correlation false false + box.correlation false true +
    box.correlation true false - box.correlation true true

def processProbePrWeight (x y a b : Bool) : ℚ :=
  if processProbeBitXor a b = processProbeParity x y then 1 / 2 else 0

theorem process_probe_pr_weight_nonnegative (x y a b : Bool) :
    0 ≤ processProbePrWeight x y a b := by
  cases x <;> cases y <;> cases a <;> cases b <;>
    norm_num [processProbePrWeight, processProbeBitXor, processProbeParity]

theorem process_probe_pr_normalized (x y : Bool) :
    processProbePrWeight x y false false +
      processProbePrWeight x y false true +
      processProbePrWeight x y true false +
      processProbePrWeight x y true true = 1 := by
  cases x <;> cases y <;>
    norm_num [processProbePrWeight, processProbeBitXor, processProbeParity]

theorem process_probe_pr_alice_uniform (x y a : Bool) :
    processProbePrWeight x y a false + processProbePrWeight x y a true =
      1 / 2 := by
  cases x <;> cases y <;> cases a <;>
    norm_num [processProbePrWeight, processProbeBitXor, processProbeParity]

theorem process_probe_pr_bob_uniform (x y b : Bool) :
    processProbePrWeight x y false b + processProbePrWeight x y true b =
      1 / 2 := by
  cases x <;> cases y <;> cases b <;>
    norm_num [processProbePrWeight, processProbeBitXor, processProbeParity]

def processProbePrBox : ProcessProbeNoSignallingBox where
  weight := processProbePrWeight
  weightNonnegative := process_probe_pr_weight_nonnegative
  normalized := process_probe_pr_normalized
  aliceMarginalIndependent := by
    intro x a y₀ y₁
    rw [process_probe_pr_alice_uniform, process_probe_pr_alice_uniform]
  bobMarginalIndependent := by
    intro y b x₀ x₁
    rw [process_probe_pr_bob_uniform, process_probe_pr_bob_uniform]

theorem process_probe_pr_correlation (x y : Bool) :
    processProbePrBox.correlation x y =
      if processProbeParity x y then -1 else 1 := by
  cases x <;> cases y <;>
    norm_num [ProcessProbeNoSignallingBox.correlation, processProbePrBox,
      processProbePrWeight, processProbeBitXor, processProbeParity,
      processProbeOutcomeSign]

theorem process_probe_pr_chsh_four :
    processProbePrBox.chsh = 4 := by
  norm_num [ProcessProbeNoSignallingBox.chsh, process_probe_pr_correlation,
    processProbeParity]

structure OrientedProcessTheory where
  Process : Type → Type → Type
  identity : ∀ {A : Type}, Process A A
  sequential : ∀ {A B C : Type}, Process A B → Process B C → Process A C
  dagger : ∀ {A B : Type}, Process A B → Process B A
  parallel : ∀ {A B C D : Type},
    Process A B → Process C D → Process (A × C) (B × D)
  discard : ∀ {A : Type}, Process A Unit
  sequentialAssociative : ∀ {A B C D : Type}
    (first : Process A B) (second : Process B C) (third : Process C D),
      sequential (sequential first second) third =
        sequential first (sequential second third)
  sequentialLeftIdentity : ∀ {A B : Type} (process : Process A B),
    sequential identity process = process
  sequentialRightIdentity : ∀ {A B : Type} (process : Process A B),
    sequential process identity = process
  daggerInvolutive : ∀ {A B : Type} (process : Process A B),
    dagger (dagger process) = process
  daggerSequential : ∀ {A B C : Type}
    (first : Process A B) (second : Process B C),
      dagger (sequential first second) =
        sequential (dagger second) (dagger first)
  parallelSequentialInterchange : ∀ {A B C D E F : Type}
    (firstLeft : Process A B) (secondLeft : Process B C)
    (firstRight : Process D E) (secondRight : Process E F),
      sequential
          (parallel firstLeft firstRight)
          (parallel secondLeft secondRight) =
        parallel
          (sequential firstLeft secondLeft)
          (sequential firstRight secondRight)

def OrientedProcessTheory.State
    (theory : OrientedProcessTheory) (A : Type) : Type :=
  theory.Process Unit A

def OrientedProcessTheory.Effect
    (theory : OrientedProcessTheory) (A : Type) : Type :=
  theory.Process A Unit

def OrientedProcessTheory.Scalar
    (theory : OrientedProcessTheory) : Type :=
  theory.Process Unit Unit

def RelProcess (A B : Type) : Type := A → B → Prop

def relIdentity {A : Type} : RelProcess A A :=
  fun source target => source = target

def relSequential {A B C : Type}
    (first : RelProcess A B) (second : RelProcess B C) : RelProcess A C :=
  fun source target => ∃ middle, first source middle ∧ second middle target

def relDagger {A B : Type} (process : RelProcess A B) : RelProcess B A :=
  fun target source => process source target

def relParallel {A B C D : Type}
    (left : RelProcess A B) (right : RelProcess C D) :
    RelProcess (A × C) (B × D) :=
  fun source target => left source.1 target.1 ∧ right source.2 target.2

def relDiscard {A : Type} : RelProcess A Unit :=
  fun _ _ => True

theorem rel_sequential_associative {A B C D : Type}
    (first : RelProcess A B) (second : RelProcess B C)
    (third : RelProcess C D) :
    relSequential (relSequential first second) third =
      relSequential first (relSequential second third) := by
  funext source target
  apply propext
  constructor
  · rintro ⟨middleRight, ⟨middleLeft, firstStep, secondStep⟩, thirdStep⟩
    exact ⟨middleLeft, firstStep, middleRight, secondStep, thirdStep⟩
  · rintro ⟨middleLeft, firstStep, middleRight, secondStep, thirdStep⟩
    exact ⟨middleRight, ⟨middleLeft, firstStep, secondStep⟩, thirdStep⟩

theorem rel_sequential_left_identity {A B : Type}
    (process : RelProcess A B) :
    relSequential relIdentity process = process := by
  funext source target
  apply propext
  constructor
  · rintro ⟨middle, sourceEqualsMiddle, step⟩
    subst middle
    exact step
  · intro step
    exact ⟨source, rfl, step⟩

theorem rel_sequential_right_identity {A B : Type}
    (process : RelProcess A B) :
    relSequential process relIdentity = process := by
  funext source target
  apply propext
  constructor
  · rintro ⟨middle, step, middleEqualsTarget⟩
    subst target
    exact step
  · intro step
    exact ⟨target, step, rfl⟩

theorem rel_dagger_involutive {A B : Type}
    (process : RelProcess A B) :
    relDagger (relDagger process) = process := by
  rfl

theorem rel_dagger_sequential {A B C : Type}
    (first : RelProcess A B) (second : RelProcess B C) :
    relDagger (relSequential first second) =
      relSequential (relDagger second) (relDagger first) := by
  funext target source
  apply propext
  constructor
  · rintro ⟨middle, firstStep, secondStep⟩
    exact ⟨middle, secondStep, firstStep⟩
  · rintro ⟨middle, secondStep, firstStep⟩
    exact ⟨middle, firstStep, secondStep⟩

theorem rel_parallel_sequential_interchange {A B C D E F : Type}
    (firstLeft : RelProcess A B) (secondLeft : RelProcess B C)
    (firstRight : RelProcess D E) (secondRight : RelProcess E F) :
    relSequential
        (relParallel firstLeft firstRight)
        (relParallel secondLeft secondRight) =
      relParallel
        (relSequential firstLeft secondLeft)
        (relSequential firstRight secondRight) := by
  funext source target
  apply propext
  constructor
  · rintro ⟨middle, ⟨firstLeftStep, firstRightStep⟩,
      secondLeftStep, secondRightStep⟩
    exact ⟨⟨middle.1, firstLeftStep, secondLeftStep⟩,
      middle.2, firstRightStep, secondRightStep⟩
  · rintro ⟨⟨middleLeft, firstLeftStep, secondLeftStep⟩,
      middleRight, firstRightStep, secondRightStep⟩
    exact ⟨(middleLeft, middleRight),
      ⟨firstLeftStep, firstRightStep⟩,
      secondLeftStep, secondRightStep⟩

def relationalOrientedProcessTheory : OrientedProcessTheory where
  Process := RelProcess
  identity := relIdentity
  sequential := relSequential
  dagger := relDagger
  parallel := relParallel
  discard := relDiscard
  sequentialAssociative := rel_sequential_associative
  sequentialLeftIdentity := rel_sequential_left_identity
  sequentialRightIdentity := rel_sequential_right_identity
  daggerInvolutive := rel_dagger_involutive
  daggerSequential := rel_dagger_sequential
  parallelSequentialInterchange := rel_parallel_sequential_interchange

def emptyRelScalar : RelProcess Unit Unit :=
  fun _ _ => False

def inhabitedRelScalar : RelProcess Unit Unit :=
  fun _ _ => True

theorem every_relational_scalar_is_empty_or_inhabited
    (scalar : RelProcess Unit Unit) :
    scalar = emptyRelScalar ∨ scalar = inhabitedRelScalar := by
  classical
  by_cases supported : scalar () ()
  · right
    funext source target
    cases source
    cases target
    apply propext
    simp [inhabitedRelScalar, supported]
  · left
    funext source target
    cases source
    cases target
    apply propext
    simp [emptyRelScalar, supported]

theorem relational_process_scalars_have_no_three_distinct_values :
    ¬ ∃ zero half one : RelProcess Unit Unit,
      zero ≠ half ∧ zero ≠ one ∧ half ≠ one := by
  rintro ⟨zero, half, one, zeroNeHalf, zeroNeOne, halfNeOne⟩
  rcases every_relational_scalar_is_empty_or_inhabited zero with
      rfl | rfl <;>
    rcases every_relational_scalar_is_empty_or_inhabited half with
      rfl | rfl <;>
    rcases every_relational_scalar_is_empty_or_inhabited one with
      rfl | rfl <;>
    simp_all

structure OrientedProcessReadoutModel extends OrientedProcessTheory where
  readout : ProcessProbeNoSignallingBox

def relationalPrReadoutModel : OrientedProcessReadoutModel where
  toOrientedProcessTheory := relationalOrientedProcessTheory
  readout := processProbePrBox

def ProcessProbeNoSignallingBox.PassesSquaredTsirelsonScreen
    (box : ProcessProbeNoSignallingBox) : Prop :=
  box.chsh * box.chsh ≤ 8

theorem relational_pr_readout_reaches_chsh_four :
    relationalPrReadoutModel.readout.chsh = 4 := by
  exact process_probe_pr_chsh_four

theorem relational_pr_readout_fails_squared_tsirelson_screen :
    ¬ relationalPrReadoutModel.readout.PassesSquaredTsirelsonScreen := by
  rw [ProcessProbeNoSignallingBox.PassesSquaredTsirelsonScreen,
    relational_pr_readout_reaches_chsh_four]
  norm_num

theorem oriented_process_structure_plus_no_signalling_does_not_force_tsirelson :
    ¬ ∀ model : OrientedProcessReadoutModel,
      model.readout.PassesSquaredTsirelsonScreen := by
  intro forced
  exact relational_pr_readout_fails_squared_tsirelson_screen
    (forced relationalPrReadoutModel)

inductive OrientedRelationalProcessFinding where
  | associativeSequentialCompositionExists
  | involutiveDaggerExists
  | parallelInterchangeExists
  | statesEffectsAndDiscardExist
  | relationalScalarsHaveOnlyTwoValues
  | normalizedNoSignallingPrReadoutCanBeAttached
  | squaredTsirelsonScreenFails
  | orientedProcessSkeletonIsInsufficient
deriving DecidableEq, Repr

def orientedRelationalProcessFindings :
    List OrientedRelationalProcessFinding :=
  [ .associativeSequentialCompositionExists,
    .involutiveDaggerExists,
    .parallelInterchangeExists,
    .statesEffectsAndDiscardExist,
    .relationalScalarsHaveOnlyTwoValues,
    .normalizedNoSignallingPrReadoutCanBeAttached,
    .squaredTsirelsonScreenFails,
    .orientedProcessSkeletonIsInsufficient ]

theorem oriented_relational_process_probe_records_eight_findings :
    orientedRelationalProcessFindings.length = 8 := by
  rfl

inductive OrientedRelationalProcessOpenObligation where
  | deriveOrderedProbabilityScalarsFromLowerPrimitives
  | derivePositiveReadoutCompatibleWithSequentialAndParallelComposition
  | derivePurificationThatExcludesRelationalAndPrModels
  | deriveTsirelsonBoundaryWithoutHilbertImport
  | deriveComplexCarrierWithoutAssumingQuantumTheory
deriving DecidableEq, Repr

def orientedRelationalProcessOpenObligations :
    List OrientedRelationalProcessOpenObligation :=
  [ .deriveOrderedProbabilityScalarsFromLowerPrimitives,
    .derivePositiveReadoutCompatibleWithSequentialAndParallelComposition,
    .derivePurificationThatExcludesRelationalAndPrModels,
    .deriveTsirelsonBoundaryWithoutHilbertImport,
    .deriveComplexCarrierWithoutAssumingQuantumTheory ]

theorem oriented_relational_process_probe_keeps_five_open_obligations :
    orientedRelationalProcessOpenObligations.length = 5 := by
  rfl

def orientedRelationalProcessProbeStatus : String :=
  "oriented_dagger_tensor_discard_skeleton_rejected_as_sufficient_lower_base"

def orientedRelationalProcessProbeClaimBoundary : String :=
  "A relational process theory has associative composition, involutive dagger, parallel interchange, states, effects, and discard, yet its scalars have only two extensional values. Without a derived scalar/readout compatibility law it can be paired with a normalized no-signalling PR box whose CHSH value is four. This rejects the oriented process skeleton as a sufficient primitive base; it does not reject an enriched causal operational theory with derived positive scalars and universal reversible purification, and it proves neither the Standard Model nor gravity."

end IDT.QMClosure
