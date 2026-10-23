import Proofs.QMClosure.CoherentReferencePositivity

namespace IDT.QMClosure.DestructiveCompositionBoundary

open CoherentReference

/-!
# Destructive composition and the outer quartic countermodel

These are exact rational weight-calculus results, not detector probabilities
or a derivation of quantum mechanics. Pair kernels and tensor multiplication
are supplied for the first diagnostic, not derived from physical primitives.
The quartic family deliberately lives outside the pair-kernel ansatz.
-/

/-- A normalized, partially destructive companion; its off-diagonal is negative. -/
def partialDestructive : Kernel Bool := fun i j => if i = j then 1 else -1 / 2

theorem candidate_and_companion_normalized :
    eventWeight candidate Finset.univ = 1 ∧
      eventWeight partialDestructive Finset.univ = 1 := by
  constructor
  · exact both_local_kernels_normalized.1
  · norm_num [eventWeight, partialDestructive, Fintype.sum_bool]

theorem candidate_event_nonnegative (event : Finset Bool) :
    0 ≤ eventWeight candidate event :=
  entrywise_nonnegative_gives_event_positivity candidate candidate_entrywise_positive event

set_option maxRecDepth 4096 in
theorem companion_all_events_nonnegative :
    ∀ event : Finset Bool, 0 ≤ eventWeight partialDestructive event := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem one_companion_all_events_nonnegative :
    ∀ event : Finset (Bool × Bool),
      0 ≤ eventWeight (tensor candidate partialDestructive) event := by
  decide +kernel

/-- ((d,a),b), with d = a xor b. No rescaling of this event is performed. -/
def parityEvent : Finset ((Bool × Bool) × Bool) :=
  {((false, false), false), ((true, false), true),
    ((true, true), false), ((false, true), true)}

theorem two_companions_parity_weight_negative :
    eventWeight (tensor (tensor candidate partialDestructive) partialDestructive)
      parityEvent = -1 / 2 := by
  norm_num [eventWeight, tensor, candidate, partialDestructive, parityEvent]

theorem one_companion_test_does_not_suffice :
    (∀ event : Finset (Bool × Bool),
      0 ≤ eventWeight (tensor candidate partialDestructive) event) ∧
    ¬ (∀ event : Finset ((Bool × Bool) × Bool),
      0 ≤ eventWeight (tensor (tensor candidate partialDestructive) partialDestructive)
        event) := by
  refine ⟨one_companion_all_events_nonnegative, ?_⟩
  intro positive
  have h := positive parityEvent
  rw [two_companions_parity_weight_negative] at h
  norm_num at h

section Quartic

variable {α β γ : Type*}

def quarticWeight (a : α → ℚ) (event : Finset α) : ℚ :=
  (∑ i ∈ event, a i) ^ 4

theorem quartic_event_nonnegative (a : α → ℚ) (event : Finset α) :
    0 ≤ quarticWeight a event := by
  exact pow_nonneg (sq_nonneg (∑ i ∈ event, a i)) 2 |>.trans_eq (by
    simp [quarticWeight, ← pow_mul])

def tensorAmplitude (a : α → ℚ) (b : β → ℚ) : α × β → ℚ :=
  fun i => a i.1 * b i.2

theorem quartic_product_events (a : α → ℚ) (b : β → ℚ)
    (event : Finset α) (other : Finset β) :
    quarticWeight (tensorAmplitude a b) (event ×ˢ other) =
      quarticWeight a event * quarticWeight b other := by
  simp only [quarticWeight, tensorAmplitude, Finset.sum_product]
  rw [← Finset.sum_mul_sum, mul_pow]

variable [Fintype α] [Fintype β] [Fintype γ]

def AmplitudeNormalized (a : α → ℚ) : Prop := ∑ i, a i = 1

theorem quartic_normalized (a : α → ℚ) (h : AmplitudeNormalized a) :
    quarticWeight a Finset.univ = 1 := by
  change (∑ i, a i) ^ 4 = 1
  rw [h, one_pow]

theorem tensor_amplitude_normalized (a : α → ℚ) (b : β → ℚ)
    (ha : AmplitudeNormalized a) (hb : AmplitudeNormalized b) :
    AmplitudeNormalized (tensorAmplitude a b) := by
  simp only [AmplitudeNormalized, tensorAmplitude, Fintype.sum_prod_type]
  rw [← Finset.sum_mul_sum, ha, hb, one_mul]

variable [DecidableEq γ]

/-- Push amplitudes forward by summing fibers, without renormalization. -/
def coarseAmplitude (a : α → ℚ) (f : α → γ) : γ → ℚ :=
  fun j => ∑ i ∈ Finset.univ.filter (fun i => f i = j), a i

theorem coarse_amplitude_normalized (a : α → ℚ) (f : α → γ)
    (ha : AmplitudeNormalized a) : AmplitudeNormalized (coarseAmplitude a f) := by
  unfold AmplitudeNormalized coarseAmplitude
  rw [Finset.sum_fiberwise]
  exact ha

omit [Fintype γ] in
theorem quartic_coarse_event (a : α → ℚ) (f : α → γ) (event : Finset γ) :
    quarticWeight (coarseAmplitude a f) event =
      quarticWeight a (Finset.univ.filter (fun i => f i ∈ event)) := by
  unfold quarticWeight coarseAmplitude
  rw [Finset.sum_fiberwise_eq_sum_filter]

end Quartic

def quarticExample : Fin 5 → ℚ := ![1, 1, 1, -1, -1]

theorem quartic_example_normalized : AmplitudeNormalized quarticExample := by
  norm_num [AmplitudeNormalized, quarticExample, Fin.sum_univ_succ]

theorem quartic_example_cancellation : quarticWeight quarticExample {0, 3} = 0 := by
  decide +kernel

/-- The inclusion-exclusion I3 diagnostic on three pairwise disjoint singleton events. -/
def eventThirdOrder {α : Type*} [DecidableEq α] (weight : Finset α → ℚ)
    (a b c : Finset α) : ℚ :=
  weight (a ∪ b ∪ c) - weight (a ∪ b) - weight (a ∪ c) - weight (b ∪ c) +
    weight a + weight b + weight c

theorem quartic_example_third_order :
    eventThirdOrder (quarticWeight quarticExample) {0} {1} {2} = 36 := by
  decide +kernel

theorem quartic_example_disjoint_events :
    Disjoint ({0} : Finset (Fin 5)) {1} ∧
    Disjoint ({0} : Finset (Fin 5)) {2} ∧
    Disjoint ({1} : Finset (Fin 5)) {2} := by
  decide +kernel

/-!
## Machine-visible research ledger

Only the entries marked `compiledArtifact` name theorems proved above. The
paper-only entries record arguments awaiting formalization, not checked
universal theorems. None of the statuses is a manifest proof-status upgrade.
-/

inductive ResearchStatus where
  | compiledArtifact
  | paperOnlyPendingFormalization
  | openPhysicalBridge
  deriving DecidableEq, Repr

inductive ResearchItem where
  | oneDestructiveCompanionInsufficient
  | quarticNormalizedTensorAndCoarseClosure
  | quarticCancellationWithNonzeroThirdOrder
  | fixedSeedGeneratesIntegerReferenceCoefficients
  | hermitianRealSquareTestImpliesComplexPositivity
  | imperfectNegativeSeedParityLimit
  | pairArityAndThirdOrderOrigin
  | complexCarrier
  | reversibleDynamics
  | detectorOutcomeProbabilities
  deriving DecidableEq, Repr

def researchStatus : ResearchItem → ResearchStatus
  | .oneDestructiveCompanionInsufficient
  | .quarticNormalizedTensorAndCoarseClosure
  | .quarticCancellationWithNonzeroThirdOrder => .compiledArtifact
  | .fixedSeedGeneratesIntegerReferenceCoefficients
  | .hermitianRealSquareTestImpliesComplexPositivity
  | .imperfectNegativeSeedParityLimit => .paperOnlyPendingFormalization
  | .pairArityAndThirdOrderOrigin
  | .complexCarrier
  | .reversibleDynamics
  | .detectorOutcomeProbabilities => .openPhysicalBridge

inductive SuppliedAssumption where
  | pairKernelRepresentation
  | tensorMultiplication
  | unlimitedIndependentCopies
  | allCorrelatedEventsAdmitted
  | destructiveCompanionAvailable
  | hermitianRepresentation
  deriving DecidableEq, Repr

def compositionRouteAssumptions : List SuppliedAssumption :=
  [.pairKernelRepresentation, .tensorMultiplication,
    .unlimitedIndependentCopies, .allCorrelatedEventsAdmitted,
    .destructiveCompanionAvailable]

/-- Paper argument, NOT a checked theorem: the exact seed C = t tᵀ with
t=(1,1,-1) must be supplied as an available companion.
Its kth tensor power has (3^k+1)/2 positive and (3^k-1)/2 negative amplitudes.
Correlated events encode any integer vector v once 3^k ≥ 2 max |v| + 1;
under the supplied composition assumptions this would force real PSD. -/
def fixedSeedArgument : ResearchStatus := .paperOnlyPendingFormalization

/-- Paper argument, NOT a checked theorem: assuming a Hermitian representation
D=A+iB (not deriving the complex carrier) and
w=x⊗y-y⊗x, wᵀ(D⊗D)w is
2[(xᵀAx)(yᵀAy)-(xᵀAy)^2-(xᵀBy)^2].
Real quadratic positivity of D and D⊗D would imply complex PSD. -/
def hermitianSquareArgument : ResearchStatus := .paperOnlyPendingFormalization

def hermitianExtensionAssumptions : List SuppliedAssumption :=
  .hermitianRepresentation :: compositionRouteAssumptions

/-- A generic imperfect negative seed requires a parity-limit argument;
the finite two-copy calculation above does not prove that universal claim. -/
def imperfectSeedArgument : ResearchStatus := .paperOnlyPendingFormalization

end IDT.QMClosure.DestructiveCompositionBoundary
