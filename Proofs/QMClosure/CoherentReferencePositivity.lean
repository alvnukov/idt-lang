import Mathlib.Tactic

namespace IDT.QMClosure.CoherentReference

/-!
# Event positivity, self-composition and coherent reference tests

We work with finite real-rational pair kernels. Event weights sum the kernel
over pairs of histories in an event. These are interference weights, not an
additive probability distribution over mutually exclusive detector outcomes.

A symmetric two-history kernel with diagonal 1/6 and off-diagonal 1/3 has total
weight 1 and positive entries. Every finite tensor power therefore has
nonnegative event weights. Its quadratic extension has zero third-order term,
but is negative on the signed coefficient vector (1,-2).

The rank-one reference built from (1,-2) has nonnegative event weights (squares
of sums) and total weight 1. Composing the two normalized kernels gives weight
-1/2 on the diagonal event. Thus positivity under arbitrarily many self-copies
does not imply compatibility with independently admitted coherent references.

For arbitrary finite carriers we prove a precise conditional equivalence:
nonnegative quadratic form on every rational vector iff every diagonal event
after tensoring with a real rank-one reference has nonnegative weight. The
general reference tests are unnormalized; the concrete rejection above uses
normalized kernels. This is not a classification of all normalized quantum
systems. For symmetric kernels the condition is rational positive
semidefiniteness; complex phases and the Hilbert carrier are not derived.

Inputs: the pair-kernel representation, tensor multiplication on independent
history indices, summation over events, and availability of every signed
rank-one reference. Those references already have square weights. Their
availability remains a lower-primitive obligation, not a derived Born rule.

Source scope: Dowker-Wilkes, arXiv:2011.06120v2, Theorem 2 establishes Galois
self-duality of strongly positive systems; Theorem 3 assumes BOTH tensor
closure and Galois self-duality for uniqueness. Mere tensor closure is weaker.
Our finite rational calculation is proved independently below and does not
formalize that external theorem about general complex/infinite systems.
-/

variable {α β : Type*}

abbrev Kernel (α : Type*) := α → α → ℚ

def eventWeight (K : Kernel α) (event : Finset α) : ℚ :=
  ∑ i ∈ event, ∑ j ∈ event, K i j

def EntrywiseNonnegative (K : Kernel α) : Prop := ∀ i j, 0 ≤ K i j

theorem entrywise_nonnegative_gives_event_positivity (K : Kernel α)
    (positive : EntrywiseNonnegative K) (event : Finset α) :
    0 ≤ eventWeight K event := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => positive i j))

def tensor (K : Kernel α) (R : Kernel β) : Kernel (α × β) :=
  fun i j => K i.1 j.1 * R i.2 j.2

theorem entrywise_nonnegative_closed_under_tensor (K : Kernel α) (R : Kernel β)
    (hK : EntrywiseNonnegative K) (hR : EntrywiseNonnegative R) :
    EntrywiseNonnegative (tensor K R) := by
  intro i j
  exact mul_nonneg (hK _ _) (hR _ _)

def tensorPower (K : Kernel α) (copies : ℕ) : Kernel (Fin copies → α) :=
  fun i j => ∏ k : Fin copies, K (i k) (j k)

theorem all_self_copies_have_nonnegative_events (K : Kernel α)
    (positive : EntrywiseNonnegative K) (copies : ℕ)
    (event : Finset (Fin copies → α)) :
    0 ≤ eventWeight (tensorPower K copies) event := by
  apply entrywise_nonnegative_gives_event_positivity
  intro i j
  exact Finset.prod_nonneg (fun k _ => positive (i k) (j k))

def reference (v : α → ℚ) : Kernel α := fun i j => v i * v j

theorem reference_event_is_square (v : α → ℚ) (event : Finset α) :
    eventWeight (reference v) event = (∑ i ∈ event, v i) ^ 2 := by
  unfold eventWeight reference
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  ring

theorem reference_event_nonnegative (v : α → ℚ) (event : Finset α) :
    0 ≤ eventWeight (reference v) event := by
  rw [reference_event_is_square]
  exact sq_nonneg _

section Finite
variable [Fintype α]

def quadratic (K : Kernel α) (v : α → ℚ) : ℚ :=
  ∑ i, ∑ j, v i * K i j * v j

def QuadraticNonnegative (K : Kernel α) : Prop := ∀ v, 0 ≤ quadratic K v

def diagonalEvent : Finset (α × α) :=
  Finset.univ.map ⟨fun i => (i, i), fun _ _ h => congrArg Prod.fst h⟩

theorem reference_diagonal_equals_quadratic (K : Kernel α) (v : α → ℚ) :
    eventWeight (tensor K (reference v)) diagonalEvent = quadratic K v := by
  simp [eventWeight, diagonalEvent, tensor, reference, quadratic]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem coherent_reference_tests_iff_quadratic_nonnegative (K : Kernel α) :
    (∀ v : α → ℚ, 0 ≤ eventWeight (tensor K (reference v)) diagonalEvent) ↔
      QuadraticNonnegative K := by
  simp only [reference_diagonal_equals_quadratic, QuadraticNonnegative]

theorem negative_direction_yields_negative_composite_event
    (K : Kernel α) (v : α → ℚ) (negative : quadratic K v < 0) :
    eventWeight (tensor K (reference v)) diagonalEvent < 0 := by
  rwa [reference_diagonal_equals_quadratic]

/-- No division or setting-dependent normalization enters this diagnostic. -/
def thirdOrder (K : Kernel α) (u v w : α → ℚ) : ℚ :=
  quadratic K (u + v + w) - quadratic K (u + v) - quadratic K (u + w) -
    quadratic K (v + w) + quadratic K u + quadratic K v + quadratic K w

theorem pair_kernel_third_order_vanishes (K : Kernel α) (u v w : α → ℚ) :
    thirdOrder K u v w = 0 := by
  simp only [thirdOrder, quadratic, Pi.add_apply, add_mul, mul_add,
    Finset.sum_add_distrib]
  ring

end Finite

def candidate : Kernel Bool := fun i j => if i = j then 1 / 6 else 1 / 3

def signedReference : Bool → ℚ := fun i => if i then -2 else 1

theorem candidate_symmetric : ∀ i j, candidate i j = candidate j i := by
  intro i j
  cases i <;> cases j <;> rfl

theorem candidate_entrywise_positive : EntrywiseNonnegative candidate := by
  intro i j
  cases i <;> cases j <;> norm_num [candidate]

theorem candidate_all_self_copies_pass (copies : ℕ)
    (event : Finset (Fin copies → Bool)) :
    0 ≤ eventWeight (tensorPower candidate copies) event :=
  all_self_copies_have_nonnegative_events candidate candidate_entrywise_positive copies event

theorem both_local_kernels_normalized :
    eventWeight candidate Finset.univ = 1 ∧
      eventWeight (reference signedReference) Finset.univ = 1 := by
  norm_num [eventWeight, candidate, reference, signedReference, Fintype.sum_bool]

theorem candidate_has_a_negative_signed_direction :
    quadratic candidate signedReference = -1 / 2 := by
  norm_num [quadratic, candidate, signedReference, Fintype.sum_bool]

theorem composite_has_negative_diagonal_event :
    eventWeight (tensor candidate (reference signedReference)) diagonalEvent = -1 / 2 := by
  rw [reference_diagonal_equals_quadratic]
  exact candidate_has_a_negative_signed_direction

theorem candidate_not_quadratic_nonnegative : ¬ QuadraticNonnegative candidate := by
  intro positive
  have h := positive signedReference
  rw [candidate_has_a_negative_signed_direction] at h
  norm_num at h

/-- A counterexample to selecting strong positivity by self-composition alone. -/
theorem self_copy_positivity_does_not_force_quadratic_positivity :
    ¬ (∀ K : Kernel Bool,
      (∀ copies (event : Finset (Fin copies → Bool)),
        0 ≤ eventWeight (tensorPower K copies) event) → QuadraticNonnegative K) := by
  intro forces
  exact candidate_not_quadratic_nonnegative (forces candidate candidate_all_self_copies_pass)

inductive OpenObligation where
  | derivePairKernelAndItsPhysicalEventSemantics
  | deriveIndependentTensorComposition
  | deriveAvailabilityOfSignedCoherentReferences
  | extendReferenceTestToNormalizedGeneralSystemsWithPadding
  | distinguishTensorClosureFromGaloisSelfDuality
  | reconstructComplexCarrierAndDetectorStatistics
  deriving DecidableEq, Repr

def openObligations : List OpenObligation :=
  [ .derivePairKernelAndItsPhysicalEventSemantics,
    .deriveIndependentTensorComposition,
    .deriveAvailabilityOfSignedCoherentReferences,
    .extendReferenceTestToNormalizedGeneralSystemsWithPadding,
    .distinguishTensorClosureFromGaloisSelfDuality,
    .reconstructComplexCarrierAndDetectorStatistics ]

end IDT.QMClosure.CoherentReference
