import Proofs.QMClosure.CanonicalQuadraticHilbert
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace IDT.QMClosure.QuadraticReadoutEffects

open QuadraticRecordRefinement PositiveQuadraticPolarization
open QuadraticHermitianKernel CanonicalQuadraticHilbert
open scoped BigOperators ComplexOrder

noncomputable section

/-!
Conditional mathematical effects from positive quadratic branch readouts.
The carrier has only an additive commutative group structure. The common
quarter-turn and the branch readouts are supplied; all complex scalars,
continuity, and completion belong to the constructed output spaces.
No physical instrument, actualization, projectivity, state update, or full-QM
claim is established by this construction.
-/

variable {V : Type*} [AddCommGroup V] {Q : V → ℝ}

/-- A positive quadratic branch dominated by the total, with the SAME phase. -/
structure Branch (phase : QuadraticPhase Q) where
  q : V → ℝ
  positive : PositiveQuadratic q
  invariant : ∀ x, q (phase.J x) = q x
  dominated : ∀ x, q x ≤ Q x

variable (h : PositiveQuadratic Q) {phase : QuadraticPhase Q}

def Branch.branchPhase (b : Branch phase) : QuadraticPhase b.q where
  J := phase.J
  square := phase.square
  preserves := b.invariant

def Branch.residual (b : Branch phase) : V → ℝ := fun x => Q x - b.q x

include h in
theorem Branch.residual_positive (b : Branch phase) : PositiveQuadratic b.residual where
  nonnegative x := sub_nonneg.mpr (b.dominated x)
  parallelogram x y := by
    have ht := h.parallelogram x y
    have hb := b.positive.parallelogram x y
    dsimp [Branch.residual]
    linarith

def Branch.residualPhase (b : Branch phase) : QuadraticPhase b.residual where
  J := phase.J
  square := phase.square
  preserves x := by simp [Branch.residual, phase.preserves, b.invariant]

theorem Branch.kernel_decomposition (b : Branch phase) (x y : V) :
    kernel phase x y = kernel b.branchPhase x y + kernel b.residualPhase x y := by
  dsimp [kernel, polarization, Branch.branchPhase, Branch.residualPhase, Branch.residual]
  push_cast
  ring

/-- Finite complex coefficient synthesis; no carrier scalar multiplication. -/
def synthesis (phase : QuadraticPhase Q) : (V →₀ ℂ) →ₗ[ℂ] Hilbert h phase :=
  Finsupp.linearCombination ℂ (feature h phase)

theorem synthesis_single (phase : QuadraticPhase Q) (x : V) :
    synthesis h phase (Finsupp.single x 1) = feature h phase x := by
  simp [synthesis]

theorem denseRange_synthesis (phase : QuadraticPhase Q) : DenseRange (synthesis h phase) := by
  change Dense (LinearMap.range (synthesis h phase) : Set (Hilbert h phase))
  rw [synthesis, Finsupp.range_linearCombination]
  exact dense_span_feature h phase

theorem inner_synthesis (phase : QuadraticPhase Q) (a b : V →₀ ℂ) :
    inner ℂ (synthesis h phase a) (synthesis h phase b) =
      a.sum (fun x c => b.sum (fun y d => star c * kernel phase x y * d)) := by
  classical
  simp [synthesis, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner,
    inner_sum, inner_smul_left, inner_smul_right, inner_feature, mul_comm,
    mul_left_comm, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The full coefficient inequality follows from a positive residual kernel.
A bound only on individual feature vectors would not suffice. -/
theorem Branch.synthesis_norm_sq (b : Branch phase) (a : V →₀ ℂ) :
    ‖synthesis h phase a‖ ^ 2 =
      ‖synthesis b.positive b.branchPhase a‖ ^ 2 +
      ‖synthesis (b.residual_positive h) b.residualPhase a‖ ^ 2 := by
  have hi : inner ℂ (synthesis h phase a) (synthesis h phase a) =
      inner ℂ (synthesis b.positive b.branchPhase a) (synthesis b.positive b.branchPhase a) +
      inner ℂ (synthesis (b.residual_positive h) b.residualPhase a)
        (synthesis (b.residual_positive h) b.residualPhase a) := by
    simp only [inner_synthesis, b.kernel_decomposition, mul_add, add_mul,
      Finsupp.sum_add]
  simp only [norm_sq_eq_re_inner (𝕜 := ℂ), hi, map_add]

theorem Branch.synthesis_norm_le (b : Branch phase) (a : V →₀ ℂ) :
    ‖synthesis b.positive b.branchPhase a‖ ≤ ‖synthesis h phase a‖ := by
  have he := b.synthesis_norm_sq h a
  nlinarith [sq_nonneg ‖synthesis (b.residual_positive h) b.residualPhase a‖,
    norm_nonneg (synthesis b.positive b.branchPhase a), norm_nonneg (synthesis h phase a)]

/-- The canonical contraction, defined on the entire completed output. -/
def Branch.contraction (b : Branch phase) : Hilbert h phase →L[ℂ] Hilbert b.positive b.branchPhase :=
  (synthesis b.positive b.branchPhase).extendOfNorm (synthesis h phase)

theorem Branch.contraction_synthesis (b : Branch phase) (a : V →₀ ℂ) :
    b.contraction h (synthesis h phase a) = synthesis b.positive b.branchPhase a := by
  apply LinearMap.extendOfNorm_eq (denseRange_synthesis h phase)
  exact ⟨1, fun a => by simpa using b.synthesis_norm_le h a⟩

theorem Branch.contraction_feature (b : Branch phase) (x : V) :
    b.contraction h (feature h phase x) = feature b.positive b.branchPhase x := by
  simpa only [synthesis_single] using b.contraction_synthesis h (Finsupp.single x 1)

theorem Branch.contraction_norm_le (b : Branch phase) : ‖b.contraction h‖ ≤ 1 := by
  apply LinearMap.opNorm_extendOfNorm_le (denseRange_synthesis h phase) (by norm_num)
  intro a
  simpa using b.synthesis_norm_le h a

theorem Branch.contraction_unique (b : Branch phase)
    (T : Hilbert h phase →L[ℂ] Hilbert b.positive b.branchPhase)
    (on_feature : ∀ x, T (feature h phase x) = feature b.positive b.branchPhase x) :
    T = b.contraction h := by
  apply ContinuousLinearMap.ext_on (dense_span_feature h phase)
  rintro _ ⟨x, rfl⟩
  rw [on_feature, b.contraction_feature]

/-- A branch effect on the total canonical Hilbert space. -/
def Branch.effect (b : Branch phase) : Hilbert h phase →L[ℂ] Hilbert h phase :=
  (b.contraction h).adjoint.comp (b.contraction h)

theorem Branch.effect_kernel (b : Branch phase) (x y : V) :
    inner ℂ (feature h phase x) (b.effect h (feature h phase y)) =
      kernel b.branchPhase x y := by
  change inner ℂ _ ((b.contraction h).adjoint (b.contraction h _)) = _
  rw [ContinuousLinearMap.adjoint_inner_right, b.contraction_feature,
    b.contraction_feature, inner_feature]

theorem Branch.effect_diagonal (b : Branch phase) (x : V) :
    inner ℂ (feature h phase x) (b.effect h (feature h phase x)) = (b.q x : ℂ) := by
  rw [b.effect_kernel, QuadraticHermitianKernel.diagonal b.positive b.branchPhase]

theorem Branch.effect_positive (b : Branch phase) : (b.effect h).IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self (b.contraction h)

theorem Branch.effect_norm_le (b : Branch phase) : ‖b.effect h‖ ≤ 1 := by
  rw [Branch.effect, ContinuousLinearMap.norm_adjoint_comp_self]
  have hn := b.contraction_norm_le h
  nlinarith [norm_nonneg (b.contraction h)]

/-- Matrix elements on the generating features determine a bounded operator.
This uses the dense complex span twice, not a density assertion about diagonals. -/
theorem operator_ext (phase : QuadraticPhase Q)
    {T U : Hilbert h phase →L[ℂ] Hilbert h phase}
    (matrix_elements : ∀ x y, inner ℂ (feature h phase x) (T (feature h phase y)) =
      inner ℂ (feature h phase x) (U (feature h phase y))) : T = U := by
  apply ContinuousLinearMap.ext_on (dense_span_feature h phase)
  rintro _ ⟨y, rfl⟩
  apply (denseRange_synthesis h phase).eq_of_inner_right ℂ
  intro a
  classical
  simp [synthesis, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner,
    inner_smul_left, matrix_elements]

/-- The complementary readout is positive because the original is dominated. -/
def Branch.complement (b : Branch phase) : Branch phase where
  q := b.residual
  positive := b.residual_positive h
  invariant x := by simp [Branch.residual, phase.preserves, b.invariant]
  dominated x := by
    have hp := b.positive.nonnegative x
    dsimp [Branch.residual]
    linarith

theorem Branch.effect_add_complement (b : Branch phase) :
    b.effect h + (b.complement h).effect h = 1 := by
  apply operator_ext h phase
  intro x y
  simp only [ContinuousLinearMap.add_apply, inner_add_right, Branch.effect_kernel,
    ContinuousLinearMap.one_apply, inner_feature]
  exact (b.kernel_decomposition x y).symm

theorem Branch.effect_le_one (b : Branch phase) : b.effect h ≤ 1 := by
  rw [ContinuousLinearMap.le_def]
  have he : (1 : Hilbert h phase →L[ℂ] Hilbert h phase) - b.effect h =
      (b.complement h).effect h := by
    rw [← b.effect_add_complement h]
    abel
  rw [he]
  exact (b.complement h).effect_positive h

/-- A finite nonnegative quadratic resolution of the total readout. -/
structure Resolution (phase : QuadraticPhase Q) (R : Type*) [Fintype R] where
  q : R → V → ℝ
  positive : ∀ r, PositiveQuadratic (q r)
  invariant : ∀ r x, q r (phase.J x) = q r x
  total : ∀ x, ∑ r, q r x = Q x

variable {R : Type*} [Fintype R]

/-- Domination is derived from the finite nonnegative resolution. -/
theorem Resolution.dominated (s : Resolution phase R) (r : R) (x : V) : s.q r x ≤ Q x := by
  rw [← s.total x]
  exact Finset.single_le_sum (fun i _ => (s.positive i).nonnegative x) (Finset.mem_univ r)

def Resolution.branch (s : Resolution phase R) (r : R) : Branch phase where
  q := s.q r
  positive := s.positive r
  invariant := s.invariant r
  dominated := s.dominated r

theorem Resolution.polarization_sum (s : Resolution phase R) (x y : V) :
    ∑ r, polarization (s.q r) x y = polarization Q x y := by
  simp only [polarization, ← Finset.sum_div, Finset.sum_sub_distrib, s.total]

theorem Resolution.kernel_sum (s : Resolution phase R) (x y : V) :
    ∑ r, kernel (s.branch r).branchPhase x y = kernel phase x y := by
  change (∑ r, ((polarization (s.q r) x y : ℂ) +
    Complex.I * (polarization (s.q r) (phase.J x) y : ℂ))) = _
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Complex.ofReal_sum,
    ← Complex.ofReal_sum, s.polarization_sum, s.polarization_sum]
  rfl

/-- A finite POVM resolution on the entire, possibly infinite-dimensional,
canonical Hilbert output. The outcome type may be empty. -/
theorem Resolution.sum_effect_eq_one (s : Resolution phase R) :
    ∑ r, (s.branch r).effect h = 1 := by
  apply operator_ext h phase
  intro x y
  simp only [ContinuousLinearMap.sum_apply, inner_sum, Branch.effect_kernel,
    s.kernel_sum, ContinuousLinearMap.one_apply, inner_feature]

theorem Resolution.finite_povm (s : Resolution phase R) :
    (∀ r, ((s.branch r).effect h).IsPositive) ∧
    (∀ r, (s.branch r).effect h ≤ 1) ∧
    (∀ r, ‖(s.branch r).effect h‖ ≤ 1) ∧
    (∑ r, (s.branch r).effect h) = 1 := by
  exact ⟨fun r => (s.branch r).effect_positive h,
    fun r => (s.branch r).effect_le_one h,
    fun r => (s.branch r).effect_norm_le h, s.sum_effect_eq_one h⟩

/-- Explicit scope: mathematical construction, no scientific claim upgrade. -/
inductive BoundaryRole where
  | suppliedPositiveQuadraticBranchReadouts
  | suppliedCommonQuarterTurnInvariance
  | dominationDerivedFromNonnegativeFiniteResolution
  | provedFullComplexCoefficientContraction
  | constructedPositiveBoundedEffectsAndFiniteResolution
  | arbitraryDimensionAndNullDirectionsAllowed
  | noCarrierScalarTopologyOrHalvingPremise
  | noPhysicalChannelOrInstrumentAvailability
  | noActualizationProjectivityRepeatabilityOrStateUpdate
  | doesNotProveFullQMOrUpgradeManifestStatus
  deriving DecidableEq, Repr

def boundaryRoles : List BoundaryRole := [
  .suppliedPositiveQuadraticBranchReadouts,
  .suppliedCommonQuarterTurnInvariance,
  .dominationDerivedFromNonnegativeFiniteResolution,
  .provedFullComplexCoefficientContraction,
  .constructedPositiveBoundedEffectsAndFiniteResolution,
  .arbitraryDimensionAndNullDirectionsAllowed,
  .noCarrierScalarTopologyOrHalvingPremise,
  .noPhysicalChannelOrInstrumentAvailability,
  .noActualizationProjectivityRepeatabilityOrStateUpdate,
  .doesNotProveFullQMOrUpgradeManifestStatus]

end

end IDT.QMClosure.QuadraticReadoutEffects
