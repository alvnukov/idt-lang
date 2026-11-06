import Proofs.QMClosure.CanonicalQuadraticHilbert
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.LinearMap

namespace IDT.QMClosure.CanonicalHilbertUniqueness

open QuadraticRecordRefinement PositiveQuadraticPolarization QuadraticHermitianKernel
open CanonicalQuadraticHilbert

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
Uniqueness is relative to the specified quadratic readout and quarter-turn.
Hilbert structure is required only on a comparison output, never on the native
carrier. A kernel realization extends to an isometric embedding; density of its
complex span is exactly the additional premise used for surjectivity. An unused
orthogonal summand therefore does not give a whole-output uniqueness claim.
-/

variable {V : Type*} [AddCommGroup V] {Q : V → ℝ}
variable (h : PositiveQuadratic Q) (phase : QuadraticPhase Q)
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Linear extension of a comparison feature family from the free complex module. -/
def freeMap (ψ : V → K) : Free h phase →ₗ[ℂ] K :=
  Finsupp.linearCombination ℂ ψ

private theorem coe_free_eq (f : Free h phase) :
    (f : Hilbert h phase) = Finsupp.linearCombination ℂ (feature h phase) f := by
  classical
  induction f using Finsupp.induction with
  | zero =>
      simpa only [map_zero] using (UniformSpace.Completion.coe_zero (α := Free h phase))
  | single_add x a f _ _ ih =>
      have hs : UniformSpace.Completion.coe' (α := Free h phase) (Finsupp.single x a) =
          Finsupp.linearCombination ℂ (feature h phase) (Finsupp.single x a) := by
        rw [Finsupp.linearCombination_single]
        change UniformSpace.Completion.coe' (α := Free h phase) (Finsupp.single x a) =
          a • UniformSpace.Completion.coe' (α := Free h phase) (Finsupp.single x (1 : ℂ))
        have hm : a • (Finsupp.single x (1 : ℂ) : Free h phase) = Finsupp.single x a :=
          (Finsupp.smul_single a x (1 : ℂ)).trans (by simp)
        exact (congrArg (UniformSpace.Completion.coe' (α := Free h phase)) hm).symm.trans
          (UniformSpace.Completion.coe_smul (X := Free h phase) a (Finsupp.single x 1))
      rw [map_add, UniformSpace.Completion.coe_add (α := Free h phase)]
      exact congrArg₂ (fun a b : Hilbert h phase => a + b) hs ih

omit [CompleteSpace K] in
theorem inner_freeMap (ψ : V → K)
    (hψ : ∀ x y, inner ℂ (ψ x) (ψ y) = kernel phase x y)
    (f g : Free h phase) :
    inner ℂ (freeMap h phase ψ f) (freeMap h phase ψ g) =
      inner ℂ (f : Hilbert h phase) (g : Hilbert h phase) := by
  rw [coe_free_eq, coe_free_eq]
  change inner ℂ ((Finsupp.linearCombination ℂ ψ) (f : V →₀ ℂ))
    ((Finsupp.linearCombination ℂ ψ) (g : V →₀ ℂ)) = _
  simp only [Finsupp.linearCombination_apply, Finsupp.sum_inner,
    Finsupp.inner_sum, inner_smul_left, inner_smul_right, hψ, inner_feature]

omit [CompleteSpace K] in
theorem norm_freeMap (ψ : V → K)
    (hψ : ∀ x y, inner ℂ (ψ x) (ψ y) = kernel phase x y) (f : Free h phase) :
    ‖freeMap h phase ψ f‖ = ‖(f : Hilbert h phase)‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
    inner_freeMap h phase ψ hψ]

/-- The map descends through null differences and extends to the completion. -/
def extension (ψ : V → K) : Hilbert h phase →L[ℂ] K :=
  (freeMap h phase ψ).extendOfNorm
    (UniformSpace.Completion.toComplₗᵢ : Free h phase →ₗᵢ[ℂ] Hilbert h phase).toLinearMap

theorem extension_coe (ψ : V → K)
    (hψ : ∀ x y, inner ℂ (ψ x) (ψ y) = kernel phase x y) (f : Free h phase) :
    extension h phase ψ (f : Hilbert h phase) = freeMap h phase ψ f := by
  apply LinearMap.extendOfNorm_eq
  · exact UniformSpace.Completion.denseRange_coe
  · exact ⟨1, fun f => by simpa using (norm_freeMap h phase ψ hψ f).le⟩

theorem extension_feature (ψ : V → K)
    (hψ : ∀ x y, inner ℂ (ψ x) (ψ y) = kernel phase x y) (x : V) :
    extension h phase ψ (feature h phase x) = ψ x := by
  rw [feature, extension_coe h phase ψ hψ]
  change (Finsupp.linearCombination ℂ ψ) (Finsupp.single x 1) = ψ x
  simp

theorem norm_extension (ψ : V → K)
    (hψ : ∀ x y, inner ℂ (ψ x) (ψ y) = kernel phase x y) (u : Hilbert h phase) :
    ‖extension h phase ψ u‖ = ‖u‖ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) continuous_norm
  | ih f => rw [extension_coe h phase ψ hψ, norm_freeMap h phase ψ hψ]

/-- No density premise is needed for the canonical isometric embedding. -/
def embedding (ψ : V → K)
    (hψ : ∀ x y, inner ℂ (ψ x) (ψ y) = kernel phase x y) :
    Hilbert h phase →ₗᵢ[ℂ] K :=
  { (extension h phase ψ).toLinearMap with norm_map' := norm_extension h phase ψ hψ }

theorem embedding_feature (ψ : V → K)
    (hψ : ∀ x y, inner ℂ (ψ x) (ψ y) = kernel phase x y) (x : V) :
    embedding h phase ψ hψ (feature h phase x) = ψ x :=
  extension_feature h phase ψ hψ x

theorem embedding_unique (ψ : V → K)
    (hψ : ∀ x y, inner ℂ (ψ x) (ψ y) = kernel phase x y)
    (T : Hilbert h phase →ₗᵢ[ℂ] K) (hT : ∀ x, T (feature h phase x) = ψ x) :
    T = embedding h phase ψ hψ := by
  have he : T.toContinuousLinearMap = (embedding h phase ψ hψ).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext_on (dense_span_feature h phase)
    rintro _ ⟨x, rfl⟩
    exact (hT x).trans (embedding_feature h phase ψ hψ x).symm
  ext u
  exact congrArg (fun f : Hilbert h phase →L[ℂ] K => f u) he

/-- The embedding fills precisely the closed complex span of the comparison family. -/
theorem range_embedding (ψ : V → K)
    (hψ : ∀ x y, inner ℂ (ψ x) (ψ y) = kernel phase x y) :
    Set.range (embedding h phase ψ hψ) =
      ((Submodule.span ℂ (Set.range ψ)).topologicalClosure : Set K) := by
  let T := embedding h phase ψ hψ
  let S := (Submodule.span ℂ (Set.range ψ)).topologicalClosure
  have hs : Submodule.span ℂ (Set.range (feature h phase)) ≤ S.comap T.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    change T (feature h phase x) ∈ S
    rw [embedding_feature]
    exact (Submodule.span ℂ (Set.range ψ)).le_topologicalClosure
      (Submodule.subset_span (Set.mem_range_self x))
  have hmem (u : Hilbert h phase) : T u ∈ S :=
    (dense_span_feature h phase).induction (fun _ hu => hs hu)
      ((Submodule.span ℂ (Set.range ψ)).isClosed_topologicalClosure.preimage T.continuous) u
  have hc : IsClosed (Set.range T) :=
    T.isometry.antilipschitz.isClosed_range T.isometry.uniformContinuous
  have hspan : Submodule.span ℂ (Set.range ψ) ≤ T.toLinearMap.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact ⟨feature h phase x, embedding_feature h phase ψ hψ x⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨u, rfl⟩
    exact hmem u
  · exact hc.closure_subset_iff.mpr hspan

/-- Without a density premise, the codomain is the generated closed subspace. -/
def closedSpanEmbedding (ψ : V → K)
    (hψ : ∀ x y, inner ℂ (ψ x) (ψ y) = kernel phase x y) :
    Hilbert h phase →ₗᵢ[ℂ] (Submodule.span ℂ (Set.range ψ)).topologicalClosure :=
  { (embedding h phase ψ hψ).toLinearMap.codRestrict _ (fun u => by
      change embedding h phase ψ hψ u ∈
        ((Submodule.span ℂ (Set.range ψ)).topologicalClosure : Set K)
      rw [← range_embedding h phase ψ hψ]
      exact Set.mem_range_self u) with
    norm_map' := fun u => (embedding h phase ψ hψ).norm_map u }

theorem embedding_surjective (ψ : V → K)
    (hψ : ∀ x y, inner ℂ (ψ x) (ψ y) = kernel phase x y)
    (hdense : Dense (Submodule.span ℂ (Set.range ψ) : Set K)) :
    Function.Surjective (embedding h phase ψ hψ) := by
  let T := embedding h phase ψ hψ
  have hc : IsClosed (Set.range T) :=
    T.isometry.antilipschitz.isClosed_range T.isometry.uniformContinuous
  have hs : Submodule.span ℂ (Set.range ψ) ≤ T.toLinearMap.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact ⟨feature h phase x, embedding_feature h phase ψ hψ x⟩
  intro y
  have hy := (hdense.mono hs) y
  change y ∈ closure (Set.range T) at hy
  rwa [hc.closure_eq] at hy

/-- Dense generation gives the unique whole-output complex linear isometry equivalence. -/
def equivalence (ψ : V → K)
    (hψ : ∀ x y, inner ℂ (ψ x) (ψ y) = kernel phase x y)
    (hdense : Dense (Submodule.span ℂ (Set.range ψ) : Set K)) :
    Hilbert h phase ≃ₗᵢ[ℂ] K :=
  LinearIsometryEquiv.ofSurjective (embedding h phase ψ hψ)
    (embedding_surjective h phase ψ hψ hdense)

theorem equivalence_feature (ψ : V → K)
    (hψ : ∀ x y, inner ℂ (ψ x) (ψ y) = kernel phase x y)
    (hdense : Dense (Submodule.span ℂ (Set.range ψ) : Set K)) (x : V) :
    equivalence h phase ψ hψ hdense (feature h phase x) = ψ x :=
  embedding_feature h phase ψ hψ x

theorem existsUnique_equivalence (ψ : V → K)
    (hψ : ∀ x y, inner ℂ (ψ x) (ψ y) = kernel phase x y)
    (hdense : Dense (Submodule.span ℂ (Set.range ψ) : Set K)) :
    ∃! T : Hilbert h phase ≃ₗᵢ[ℂ] K, ∀ x, T (feature h phase x) = ψ x := by
  refine ⟨equivalence h phase ψ hψ hdense, equivalence_feature h phase ψ hψ hdense, ?_⟩
  intro T hT
  have he := embedding_unique h phase ψ hψ T.toLinearIsometry hT
  ext u
  exact congrArg (fun f : Hilbert h phase →ₗᵢ[ℂ] K => f u) he

omit [CompleteSpace K] in
/-- Additivity, phase covariance and the same quadratic weight force the kernel. -/
theorem inner_eq_kernel_of_weight_phase (ψ : V →+ K)
    (hphase : ∀ x, ψ (phase.J x) = Complex.I • ψ x)
    (hweight : ∀ x, ‖ψ x‖ ^ 2 = Q x) (x y : V) :
    inner ℂ (ψ x) (ψ y) = kernel phase x y := by
  have hre (a b : V) : (inner ℂ (ψ a) (ψ b)).re = polarization Q a b := by
    change RCLike.re (inner ℂ (ψ a) (ψ b)) = _
    rw [re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
    simp only [← sq, ← map_add, hweight, polarization]
  apply Complex.ext
  · rw [kernel_re, hre]
  · have hi := hre (phase.J x) y
    rw [hphase, inner_smul_left] at hi
    simpa [kernel_im, Complex.mul_re] using hi

theorem existsUnique_equivalence_of_weight_phase (ψ : V →+ K)
    (hphase : ∀ x, ψ (phase.J x) = Complex.I • ψ x)
    (hweight : ∀ x, ‖ψ x‖ ^ 2 = Q x)
    (hdense : Dense (Submodule.span ℂ (Set.range ψ) : Set K)) :
    ∃! T : Hilbert h phase ≃ₗᵢ[ℂ] K, ∀ x, T (feature h phase x) = ψ x :=
  existsUnique_equivalence h phase ψ (inner_eq_kernel_of_weight_phase phase ψ hphase hweight) hdense

/-- Mathematical scope only; this does not prove physical closure or upgrade status. -/
inductive BoundaryRole where
  | specifiedQuadraticReadoutAndQuarterTurn
  | hilbertStructureOnlyOnComparisonOutput
  | nullDirectionsAllowed
  | noNativeCarrierScalarTopologyOrDefiniteness
  | embeddingWithoutDenseSpan
  | wholeOutputEquivalenceRequiresDenseComplexSpan
  | unusedOrthogonalSummandPreventsWholeOutputUniqueness
  | noOperationalHalfRequired
  | doesNotProveAllStatesOrProcessesPhysicallyAvailable
  | doesNotProveBornDynamicsTensorScalesOrFullQM
  | doesNotUpgradeManifestStatus
  deriving DecidableEq, Repr

def boundaryRoles : List BoundaryRole := [
  .specifiedQuadraticReadoutAndQuarterTurn,
  .hilbertStructureOnlyOnComparisonOutput,
  .nullDirectionsAllowed,
  .noNativeCarrierScalarTopologyOrDefiniteness,
  .embeddingWithoutDenseSpan,
  .wholeOutputEquivalenceRequiresDenseComplexSpan,
  .unusedOrthogonalSummandPreventsWholeOutputUniqueness,
  .noOperationalHalfRequired,
  .doesNotProveAllStatesOrProcessesPhysicallyAvailable,
  .doesNotProveBornDynamicsTensorScalesOrFullQM,
  .doesNotUpgradeManifestStatus]

end

end IDT.QMClosure.CanonicalHilbertUniqueness
