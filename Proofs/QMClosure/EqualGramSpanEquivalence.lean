import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Equal-Gram equivalences of generated closed spans

Equal Gram data on arbitrary indexed families determines a unique complex
linear isometry equivalence of their closed spans. The families may be empty,
dependent, or degenerate. No injectivity of the coefficient maps is assumed.

This is a mathematical comparison of supplied complete inner product spaces.
It does not derive a physical Hilbert space or assert physical availability of
the constructed equivalence.
-/

namespace IDT.QMClosure.EqualGramSpanEquivalence

noncomputable section

variable {I H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The closed complex span of a supplied family. -/
def closedSpan (f : I → H) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range f)).topologicalClosure

instance closedSpan_completeSpace [CompleteSpace H] (f : I → H) : CompleteSpace (closedSpan f) := by
  unfold closedSpan
  infer_instance

/-- A generator regarded as a vector of its closed span. -/
def spanGenerator (f : I → H) (i : I) : closedSpan f :=
  ⟨f i, Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self i))⟩

@[simp] theorem spanGenerator_coe (f : I → H) (i : I) :
    (spanGenerator f i : H) = f i := rfl

/-- The generators have dense algebraic span in their closed span. -/
theorem dense_spanGenerator (f : I → H) :
    Dense (Submodule.span ℂ (Set.range (spanGenerator f)) : Set (closedSpan f)) := by
  have himage : ((↑) : closedSpan f → H) ''
      (Submodule.span ℂ (Set.range (spanGenerator f)) : Set (closedSpan f)) =
      (Submodule.span ℂ (Set.range f) : Set H) := by
    change ((Submodule.span ℂ (Set.range (spanGenerator f))).map (closedSpan f).subtype :
      Set H) = _
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [Subtype.dense_iff]
  change (closure (Submodule.span ℂ (Set.range f) : Set H)) ⊆ _
  exact closure_mono himage.symm.subset

/-- Finite coefficient combinations have dense range whenever the family spans densely. -/
theorem denseRange_linearCombination (f : I → H)
    (hf : Dense (Submodule.span ℂ (Set.range f) : Set H)) :
    DenseRange (Finsupp.linearCombination ℂ f) := by
  change Dense (LinearMap.range (Finsupp.linearCombination ℂ f) : Set H)
  rw [Finsupp.range_linearCombination]
  exact hf

/-- Equal Gram entries give equal inner products of all finite combinations. -/
theorem inner_linearCombination (f : I → H) (g : I → K)
    (hGram : ∀ i j, inner ℂ (f i) (f j) = inner ℂ (g i) (g j))
    (a b : I →₀ ℂ) :
    inner ℂ (Finsupp.linearCombination ℂ f a) (Finsupp.linearCombination ℂ f b) =
      inner ℂ (Finsupp.linearCombination ℂ g a) (Finsupp.linearCombination ℂ g b) := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum,
    inner_smul_left, inner_smul_right, hGram]

/-- Norm agreement does not require the finite-combination maps to be injective. -/
theorem norm_linearCombination (f : I → H) (g : I → K)
    (hGram : ∀ i j, inner ℂ (f i) (f j) = inner ℂ (g i) (g j)) (a : I →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ g a‖ = ‖Finsupp.linearCombination ℂ f a‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
    inner_linearCombination f g hGram]

variable [CompleteSpace H] [CompleteSpace K]

/-- The unique isometry equivalence determined by two dense equal-Gram families. -/
def denseEquivalence (f : I → H) (g : I → K)
    (hf : Dense (Submodule.span ℂ (Set.range f) : Set H))
    (hg : Dense (Submodule.span ℂ (Set.range g) : Set K))
    (hGram : ∀ i j, inner ℂ (f i) (f j) = inner ℂ (g i) (g j)) : H ≃ₗᵢ[ℂ] K :=
  (LinearEquiv.refl ℂ (I →₀ ℂ)).extendOfIsometry
    (Finsupp.linearCombination ℂ f) (Finsupp.linearCombination ℂ g)
    (denseRange_linearCombination f hf) (denseRange_linearCombination g hg)
    (norm_linearCombination f g hGram)

@[simp] theorem denseEquivalence_apply (f : I → H) (g : I → K)
    (hf : Dense (Submodule.span ℂ (Set.range f) : Set H))
    (hg : Dense (Submodule.span ℂ (Set.range g) : Set K))
    (hGram : ∀ i j, inner ℂ (f i) (f j) = inner ℂ (g i) (g j)) (i : I) :
    denseEquivalence f g hf hg hGram (f i) = g i := by
  have h := LinearEquiv.extendOfIsometry_eq (LinearEquiv.refl ℂ (I →₀ ℂ))
    (Finsupp.linearCombination ℂ f) (Finsupp.linearCombination ℂ g)
    (denseRange_linearCombination f hf) (denseRange_linearCombination g hg)
    (norm_linearCombination f g hGram) (Finsupp.single i 1)
  simpa only [denseEquivalence, Finsupp.linearCombination_single, one_smul,
    LinearEquiv.refl_apply] using h

omit [CompleteSpace H] [CompleteSpace K] in
/-- Two continuous linear isometry equivalences agree if they agree on a dense family. -/
theorem dense_generator_ext (f : I → H)
    (hf : Dense (Submodule.span ℂ (Set.range f) : Set H))
    (U W : H ≃ₗᵢ[ℂ] K) (h : ∀ i, U (f i) = W (f i)) : U = W := by
  have hcomp : (U : H → K) ∘ Finsupp.linearCombination ℂ f =
      (W : H → K) ∘ Finsupp.linearCombination ℂ f := by
    funext a
    change U.toLinearMap (Finsupp.linearCombination ℂ f a) =
      W.toLinearMap (Finsupp.linearCombination ℂ f a)
    rw [Finsupp.apply_linearCombination, Finsupp.apply_linearCombination]
    have hfamily : (U.toLinearMap : H → K) ∘ f = (W.toLinearMap : H → K) ∘ f :=
      funext h
    rw [hfamily]
  have heq := (denseRange_linearCombination f hf).equalizer U.continuous W.continuous hcomp
  exact DFunLike.ext _ _ (congrFun heq)

theorem denseEquivalence_unique (f : I → H) (g : I → K)
    (hf : Dense (Submodule.span ℂ (Set.range f) : Set H))
    (hg : Dense (Submodule.span ℂ (Set.range g) : Set K))
    (hGram : ∀ i j, inner ℂ (f i) (f j) = inner ℂ (g i) (g j))
    (U : H ≃ₗᵢ[ℂ] K) (hU : ∀ i, U (f i) = g i) :
    U = denseEquivalence f g hf hg hGram := by
  apply dense_generator_ext f hf
  intro i
  rw [hU, denseEquivalence_apply]

/-- Equal-Gram families determine an equivalence of their generated closed spans. -/
def closedSpanEquivalence (f : I → H) (g : I → K)
    (hGram : ∀ i j, inner ℂ (f i) (f j) = inner ℂ (g i) (g j)) :
    closedSpan f ≃ₗᵢ[ℂ] closedSpan g := by
  letI : CompleteSpace (closedSpan f) := closedSpan_completeSpace f
  letI : CompleteSpace (closedSpan g) := closedSpan_completeSpace g
  exact @denseEquivalence I (closedSpan f) (closedSpan g)
    _ _ _ _ (closedSpan_completeSpace f) (closedSpan_completeSpace g)
    (spanGenerator f) (spanGenerator g)
    (dense_spanGenerator f) (dense_spanGenerator g) hGram

@[simp] theorem closedSpanEquivalence_apply (f : I → H) (g : I → K)
    (hGram : ∀ i j, inner ℂ (f i) (f j) = inner ℂ (g i) (g j)) (i : I) :
    closedSpanEquivalence f g hGram (spanGenerator f i) = spanGenerator g i := by
  letI : CompleteSpace (closedSpan f) := closedSpan_completeSpace f
  letI : CompleteSpace (closedSpan g) := closedSpan_completeSpace g
  exact @denseEquivalence_apply I (closedSpan f) (closedSpan g)
    _ _ _ _ (closedSpan_completeSpace f) (closedSpan_completeSpace g)
    (spanGenerator f) (spanGenerator g) (dense_spanGenerator f) (dense_spanGenerator g) hGram i

theorem closedSpanEquivalence_unique (f : I → H) (g : I → K)
    (hGram : ∀ i j, inner ℂ (f i) (f j) = inner ℂ (g i) (g j))
    (U : closedSpan f ≃ₗᵢ[ℂ] closedSpan g)
    (hU : ∀ i, U (spanGenerator f i) = spanGenerator g i) :
    U = closedSpanEquivalence f g hGram := by
  letI : CompleteSpace (closedSpan f) := closedSpan_completeSpace f
  letI : CompleteSpace (closedSpan g) := closedSpan_completeSpace g
  exact @denseEquivalence_unique I (closedSpan f) (closedSpan g)
    _ _ _ _ (closedSpan_completeSpace f) (closedSpan_completeSpace g)
    (spanGenerator f) (spanGenerator g) (dense_spanGenerator f) (dense_spanGenerator g) hGram U hU

end

end IDT.QMClosure.EqualGramSpanEquivalence
