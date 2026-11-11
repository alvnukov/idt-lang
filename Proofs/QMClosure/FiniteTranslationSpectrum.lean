import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Algebraic joint spectrum of a finite-dimensional integer translate span

Joint-primary decomposition infrastructure.
No polynomial extraction, dilation classification, real-rank transfer, or physical
interpretation is asserted here. Finite dimension is an explicit hypothesis.
-/

noncomputable section

namespace FiniteTranslationSpectrum

open scoped BigOperators DirectSum

attribute [local instance] Classical.propDecidable

abbrev G := ℤ × ℤ

def translate (a : G) (g : G → ℂ) : G → ℂ := fun z => g (z + a)

def translationSpanC (f : G → ℂ) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (Set.range fun a : G => translate a f)

abbrev TranslationSpace (f : G → ℂ) := translationSpanC f

def translateLinearMap (a : G) : Module.End ℂ (G → ℂ) where
  toFun := translate a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem translate_mem_translationSpan (f : G → ℂ) (a : G)
    {g : G → ℂ} (hg : g ∈ translationSpanC f) :
    translate a g ∈ translationSpanC f := by
  have hclosed : translationSpanC f ≤
      (translationSpanC f).comap (translateLinearMap a) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    change translate a (translate b f) ∈ translationSpanC f
    apply Submodule.subset_span
    refine ⟨a + b, ?_⟩
    funext z
    simp only [translate, add_assoc]
  exact hclosed hg

/-- Every integer translation is a linear automorphism of the translate span. -/
def translationLinearEquiv (f : G → ℂ) (a : G) :
    TranslationSpace f ≃ₗ[ℂ] TranslationSpace f where
  toFun g := ⟨translate a g, translate_mem_translationSpan f a g.property⟩
  invFun g := ⟨translate (-a) g, translate_mem_translationSpan f (-a) g.property⟩
  left_inv g := by
    apply Subtype.ext
    funext z
    simp only [translate, add_assoc, neg_add_cancel, add_zero]
  right_inv g := by
    apply Subtype.ext
    funext z
    simp only [translate, add_assoc, add_neg_cancel, add_zero]
  map_add' g h := by
    apply Subtype.ext
    rfl
  map_smul' c g := by
    apply Subtype.ext
    rfl

def translationEnd (f : G → ℂ) (a : G) :
    Module.End ℂ (TranslationSpace f) :=
  (translationLinearEquiv f a).toLinearMap

@[simp] theorem translationEnd_apply (f : G → ℂ) (a : G)
    (g : TranslationSpace f) (z : G) :
    ((translationEnd f a g : TranslationSpace f) : G → ℂ) z =
      (g : G → ℂ) (z + a) := rfl

theorem translationEnd_injective (f : G → ℂ) (a : G) :
    Function.Injective (translationEnd f a) :=
  (translationLinearEquiv f a).injective

theorem translationEnd_commute (f : G → ℂ) (a b : G) :
    Commute (translationEnd f a) (translationEnd f b) := by
  change translationEnd f a * translationEnd f b =
    translationEnd f b * translationEnd f a
  apply LinearMap.ext
  intro g
  apply Subtype.ext
  funext z
  change (g : G → ℂ) ((z + a) + b) = (g : G → ℂ) ((z + b) + a)
  ac_rfl

def coordinateStep (i : Fin 2) : G :=
  if i = 0 then (1, 0) else (0, 1)

def coordinateEnd (f : G → ℂ) (i : Fin 2) :
    Module.End ℂ (TranslationSpace f) :=
  translationEnd f (coordinateStep i)

theorem coordinateEnd_injective (f : G → ℂ) (i : Fin 2) :
    Function.Injective (coordinateEnd f i) :=
  translationEnd_injective f (coordinateStep i)

theorem coordinateEnd_pairwise_commute (f : G → ℂ) :
    Pairwise fun i j : Fin 2 => Commute (coordinateEnd f i) (coordinateEnd f j) := by
  intro i j _
  exact translationEnd_commute f (coordinateStep i) (coordinateStep j)

/-- Characters are represented here by their two coordinate eigenvalues.
Nonzero eigenvalues are proved for every nonzero joint component below. -/
def jointBlock (f : G → ℂ) (χ : Fin 2 → ℂ) :
    Submodule ℂ (TranslationSpace f) :=
  ⨅ i, (coordinateEnd f i).maxGenEigenspace (χ i)

theorem translationEnd_mapsTo_jointBlock (f : G → ℂ) (a : G)
    (χ : Fin 2 → ℂ) :
    Set.MapsTo (translationEnd f a) (jointBlock f χ) (jointBlock f χ) := by
  intro v hv
  apply (Submodule.mem_iInf _).mpr
  intro i
  exact Module.End.mapsTo_maxGenEigenspace_of_comm
    (translationEnd_commute f (coordinateStep i) a) (χ i)
    ((Submodule.mem_iInf _).mp hv i)

theorem jointBlock_independent (f : G → ℂ) :
    iSupIndep (jointBlock f) := by
  apply Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
  intro i j μ
  exact Module.End.mapsTo_maxGenEigenspace_of_comm
    (translationEnd_commute f (coordinateStep j) (coordinateStep i)) μ

section FiniteDimension

variable (f : G → ℂ) [FiniteDimensional ℂ (TranslationSpace f)]

theorem jointBlock_iSup_eq_top :
    ⨆ χ : Fin 2 → ℂ, jointBlock f χ = ⊤ := by
  apply Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (coordinateEnd f) (coordinateEnd_pairwise_commute f)
  intro i
  exact Module.End.iSup_maxGenEigenspace_eq_top (coordinateEnd f i)

theorem jointBlock_isInternal : DirectSum.IsInternal (jointBlock f) := by
  classical
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (jointBlock_independent f) (jointBlock_iSup_eq_top f)

noncomputable instance jointDecomposition :
    DirectSum.Decomposition (jointBlock f) :=
  (jointBlock_isInternal f).chooseDecomposition

/-- A finitely supported joint-primary decomposition of any translate-span vector. -/
def jointComponents (v : TranslationSpace f) :
    ⨁ χ : Fin 2 → ℂ, jointBlock f χ :=
  DirectSum.decomposeLinearEquiv (jointBlock f) v

theorem jointComponents_mem (v : TranslationSpace f) (χ : Fin 2 → ℂ) :
    (jointComponents f v χ : TranslationSpace f) ∈ jointBlock f χ :=
  (jointComponents f v χ).property

theorem sum_jointComponents (v : TranslationSpace f) :
    (∑ χ ∈ (jointComponents f v).support,
      (jointComponents f v χ : TranslationSpace f)) = v := by
  classical
  exact DirectSum.sum_support_decompose (jointBlock f) v

/-- Projection onto a joint-primary block, with values in the original module. -/
def jointProjection (χ : Fin 2 → ℂ) :
    Module.End ℂ (TranslationSpace f) :=
  (jointBlock f χ).subtype ∘ₗ
    (DirectSum.component ℂ (Fin 2 → ℂ) (fun θ => jointBlock f θ) χ) ∘ₗ
      (DirectSum.decomposeLinearEquiv (jointBlock f)).toLinearMap

@[simp] theorem jointProjection_apply (χ : Fin 2 → ℂ) (v : TranslationSpace f) :
    jointProjection f χ v = (jointComponents f v χ : TranslationSpace f) := rfl

theorem jointProjection_of_mem (χ : Fin 2 → ℂ) {v : TranslationSpace f}
    (hv : v ∈ jointBlock f χ) : jointProjection f χ v = v := by
  exact DirectSum.decompose_of_mem_same (jointBlock f) hv

theorem jointProjection_of_mem_ne (χ θ : Fin 2 → ℂ) {v : TranslationSpace f}
    (hv : v ∈ jointBlock f θ) (hne : θ ≠ χ) :
    jointProjection f χ v = 0 := by
  exact DirectSum.decompose_of_mem_ne (jointBlock f) hv hne

/-- Joint-primary projections intertwine every integer translation. -/
theorem jointProjection_translationEnd (χ : Fin 2 → ℂ) (a : G)
    (v : TranslationSpace f) :
    jointProjection f χ (translationEnd f a v) =
      translationEnd f a (jointProjection f χ v) := by
  classical
  have hblock (θ : Fin 2 → ℂ) (w : TranslationSpace f)
      (hw : w ∈ jointBlock f θ) :
      jointProjection f χ (translationEnd f a w) =
        translationEnd f a (jointProjection f χ w) := by
    have htw := translationEnd_mapsTo_jointBlock f a θ hw
    by_cases hθ : θ = χ
    · subst θ
      rw [jointProjection_of_mem f χ htw, jointProjection_of_mem f χ hw]
    · rw [jointProjection_of_mem_ne f χ θ htw hθ,
        jointProjection_of_mem_ne f χ θ hw hθ, map_zero]
  have hsum := sum_jointComponents f v
  calc
    jointProjection f χ (translationEnd f a v) =
        jointProjection f χ (translationEnd f a
          (∑ θ ∈ (jointComponents f v).support,
            (jointComponents f v θ : TranslationSpace f))) := by rw [hsum]
    _ = ∑ θ ∈ (jointComponents f v).support,
        jointProjection f χ (translationEnd f a
          (jointComponents f v θ : TranslationSpace f)) := by
      simp only [map_sum]
    _ = ∑ θ ∈ (jointComponents f v).support,
        translationEnd f a (jointProjection f χ
          (jointComponents f v θ : TranslationSpace f)) := by
      apply Finset.sum_congr rfl
      intro θ _
      exact hblock θ _ (jointComponents_mem f v θ)
    _ = translationEnd f a (jointProjection f χ
        (∑ θ ∈ (jointComponents f v).support,
          (jointComponents f v θ : TranslationSpace f))) := by
      simp only [map_sum]
    _ = translationEnd f a (jointProjection f χ v) := by rw [hsum]

/-- A nonzero joint-primary vector has nonzero coordinate eigenvalues. -/
theorem coordinate_ne_zero_of_jointBlock_mem (χ : Fin 2 → ℂ)
    {v : TranslationSpace f} (hv : v ∈ jointBlock f χ) (hne : v ≠ 0)
    (i : Fin 2) : χ i ≠ 0 := by
  intro hzero
  have hvi : v ∈ (coordinateEnd f i).maxGenEigenspace (χ i) :=
    (Submodule.mem_iInf _).mp hv i
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace
    (coordinateEnd f i) (χ i) v).mp hvi
  have hoperator : coordinateEnd f i - χ i • (1 : Module.End ℂ (TranslationSpace f)) =
      coordinateEnd f i := by
    ext w
    simp [hzero]
  have hk' : ((coordinateEnd f i) ^ k) v = 0 := by
    rw [hoperator] at hk
    exact hk
  have hpow : Function.Injective
      (fun w : TranslationSpace f => ((coordinateEnd f i) ^ k) w) := by
    simpa only [Module.End.coe_pow] using (coordinateEnd_injective f i).iterate k
  exact hne (hpow (by simpa only [map_zero] using hk'))

/-- The original function belongs to its global translate span via the zero shift. -/
def original : TranslationSpace f :=
  ⟨f, by
    apply Submodule.subset_span
    refine ⟨0, ?_⟩
    funext z
    simp only [translate, add_zero]⟩

def readoutComponents : ⨁ χ : Fin 2 → ℂ, jointBlock f χ :=
  jointComponents f (original f)

theorem sum_readoutComponents :
    (∑ χ ∈ (readoutComponents f).support,
      (readoutComponents f χ : TranslationSpace f)) = original f := by
  classical
  exact sum_jointComponents f (original f)

theorem readoutComponents_mem (χ : Fin 2 → ℂ) :
    (readoutComponents f χ : TranslationSpace f) ∈ jointBlock f χ :=
  (readoutComponents f χ).property

theorem readoutComponents_coordinate_ne_zero (χ : Fin 2 → ℂ)
    (hne : (readoutComponents f χ : TranslationSpace f) ≠ 0) (i : Fin 2) :
    χ i ≠ 0 :=
  coordinate_ne_zero_of_jointBlock_mem f χ (readoutComponents_mem f χ) hne i

end FiniteDimension

end FiniteTranslationSpectrum
