import Proofs.QMClosure.FiniteMixtureContinuationRank
import Proofs.QMClosure.FiniteTranslationSpectrum
import Mathlib.Data.Complex.BigOperators

/-!
# Complex translate-rank bounds from real mixture congruence

The supplied congruence quantifies over all finite probability ensembles with
real weights. Its real affine coefficient witnesses also give complex span
membership after casting. The resulting complex bound uses the same augmented
probe family and requires no comparison of real and complex dimensions.
-/

noncomputable section

namespace MixtureProbeComplexRank

open FiniteMixtureContinuationRank
open scoped BigOperators

variable {X : Type*} {k : ℕ}

/-- The real augmented probes, viewed as complex-valued functions. -/
def castAugmentedProbe (P : X → Fin k → ℝ) :
    Option (Fin k) → X → ℂ :=
  fun j x => (augmentedProbe P j x : ℂ)

def complexProbeSpace (P : X → Fin k → ℝ) : Submodule ℂ (X → ℂ) :=
  Submodule.span ℂ (Set.range (castAugmentedProbe P))

instance complexProbeSpace_finiteDimensional (P : X → Fin k → ℝ) :
    FiniteDimensional ℂ (complexProbeSpace P) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range (castAugmentedProbe P))

theorem finrank_complexProbeSpace_le (P : X → Fin k → ℝ) :
    Module.finrank ℂ (complexProbeSpace P) ≤ k + 1 := by
  simpa [complexProbeSpace, Set.finrank] using
    (finrank_range_le_card (R := ℂ) (castAugmentedProbe P))

/-- Real span membership provides explicit coefficients for the cast identity. -/
theorem cast_mem_complexProbeSpace (P : X → Fin k → ℝ)
    {g : X → ℝ} (hg : g ∈ probeSpace P) :
    (fun x => (g x : ℂ)) ∈ complexProbeSpace P := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hg
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
  refine ⟨fun j => (c j : ℂ), ?_⟩
  funext x
  have hx : (∑ j, c j * augmentedProbe P j x) = g x := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hc x
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    castAugmentedProbe, Complex.ofReal_sum, Complex.ofReal_mul] using
      congrArg Complex.ofReal hx

/-- Local real-ensemble congruence bounds every coordinate's complex translate
span by the complex span of the original augmented probes. -/
theorem translationSpanC_le_complexProbeSpace
    (P : IntegerLattice → Fin k → ℝ)
    (hlocal : ∀ j, MixtureCongruent P (fun x => x + localStep j)) (i : Fin k) :
    FiniteTranslationSpectrum.translationSpanC (fun z => (P z i : ℂ)) ≤
      complexProbeSpace P := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact cast_mem_complexProbeSpace P
    (lattice_translate_mem P hlocal a (augmentedProbe_mem P (some i)))

theorem translationSpanC_finiteDimensional
    (P : IntegerLattice → Fin k → ℝ)
    (hlocal : ∀ j, MixtureCongruent P (fun x => x + localStep j)) (i : Fin k) :
    FiniteDimensional ℂ
      (FiniteTranslationSpectrum.TranslationSpace (fun z => (P z i : ℂ))) :=
  Submodule.finiteDimensional_of_le (translationSpanC_le_complexProbeSpace P hlocal i)

theorem finrank_translationSpanC_le
    (P : IntegerLattice → Fin k → ℝ)
    (hlocal : ∀ j, MixtureCongruent P (fun x => x + localStep j)) (i : Fin k) :
    Module.finrank ℂ
      (FiniteTranslationSpectrum.TranslationSpace (fun z => (P z i : ℂ))) ≤ k + 1 :=
  (Submodule.finrank_mono (translationSpanC_le_complexProbeSpace P hlocal i)).trans
    (finrank_complexProbeSpace_le P)

theorem four_probe_complex_translation_rank_le_five
    (P : IntegerLattice → Fin 4 → ℝ)
    (hlocal : ∀ j, MixtureCongruent P (fun x => x + localStep j)) :
    FiniteDimensional ℂ
        (FiniteTranslationSpectrum.TranslationSpace (fun z => (P z 0 : ℂ))) ∧
      Module.finrank ℂ
        (FiniteTranslationSpectrum.TranslationSpace (fun z => (P z 0 : ℂ))) ≤ 5 :=
  ⟨translationSpanC_finiteDimensional P hlocal 0,
    finrank_translationSpanC_le P hlocal 0⟩

end MixtureProbeComplexRank
