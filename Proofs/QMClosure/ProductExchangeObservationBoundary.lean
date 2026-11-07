import Proofs.QMClosure.ProductFeatureExchange
import Proofs.QMClosure.CoherentPortRayBoundary
import Mathlib.Analysis.InnerProductSpace.Positive

namespace IDT.QMClosure.ProductExchangeObservationBoundary

open ProductFeatureExchange QuadraticHermitianKernel
open CoherentPortRayBoundary
open scoped ComplexOrder

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
These are mathematical observation controls on the constructed product-feature
span. All weighted ordered-product assumptions remain supplied. A commuting
operator gives the same response on a generator and its exchange. A strict
kernel pair also admits a mathematical positive-contraction discriminator;
its physical or native availability is not established.

No exchange sector, species, spin-statistics, actualization, matter regime,
raw/global exchange, target exhaustion, probability law, or full QM is derived.
Equality of these two responses does not identify arbitrary states or hide
their sector weights.
-/

section IsometricInvariance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Pointwise commutation suffices; no involution or positivity is required. -/
theorem inner_invariant (U : H ≃ₗᵢ[ℂ] H) (E : H →L[ℂ] H)
    (hcomm : ∀ u, E (U u) = U (E u)) (u : H) :
    inner ℂ (U u) (E (U u)) = inner ℂ u (E u) := by
  rw [hcomm, U.inner_map_map]

/-- A numerical identity, including zero under the division convention. -/
theorem normalizedExpectation_invariant (U : H ≃ₗᵢ[ℂ] H) (E : H →L[ℂ] H)
    (hcomm : ∀ u, E (U u) = U (E u)) (u : H) :
    normalizedExpectation E (U u) = normalizedExpectation E u := by
  simp only [normalizedExpectation, inner_invariant U E hcomm, U.norm_map]

end IsometricInvariance

variable {A C : Type*} [AddCommGroup A] [AddCommGroup C]
variable (D : Bridge A C)

def productWeight (z : A × A) : ℝ := D.QA z.1 * D.QA z.2

def exchangeOverlap (z : A × A) : ℝ :=
  Complex.normSq (kernel D.jA z.1 z.2)

/-- The full complex exchange matrix element is real, not only its real part. -/
theorem inner_exchange_generator (z : A × A) :
    inner ℂ (generator D z) (exchange D (generator D z)) =
      (exchangeOverlap D z : ℂ) := by
  rw [exchange_generator, inner_generator]
  dsimp [exchangeOverlap]
  rw [Complex.normSq_eq_conj_mul_self]
  have hh := hermitian D.hA D.jA z.2 z.1
  change star (kernel D.jA z.1 z.2) = kernel D.jA z.2 z.1 at hh
  rw [← hh]
  exact mul_comm _ _

theorem strict_pair_facts (z : A × A)
    (hstrict : exchangeOverlap D z < productWeight D z) :
    0 < productWeight D z ∧ generator D z ≠ 0 ∧
      plus D (generator D z) ≠ 0 ∧ minus D (generator D z) ≠ 0 := by
  have hr : 0 ≤ exchangeOverlap D z := Complex.normSq_nonneg _
  have hq : 0 < productWeight D z := lt_of_le_of_lt hr hstrict
  refine ⟨hq, ?_, ?_, ?_⟩
  · intro hz
    have hn := norm_generator_sq D z
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hn
    change 0 = productWeight D z at hn
    linarith
  · intro hz
    have hn := plus_generator_norm_sq D z
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hn
    change 0 = (productWeight D z + exchangeOverlap D z) / 2 at hn
    linarith
  · intro hz
    have hn := minus_generator_norm_sq D z
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hn
    change 0 = (productWeight D z - exchangeOverlap D z) / 2 at hn
    linarith

/-- A mathematical projector; no native effect-availability claim is made. -/
def generatorProjector (z : A × A) : Hp D →L[ℂ] Hp D := by
  letI : CompleteSpace (Hp D) := hp_completeSpace D
  letI : CompleteSpace (ℂ ∙ generator D z) := FiniteDimensional.complete ℂ _
  exact (ℂ ∙ generator D z).starProjection

theorem generatorProjector_positive (z : A × A) :
    (generatorProjector D z).IsPositive := by
  letI : CompleteSpace (Hp D) := hp_completeSpace D
  letI : CompleteSpace (ℂ ∙ generator D z) := FiniteDimensional.complete ℂ _
  exact ContinuousLinearMap.IsPositive.of_isStarProjection
    (isStarProjection_starProjection (U := ℂ ∙ generator D z))

theorem generatorProjector_le_one (z : A × A) : generatorProjector D z ≤ 1 := by
  letI : CompleteSpace (Hp D) := hp_completeSpace D
  letI : CompleteSpace (ℂ ∙ generator D z) := FiniteDimensional.complete ℂ _
  change (ℂ ∙ generator D z).starProjection ≤ 1
  rw [← Submodule.starProjection_top']
  exact Submodule.starProjection_le_starProjection_iff.mpr le_top

theorem generatorProjector_norm_le (z : A × A) : ‖generatorProjector D z‖ ≤ 1 := by
  letI : CompleteSpace (Hp D) := hp_completeSpace D
  letI : CompleteSpace (ℂ ∙ generator D z) := FiniteDimensional.complete ℂ _
  exact Submodule.starProjection_norm_le _

theorem generatorProjector_self (z : A × A) :
    generatorProjector D z (generator D z) = generator D z := by
  letI : CompleteSpace (Hp D) := hp_completeSpace D
  letI : CompleteSpace (ℂ ∙ generator D z) := FiniteDimensional.complete ℂ _
  exact Submodule.starProjection_eq_self_iff.mpr
    (Submodule.mem_span_singleton_self _)

theorem generatorProjector_expectation_self (z : A × A)
    (hstrict : exchangeOverlap D z < productWeight D z) :
    normalizedExpectation (generatorProjector D z) (generator D z) = 1 := by
  have hg := (strict_pair_facts D z hstrict).2.1
  have hn : ‖generator D z‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hg)
  have hinner : (inner ℂ (generator D z) (generator D z)).re =
      ‖generator D z‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) (generator D z)).symm
  rw [normalizedExpectation, generatorProjector_self, hinner]
  exact div_self hn

theorem generatorProjector_expectation_exchange (z : A × A) :
    normalizedExpectation (generatorProjector D z) (exchange D (generator D z)) =
      (exchangeOverlap D z / productWeight D z) ^ 2 := by
  have hs : inner ℂ (exchange D (generator D z)) (generator D z) =
      (exchangeOverlap D z : ℂ) := by
    rw [← inner_conj_symm, inner_exchange_generator]
    simp
  letI : CompleteSpace (Hp D) := hp_completeSpace D
  letI : CompleteSpace (ℂ ∙ generator D z) := FiniteDimensional.complete ℂ _
  have hp : generatorProjector D z (exchange D (generator D z)) =
      ((exchangeOverlap D z / productWeight D z : ℝ) : ℂ) • generator D z := by
    rw [generatorProjector, Submodule.starProjection_singleton,
      inner_exchange_generator, norm_generator_sq]
    simp only [Complex.ofReal_div, productWeight]
    rfl
  rw [normalizedExpectation, hp, inner_smul_right, hs, (exchange D).norm_map,
    norm_generator_sq]
  change (((exchangeOverlap D z / productWeight D z : ℝ) : ℂ) *
    (exchangeOverlap D z : ℂ)).re / productWeight D z = _
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  ring

theorem generatorProjector_expectation_exchange_lt_one (z : A × A)
    (hstrict : exchangeOverlap D z < productWeight D z) :
    normalizedExpectation (generatorProjector D z) (exchange D (generator D z)) < 1 := by
  rw [generatorProjector_expectation_exchange D z]
  have hq := (strict_pair_facts D z hstrict).1
  have hr : 0 ≤ exchangeOverlap D z := Complex.normSq_nonneg _
  have hnonneg : 0 ≤ exchangeOverlap D z / productWeight D z := div_nonneg hr hq.le
  have hlt : exchangeOverlap D z / productWeight D z < 1 :=
    (div_lt_one hq).mpr hstrict
  nlinarith

/-- The discriminator forbids any complex scalar relation for a strict pair. -/
theorem exchange_not_scalar (z : A × A)
    (hstrict : exchangeOverlap D z < productWeight D z) :
    ¬ ∃ c : ℂ, exchange D (generator D z) = c • generator D z := by
  rintro ⟨c, hc⟩
  have hg := (strict_pair_facts D z hstrict).2.1
  have hsg : exchange D (generator D z) ≠ 0 := by
    intro hz
    exact hg ((exchange D).injective (by simpa using hz))
  have hcz : c ≠ 0 := by
    intro hz
    apply hsg
    simp [hc, hz]
  have he := normalizedExpectation_scalar (generatorProjector D z) c hcz (generator D z)
  rw [← hc, generatorProjector_expectation_self D z hstrict] at he
  have hl := generatorProjector_expectation_exchange_lt_one D z hstrict
  linarith

/-- One and the same strict generator has both sectors and the stated responses. -/
theorem strict_pair_observation_boundary (z : A × A)
    (hstrict : exchangeOverlap D z < productWeight D z) :
    generator D z ≠ 0 ∧
    plus D (generator D z) ≠ 0 ∧ minus D (generator D z) ≠ 0 ∧
    (∀ E : Hp D →L[ℂ] Hp D,
      (∀ u, E (exchange D u) = exchange D (E u)) →
      inner ℂ (exchange D (generator D z)) (E (exchange D (generator D z))) =
        inner ℂ (generator D z) (E (generator D z)) ∧
      normalizedExpectation E (exchange D (generator D z)) =
        normalizedExpectation E (generator D z)) ∧
    (generatorProjector D z).IsPositive ∧ generatorProjector D z ≤ 1 ∧
    ‖generatorProjector D z‖ ≤ 1 ∧
    normalizedExpectation (generatorProjector D z) (generator D z) = 1 ∧
    normalizedExpectation (generatorProjector D z) (exchange D (generator D z)) =
      (exchangeOverlap D z / productWeight D z) ^ 2 ∧
    normalizedExpectation (generatorProjector D z) (exchange D (generator D z)) < 1 ∧
    ¬ ∃ c : ℂ, exchange D (generator D z) = c • generator D z := by
  obtain ⟨_, hg, hp, hm⟩ := strict_pair_facts D z hstrict
  refine ⟨hg, hp, hm, ?_, generatorProjector_positive D z,
    generatorProjector_le_one D z, generatorProjector_norm_le D z,
    generatorProjector_expectation_self D z hstrict,
    generatorProjector_expectation_exchange D z,
    generatorProjector_expectation_exchange_lt_one D z hstrict,
    exchange_not_scalar D z hstrict⟩
  intro E hcomm
  exact ⟨inner_invariant (exchange D) E hcomm _,
    normalizedExpectation_invariant (exchange D) E hcomm _⟩

/-- Nontrivial minus range supplies a strict pair, never unconditional existence. -/
theorem minus_range_observation_witness (hminus : (minus D).range ≠ ⊥) :
    ∃ z : A × A, exchangeOverlap D z < productWeight D z ∧
      generator D z ≠ 0 ∧ plus D (generator D z) ≠ 0 ∧
      minus D (generator D z) ≠ 0 ∧
      (∀ E : Hp D →L[ℂ] Hp D,
        (∀ u, E (exchange D u) = exchange D (E u)) →
        inner ℂ (exchange D (generator D z)) (E (exchange D (generator D z))) =
          inner ℂ (generator D z) (E (generator D z)) ∧
        normalizedExpectation E (exchange D (generator D z)) =
          normalizedExpectation E (generator D z)) ∧
      (generatorProjector D z).IsPositive ∧ generatorProjector D z ≤ 1 ∧
      ‖generatorProjector D z‖ ≤ 1 ∧
      normalizedExpectation (generatorProjector D z) (generator D z) = 1 ∧
      normalizedExpectation (generatorProjector D z) (exchange D (generator D z)) =
        (exchangeOverlap D z / productWeight D z) ^ 2 ∧
      normalizedExpectation (generatorProjector D z) (exchange D (generator D z)) < 1 ∧
      ¬ ∃ c : ℂ, exchange D (generator D z) = c • generator D z := by
  obtain ⟨x, y, hxy⟩ := (minus_range_ne_bot_iff D).mp hminus
  have hs : exchangeOverlap D (x, y) < productWeight D (x, y) := hxy
  obtain ⟨hg, hp, hm, hcomm, hpos, hle, hn, hself, hex, hlt, hscalar⟩ :=
    strict_pair_observation_boundary D (x, y) hs
  exact ⟨(x, y), hs, hg, hp, hm, hcomm, hpos, hle, hn, hself, hex, hlt, hscalar⟩

inductive BoundaryRole where
  | allWeightedOrderedProductAssumptionsSupplied
  | constructedProductGeneratedSpanOnly
  | responseEqualityOnlyForExchangeRelatedPair
  | mathematicalProjectorNotNativeEffectAvailability
  | noProbabilityLawOrBornInput
  | noSectorSpeciesSpinStatisticsOrActualization
  | noRawGlobalExchangeOrTargetExhaustion
  | allMatterRegimesUnassessed
  | noQMOrManifestUpgrade
  deriving DecidableEq, Repr

end

end IDT.QMClosure.ProductExchangeObservationBoundary
