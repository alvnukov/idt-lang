import Proofs.QMClosure.CanonicalQuadraticHilbert
import Proofs.QMClosure.PairExchangeCombinations
import Proofs.QMClosure.EqualGramSpanEquivalence
import Proofs.QMClosure.UnitaryInvolutionProjections

namespace IDT.QMClosure.ProductFeatureExchange

open QuadraticRecordRefinement PositiveQuadraticPolarization QuadraticHermitianKernel

noncomputable section

/-!
This conditional construction acts only on the closed complex span of supplied
ordered-product features in the auxiliary Hilbert space constructed from QC.
Every product/readout and phase compatibility premise remains supplied. The
construction supplies neither a raw carrier exchange nor physical exchange,
product availability, exchange-sign selection, spin-statistics, actualization,
matter applicability, full target exhaustion, or full QM.
-/

variable {A C : Type*} [AddCommGroup A] [AddCommGroup C]

/-- Supplied weighted ordered-product data; none of these bridges is derived here. -/
structure Bridge (A C : Type*) [AddCommGroup A] [AddCommGroup C] where
  QA : A → ℝ
  QC : C → ℝ
  hA : PositiveQuadratic QA
  hC : PositiveQuadratic QC
  jA : QuadraticPhase QA
  jC : QuadraticPhase QC
  p : A → A → C
  addA : ∀ x x' y, p (x + x') y = p x y + p x' y
  addB : ∀ x y y', p x (y + y') = p x y + p x y'
  phaseA : ∀ x y, p (jA.J x) y = jC.J (p x y)
  phaseB : ∀ x y, p x (jA.J y) = jC.J (p x y)
  factor : ∀ x y, QC (p x y) = QA x * QA y

variable (D : Bridge A C)

/-- Constructed auxiliary output, never a supplied physical Hilbert space. -/
abbrev H := CanonicalQuadraticHilbert.Hilbert D.hC D.jC

def productFeature (z : A × A) : H D :=
  CanonicalQuadraticHilbert.feature D.hC D.jC (D.p z.1 z.2)

/-- The exchange domain is only the product-generated closed subspace. -/
abbrev Hp := EqualGramSpanEquivalence.closedSpan (productFeature D)

instance hp_completeSpace : CompleteSpace (Hp D) :=
  EqualGramSpanEquivalence.closedSpan_completeSpace (productFeature D)

instance hp_clmStar : Star (Hp D →L[ℂ] Hp D) :=
  @ContinuousLinearMap.instStarId ℂ (Hp D) _ _ _ (hp_completeSpace D)

def generator (z : A × A) : Hp D :=
  EqualGramSpanEquivalence.spanGenerator (productFeature D) z

theorem dense_generator :
    Dense (Submodule.span ℂ (Set.range (generator D)) : Set (Hp D)) :=
  EqualGramSpanEquivalence.dense_spanGenerator (productFeature D)

private theorem swapped_range :
    Set.range (fun z : A × A => generator D z.swap) = Set.range (generator D) := by
  ext u
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.swap, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z.swap, by simp⟩

private theorem dense_swapped_generator :
    Dense (Submodule.span ℂ (Set.range (fun z : A × A => generator D z.swap)) :
      Set (Hp D)) := by
  rw [swapped_range]
  exact dense_generator D

theorem inner_generator (z w : A × A) :
    inner ℂ (generator D z) (generator D w) =
      kernel D.jA z.1 w.1 * kernel D.jA z.2 w.2 := by
  change inner ℂ (CanonicalQuadraticHilbert.feature D.hC D.jC (D.p z.1 z.2))
    (CanonicalQuadraticHilbert.feature D.hC D.jC (D.p w.1 w.2)) = _
  rw [CanonicalQuadraticHilbert.inner_feature]
  exact CompositeProductKernel.product_kernel D.hA D.hC D.jA D.jA D.jC D.p
    D.addA D.addB D.phaseA D.phaseB D.factor z.1 w.1 z.2 w.2

theorem equalGram (z w : A × A) :
    inner ℂ (generator D z) (generator D w) =
      inner ℂ (generator D z.swap) (generator D w.swap) := by
  rw [inner_generator, inner_generator]
  exact mul_comm _ _

/-- The uniquely determined exchange isometry on the product-generated span. -/
def exchange : Hp D ≃ₗᵢ[ℂ] Hp D :=
  @EqualGramSpanEquivalence.denseEquivalence (A × A) (Hp D) (Hp D)
    _ _ _ _ (hp_completeSpace D) (hp_completeSpace D) (generator D)
    (fun z => generator D z.swap) (dense_generator D) (dense_swapped_generator D)
    (equalGram D)

theorem exchange_generator (z : A × A) :
    exchange D (generator D z) = generator D z.swap :=
  @EqualGramSpanEquivalence.denseEquivalence_apply (A × A) (Hp D) (Hp D)
    _ _ _ _ (hp_completeSpace D) (hp_completeSpace D) (generator D)
    (fun z => generator D z.swap) (dense_generator D) (dense_swapped_generator D)
    (equalGram D) z

theorem exchange_unique (U : Hp D ≃ₗᵢ[ℂ] Hp D)
    (hU : ∀ z, U (generator D z) = generator D z.swap) : U = exchange D := by
  apply EqualGramSpanEquivalence.dense_generator_ext (generator D) (dense_generator D)
  intro z
  rw [hU, exchange_generator]

theorem exchange_involutive : Function.Involutive (exchange D) := by
  have he : (exchange D).trans (exchange D) = LinearIsometryEquiv.refl ℂ (Hp D) := by
    apply EqualGramSpanEquivalence.dense_generator_ext (generator D) (dense_generator D)
    intro z
    change exchange D (exchange D (generator D z)) = generator D z
    rw [exchange_generator, exchange_generator, Prod.swap_swap]
  intro u
  exact congrArg (fun U : Hp D ≃ₗᵢ[ℂ] Hp D => U u) he

abbrev plus := UnitaryInvolutionProjections.plus (exchange D)
abbrev minus := UnitaryInvolutionProjections.minus (exchange D)

theorem exchange_selfAdjoint :
    @IsSelfAdjoint (Hp D →L[ℂ] Hp D) (hp_clmStar D)
      (UnitaryInvolutionProjections.op (exchange D)) :=
  @UnitaryInvolutionProjections.op_selfAdjoint (Hp D) _ _ (hp_completeSpace D) (exchange D) (exchange_involutive D)

theorem plus_selfAdjoint : @IsSelfAdjoint (Hp D →L[ℂ] Hp D) (hp_clmStar D) (plus D) :=
  @UnitaryInvolutionProjections.plus_selfAdjoint (Hp D) _ _ (hp_completeSpace D) (exchange D) (exchange_involutive D)

theorem minus_selfAdjoint : @IsSelfAdjoint (Hp D →L[ℂ] Hp D) (hp_clmStar D) (minus D) :=
  @UnitaryInvolutionProjections.minus_selfAdjoint (Hp D) _ _ (hp_completeSpace D) (exchange D) (exchange_involutive D)

theorem plus_idempotent : IsIdempotentElem (plus D) :=
  UnitaryInvolutionProjections.plus_idempotent (exchange D) (exchange_involutive D)

theorem minus_idempotent : IsIdempotentElem (minus D) :=
  UnitaryInvolutionProjections.minus_idempotent (exchange D) (exchange_involutive D)

theorem plus_range_closed : IsClosed ((plus D).range : Set (Hp D)) :=
  UnitaryInvolutionProjections.range_plus_closed (exchange D) (exchange_involutive D)

theorem minus_range_closed : IsClosed ((minus D).range : Set (Hp D)) :=
  UnitaryInvolutionProjections.range_minus_closed (exchange D) (exchange_involutive D)

/-- Unnormalized raw plus feature, regarded as a member of Hp. -/
def plusGenerator (z : A × A) : Hp D := generator D z + generator D z.swap

/-- Unnormalized raw minus feature, regarded as a member of Hp. -/
def minusGenerator (z : A × A) : Hp D := generator D z - generator D z.swap

theorem coe_plusGenerator (z : A × A) :
    (plusGenerator D z : H D) = CanonicalQuadraticHilbert.feature D.hC D.jC
      (PairExchangeCombinations.plusPair D.p z.1 z.2) := by
  change CanonicalQuadraticHilbert.feature D.hC D.jC (D.p z.1 z.2) +
    CanonicalQuadraticHilbert.feature D.hC D.jC (D.p z.2 z.1) = _
  exact (CanonicalQuadraticHilbert.feature_add D.hC D.jC _ _).symm

theorem coe_minusGenerator (z : A × A) :
    (minusGenerator D z : H D) = CanonicalQuadraticHilbert.feature D.hC D.jC
      (PairExchangeCombinations.minusPair D.p z.1 z.2) := by
  change CanonicalQuadraticHilbert.featureHom D.hC D.jC (D.p z.1 z.2) -
    CanonicalQuadraticHilbert.featureHom D.hC D.jC (D.p z.2 z.1) =
      CanonicalQuadraticHilbert.featureHom D.hC D.jC (D.p z.1 z.2 - D.p z.2 z.1)
  exact (map_sub (CanonicalQuadraticHilbert.featureHom D.hC D.jC) _ _).symm

theorem plus_generator (z : A × A) :
    plus D (generator D z) = (1 / 2 : ℂ) • plusGenerator D z := by
  rw [UnitaryInvolutionProjections.plus_apply, exchange_generator]
  rfl

theorem minus_generator (z : A × A) :
    minus D (generator D z) = (1 / 2 : ℂ) • minusGenerator D z := by
  rw [UnitaryInvolutionProjections.minus_apply, exchange_generator]
  rfl

theorem coe_plus_generator (z : A × A) :
    (plus D (generator D z) : H D) = (1 / 2 : ℂ) •
      CanonicalQuadraticHilbert.feature D.hC D.jC
        (PairExchangeCombinations.plusPair D.p z.1 z.2) := by
  rw [plus_generator]
  exact congrArg ((1 / 2 : ℂ) • ·) (coe_plusGenerator D z)

theorem coe_minus_generator (z : A × A) :
    (minus D (generator D z) : H D) = (1 / 2 : ℂ) •
      CanonicalQuadraticHilbert.feature D.hC D.jC
        (PairExchangeCombinations.minusPair D.p z.1 z.2) := by
  rw [minus_generator]
  exact congrArg ((1 / 2 : ℂ) • ·) (coe_minusGenerator D z)

theorem norm_generator_sq (z : A × A) :
    ‖generator D z‖ ^ 2 = D.QA z.1 * D.QA z.2 := by
  change ‖CanonicalQuadraticHilbert.feature D.hC D.jC (D.p z.1 z.2)‖ ^ 2 = _
  rw [CanonicalQuadraticHilbert.norm_feature_sq, D.factor]

theorem re_inner_exchange_generator (z : A × A) :
    (inner ℂ (generator D z) (exchange D (generator D z))).re =
      Complex.normSq (kernel D.jA z.1 z.2) := by
  rw [exchange_generator]
  change (inner ℂ (CanonicalQuadraticHilbert.feature D.hC D.jC (D.p z.1 z.2))
    (CanonicalQuadraticHilbert.feature D.hC D.jC (D.p z.2 z.1))).re = _
  rw [CanonicalQuadraticHilbert.inner_feature, kernel_re]
  exact PairExchangeCombinations.cross_polarization D.hA D.hC D.jA D.jC D.p
    D.addA D.addB D.phaseA D.phaseB D.factor z.1 z.2

theorem plus_generator_norm_sq (z : A × A) :
    ‖plus D (generator D z)‖ ^ 2 =
      (D.QA z.1 * D.QA z.2 + Complex.normSq (kernel D.jA z.1 z.2)) / 2 := by
  rw [UnitaryInvolutionProjections.plus_norm_sq, norm_generator_sq,
    re_inner_exchange_generator]

theorem minus_generator_norm_sq (z : A × A) :
    ‖minus D (generator D z)‖ ^ 2 =
      (D.QA z.1 * D.QA z.2 - Complex.normSq (kernel D.jA z.1 z.2)) / 2 := by
  rw [UnitaryInvolutionProjections.minus_norm_sq, norm_generator_sq,
    re_inner_exchange_generator]

private theorem span_half (f : A × A → Hp D) :
    Submodule.span ℂ (Set.range (fun z => (1 / 2 : ℂ) • f z)) =
      Submodule.span ℂ (Set.range f) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self z))
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    have h := Submodule.smul_mem
      (Submodule.span ℂ (Set.range (fun z => (1 / 2 : ℂ) • f z))) (2 : ℂ)
      (Submodule.subset_span (Set.mem_range_self z))
    simpa only [smul_smul, show (2 : ℂ) * (1 / 2 : ℂ) = 1 by norm_num,
      one_smul] using h

theorem plus_range_eq_closedSpan :
    (plus D).range = EqualGramSpanEquivalence.closedSpan (plusGenerator D) := by
  rw [UnitaryInvolutionProjections.plus_range_eq_closedSpan
    (exchange D) (exchange_involutive D) (generator D) (dense_generator D)]
  change (Submodule.span ℂ (Set.range (fun z => plus D (generator D z)))).topologicalClosure =
    (Submodule.span ℂ (Set.range (plusGenerator D))).topologicalClosure
  have heq : (fun z => plus D (generator D z)) =
      (fun z => (1 / 2 : ℂ) • plusGenerator D z) := funext (plus_generator D)
  rw [heq, span_half]

theorem minus_range_eq_closedSpan :
    (minus D).range = EqualGramSpanEquivalence.closedSpan (minusGenerator D) := by
  rw [UnitaryInvolutionProjections.minus_range_eq_closedSpan
    (exchange D) (exchange_involutive D) (generator D) (dense_generator D)]
  change (Submodule.span ℂ (Set.range (fun z => minus D (generator D z)))).topologicalClosure =
    (Submodule.span ℂ (Set.range (minusGenerator D))).topologicalClosure
  have heq : (fun z => minus D (generator D z)) =
      (fun z => (1 / 2 : ℂ) • minusGenerator D z) := funext (minus_generator D)
  rw [heq, span_half]

theorem plus_add_minus (u : Hp D) : plus D u + minus D u = u := by
  have he := UnitaryInvolutionProjections.plus_add_minus (exchange D)
  exact congrArg (fun P : Hp D →L[ℂ] Hp D => P u) he

theorem mixed_inner (u v : Hp D) : inner ℂ (plus D u) (minus D v) = 0 :=
  @UnitaryInvolutionProjections.mixed_inner (Hp D) _ _ (hp_completeSpace D) (exchange D) (exchange_involutive D) u v

theorem orthogonal_decomposition (u : Hp D) :
    ∃ uplus ∈ (plus D).range, ∃ uminus ∈ (minus D).range,
      u = uplus + uminus ∧ inner ℂ uplus uminus = 0 := by
  exact ⟨plus D u, ⟨u, rfl⟩, minus D u, ⟨u, rfl⟩,
    (plus_add_minus D u).symm, mixed_inner D u u⟩

/-- Exact nontriviality criterion, with no assumed orthogonal-pair witness. -/
theorem minus_range_ne_bot_iff :
    (minus D).range ≠ ⊥ ↔
      ∃ x y, Complex.normSq (kernel D.jA x y) < D.QA x * D.QA y := by
  rw [UnitaryInvolutionProjections.range_ne_bot_iff (minus D) (generator D)
    (dense_generator D)]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z.1, z.2, ?_⟩
    have hn : 0 < ‖minus D (generator D z)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
    rw [minus_generator_norm_sq] at hn
    linarith
  · rintro ⟨x, y, hxy⟩
    refine ⟨(x, y), ?_⟩
    intro hz
    have hn := minus_generator_norm_sq D (x, y)
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hn
    dsimp at hn
    linarith

/-- No physical or whole-target interpretation is part of this theorem cluster. -/
inductive BoundaryRole where
  | allWeightedBridgeAssumptionsRemainSupplied
  | constructedAuxiliaryHilbertOnly
  | productGeneratedClosedSpanOnly
  | noRawCarrierExchangeOrRawHalf
  | noPhysicalExchangeProjectionOrProductAvailability
  | noExchangeSignSpeciesOrSpinStatisticsSelection
  | allMatterRegimesUnassessed
  | noActualizationFullQMOrManifestUpgrade
  deriving DecidableEq, Repr

end

end IDT.QMClosure.ProductFeatureExchange
