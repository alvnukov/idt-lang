import Proofs.QMClosure.NativeIsotropicGaussianFamily
import Proofs.QMClosure.NativeStationaryNoiseCharacterization

/-!
# A first-marginal native process on a preparation family

Probability preparations on the supplied real two-coordinate carrier are equipped
with a raw operation whose square swaps the inputs. Only the first marginal of
the supplied native mixer is assumed. Gaussianity, common coordinate variance,
full output independence, and diagonal transparency of preparation laws follow.
A non-Dirac member then supplies the finite entropy needed by the classical
statistical-process bridge on the observed preparation range. The carrier and
native mixing channel remain supplied mathematical inputs.
-/

namespace IDT.QMClosure.NativeMarginalProcessBridge

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal ENNReal

abbrev Sample := NativeGaussianStatisticalProcess.Sample
abbrev PairSample := Sample × Sample
abbrev G := NativeGaussianStatisticalProcess.G
abbrev firstOutput := NativeStationaryNoiseCharacterization.firstOutput

def secondOutput : PairSample →L[ℝ] Sample :=
  (ContinuousLinearMap.snd ℝ Sample Sample).comp G

universe u

/-- Weak family data, with only one observed output marginal supplied. -/
structure Contract (V : Type u) where
  preparation : V → Measure Sample
  probability : ∀ x, IsProbabilityMeasure (preparation x)
  operation : V × V → V × V
  square : ∀ p, operation (operation p) = p.swap
  firstMarginal : ∀ p,
    ((preparation p.1).prod (preparation p.2)).map firstOutput =
      preparation (operation p).1

namespace Contract

variable {V : Type u} (D : Contract V)

/-- The square law forces the raw operation to commute with swapping. -/
theorem operation_swap (p : V × V) : D.operation p.swap = (D.operation p).swap := by
  calc
    D.operation p.swap = D.operation (D.operation (D.operation p)) :=
      congrArg D.operation (D.square p).symm
    _ = (D.operation p).swap := D.square (D.operation p)

def diagonalPartner (x : V) : V := (D.operation (x, x)).1

theorem operation_diagonal (x : V) :
    D.operation (x, x) = (D.diagonalPartner x, D.diagonalPartner x) := by
  have h := congrArg Prod.fst (D.operation_swap (x, x))
  apply Prod.ext
  · rfl
  · exact h.symm

theorem operation_partner_diagonal (x : V) :
    D.operation (D.diagonalPartner x, D.diagonalPartner x) = (x, x) := by
  rw [← D.operation_diagonal, D.square]
  rfl

/-- Raw diagonal labels may cycle, but their laws obey two-step smoothing. -/
theorem twoStepStationary (x : V) :
    NativeStationaryNoiseCharacterization.TwoStepStationary (D.preparation x) := by
  change NativeStationaryNoiseCharacterization.smoothing
    (NativeStationaryNoiseCharacterization.smoothing (D.preparation x)) = D.preparation x
  have hfirst : NativeStationaryNoiseCharacterization.smoothing (D.preparation x) =
      D.preparation (D.diagonalPartner x) := D.firstMarginal (x, x)
  rw [hfirst]
  change ((D.preparation (D.diagonalPartner x)).prod
    (D.preparation (D.diagonalPartner x))).map firstOutput = D.preparation x
  simpa only [D.operation_partner_diagonal] using
    D.firstMarginal (D.diagonalPartner x, D.diagonalPartner x)

/-- Actual coordinate means of a preparation. -/
def mean (x : V) : Sample :=
  (∫ s : Sample, s.1 ∂D.preparation x, ∫ s : Sample, s.2 ∂D.preparation x)

/-- Actual coordinate variance, shown below to be common across the family. -/
def coordinateVariance (x : V) : ℝ≥0 :=
  (variance Prod.fst (D.preparation x)).toNNReal

theorem preparation_eq_gaussian (x : V) :
    D.preparation x = NativeIsotropicGaussianFamily.preparation
      (D.coordinateVariance x) (D.mean x) := by
  letI : IsProbabilityMeasure (D.preparation x) := D.probability x
  exact NativeStationaryNoiseCharacterization.eq_product_gaussian_of_twoStepStationary
    (D.preparation x) (D.twoStepStationary x)

theorem G_swap (s : PairSample) : G s.swap = (G s).swap := by
  ext <;> simp [NativeGaussianStatisticalProcess.G_apply] <;> ring

private theorem firstOutput_swap :
    (fun s : PairSample => firstOutput s.swap) = secondOutput := by
  funext s
  change (G s.swap).1 = (G s).2
  rw [G_swap]
  rfl

/-- Ordered first-marginal covariance also fixes the second marginal. -/
theorem secondMarginal (p : V × V) :
    ((D.preparation p.1).prod (D.preparation p.2)).map secondOutput =
      D.preparation (D.operation p).2 := by
  letI (x : V) : IsProbabilityMeasure (D.preparation x) := D.probability x
  have h := D.firstMarginal p.swap
  rw [← Measure.prod_swap, Measure.map_map (by fun_prop) measurable_swap] at h
  simpa only [Function.comp_def, firstOutput_swap, D.operation_swap] using h

-- These parameter theorems use the helper's preparation_ext_iff API.
theorem output_first_parameters (p : V × V) :
    D.coordinateVariance (D.operation p).1 =
        (D.coordinateVariance p.1 + D.coordinateVariance p.2) / 2 ∧
      D.mean (D.operation p).1 = (G (D.mean p.1, D.mean p.2)).1 := by
  have h := D.firstMarginal p
  rw [D.preparation_eq_gaussian p.1, D.preparation_eq_gaussian p.2,
    D.preparation_eq_gaussian (D.operation p).1,
    show firstOutput = NativeIsotropicGaussianFamily.first from rfl,
    NativeIsotropicGaussianFamily.map_first_preparation_prod] at h
  exact ((NativeIsotropicGaussianFamily.preparation_ext_iff _ _ _ _).mp h.symm)

theorem output_second_parameters (p : V × V) :
    D.coordinateVariance (D.operation p).2 =
        (D.coordinateVariance p.1 + D.coordinateVariance p.2) / 2 ∧
      D.mean (D.operation p).2 = (G (D.mean p.1, D.mean p.2)).2 := by
  have h := D.secondMarginal p
  rw [D.preparation_eq_gaussian p.1, D.preparation_eq_gaussian p.2,
    D.preparation_eq_gaussian (D.operation p).2,
    show secondOutput = NativeIsotropicGaussianFamily.second from rfl,
    NativeIsotropicGaussianFamily.map_second_preparation_prod] at h
  exact ((NativeIsotropicGaussianFamily.preparation_ext_iff _ _ _ _).mp h.symm)

/-- Applying both marginal variance laws twice forces a single family variance. -/
theorem coordinateVariance_eq (x y : V) :
    D.coordinateVariance x = D.coordinateVariance y := by
  have h₁ := (D.output_first_parameters (x, y)).1
  have h₂ := (D.output_second_parameters (x, y)).1
  have h₃ := (D.output_first_parameters (D.operation (x, y))).1
  rw [D.square] at h₃
  have hr₁ := congrArg (fun v : ℝ≥0 => (v : ℝ)) h₁
  have hr₂ := congrArg (fun v : ℝ≥0 => (v : ℝ)) h₂
  have hr₃ := congrArg (fun v : ℝ≥0 => (v : ℝ)) h₃
  simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_ofNat, Prod.fst_swap]
    at hr₁ hr₂ hr₃
  apply NNReal.coe_injective
  linarith

theorem mean_compatibility (p : V × V) :
    G (D.mean p.1, D.mean p.2) =
      (D.mean (D.operation p).1, D.mean (D.operation p).2) := by
  exact Prod.ext (D.output_first_parameters p).2.symm
    (D.output_second_parameters p).2.symm

/-- Equal actual means identify exactly the observed preparation laws. -/
theorem mean_eq_iff_preparation_eq (x y : V) :
    D.mean x = D.mean y ↔ D.preparation x = D.preparation y := by
  rw [D.preparation_eq_gaussian x, D.preparation_eq_gaussian y,
    NativeIsotropicGaussianFamily.preparation_ext_iff]
  exact ⟨fun h => ⟨D.coordinateVariance_eq x y, h⟩, And.right⟩

/-- Full covariance, including output independence, follows at the common variance. -/
theorem map_preparation_prod (p : V × V) :
    ((D.preparation p.1).prod (D.preparation p.2)).map G =
      (D.preparation (D.operation p).1).prod (D.preparation (D.operation p).2) := by
  simp only [D.preparation_eq_gaussian]
  rw [D.coordinateVariance_eq p.2 p.1,
    D.coordinateVariance_eq (D.operation p).1 p.1,
    D.coordinateVariance_eq (D.operation p).2 p.1,
    NativeIsotropicGaussianFamily.map_preparation_prod, D.mean_compatibility]

/-- Transparency concerns preparation laws, without asserting raw-label equality. -/
theorem preparation_diagonal (x : V) :
    D.preparation (D.operation (x, x)).1 = D.preparation x := by
  have hm := (D.output_first_parameters (x, x)).2
  rw [NativeIsotropicGaussianFamily.G_diagonal] at hm
  rw [D.preparation_eq_gaussian, D.preparation_eq_gaussian,
    D.coordinateVariance_eq (D.operation (x, x)).1 x, hm]

abbrev Observed := Set.range D.preparation

private def representative (x : D.Observed) : V := Classical.choose x.property

private theorem representative_spec (x : D.Observed) :
    D.preparation (D.representative x) = x.val := Classical.choose_spec x.property

/-- The observed operation has exact marginal laws independent of representatives. -/
def observedOperation (p : D.Observed × D.Observed) : D.Observed × D.Observed :=
  let out := D.operation (D.representative p.1, D.representative p.2)
  (⟨D.preparation out.1, ⟨out.1, rfl⟩⟩, ⟨D.preparation out.2, ⟨out.2, rfl⟩⟩)

theorem observedOperation_first (p : D.Observed × D.Observed) :
    (D.observedOperation p).1.val = (p.1.val.prod p.2.val).map firstOutput := by
  change D.preparation (D.operation (D.representative p.1, D.representative p.2)).1 = _
  rw [← D.firstMarginal, D.representative_spec, D.representative_spec]

theorem observedOperation_second (p : D.Observed × D.Observed) :
    (D.observedOperation p).2.val = (p.1.val.prod p.2.val).map secondOutput := by
  change D.preparation (D.operation (D.representative p.1, D.representative p.2)).2 = _
  rw [← D.secondMarginal, D.representative_spec, D.representative_spec]

def observe (x : V) : D.Observed :=
  ⟨D.preparation x, ⟨x, rfl⟩⟩

theorem observedOperation_preparations (x y : V) :
    D.observedOperation (D.observe x, D.observe y) =
      (D.observe (D.operation (x, y)).1,
        D.observe (D.operation (x, y)).2) := by
  apply Prod.ext
  · apply Subtype.ext
    exact (D.observedOperation_first _).trans (D.firstMarginal (x, y))
  · apply Subtype.ext
    exact (D.observedOperation_second _).trans (D.secondMarginal (x, y))

theorem observedOperation_square (p : D.Observed × D.Observed) :
    D.observedOperation (D.observedOperation p) = p.swap := by
  obtain ⟨x, hx⟩ := p.1.property
  obtain ⟨y, hy⟩ := p.2.property
  have hp : p = (D.observe x, D.observe y) :=
    Prod.ext (Subtype.ext hx.symm) (Subtype.ext hy.symm)
  rw [hp, D.observedOperation_preparations, D.observedOperation_preparations, D.square]
  rfl

theorem observedOperation_transparent (x : D.Observed) :
    D.observedOperation (x, x) = (x, x) := by
  obtain ⟨y, hy⟩ := x.property
  have hx : x = D.observe y := Subtype.ext hy.symm
  rw [hx, D.observedOperation_preparations]
  apply Prod.ext
  · exact Subtype.ext (D.preparation_diagonal y)
  · apply Subtype.ext
    have h := congrArg (fun p : V × V => D.preparation p.2) (D.operation_diagonal y)
    exact h.trans (D.preparation_diagonal y)

/-- A non-Dirac member rules out the common zero-variance branch. -/
theorem commonVariance_pos_of_nonDirac (x₀ xₙ : V)
    (h : ∀ m : Sample, D.preparation xₙ ≠ Measure.dirac m) :
    0 < D.coordinateVariance x₀ := by
  by_contra hn
  have hz : D.coordinateVariance x₀ = 0 := le_antisymm (not_lt.mp hn) bot_le
  apply h (D.mean xₙ)
  rw [D.preparation_eq_gaussian, D.coordinateVariance_eq xₙ x₀, hz]
  exact NativeIsotropicGaussianFamily.preparation_zero _

/-- At zero common variance, even one-way absolute continuity forces equal laws. -/
theorem preparation_eq_of_ac_of_zeroVariance (x y : V)
    (hz : D.coordinateVariance x = 0)
    (hac : D.preparation x ≪ D.preparation y) :
    D.preparation x = D.preparation y := by
  have hzy : D.coordinateVariance y = 0 := (D.coordinateVariance_eq y x).trans hz
  have hx := D.preparation_eq_gaussian x
  have hy := D.preparation_eq_gaussian y
  rw [hz, NativeIsotropicGaussianFamily.preparation_zero] at hx
  rw [hzy, NativeIsotropicGaussianFamily.preparation_zero] at hy
  rw [hx, hy] at hac ⊢
  have hm : D.mean x = D.mean y := by
    by_contra hmn
    have hzero : Measure.dirac (D.mean y) {D.mean x} = 0 := by
      simp [Ne.symm hmn]
    have hbad := hac hzero
    simp at hbad
  rw [hm]

/-- Ordered entropy is finite exactly in the positive-variance or equal-law cases. -/
theorem klDiv_ne_top_iff (x y : V) :
    klDiv (D.preparation x) (D.preparation y) ≠ ∞ ↔
      0 < D.coordinateVariance x ∨ D.preparation x = D.preparation y := by
  constructor
  · intro h
    by_cases hv : 0 < D.coordinateVariance x
    · exact Or.inl hv
    · exact Or.inr (D.preparation_eq_of_ac_of_zeroVariance x y
        (le_antisymm (not_lt.mp hv) bot_le)
        (InformationTheory.klDiv_ne_top_iff.mp h).1)
  · rintro (hv | heq)
    · rw [D.preparation_eq_gaussian x, D.preparation_eq_gaussian y,
        D.coordinateVariance_eq y x]
      exact NativeIsotropicGaussianFamily.klDiv_preparation_ne_top
        (D.coordinateVariance x) (ne_of_gt hv) _ _
    · letI : IsProbabilityMeasure (D.preparation y) := D.probability y
      rw [heq]
      simp

/-- All directed entropies are finite exactly at positive variance or for a constant family. -/
theorem finiteEntropy_iff (x₀ : V) :
    (∀ x y, klDiv (D.preparation x) (D.preparation y) ≠ ∞) ↔
      0 < D.coordinateVariance x₀ ∨ ∀ x y, D.preparation x = D.preparation y := by
  constructor
  · intro h
    by_cases hv : 0 < D.coordinateVariance x₀
    · exact Or.inl hv
    · right
      intro x y
      rcases (D.klDiv_ne_top_iff x y).mp (h x y) with hpos | heq
      · exact False.elim (hv ((D.coordinateVariance_eq x x₀) ▸ hpos))
      · exact heq
  · intro h x y
    apply (D.klDiv_ne_top_iff x y).mpr
    rcases h with hv | heq
    · exact Or.inl ((D.coordinateVariance_eq x x₀).symm ▸ hv)
    · exact Or.inr (heq x y)

/-- Finite ordered entropy is the precise entropy input to the observed bridge. -/
def observedContractOfFiniteEntropy (x₀ : V)
    (hfinite : ∀ x y, klDiv (D.preparation x) (D.preparation y) ≠ ∞) :
    ClassicalStatisticalProcessBridge.Contract D.Observed Sample where
  preparation := Subtype.val
  probability := fun x => by
    rw [← D.representative_spec x]
    exact D.probability _
  finiteEntropy := fun x y => by
    rw [← D.representative_spec x, ← D.representative_spec y]
    exact hfinite _ _
  chosenZero := D.observe x₀
  operation := D.observedOperation
  square := D.observedOperation_square
  transparent := D.observedOperation_transparent
  channel := NativeGaussianStatisticalProcess.channel
  markov := inferInstance
  covariance := fun p => by
    rw [NativeGaussianStatisticalProcess.channel, Measure.deterministic_comp_eq_map]
    rw [← D.representative_spec p.1, ← D.representative_spec p.2]
    exact D.map_preparation_prod (D.representative p.1, D.representative p.2)

/-- One-way domination by a reference law suffices for the observed classical bridge. -/
def observedContractOfReferenceAC (x₀ : V)
    (hdom : ∀ x, D.preparation x ≪ D.preparation x₀) :
    ClassicalStatisticalProcessBridge.Contract D.Observed Sample :=
  D.observedContractOfFiniteEntropy x₀ ((D.finiteEntropy_iff x₀).mpr (by
    by_cases hv : 0 < D.coordinateVariance x₀
    · exact Or.inl hv
    · right
      have hz : D.coordinateVariance x₀ = 0 := le_antisymm (not_lt.mp hv) bot_le
      intro x y
      have hx := D.preparation_eq_of_ac_of_zeroVariance x x₀
        ((D.coordinateVariance_eq x x₀).trans hz) (hdom x)
      have hy := D.preparation_eq_of_ac_of_zeroVariance y x₀
        ((D.coordinateVariance_eq y x₀).trans hz) (hdom y)
      exact hx.trans hy.symm))

/-- A non-Dirac member supplies finite ordered entropy at the common positive variance. -/
def observedContract (x₀ xₙ : V)
    (h : ∀ m : Sample, D.preparation xₙ ≠ Measure.dirac m) :
    ClassicalStatisticalProcessBridge.Contract D.Observed Sample :=
  D.observedContractOfFiniteEntropy x₀ (fun x y => by
    rw [D.preparation_eq_gaussian, D.preparation_eq_gaussian,
      D.coordinateVariance_eq x x₀, D.coordinateVariance_eq y x₀]
    exact NativeIsotropicGaussianFamily.klDiv_preparation_ne_top
      (D.coordinateVariance x₀) (ne_of_gt (D.commonVariance_pos_of_nonDirac x₀ xₙ h)) _ _)

/-- Constant families also have finite entropy, including the constant Dirac case. -/
def observedContractOfConstant (x₀ : V)
    (hconstant : ∀ x y, D.preparation x = D.preparation y) :
    ClassicalStatisticalProcessBridge.Contract D.Observed Sample :=
  D.observedContractOfFiniteEntropy x₀ (fun x y => by
    letI : IsProbabilityMeasure (D.preparation y) := D.probability y
    rw [hconstant x y]
    simp)

end Contract
end
end IDT.QMClosure.NativeMarginalProcessBridge
