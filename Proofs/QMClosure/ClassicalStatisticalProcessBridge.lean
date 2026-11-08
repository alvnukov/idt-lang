import Proofs.QMClosure.RelativeEntropyDataProcessing
import Proofs.QMClosure.PairComparisonReconstruction

/-!
# A common classical process supplies an additive pair comparison

A preparation is an ordinary probability measure on an arbitrary measurable space.
A single state-independent Markov kernel implements the complete binary operation
on every independent pair of preparations. All directed pairwise KL divergences
are finite. The symmetrized KL comparison is then nonexpanding under that operation.
Square-swap and the fixed diagonal feed the existing pair-comparison reconstruction.

Finite pairwise relative entropy is an explicit stronger input than positive affinity.
This route uses symmetrized KL directly and makes no identification with affinity.
The radial readout is defined by comparison to a chosen preparation. Identifying
it with an independent detector response remains a separate physical obligation.
No Born actualization or full QM closure follows from this conditional result.
-/

namespace IDT.QMClosure.ClassicalStatisticalProcessBridge

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open RelativeEntropyDataProcessing
open scoped ENNReal

universe u v
variable {V : Type u} {Ω : Type v} [MeasurableSpace Ω]

/-- Ordinary classical preparation/process data. The channel is common to every pair. -/
structure Contract (V : Type u) (Ω : Type v) [MeasurableSpace Ω] where
  preparation : V → Measure Ω
  probability : ∀ x, IsProbabilityMeasure (preparation x)
  finiteEntropy : ∀ x y, klDiv (preparation x) (preparation y) ≠ ∞
  chosenZero : V
  operation : V × V → V × V
  square : ∀ p, operation (operation p) = p.swap
  transparent : ∀ x, operation (x, x) = (x, x)
  channel : Kernel (Ω × Ω) (Ω × Ω)
  markov : IsMarkovKernel channel
  covariance : ∀ p, channel ∘ₘ ((preparation p.1).prod (preparation p.2)) =
    (preparation (operation p).1).prod (preparation (operation p).2)

namespace Contract

variable (D : Contract V Ω)

/-- The ordinary symmetrized relative entropy of two preparation measures. -/
def comparison (x y : V) : ℝ :=
  (klDiv (D.preparation x) (D.preparation y)).toReal +
    (klDiv (D.preparation y) (D.preparation x)).toReal

theorem comparison_symmetric (x y : V) : D.comparison x y = D.comparison y x :=
  add_comm _ _

theorem comparison_nonnegative (x y : V) : 0 ≤ D.comparison x y :=
  add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

theorem comparison_diagonal (x : V) : D.comparison x x = 0 := by
  letI : IsProbabilityMeasure (D.preparation x) := D.probability x
  simp [comparison]

/-- Product additivity is inherited from actual measure-theoretic KL. -/
theorem pairEntropy (p q : V × V) :
    klDiv ((D.preparation p.1).prod (D.preparation p.2))
      ((D.preparation q.1).prod (D.preparation q.2)) =
    klDiv (D.preparation p.1) (D.preparation q.1) +
      klDiv (D.preparation p.2) (D.preparation q.2) := by
  letI (x : V) : IsProbabilityMeasure (D.preparation x) := D.probability x
  exact klDiv_prod _ _ _ _

/-- One directed comparison contracts as a consequence of the common channel. -/
theorem directed_pair_nonexpanding (p q : V × V) :
    (klDiv (D.preparation (D.operation p).1) (D.preparation (D.operation q).1)).toReal +
      (klDiv (D.preparation (D.operation p).2) (D.preparation (D.operation q).2)).toReal ≤
    (klDiv (D.preparation p.1) (D.preparation q.1)).toReal +
      (klDiv (D.preparation p.2) (D.preparation q.2)).toReal := by
  letI (x : V) : IsProbabilityMeasure (D.preparation x) := D.probability x
  letI : IsMarkovKernel D.channel := D.markov
  have h := klDiv_markov_le ((D.preparation p.1).prod (D.preparation p.2))
    ((D.preparation q.1).prod (D.preparation q.2)) D.channel
  rw [D.covariance, D.covariance, D.pairEntropy, D.pairEntropy] at h
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨D.finiteEntropy _ _, D.finiteEntropy _ _⟩) h
  simpa only [ENNReal.toReal_add (D.finiteEntropy _ _) (D.finiteEntropy _ _)] using hreal

/-- No comparison-level data-processing inequality is assumed by the contract. -/
theorem comparison_nonexpanding :
    RawProcessComparisonBridge.PairComparisonNonexpanding D.comparison D.operation := by
  intro p q
  have hf := D.directed_pair_nonexpanding p q
  have hr := D.directed_pair_nonexpanding q p
  dsimp [RawProcessComparisonBridge.pairComparison, comparison]
  linarith

/-- The common classical process discharges the reconstruction's comparison premise. -/
def reconstruction : PairComparisonReconstruction.Contract V where
  chosenZero := D.chosenZero
  operation := D.operation
  comparison := D.comparison
  square := D.square
  transparent := D.transparent
  symmetric := D.comparison_symmetric
  nonnegative := D.comparison_nonnegative
  diagonal := D.comparison_diagonal
  nonexpanding := D.comparison_nonexpanding

abbrev Hilbert := D.reconstruction.Hilbert

def feature (x : V) : D.Hilbert := D.reconstruction.feature x

/-- The entire symmetrized relative entropy is reconstructed as squared distance. -/
theorem comparison_eq_norm_sub_sq (x y : V) :
    D.comparison x y = ‖D.feature x - D.feature y‖ ^ 2 :=
  D.reconstruction.comparison_eq_norm_sub_sq x y

/-- The new radial readout is comparison with the selected reference preparation. -/
theorem norm_feature_sq (x : V) :
    ‖D.feature x‖ ^ 2 = D.comparison x D.chosenZero :=
  D.reconstruction.norm_feature_sq x

/-- Zero comparison has its ordinary probabilistic meaning under finite entropy. -/
theorem comparison_eq_zero_iff (x y : V) :
    D.comparison x y = 0 ↔ D.preparation x = D.preparation y := by
  letI (x : V) : IsProbabilityMeasure (D.preparation x) := D.probability x
  constructor
  · intro h
    have hz : (klDiv (D.preparation x) (D.preparation y)).toReal = 0 := by
      have hn := ENNReal.toReal_nonneg (a := klDiv (D.preparation y) (D.preparation x))
      dsimp [comparison] at h
      exact le_antisymm (by linarith) ENNReal.toReal_nonneg
    apply klDiv_eq_zero_iff.mp
    exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (D.finiteEntropy x y)
  · intro h
    simp [comparison, h]

/-- The reconstructed feature distinguishes exactly the preparation measures. -/
theorem feature_eq_iff_preparation_eq (x y : V) :
    D.feature x = D.feature y ↔ D.preparation x = D.preparation y := by
  rw [← D.comparison_eq_zero_iff x y, D.comparison_eq_norm_sub_sq,
    sq_eq_zero_iff, norm_eq_zero, sub_eq_zero]

end Contract
end
end IDT.QMClosure.ClassicalStatisticalProcessBridge
