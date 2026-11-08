import Proofs.QMClosure.ClassicalStatisticalProcessBridge
import Proofs.QMClosure.DetectorEffectOperations

/-!
# Complementary detector coincidence conservation under finite relative entropy

For an actual common classical statistical process, conservation of both the
accept–accept and reject–reject probabilities of one binary detector forces that
detector's acceptance to be constant on the preparation family. The proof uses
the reconstructed squared comparison and actual Markov data processing for the
binary detector. Finite directed KL is required before taking real values.

This is a conditional obstruction for this statistical process contract. It
does not supply detector completeness, Born actualization, or full QM closure.
-/

namespace IDT.QMClosure.ComplementaryDetectorConservationWall

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open InvariantEffectReadoutBridge DetectorEffectOperations
open RawSparseConservationSelection
open scoped ENNReal

universe u v
variable {V : Type u} {Ω : Type v} [MeasurableSpace Ω]

def response (D : ClassicalStatisticalProcessBridge.Contract V Ω)
    (g : Effect Ω) (x : V) : ℝ := g.acceptance (D.preparation x)

def binaryLaw (D : ClassicalStatisticalProcessBridge.Contract V Ω)
    (g : Effect Ω) (x : V) : Measure Bool := g.binaryKernel ∘ₘ D.preparation x

/-- Equality of acceptance identifies both probabilities of the actual detector. -/
theorem binaryLaw_eq_of_response_eq
    (D : ClassicalStatisticalProcessBridge.Contract V Ω) (g : Effect Ω)
    {x y : V} (h : response D g x = response D g y) :
    binaryLaw D g x = binaryLaw D g y := by
  letI (z : V) : IsProbabilityMeasure (D.preparation z) := D.probability z
  apply Measure.ext_of_singleton
  intro b
  cases b
  · simpa only [binaryLaw, g.binaryKernel_comp_false] using
      congrArg (fun t : ℝ => ENNReal.ofReal (1 - t)) h
  · simpa only [binaryLaw, g.binaryKernel_comp_true] using
      congrArg ENNReal.ofReal h

/-- Distinct acceptance probabilities give distinct actual binary measures. -/
theorem response_eq_of_binaryLaw_eq
    (D : ClassicalStatisticalProcessBridge.Contract V Ω) (g : Effect Ω)
    {x y : V} (h : binaryLaw D g x = binaryLaw D g y) :
    response D g x = response D g y := by
  letI (z : V) : IsProbabilityMeasure (D.preparation z) := D.probability z
  have he := congrArg (fun μ : Measure Bool => μ {true}) h
  simp only [binaryLaw, g.binaryKernel_comp_true] at he
  have hr := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (g.acceptance_nonnegative _)] using hr

/-- Detector data processing preserves the explicit finite-entropy safeguard. -/
theorem binaryLaw_klDiv_ne_top
    (D : ClassicalStatisticalProcessBridge.Contract V Ω) (g : Effect Ω) (x y : V) :
    klDiv (binaryLaw D g x) (binaryLaw D g y) ≠ ∞ := by
  letI (z : V) : IsProbabilityMeasure (D.preparation z) := D.probability z
  exact ne_top_of_le_ne_top (D.finiteEntropy x y)
    (RelativeEntropyDataProcessing.klDiv_markov_le _ _ g.binaryKernel)

/-- The directed detector divergence is bounded by the supplied squared comparison. -/
theorem binaryLaw_klDiv_toReal_le_comparison
    (D : ClassicalStatisticalProcessBridge.Contract V Ω) (g : Effect Ω) (x y : V) :
    (klDiv (binaryLaw D g x) (binaryLaw D g y)).toReal ≤ D.comparison x y := by
  letI (z : V) : IsProbabilityMeasure (D.preparation z) := D.probability z
  have h := ENNReal.toReal_mono (D.finiteEntropy x y)
    (RelativeEntropyDataProcessing.klDiv_markov_le
      (D.preparation x) (D.preparation y) g.binaryKernel)
  exact h.trans (le_add_of_nonneg_right ENNReal.toReal_nonneg)

private theorem comparison_half_B (D : PairComparisonReconstruction.Contract V) (x y : V) :
    D.comparison (B D.raw x) (B D.raw y) = D.comparison x y / 2 := by
  have ha := D.G_half_B x y
  have hx := D.G_half_B x x
  have hy := D.G_half_B y y
  rw [D.G_diagonal, D.G_diagonal] at hx hy
  dsimp [PairComparisonReconstruction.Contract.G] at ha
  linarith

/-- Both output ports halve the squared comparison to the fixed reference. -/
theorem output_comparison_half
    (D : ClassicalStatisticalProcessBridge.Contract V Ω) (x : V) :
    D.comparison (D.operation (x, D.chosenZero)).1 D.chosenZero =
        D.comparison x D.chosenZero / 2 ∧
      D.comparison (D.operation (x, D.chosenZero)).2 D.chosenZero =
        D.comparison x D.chosenZero / 2 := by
  constructor
  · change D.reconstruction.comparison (A D.reconstruction.raw x) D.chosenZero = _
    have hzero : A D.reconstruction.raw D.chosenZero = D.chosenZero :=
      A_zero D.reconstruction.raw
    have h := D.reconstruction.comparison_half_A x D.chosenZero
    rw [hzero] at h
    exact h
  · have hs := second_eq_reverse D.reconstruction.raw x D.chosenZero
    change (D.operation (x, D.chosenZero)).2 = B D.reconstruction.raw x at hs
    rw [hs]
    change D.reconstruction.comparison (B D.reconstruction.raw x) D.chosenZero = _
    have hzero : B D.reconstruction.raw D.chosenZero = D.chosenZero :=
      B_zero D.reconstruction.raw
    have h := comparison_half_B D.reconstruction x D.chosenZero
    rw [hzero] at h
    exact h

private theorem response_retained {a b c d : ℝ}
    (haccept : a * b = c * d)
    (hreject : (1 - a) * (1 - b) = (1 - c) * (1 - d)) :
    a = c ∨ b = c := by
  have hsum : a + b = c + d := by nlinarith
  have hfactor : (a - c) * (b - c) = 0 := by
    calc
      (a - c) * (b - c) = a * b - c * (a + b) + c * c := by ring
      _ = c * d - c * (c + d) + c * c := by rw [haccept, hsum]
      _ = 0 := by ring
  rcases mul_eq_zero.mp hfactor with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

/-- Keeping either output retaining the response gives arbitrarily small comparison.
The comparison is a squared-distance quantity and is halved at each step. -/
theorem exists_dyadic_response_representative
    (D : ClassicalStatisticalProcessBridge.Contract V Ω) (g : Effect Ω)
    (haccept : ∀ p : V × V,
      response D g (D.operation p).1 * response D g (D.operation p).2 =
        response D g p.1 * response D g p.2)
    (hreject : ∀ p : V × V,
      (1 - response D g (D.operation p).1) * (1 - response D g (D.operation p).2) =
        (1 - response D g p.1) * (1 - response D g p.2))
    (y : V) (n : ℕ) :
    ∃ z : V, response D g z = response D g y ∧
      D.comparison z D.chosenZero = (1 / 2 : ℝ) ^ n * D.comparison y D.chosenZero := by
  induction n with
  | zero => exact ⟨y, rfl, by simp⟩
  | succ n ih =>
    obtain ⟨z, hz, hc⟩ := ih
    have hretain := response_retained (haccept (z, D.chosenZero))
      (hreject (z, D.chosenZero))
    have hhalf := output_comparison_half D z
    rcases hretain with hfirst | hsecond
    · refine ⟨(D.operation (z, D.chosenZero)).1, hfirst.trans hz, ?_⟩
      rw [hhalf.1, hc, pow_succ]
      ring
    · refine ⟨(D.operation (z, D.chosenZero)).2, hsecond.trans hz, ?_⟩
      rw [hhalf.2, hc, pow_succ]
      ring

/-- Conserving accept–accept and reject–reject coincidences forces a constant
acceptance probability under the finite-KL common-process contract. -/
theorem response_eq_reference
    (D : ClassicalStatisticalProcessBridge.Contract V Ω) (g : Effect Ω)
    (haccept : ∀ p : V × V,
      response D g (D.operation p).1 * response D g (D.operation p).2 =
        response D g p.1 * response D g p.2)
    (hreject : ∀ p : V × V,
      (1 - response D g (D.operation p).1) * (1 - response D g (D.operation p).2) =
        (1 - response D g p.1) * (1 - response D g p.2))
    (y : V) : response D g y = response D g D.chosenZero := by
  letI (z : V) : IsProbabilityMeasure (D.preparation z) := D.probability z
  letI (z : V) : IsProbabilityMeasure (binaryLaw D g z) := by
    unfold binaryLaw
    infer_instance
  by_contra hresponse
  have hneq : binaryLaw D g y ≠ binaryLaw D g D.chosenZero :=
    fun h => hresponse (response_eq_of_binaryLaw_eq D g h)
  have hklzero : klDiv (binaryLaw D g y) (binaryLaw D g D.chosenZero) ≠ 0 :=
    fun h => hneq (klDiv_eq_zero_iff.mp h)
  let δ := (klDiv (binaryLaw D g y) (binaryLaw D g D.chosenZero)).toReal
  have hδ : 0 < δ := ENNReal.toReal_pos hklzero (binaryLaw_klDiv_ne_top D g _ _)
  have hbound (n : ℕ) : δ ≤ (1 / 2 : ℝ) ^ n * D.comparison y D.chosenZero := by
    obtain ⟨z, hz, hc⟩ := exists_dyadic_response_representative D g haccept hreject y n
    have heq := binaryLaw_eq_of_response_eq D g hz
    have hdpi := binaryLaw_klDiv_toReal_le_comparison D g z D.chosenZero
    rw [heq, hc] at hdpi
    exact hdpi
  have hC : 0 < D.comparison y D.chosenZero := by
    have h := hbound 0
    simp only [pow_zero, one_mul] at h
    exact hδ.trans_le h
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hδ hC)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hsmall : (1 / 2 : ℝ) ^ n * D.comparison y D.chosenZero < δ :=
    (lt_div_iff₀ hC).mp hn
  exact (not_lt_of_ge (hbound n)) hsmall

def CoincidenceConserved (D : ClassicalStatisticalProcessBridge.Contract V Ω)
    (g : Effect Ω) : Prop :=
  ∀ p : V × V, response D g (D.operation p).1 * response D g (D.operation p).2 =
    response D g p.1 * response D g p.2

/-- Equivalent detector presentation using the actual complementary effect. -/
theorem acceptance_eq_reference_of_complement
    (D : ClassicalStatisticalProcessBridge.Contract V Ω) (g : Effect Ω)
    (hg : CoincidenceConserved D g) (hc : CoincidenceConserved D (complement g)) (y : V) :
    g.acceptance (D.preparation y) = g.acceptance (D.preparation D.chosenZero) := by
  letI (z : V) : IsProbabilityMeasure (D.preparation z) := D.probability z
  apply response_eq_reference D g hg
  intro p
  simpa only [response, acceptance_complement] using hc p

/-- Pairwise form of the complementary detector obstruction. -/
theorem acceptance_eq_of_complement
    (D : ClassicalStatisticalProcessBridge.Contract V Ω) (g : Effect Ω)
    (hg : CoincidenceConserved D g) (hc : CoincidenceConserved D (complement g)) (x y : V) :
    g.acceptance (D.preparation x) = g.acceptance (D.preparation y) :=
  (acceptance_eq_reference_of_complement D g hg hc x).trans
    (acceptance_eq_reference_of_complement D g hg hc y).symm

/-- With accept–accept conservation fixed, complement conservation is equivalent
to conservation of an equally randomized sure/accept detector. -/
theorem complement_iff_average_sure
    (D : ClassicalStatisticalProcessBridge.Contract V Ω) (g : Effect Ω)
    (hg : CoincidenceConserved D g) :
    CoincidenceConserved D (complement g) ↔
      CoincidenceConserved D (average sure g) := by
  letI (z : V) : IsProbabilityMeasure (D.preparation z) := D.probability z
  constructor <;> intro h p
  · have ha := hg p
    have hc := h p
    simp only [response, acceptance_complement] at hc
    simp only [response, acceptance_average, acceptance_sure]
    dsimp [response] at ha
    nlinarith
  · have ha := hg p
    have hm := h p
    simp only [response, acceptance_average, acceptance_sure] at hm
    simp only [response, acceptance_complement]
    dsimp [response] at ha
    nlinarith

/-- The same wall follows from the detector and its sure/accept randomization. -/
theorem acceptance_eq_reference_of_average_sure
    (D : ClassicalStatisticalProcessBridge.Contract V Ω) (g : Effect Ω)
    (hg : CoincidenceConserved D g)
    (hm : CoincidenceConserved D (average sure g)) (y : V) :
    g.acceptance (D.preparation y) = g.acceptance (D.preparation D.chosenZero) :=
  acceptance_eq_reference_of_complement D g hg
    ((complement_iff_average_sure D g hg).mpr hm) y

end
end IDT.QMClosure.ComplementaryDetectorConservationWall
