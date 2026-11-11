import Proofs.QMClosure.NativePositiveSupportReadout
import Proofs.QMClosure.NativeRegularReadoutCountercontrol

/-!
# Sign and universal-cancellation controls

Negative canonical coefficients are forced at arbitrarily high total degree
for each positive-parameter regular native counterreadout. Positive event
activation on original a/b bags does not extend to an ontology on all arbitrary
signed original bags, whose coherent cancellation gives a finite obstruction.
-/

noncomputable section

namespace IDT.QMClosure.NativePositiveSupportReadoutControls

open scoped BigOperators
open NativeInitialHistoryPresentation
open NativeGeneratorMixtureReadout
open OriginalOccurrenceKernel
open OriginalMaskLocalKernel
open PersistentOriginalEventAtoms
open NativePositiveSupportReadout
open NativeRegularReadoutCountercontrol

attribute [local instance] presentationCommRing presentationCharZero

theorem counterWeight_canonical_negative_arbitrarily_high (c : ℝ) (hc : 0 < c) :
    ∀ D : ℕ, ∃ j k : ℕ, D < j + k ∧ countKernel (counterWeight c) j k < 0 :=
  canonical_negative_arbitrarily_high (counterWeight_native c) (counterWeight_not_norm c hc)

/-- A small exact sign witness accompanies the universal high-degree result. -/
theorem counterWeight_canonical_three_one (c : ℝ) :
    countKernel (counterWeight c) 3 1 = -(288 : ℝ) * c / 125 := by
  norm_num [countKernel, cardinalSum, Finset.sum_range_succ, bagEval,
    counterWeight, ambientWeight, angularCorrection, quarticImag_formula,
    ComplexModel.a, ComplexModel.b, Complex.normSq_apply, map_add, map_mul]
  <;> ring

theorem counterWeight_no_allMaskEventFamily (c : ℝ) (hc : 0 < c) :
    ¬ AllMaskEventFamily (counterWeight c) := by
  intro H
  have hpos := countKernel_nonnegative_of_allMaskEventFamily H 3 1
  rw [counterWeight_canonical_three_one] at hpos
  nlinarith

/-- Original tags remain distinct even when their native values cancel. -/
def signedPairMaskEval (p : Presentation) (S : Finset (Fin 2)) : Presentation :=
  ∑ t ∈ S, if t = 0 then p else -p

@[simp] theorem signedPairMaskEval_empty (p : Presentation) :
    signedPairMaskEval p ∅ = 0 := by simp [signedPairMaskEval]

@[simp] theorem signedPairMaskEval_first (p : Presentation) :
    signedPairMaskEval p {0} = p := by simp [signedPairMaskEval]

@[simp] theorem signedPairMaskEval_second (p : Presentation) :
    signedPairMaskEval p {1} = -p := by simp [signedPairMaskEval]

@[simp] theorem signedPairMaskEval_both (p : Presentation) :
    signedPairMaskEval p {0, 1} = 0 := by simp [signedPairMaskEval]

/-- A positive singleton and a zero readout at coherent cancellation exclude
inclusion monotonicity on arbitrary-original signed masks. -/
theorem signedPair_not_monotone (W : Presentation → ℝ) (hzero : W 0 = 0)
    (p : Presentation) (hpos : 0 < W p) :
    ¬ Monotone (fun S => W (signedPairMaskEval p S)) := by
  intro hmono
  have h := hmono (show ({0} : Finset (Fin 2)) ⊆ {0, 1} by simp)
  simpa [hzero, not_le_of_gt hpos] using h

/-- This obstruction concerns an arbitrary-original signed pair. The selected
original a/b event family is a separately supplied restricted family. -/
theorem signedPair_no_positive_events (W : Presentation → ℝ) (hzero : W 0 = 0)
    (p : Presentation) (hpos : 0 < W p) :
    ¬∃ A : EventApparatus (Fin 2), A.value = fun S => W (signedPairMaskEval p S) := by
  apply cancellation_obstructs_positive_events (fun S => W (signedPairMaskEval p S))
    (show ({0} : Finset (Fin 2)) ⊆ {0, 1} by simp)
  · simpa using hpos
  · simpa using hzero

/-- Sign reversal is derived from two native phase turns. -/
theorem native_readout_neg {W : Presentation → ℝ} (L : NativeTransfer W)
    (p : Presentation) : W (-p) = W p := by
  have hturn : phase * (phase * p) = -p := by
    calc
      _ = phase ^ 2 * p := by ring
      _ = -p := by rw [phase_square]; ring
  have h := readout_phase_mul L (phase * p)
  rw [hturn, readout_phase_mul L p] at h
  exact h

/-- The signed a,-a pair has readings 0,1/2,1/2,0 and coefficient -1. -/
theorem native_signed_a_pairMobius {W : Presentation → ℝ} (L : NativeTransfer W) :
    mobius (fun S => W (signedPairMaskEval a S)) ({0, 1} : Finset (Fin 2)) = -1 := by
  rw [mobius_insert (fun S => W (signedPairMaskEval a S))
    0 ({1} : Finset (Fin 2)) (by decide)]
  rw [show ({1} : Finset (Fin 2)) = insert 1 ∅ by simp]
  rw [mobius_insert _ 1 (∅ : Finset (Fin 2)) (by simp)]
  norm_num [mobius, signedPairMaskEval, readout_zero L, readout_a L, native_readout_neg L]

theorem native_signed_a_no_positive_events {W : Presentation → ℝ} (L : NativeTransfer W) :
    ¬∃ A : EventApparatus (Fin 2), A.value = fun S => W (signedPairMaskEval a S) := by
  apply signedPair_no_positive_events W (readout_zero L) a
  rw [readout_a L]
  norm_num

end IDT.QMClosure.NativePositiveSupportReadoutControls
