import Proofs.QMClosure.BalancedNonmedialMixerWitness
import Proofs.QMClosure.BalancedNonmedialMixerRegularity
import Proofs.QMClosure.HomogeneousProductInterchange

/-!
# A generated eight-wire continuation probe in one nonlinear raw model

The preparation uses seven actual vacuum splits from a unit reference at port zero. The same
nonlinear gate and its own `rawLaw` are used for every continuation. Both words
retain all eight outputs; the displayed row is a four-output coarse graining.
The selected two-by-four arrangement supplies no physical independent-party
interpretation. The result is continuation sensitivity in this same model,
not a physical signalling theorem or a new first generated nonlinear/native
distinction: the earlier three-gate distinction already exists in the witness.
-/

namespace IDT.QMClosure.GeneratedNonmedialAxisProbe

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open BalancedNonmedialMixerCore BalancedNonmedialMixerWitness
open BalancedNonmedialMixerRegularity
open WeightFreeRawProbability (evalRaw)
open scoped BigOperators

/-- The existing nonlinear gate has the generic product-input hypothesis. -/
theorem gate_jointHomogeneous : HomogeneousProductInterchange.JointHomogeneous gate := by
  intro t p
  exact gate_joint_complex_homogeneity t p.1 p.2

/-- Product-input interchange is a restricted control for this same gate. -/
theorem product_input_interchange (a b : ℂ × ℂ) :
    RawNetworkMedialWall.columns gate
        (RawNetworkMedialWall.rows gate (HomogeneousProductInterchange.productArray a b)) =
      RawNetworkMedialWall.rows gate
        (RawNetworkMedialWall.columns gate (HomogeneousProductInterchange.productArray a b)) :=
  HomogeneousProductInterchange.interchange_productArray gate gate
    gate_jointHomogeneous gate_jointHomogeneous a b

def q : ℂ := (1 - Complex.I) / 4

theorem q_normSq : Complex.normSq q = 1 / 8 := by
  norm_num [q, Complex.normSq_apply, Complex.div_re, Complex.div_im,
    Complex.mul_re, Complex.mul_im]

/-- The literal order is 04;02;46;01;23;45;67. Every new target is vacuum. -/
def prep : Native (Fin 8) :=
  .seq (.pair 0 4 (by decide))
    (.seq (.pair 0 2 (by decide))
      (.seq (.pair 4 6 (by decide))
        (.seq (.pair 0 1 (by decide))
          (.seq (.pair 2 3 (by decide))
            (.seq (.pair 4 5 (by decide)) (.pair 6 7 (by decide)))))))

/-- A: four column pairs, with no output discarded. -/
def columnWord : Native (Fin 8) :=
  .seq (.pair 3 1 (by decide))
    (.seq (.pair 5 6 (by decide))
      (.seq (.pair 0 2 (by decide)) (.pair 4 7 (by decide))))

/-- B: the first two entries of each of the two displayed rows. -/
def rowWord : Native (Fin 8) :=
  .seq (.pair 3 5 (by decide)) (.pair 1 6 (by decide))

def afterA : Native (Fin 8) := .seq prep columnWord
def afterB : Native (Fin 8) := .seq prep rowWord
def afterBA : Native (Fin 8) := .seq afterB columnWord
def afterAB : Native (Fin 8) := .seq afterA rowWord

def prepared (c : Native (Fin 8)) : Fin 8 → ℂ :=
  RawNetworkMedialWall.prepared gate 0 1 0 c

/-- A complete generated array, factored by the common nonzero scale. -/
theorem prep_output : prepared prep =
    ![-q, q * Complex.I, q * Complex.I, q, q * Complex.I, q, q, -(q * Complex.I)] := by
  funext i
  fin_cases i <;>
    simp [prepared, RawNetworkMedialWall.prepared, RawNetworkMedialWall.rawSource,
      prep, evalRaw, gate_vacuum_right] <;>
    apply Complex.ext <;>
    norm_num [q, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]

theorem prep_output_explicit : prepared prep =
    ![(-1 + Complex.I) / 4, (1 + Complex.I) / 4, (1 + Complex.I) / 4,
      (1 - Complex.I) / 4, (1 + Complex.I) / 4, (1 - Complex.I) / 4,
      (1 - Complex.I) / 4, (-1 - Complex.I) / 4] := by
  rw [prep_output]
  funext i
  fin_cases i <;> apply Complex.ext <;>
    norm_num [q, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]

/-- The selected block is not a scalar product array: its minor is nonzero. -/
theorem selected_block_minor_ne_zero :
    prepared prep 3 * prepared prep 6 ≠ prepared prep 5 * prepared prep 1 := by
  intro h
  simp only [prep_output] at h
  change q * q = q * (q * Complex.I) at h
  have hi := congrArg Complex.im h
  norm_num [q, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] at hi

/-- Swap equivariance here is a consequence of this gate's checked square law. -/
private theorem gate_swap (x y : ℂ) :
    gate (y, x) = ((gate (x, y)).2, (gate (x, y)).1) := by
  have h := gate_square (gate (x, y))
  rw [gate_square (x, y)] at h
  exact h

private theorem gate_neg_one_I : gate (-1, Complex.I) =
    (0, Complex.I * (1 + Complex.I)) := by
  have h := gate_joint_complex_homogeneity Complex.I Complex.I 1
  simpa only [Complex.I_mul_I, mul_one, gate_I_one, mul_zero] using h

private theorem gate_I_neg_I : gate (Complex.I, -Complex.I) = (-1, 1) := by
  have ht : turn 0 (2 * Complex.I) = (-2 : ℂ) := by
    norm_num [turn, frozenTurn, k, R, A, B, BalancedNonmedialMixerCore.q,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]
  have hr : rotated 0 (2 * Complex.I) = (-2 : ℂ) := by
    rw [rotated, ht]
    norm_num
  change ((Complex.I + -Complex.I + rotated (Complex.I + -Complex.I)
      (Complex.I - -Complex.I)) / 2,
    (Complex.I + -Complex.I - rotated (Complex.I + -Complex.I)
      (Complex.I - -Complex.I)) / 2) = _
  rw [show (Complex.I + -Complex.I : ℂ) = 0 by ring,
    show (Complex.I - -Complex.I : ℂ) = 2 * Complex.I by ring, hr]
  norm_num

/-- The plus branch comes from the old selected minus branch by swap and sum. -/
def selectedPlus : ℂ :=
  1 + Complex.I / 2 + (52 + 17 * Complex.I) / ((2 * radical : ℝ) : ℂ)

theorem gate_one_one_add_I : gate (1, 1 + Complex.I) =
    (selectedPlus, 2 + Complex.I - selectedPlus) := by
  have hs := gate_sum (1 + Complex.I) 1
  have hf : (gate (1, 1 + Complex.I)).1 = selectedPlus := by
    rw [gate_swap]
    change (gate (1 + Complex.I, 1)).2 = selectedPlus
    rw [gate_first_selected] at hs
    dsimp [selectedPlus]
    linear_combination hs
  apply Prod.ext
  · exact hf
  · have ht := gate_sum 1 (1 + Complex.I)
    rw [hf] at ht
    change (gate (1, 1 + Complex.I)).2 = 2 + Complex.I - selectedPlus
    linear_combination ht

private theorem selectedPlus_re : selectedPlus.re = 1 + 26 / radical := by
  norm_num [selectedPlus, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
  field_simp [radical_ne_zero]
  ring

private theorem selectedPlus_im : selectedPlus.im = 1 / 2 + 17 / (2 * radical) := by
  norm_num [selectedPlus, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
  field_simp [radical_ne_zero]
  ring

theorem selectedPlus_normSq : Complex.normSq selectedPlus =
    3 / 2 + 121 / (2 * radical) := by
  simp only [Complex.normSq_apply, selectedPlus_re, selectedPlus_im]
  field_simp [radical_ne_zero]
  nlinarith [radical_square]

private theorem gate_q_one_I : gate (q, q * Complex.I) =
    (q * (1 + Complex.I), 0) := by
  simpa only [mul_one, gate_one_I, mul_zero] using
    gate_joint_complex_homogeneity q 1 Complex.I

private theorem gate_q_I_one : gate (q * Complex.I, q) =
    (0, q * (1 + Complex.I)) := by
  simpa only [mul_one, gate_I_one, mul_zero] using
    gate_joint_complex_homogeneity q Complex.I 1

private theorem gate_q_neg_one_I : gate (-q, q * Complex.I) =
    (0, q * (Complex.I * (1 + Complex.I))) := by
  simpa only [mul_neg_one, gate_neg_one_I, mul_zero] using
    gate_joint_complex_homogeneity q (-1) Complex.I

private theorem gate_q_I_neg_I : gate (q * Complex.I, -(q * Complex.I)) = (-q, q) := by
  simpa only [mul_neg, mul_one, mul_neg_one, gate_I_neg_I] using
    gate_joint_complex_homogeneity q Complex.I (-Complex.I)

private theorem gate_q_vacuum : gate (q, 0) =
    (q * ((1 + Complex.I) / 2), q * ((1 - Complex.I) / 2)) := by
  rw [gate_vacuum_right]
  apply Prod.ext <;> dsimp <;> ring

private theorem gate_q_one_one_add_I : gate (q, q * (1 + Complex.I)) =
    (q * selectedPlus, q * (2 + Complex.I - selectedPlus)) := by
  simpa only [mul_one, gate_one_one_add_I] using
    gate_joint_complex_homogeneity q 1 (1 + Complex.I)

theorem afterA_output : prepared afterA =
    ![0, 0, q * (Complex.I * (1 + Complex.I)), q * (1 + Complex.I),
      -q, q, q, q] := by
  change evalRaw gate columnWord (prepared prep) = _
  rw [prep_output]
  funext i
  fin_cases i <;>
    simp [columnWord, evalRaw, gate_q_one_I, gate_transparent,
      gate_q_neg_one_I, gate_q_I_neg_I]

theorem afterB_output : prepared afterB =
    ![-q, 0, q * Complex.I, q, q * Complex.I, q, q * (1 + Complex.I),
      -(q * Complex.I)] := by
  change evalRaw gate rowWord (prepared prep) = _
  rw [prep_output]
  funext i
  fin_cases i <;> simp [rowWord, evalRaw, gate_transparent, gate_q_I_one]

theorem afterBA_output : prepared afterBA =
    ![0, q * ((1 - Complex.I) / 2), q * (Complex.I * (1 + Complex.I)),
      q * ((1 + Complex.I) / 2), -q, q * selectedPlus,
      q * (2 + Complex.I - selectedPlus), q] := by
  change evalRaw gate columnWord (prepared afterB) = _
  rw [afterB_output]
  funext i
  fin_cases i <;>
    simp [columnWord, evalRaw, gate_q_vacuum, gate_q_one_one_add_I,
      gate_q_neg_one_I, gate_q_I_neg_I]

theorem afterAB_output : prepared afterAB =
    ![0, (gate (0, q)).1, q * (Complex.I * (1 + Complex.I)),
      (gate (q * (1 + Complex.I), q)).1, -q,
      (gate (q * (1 + Complex.I), q)).2, (gate (0, q)).2, q] := by
  change evalRaw gate rowWord (prepared afterA) = _
  rw [afterA_output]
  funext i
  fin_cases i <;> simp [rowWord, evalRaw]

def row0 : Finset (Fin 8) := {3, 5, 0, 4}
def row1 : Finset (Fin 8) := {1, 6, 2, 7}

theorem rows_partition : Disjoint row0 row1 ∧ row0 ∪ row1 = Finset.univ := by
  decide

def row0Probability (c : Native (Fin 8)) : ℝ := ∑ i ∈ row0, rawLaw.prob 0 c i

theorem all_outputs_normalized (c : Native (Fin 8)) :
    ∑ i : Fin 8, rawLaw.prob 0 c i = 1 := rawLaw.normalized 0 c

private theorem row0Probability_eq (c : Native (Fin 8)) :
    row0Probability c = Complex.normSq (prepared c 3) + Complex.normSq (prepared c 5) +
      Complex.normSq (prepared c 0) + Complex.normSq (prepared c 4) := by
  simp [row0Probability, row0, raw_probability_eq_own_normSq, prepared, add_assoc]

private theorem one_add_I_normSq : Complex.normSq (1 + Complex.I) = 2 := by
  norm_num [Complex.normSq_apply]

private theorem alpha_normSq : Complex.normSq ((1 + Complex.I) / 2) = 1 / 2 := by
  norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im]

theorem row0_afterA : row0Probability afterA = 1 / 2 := by
  rw [row0Probability_eq]
  simp only [afterA_output]
  change Complex.normSq (q * (1 + Complex.I)) + Complex.normSq q +
    Complex.normSq 0 + Complex.normSq (-q) = 1 / 2
  norm_num [map_mul, q_normSq, one_add_I_normSq]

theorem row0_afterBA : row0Probability afterBA = 3 / 8 + 121 / (16 * radical) := by
  rw [row0Probability_eq]
  simp only [afterBA_output]
  change Complex.normSq (q * ((1 + Complex.I) / 2)) + Complex.normSq (q * selectedPlus) +
    Complex.normSq 0 + Complex.normSq (-q) = 3 / 8 + 121 / (16 * radical)
  norm_num [map_mul, q_normSq, alpha_normSq, one_add_I_normSq, selectedPlus_normSq]
  field_simp [radical_ne_zero]
  ring

/-- The row gate conserves the complete selected row, not an individual port. -/
theorem row0_afterAB : row0Probability afterAB = 1 / 2 := by
  have hc := gate_conserves (q * (1 + Complex.I)) q
  norm_num [map_mul, q_normSq, one_add_I_normSq] at hc
  rw [row0Probability_eq]
  simp only [afterAB_output]
  change Complex.normSq (gate (q * (1 + Complex.I), q)).1 +
    Complex.normSq (gate (q * (1 + Complex.I), q)).2 +
    Complex.normSq 0 + Complex.normSq (-q) = 1 / 2
  norm_num [q_normSq]
  nlinarith

theorem row0_afterBA_gt_half : 1 / 2 < row0Probability afterBA := by
  rw [row0_afterBA]
  have hr : 2 * radical < 121 := by nlinarith [radical_square, radical_positive]
  have hd : 0 < 16 * radical := mul_pos (by norm_num) radical_positive
  have hf : (1 / 8 : ℝ) < 121 / (16 * radical) := by
    apply (lt_div_iff₀ hd).mpr
    nlinarith
  linarith

/-- A single generated preparation and one fixed own-law exhibit the difference. -/
theorem same_model_axis_continuation_sensitivity :
    row0Probability afterA = 1 / 2 ∧
      row0Probability afterAB = 1 / 2 ∧
      row0Probability afterBA = 3 / 8 + 121 / (16 * radical) ∧
      row0Probability afterAB < row0Probability afterBA := by
  exact ⟨row0_afterA, row0_afterAB, row0_afterBA, by
    rw [row0_afterAB]
    exact row0_afterBA_gt_half⟩

end
end IDT.QMClosure.GeneratedNonmedialAxisProbe
