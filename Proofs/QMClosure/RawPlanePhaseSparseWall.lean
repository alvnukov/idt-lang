import Proofs.QMClosure.RawPlanePhaseContinuity

/-!
# A continuous plane-dependent sparse countermodel

The explicit operation on three complex coordinates passes the six universal
test families and the self-reference family. Its full sparse marginal law
fails at the displayed three-vector witness. All properties refer to the
actual operation, including its ordinary global continuity.
-/

namespace IDT.QMClosure.RawPlanePhaseSparseWall

noncomputable section

open RawPlanePhaseFamily RawPlanePhaseGeometry RawPlanePhaseControl

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

def witnessX : Vec := ![1, 0, 0]
def witnessY : Vec := ![0, 1, 0]
def witnessZ : Vec := ![1, 0, 1]

theorem witness_parameter_xy : parameter witnessX witnessY = 0 := by
  norm_num [parameter, wedge, W, witnessX, witnessY]

theorem witness_parameter_xz : parameter witnessX witnessZ = 1 := by
  norm_num [parameter, wedge, W, witnessX, witnessZ]

theorem witness_m_xy : m witnessX witnessY = native witnessX witnessY := by
  rw [m, witness_parameter_xy, familyM_zero]

theorem witness_m_yx : m witnessY witnessX = native witnessY witnessX := by
  rw [m, parameter_swap, witness_parameter_xy, familyM_zero]

theorem witness_ratio_forward :
    ratio (native witnessX witnessY) = ratio (a • witnessZ) := by
  norm_num [ratio, W, native, witnessX, witnessY, witnessZ, a, b,
    NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
    Complex.normSq_apply, Complex.div_re, Complex.div_im,
    Complex.mul_re, Complex.mul_im]

theorem witness_ratio_reverse :
    ratio (native witnessY witnessX) = ratio (b • witnessZ) := by
  norm_num [ratio, W, native, witnessX, witnessY, witnessZ, a, b,
    NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
    Complex.normSq_apply, Complex.div_re, Complex.div_im,
    Complex.mul_re, Complex.mul_im]

theorem witness_outer_forward :
    W (m (m witnessX witnessY)
      (RawSparseConservationSelection.A contract witnessZ)) = 1 := by
  rw [A_eq, witness_m_xy]
  change W (familyM _ (native witnessX witnessY) (a • witnessZ)) = 1
  rw [W_familyM_of_ratio_eq _ _ _ witness_ratio_forward]
  norm_num [W, native, witnessX, witnessY, witnessZ, a, b,
    NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
    Complex.normSq_apply, Complex.div_re, Complex.div_im,
    Complex.mul_re, Complex.mul_im]

theorem witness_outer_reverse :
    W (m (m witnessY witnessX)
      (RawSparseConservationSelection.B contract witnessZ)) = 1 := by
  rw [B_eq, witness_m_yx]
  change W (familyM _ (native witnessY witnessX) (b • witnessZ)) = 1
  rw [W_familyM_of_ratio_eq _ _ _ witness_ratio_reverse]
  norm_num [W, native, witnessX, witnessY, witnessZ, a, b,
    NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
    Complex.normSq_apply, Complex.div_re, Complex.div_im,
    Complex.mul_re, Complex.mul_im]

theorem witness_m_xz_weight : W (m witnessX witnessZ) = 21 / 10 := by
  rw [m, witness_parameter_xz, familyM, W_H]
  norm_num [W, native, H, ratio, phase, RawSparsePhaseTwistControl.phase,
    witnessX, witnessZ, a, b,
    NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
    Complex.normSq_apply, Complex.div_re, Complex.div_im,
    Complex.mul_re, Complex.mul_im]

theorem witness_A_y_weight :
    W (RawSparseConservationSelection.A contract witnessY) = 1 / 2 := by
  rw [A_eq]
  norm_num [W, witnessY, a, NativeAttenuationCircuit.a,
    Complex.normSq_apply, Complex.div_re, Complex.div_im,
    Complex.mul_re, Complex.mul_im]

/-- The sparse equation has left side `2` and right side `13/5`. -/
theorem constructed_sparse_witness :
    ∃ x y z : Vec,
      W (m (m x y) (RawSparseConservationSelection.A contract z)) +
        W (m (m y x) (RawSparseConservationSelection.B contract z)) = 2 ∧
      W (m x z) + W (RawSparseConservationSelection.A contract y) = 13 / 5 := by
  refine ⟨witnessX, witnessY, witnessZ, ?_, ?_⟩
  · rw [witness_outer_forward, witness_outer_reverse]
    norm_num
  · rw [witness_m_xz_weight, witness_A_y_weight]
    norm_num

theorem constructed_not_sparse :
    ¬ RawSparseConservationSelection.SparseMarginalLaw contract := by
  intro h
  obtain ⟨x, y, z, hl, hr⟩ := constructed_sparse_witness
  have hh := h x y z
  change W (m (m x y) _) + W (m (m y x) _) = W (m x z) + W _ at hh
  rw [hl, hr] at hh
  norm_num at hh

theorem constructed_not_observed_medial :
    ¬ RawSparseConservationSelection.ObservedMedial contract := by
  intro hm
  exact constructed_not_sparse
    (RawSparseConservationSelection.sparse_of_conserved_and_observed_medial
      contract pair_conserved hm)

/-- Universal tests, regularity, and the failed full laws hold for one operation. -/
theorem constructed_continuous_countermodel :
    RawSparseConservationTests.Tests contract ∧
    (∀ x y, RawSparseConservationTests.SparseAt contract x y
      (RawSparseConservationSelection.A contract x)) ∧
    (∀ x, 0 ≤ contract.weight x) ∧
    (∀ x, contract.weight x = 0 ↔ x = contract.chosenZero) ∧
    RawSparseConservationSelection.PairConserved contract ∧
    (∀ (c : ℂ) (x y : Vec), m (c • x) (c • y) = c • m x y) ∧
    Continuous operation ∧
    ¬ RawSparseConservationSelection.SparseMarginalLaw contract ∧
    ¬ RawSparseConservationSelection.ObservedMedial contract :=
  ⟨tests, selfSparse, weight_nonnegative, weight_eq_zero_iff,
    pair_conserved, m_smul, RawPlanePhaseContinuity.continuous_operation,
    constructed_not_sparse, constructed_not_observed_medial⟩

end
end IDT.QMClosure.RawPlanePhaseSparseWall
