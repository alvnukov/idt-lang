import Proofs.QMClosure.NativeDyadicThreeVectorSynthesis

/-!
# Native three-matrix synthesis with a dyadic first column

For a complex three-by-three matrix, assume the existing explicit invariant
contract: unitarity, fixing the uniform vector, and fourth-root determinant.
If its first column has a common Gaussian dyadic denominator, the checked
three-vector synthesis and the checked spectator stabilizer classification
construct an actual native circuit with exactly that matrix.

Only the first column needs dyadic data, but the fourth-root determinant is an
explicit hypothesis. This is not a claim that arbitrary dyadic unitary matrices
satisfy that determinant restriction, nor an arbitrary-width synthesis theorem.
No physical preparation, probability actualization, or QM closure is inferred.
-/

namespace IDT.QMClosure.NativeDyadicThreeMatrixSynthesis

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

open NativeDyadicGaussianArithmetic NativeDyadicThreeVectorSynthesis
open MixerGeneratedProcessWall NativeMixerEventConeExclusion
open NativeThreeWireStabilizer NativeThreeWireLocality
open scoped Matrix BigOperators

theorem first_column_sum {U : Mat3} (hU : Invariants U) :
    (∑ i, U i 0) = 1 := by
  have hu : U.conjTranspose.mulVec uniform = uniform :=
    (invariants_conjTranspose hU).uniform
  have h := congrArg star (congrFun hu 0)
  simpa [Matrix.mulVec, dotProduct, uniform, Matrix.conjTranspose_apply] using h

theorem first_column_norm {U : Mat3} (hU : IsUnitary U) :
    (∑ i, Complex.normSq (U i 0)) = 1 := by
  have h := congrArg (fun M : Mat3 => M 0 0) hU.1
  have hc : (∑ i, (Complex.normSq (U i 0) : ℂ)) = 1 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Matrix.one_apply_eq] using h
  exact_mod_cast hc

theorem circuit_first_column (c : NativeCircuit) :
    c.eval (single (0 : Fin 3) 1) = fun i => circuitMatrix c i 0 := by
  rw [circuit_action]
  ext i
  simp [Matrix.mulVec, dotProduct, single]

/-- Unitarity transfers a fixed first basis column to the first basis row. -/
theorem first_row_of_first_column {R : Mat3} (hR : IsUnitary R)
    (hcol : ∀ i, R i 0 = (1 : Mat3) i 0) :
    ∀ j, R 0 j = (1 : Mat3) 0 j := by
  have h00 : R 0 0 = 1 := by simpa using hcol 0
  have h10 : R 1 0 = 0 := by simpa using hcol 1
  have h20 : R 2 0 = 0 := by simpa using hcol 2
  intro j
  have h := congrArg (fun M : Mat3 => M 0 j) hR.1
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
    h00, h10, h20] using h

/-- Equal first columns leave only the already classified spectator block. -/
theorem same_first_column_factor {U C : Mat3}
    (hU : Invariants U) (hC : Invariants C)
    (hcol : ∀ i, U i 0 = C i 0) :
    ∃ r : Fin 4, U = C * spectator ^ r.val := by
  let R : Mat3 := C.conjTranspose * U
  have hR : Invariants R := invariants_mul (invariants_conjTranspose hC) hU
  have hRcol : ∀ i, R i 0 = (1 : Mat3) i 0 := by
    intro i
    have h := congrArg (fun M : Mat3 => M i 0) hC.unitary.1
    simpa only [R, Matrix.mul_apply, hcol] using h
  obtain ⟨r, hr⟩ := stabilizer_classification hR
    (first_row_of_first_column hR.unitary hRcol)
  refine ⟨r, ?_⟩
  calc
    U = C * R := by
      dsimp [R]
      rw [← Matrix.mul_assoc, hC.unitary.2, Matrix.one_mul]
    _ = C * spectator ^ r.val := by rw [hr]

/-- The native word is constructed from the first-column witness and spectator power. -/
theorem matrix_synthesis_of_dyadic_first_column (U : Mat3) (hU : Invariants U)
    (k : ℕ) (u : Fin 3 → G)
    (hcol : ∀ i, U i 0 = (u i : ℂ) / piC ^ k) :
    ∃ c : NativeCircuit, circuitMatrix c = U := by
  have hs : (∑ i, (u i : ℂ) / piC ^ k) = 1 := by
    simpa only [← hcol] using first_column_sum hU
  have hn : (∑ i, Complex.normSq ((u i : ℂ) / piC ^ k)) = 1 := by
    simpa only [← hcol] using first_column_norm hU.unitary
  obtain ⟨c, hc⟩ := normalized_three_vector_synthesizes k u hs hn
  have hCcol : ∀ i, U i 0 = circuitMatrix c i 0 := by
    intro i
    rw [circuit_first_column] at hc
    exact (hcol i).trans (congrFun hc i).symm
  obtain ⟨r, hr⟩ := same_first_column_factor hU (circuit_invariants c) hCcol
  refine ⟨.seq (appendSpectator .identity r.val) c, ?_⟩
  simp only [circuitMatrix, appendSpectator_matrix, Matrix.mul_one]
  exact hr.symm

end
end IDT.QMClosure.NativeDyadicThreeMatrixSynthesis
