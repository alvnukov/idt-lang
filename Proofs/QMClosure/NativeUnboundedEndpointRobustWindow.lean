import Proofs.QMClosure.FiniteStochasticCompact
import Proofs.QMClosure.NativeReadoutPolynomialObstruction
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# A robust fixed-state window with arbitrary complex endpoints

For a fixed finite state type, every real row-stochastic preparation kernel
and every pair of fixed complex endpoint vectors has an error at least one
positive uniform constant at some depth below `card S + 4`.

Only the kernel set is compactified. The characteristic polynomial annihilates
every fixed linear matrix-power readout, independently of endpoint magnitudes.
Its native residual is nonzero among four slots. The residual maximum divided
by the coefficient norm sum is a positive continuous function on the compact
kernel set, and bounds a finite prediction-error maximum from below.

The positive constant is existential, not a numerical or effective estimate
and not identified with `2/9`. The result concerns a fixed finite uniform
compositional preparation model; it supplies no state-independent window,
statistical confidence statement, detector actualization or QM closure.
-/

namespace IDT.QMClosure.NativeUnboundedEndpointRobustWindow

open Finset Polynomial
open FiniteReadoutRecurrence NativeFiniteStochasticReadoutWall
open NativeThreeWireProbabilityDenominator

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Characteristic-polynomial coefficients are continuous in a continuous matrix. -/
theorem continuous_charpoly_coeff {X : Type*} [TopologicalSpace X]
    (A : X → Matrix S S ℂ) (hA : Continuous A) (j : ℕ) :
    Continuous (fun x => (A x).charpoly.coeff j) := by
  let B : Matrix S S C(X, ℂ) := fun i k =>
    ⟨fun x => A x i k, hA.matrix_elem i k⟩
  have heval (x : X) : (B.charpoly.coeff j) x = (A x).charpoly.coeff j := by
    let ev : C(X, ℂ) →+* ℂ := (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom
    have hmap : B.map ev = A x := rfl
    have hc := congrArg (fun p : ℂ[X] => p.coeff j) (Matrix.charpoly_map B ev)
    simp only [hmap, Polynomial.coeff_map] at hc
    exact hc.symm
  have hfun : (fun x => (A x).charpoly.coeff j) =
      (fun x => (B.charpoly.coeff j) x) := funext fun x => (heval x).symm
  rw [hfun]
  exact (B.charpoly.coeff j).continuous

/-- Coefficient continuity for the complexification of a real kernel. -/
theorem continuous_complexify_charpoly_coeff (j : ℕ) :
    Continuous (fun P : Matrix S S ℝ =>
      (FiniteStochasticPeripheral.complexify P).charpoly.coeff j) := by
  apply continuous_charpoly_coeff
  apply continuous_matrix
  intro i k
  exact Complex.continuous_ofReal.comp (continuous_apply_apply i k)

/-- Sum of the norms of all characteristic-polynomial coefficients. -/
def coefficientNormSum (P : Matrix S S ℝ) : ℝ :=
  ∑ j ∈ range (Fintype.card S + 1),
    ‖(FiniteStochasticPeripheral.complexify P).charpoly.coeff j‖

/-- The monic leading coefficient makes the normalizing denominator at least one. -/
theorem one_le_coefficientNormSum (P : Matrix S S ℝ) : 1 ≤ coefficientNormSum P := by
  have hlead : (FiniteStochasticPeripheral.complexify P).charpoly.coeff
      (Fintype.card S) = 1 := by
    simpa only [Matrix.charpoly_natDegree_eq_dim] using
      (Matrix.charpoly_monic (FiniteStochasticPeripheral.complexify P)).coeff_natDegree
  calc
    1 = ‖(FiniteStochasticPeripheral.complexify P).charpoly.coeff (Fintype.card S)‖ := by
      rw [hlead, norm_one]
    _ ≤ coefficientNormSum P :=
      single_le_sum (fun j _ => norm_nonneg _) (mem_range.mpr (Nat.lt_succ_self _))

theorem coefficientNormSum_pos (P : Matrix S S ℝ) : 0 < coefficientNormSum P :=
  lt_of_lt_of_le zero_lt_one (one_le_coefficientNormSum P)

theorem continuous_coefficientNormSum :
    Continuous (coefficientNormSum (S := S)) :=
  continuous_finset_sum _ fun j _ => (continuous_complexify_charpoly_coeff j).norm

/-- Native residual of the characteristic-polynomial recurrence at one slot. -/
def nativeResidual (P : Matrix S S ℝ) (k : ℕ) : ℂ :=
  applyPolynomial (FiniteStochasticPeripheral.complexify P).charpoly
    (fun n => (selectedWeight n : ℂ)) k

theorem nativeResidual_eq_sum (P : Matrix S S ℝ) (k : ℕ) :
    nativeResidual P k = ∑ j ∈ range (Fintype.card S + 1),
      (FiniteStochasticPeripheral.complexify P).charpoly.coeff j *
        (selectedWeight (k + j) : ℂ) := by
  simp only [nativeResidual, applyPolynomial_eq_sum, Matrix.charpoly_natDegree_eq_dim]

theorem continuous_nativeResidual (k : ℕ) :
    Continuous (fun P : Matrix S S ℝ => nativeResidual P k) := by
  simp_rw [nativeResidual_eq_sum]
  exact continuous_finset_sum _ fun j _ =>
    (continuous_complexify_charpoly_coeff j).mul continuous_const

/-- Maximum norm of the native residual in its four separating slots. -/
def residualMax (P : Matrix S S ℝ) : ℝ :=
  (range 4).sup' (by decide) (fun k => ‖nativeResidual P k‖)

theorem continuous_residualMax : Continuous (residualMax (S := S)) :=
  Continuous.finset_sup'_apply (by decide) fun k _ => (continuous_nativeResidual k).norm

theorem residualMax_pos {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) : 0 < residualMax P := by
  obtain ⟨k, hk, hres⟩ :=
    NativeReadoutPolynomialObstruction.exists_charpoly_residual_before_four hP
  exact (Finset.lt_sup'_iff (by decide)).mpr
    ⟨k, mem_range.mpr hk, norm_pos_iff.mpr hres⟩

/-- Residual strength normalized by the recurrence coefficient norm sum. -/
def normalizedResidual (P : Matrix S S ℝ) : ℝ :=
  residualMax P / coefficientNormSum P

theorem continuous_normalizedResidual :
    Continuous (normalizedResidual (S := S)) :=
  continuous_residualMax.div continuous_coefficientNormSum
    (fun P => ne_of_gt (coefficientNormSum_pos P))

/-- Maximum prediction error on the exact cardinality-dependent window. -/
def windowError (P : Matrix S S ℝ) (μ r : S → ℂ) : ℝ :=
  (range (Fintype.card S + 4)).sup' (by exact ⟨0, mem_range.mpr (by omega)⟩)
    (fun n => ‖prediction P μ r n - (selectedWeight n : ℂ)‖)

/-- Every native residual slot is controlled by the same finite readout-error window. -/
theorem nativeResidual_norm_le (P : Matrix S S ℝ) (μ r : S → ℂ)
    (k : ℕ) (hk : k < 4) :
    ‖nativeResidual P k‖ ≤ coefficientNormSum P * windowError P μ r := by
  have hzero : ∑ j ∈ range (Fintype.card S + 1),
      (FiniteStochasticPeripheral.complexify P).charpoly.coeff j *
        prediction P μ r (k + j) = 0 := by
    have h := congrFun (NativeFixedStateFiniteWindow.charpoly_prediction P μ r) k
    simpa only [applyPolynomial_eq_sum, Matrix.charpoly_natDegree_eq_dim, Pi.zero_apply] using h
  have hres : nativeResidual P k = ∑ j ∈ range (Fintype.card S + 1),
      (FiniteStochasticPeripheral.complexify P).charpoly.coeff j *
        ((selectedWeight (k + j) : ℂ) - prediction P μ r (k + j)) := by
    simp_rw [mul_sub]
    rw [sum_sub_distrib, hzero, sub_zero, nativeResidual_eq_sum]
  calc
    ‖nativeResidual P k‖ = ‖∑ j ∈ range (Fintype.card S + 1),
        (FiniteStochasticPeripheral.complexify P).charpoly.coeff j *
          ((selectedWeight (k + j) : ℂ) - prediction P μ r (k + j))‖ := congrArg norm hres
    _ ≤ ∑ j ∈ range (Fintype.card S + 1),
        ‖(FiniteStochasticPeripheral.complexify P).charpoly.coeff j *
          ((selectedWeight (k + j) : ℂ) - prediction P μ r (k + j))‖ := norm_sum_le _ _
    _ = ∑ j ∈ range (Fintype.card S + 1),
        ‖(FiniteStochasticPeripheral.complexify P).charpoly.coeff j‖ *
          ‖prediction P μ r (k + j) - (selectedWeight (k + j) : ℂ)‖ := by
      apply sum_congr rfl
      intro j _
      rw [norm_mul, norm_sub_rev]
    _ ≤ ∑ j ∈ range (Fintype.card S + 1),
        ‖(FiniteStochasticPeripheral.complexify P).charpoly.coeff j‖ * windowError P μ r := by
      apply sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.le_sup'
        (fun n => ‖prediction P μ r n - (selectedWeight n : ℂ)‖)
        (mem_range.mpr (by have hj' := mem_range.mp hj; omega))
    _ = coefficientNormSum P * windowError P μ r := by
      rw [coefficientNormSum, sum_mul]

/-- The normalized native residual is a lower bound on every fixed-endpoint window error. -/
theorem normalizedResidual_le_windowError (P : Matrix S S ℝ) (μ r : S → ℂ) :
    normalizedResidual P ≤ windowError P μ r := by
  apply (div_le_iff₀ (coefficientNormSum_pos P)).mpr
  rw [mul_comm]
  exact Finset.sup'_le _ _ fun k hk => nativeResidual_norm_le P μ r k (mem_range.mp hk)

/-- One positive gap works for every stochastic kernel and arbitrary fixed complex endpoints. -/
theorem exists_positive_gap_before_card_add_four :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (P : Matrix S S ℝ),
      P ∈ Matrix.rowStochastic ℝ S → ∀ (μ r : S → ℂ),
        ∃ n : ℕ, n < Fintype.card S + 4 ∧
          δ ≤ ‖prediction P μ r n - (selectedWeight n : ℂ)‖ := by
  have hpositive : ∀ P ∈ (Matrix.rowStochastic ℝ S : Set (Matrix S S ℝ)),
      0 < normalizedResidual P := fun P hP =>
    div_pos (residualMax_pos hP) (coefficientNormSum_pos P)
  obtain ⟨δ, hδ, hbound⟩ :=
    FiniteStochasticCompact.isCompact_rowStochastic.exists_forall_le'
      continuous_normalizedResidual.continuousOn hpositive
  refine ⟨δ, hδ, ?_⟩
  intro P hP μ r
  have hδerror : δ ≤ windowError P μ r :=
    (hbound P hP).trans (normalizedResidual_le_windowError P μ r)
  obtain ⟨n, hn, herror⟩ := (Finset.le_sup'_iff _).mp hδerror
  exact ⟨n, mem_range.mp hn, herror⟩

end

end IDT.QMClosure.NativeUnboundedEndpointRobustWindow
