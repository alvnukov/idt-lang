import Proofs.QMClosure.FiniteStochasticPeripheral
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Twisted readouts of finite stochastic dynamics

A fixed finite real row-stochastic matrix has vanishing twisted Cesàro readout
at every infinite-order complex phase of modulus one. The initial weights and
readout vector are arbitrary fixed complex vectors. This is a matrix limit
theorem; it makes no physical preparation or interpretation claim.
-/

noncomputable section

namespace IDT.QMClosure.FiniteStochasticTwistedReadout

open Finset Filter Topology
open FiniteStochasticPeripheral

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The normalized twisted mean of one orbit component. -/
def coordinateMean (P : Matrix S S ℝ) (ζ : ℂ) (r : S → ℂ) (N : ℕ) (i : S) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ range N, (ζ⁻¹) ^ n * ((complexify P) ^ n).mulVec r i

/-- A fixed complex linear readout of a finite stochastic orbit. -/
def twistedCesaroMean (P : Matrix S S ℝ) (ζ : ℂ) (μ r : S → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ range N,
    (ζ⁻¹) ^ n * ∑ i, μ i * ((complexify P) ^ n).mulVec r i

private theorem orbit_bound {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) (r : S → ℂ) (n : ℕ) (i : S) :
    ‖((complexify P) ^ n).mulVec r i‖ ≤ ∑ j, ‖r j‖ := by
  induction n generalizing i with
  | zero =>
      simpa using single_le_sum (fun j _ => norm_nonneg (r j)) (mem_univ i)
  | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      change ‖∑ j, (P i j : ℂ) * ((complexify P) ^ n).mulVec r j‖ ≤ _
      calc
        _ ≤ ∑ j, ‖(P i j : ℂ) * ((complexify P) ^ n).mulVec r j‖ := norm_sum_le _ _
        _ = ∑ j, P i j * ‖((complexify P) ^ n).mulVec r j‖ := by
          simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hP.1 i _)]
        _ ≤ ∑ j, P i j * ∑ k, ‖r k‖ :=
          sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j) (hP.1 i j)
        _ = ∑ k, ‖r k‖ := by
          rw [← sum_mul, Matrix.sum_row_of_mem_rowStochastic hP i, one_mul]

/-- Infinite order excludes the phase from the spectrum of the transition matrix. -/
theorem shifted_det_ne_zero {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) {ζ : ℂ}
    (hζ : Complex.normSq ζ = 1)
    (horder : ∀ q : ℕ, 0 < q → ζ ^ q ≠ 1) :
    (complexify P - ζ • (1 : Matrix S S ℂ)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, heq⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have heig : (complexify P).mulVec v = ζ • v := by
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      sub_eq_zero] using heq
  obtain ⟨q, hq, _, hroot⟩ := exists_bounded_pow_eq_one hP hv heig hζ
  exact horder q hq hroot

private theorem twisted_sum_telescope (A : Matrix S S ℂ) {ζ : ℂ} (hζ : ζ ≠ 0)
    (s : S → ℂ) (N : ℕ) (i : S) :
    (∑ n ∈ range N, (ζ⁻¹) ^ n *
      (A ^ n).mulVec ((A - ζ • (1 : Matrix S S ℂ)).mulVec s) i) =
      ζ * ((ζ⁻¹) ^ N * (A ^ N).mulVec s i - s i) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ, ih]
      have hstep :
          (A ^ N).mulVec ((A - ζ • (1 : Matrix S S ℂ)).mulVec s) i =
            (A ^ (N + 1)).mulVec s i - ζ * (A ^ N).mulVec s i := by
        rw [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.smul_mulVec,
          Matrix.one_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_succ]
        rfl
      rw [hstep, pow_succ]
      ring_nf
      simp [hζ]
      ring

/-- Each fixed orbit component has vanishing twisted Cesàro mean. -/
theorem tendsto_coordinateMean_zero {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) {ζ : ℂ}
    (hζ : Complex.normSq ζ = 1)
    (horder : ∀ q : ℕ, 0 < q → ζ ^ q ≠ 1) (r : S → ℂ) (i : S) :
    Tendsto (fun N => coordinateMean P ζ r N i) atTop (𝓝 0) := by
  have hnorm : ‖ζ‖ = 1 := by
    have := Complex.normSq_eq_norm_sq ζ
    have := norm_nonneg ζ
    nlinarith
  have hζ0 : ζ ≠ 0 := by intro hz; simp [hz] at hζ
  let B := complexify P - ζ • (1 : Matrix S S ℂ)
  have hB : IsUnit B.det := isUnit_iff_ne_zero.mpr (shifted_det_ne_zero hP hζ horder)
  let s := B⁻¹.mulVec r
  have hs : B.mulVec s = r := by
    dsimp [s]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]
  have htel (N : ℕ) :
      (∑ n ∈ range N, (ζ⁻¹) ^ n * ((complexify P) ^ n).mulVec r i) =
        ζ * ((ζ⁻¹) ^ N * ((complexify P) ^ N).mulVec s i - s i) := by
    rw [← hs]
    exact twisted_sum_telescope _ hζ0 s N i
  have hbound (N : ℕ) :
      ‖coordinateMean P ζ r N i‖ ≤ (N : ℝ)⁻¹ * ((∑ j, ‖s j‖) + ‖s i‖) := by
    rw [coordinateMean, htel, norm_mul, norm_inv, Complex.norm_natCast,
      norm_mul, hnorm, one_mul]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
    calc
      _ ≤ ‖(ζ⁻¹) ^ N * ((complexify P) ^ N).mulVec s i‖ + ‖s i‖ := norm_sub_le _ _
      _ = ‖((complexify P) ^ N).mulVec s i‖ + ‖s i‖ := by
        simp [norm_pow, norm_inv, hnorm]
      _ ≤ _ := add_le_add (orbit_bound hP s N i) le_rfl
  apply squeeze_zero_norm hbound
  simpa using (tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)).mul_const
      ((∑ j, ‖s j‖) + ‖s i‖)

/-- Any fixed complex linear readout has vanishing twisted Cesàro mean.
No positivity or normalization of either fixed vector is required. -/
theorem tendsto_twistedCesaroMean_zero {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) {ζ : ℂ}
    (hζ : Complex.normSq ζ = 1)
    (horder : ∀ q : ℕ, 0 < q → ζ ^ q ≠ 1) (μ r : S → ℂ) :
    Tendsto (twistedCesaroMean P ζ μ r) atTop (𝓝 0) := by
  have hcoord (i : S) := tendsto_coordinateMean_zero hP hζ horder r i
  have hsum : Tendsto (fun N => ∑ i, μ i * coordinateMean P ζ r N i) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum univ
      (fun i _ => tendsto_const_nhds.mul (hcoord i))
  convert hsum using 1
  funext N
  simp only [twistedCesaroMean, coordinateMean, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro i hi
  ring

end IDT.QMClosure.FiniteStochasticTwistedReadout
