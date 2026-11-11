import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-!
# A Gaussian-integer readout with global real translate rank twenty

This module specifies one fixed arithmetic control on integer coordinate pairs.
Its multiplication is explicitly Gaussian. Translation uses the additive group
of the pairs. The rank theorem concerns the global span of all integer shifts.

The fixed 20 by 20 rational inverse certifies the lower bound. The upper bound
uses five residue classes, each carrying four quadratic/affine features. No
spectral classification, universal rank gap, dyadic extension, native observation
provenance, actualization, or physical interpretation is asserted here.

The external witness file has SHA-256
733f150d94e65671ffae0b1ef89d77f7b92d29960ed3ce7429a54dd9b9bd4182.
The literal certificate below is proved again by kernel-checked arithmetic.
-/

namespace IDT.QMClosure.FiniteRankReadoutFilter

noncomputable section

open scoped BigOperators Matrix

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

attribute [local simp] ZMod.natCast_eq_zero_iff

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

abbrev GaussianPair := ℤ × ℤ

/-- Explicit Gaussian multiplication on the coordinate-pair carrier. -/
def gmul (z w : GaussianPair) : GaussianPair :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- The real-valued squared norm of the integer coordinate pair. -/
def normSq (z : GaussianPair) : ℝ :=
  (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2

/-- The Gaussian quotient sending the imaginary unit to minus two modulo five. -/
def rho (z : GaussianPair) : ZMod 5 :=
  (z.1 : ZMod 5) - 2 * (z.2 : ZMod 5)

private theorem rho_eq_zero_iff (z : GaussianPair) :
    rho z = 0 ↔ (5 : ℤ) ∣ z.1 - 2 * z.2 := by
  have hcast : rho z = ((z.1 - 2 * z.2 : ℤ) : ZMod 5) := by
    simp [rho]
  rw [hcast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num

/-- The squared norm retained precisely on the nonzero quotient residues. -/
def readout (z : GaussianPair) : ℝ :=
  if rho z = 0 then 0 else normSq z

theorem rho_add (z w : GaussianPair) : rho (z + w) = rho z + rho w := by
  simp only [rho, Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

theorem rho_gmul (z w : GaussianPair) : rho (gmul z w) = rho z * rho w := by
  simp only [rho, gmul, Int.cast_sub, Int.cast_add, Int.cast_mul]
  have hfive : (5 : ZMod 5) = 0 := by decide
  linear_combination -(z.2 : ZMod 5) * (w.2 : ZMod 5) * hfive

theorem normSq_gmul (z w : GaussianPair) :
    normSq (gmul z w) = normSq z * normSq w := by
  simp only [normSq, gmul, Int.cast_sub, Int.cast_add, Int.cast_mul]
  ring

theorem readout_gmul (z w : GaussianPair) :
    readout (gmul z w) = readout z * readout w := by
  unfold readout
  rw [rho_gmul, normSq_gmul]
  by_cases hz : rho z = 0 <;> by_cases hw : rho w = 0 <;>
    simp [hz, hw, mul_eq_zero]

theorem readout_nonnegative (z : GaussianPair) : 0 ≤ readout z := by
  unfold readout
  split_ifs
  · exact le_rfl
  · exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem readout_zero : readout (0, 0) = 0 := by
  norm_num [readout, rho_eq_zero_iff, normSq]

theorem readout_one : readout (1, 0) = 1 := by
  norm_num [readout, rho_eq_zero_iff, normSq]

theorem readout_two : readout (2, 0) = 4 := by
  norm_num [readout, rho_eq_zero_iff, normSq]

theorem readout_imaginary_unit : readout (0, 1) = 1 := by
  norm_num [readout, rho_eq_zero_iff, normSq]

theorem readout_one_add_imaginary_unit : readout (1, 1) = 2 := by
  norm_num [readout, rho_eq_zero_iff, normSq]

theorem readout_five : readout (5, 0) = 0 := by
  norm_num [readout, rho_eq_zero_iff, normSq]

theorem readout_not_normSq : readout ≠ normSq := by
  intro h
  have hfive := congrFun h (5, 0)
  norm_num [readout, rho_eq_zero_iff, normSq] at hfive

/-- A nonzero integer count is annihilated by this control. -/
theorem nonzero_count_annihilated :
    ∃ n : ℤ, n ≠ 0 ∧ readout (n, 0) = 0 :=
  ⟨5, by norm_num, readout_five⟩

/-- The two explicit conjugate Gaussian integers receive different values. -/
theorem conjugation_failure : readout (2, 1) ≠ readout (2, -1) := by
  norm_num [readout, rho_eq_zero_iff, normSq]

/-- Translation by any point of the full additive integer carrier. -/
def translate (f : GaussianPair → ℝ) (a : GaussianPair) : GaussianPair → ℝ :=
  fun z => f (z + a)

/-- Global span of all translates, with no finite-window restriction. -/
def translateSpan (f : GaussianPair → ℝ) : Submodule ℝ (GaussianPair → ℝ) :=
  Submodule.span ℝ {g | ∃ a : GaussianPair, g = translate f a}

abbrev FeatureIndex := ZMod 5 × Fin 4

private def quadraticFeature (j : Fin 4) (z : GaussianPair) : ℝ :=
  ![normSq z, (z.1 : ℝ), (z.2 : ℝ), 1] j

/-- The twenty residue-localized quadratic and affine functions. -/
def feature (p : FeatureIndex) : GaussianPair → ℝ :=
  fun z => if rho z = p.1 then quadraticFeature p.2 z else 0

private def quadraticCoefficient (a : GaussianPair) (j : Fin 4) : ℝ :=
  ![1, 2 * (a.1 : ℝ), 2 * (a.2 : ℝ), normSq a] j

private def translateCoefficient (a : GaussianPair) (p : FeatureIndex) : ℝ :=
  if p.1 + rho a = 0 then 0 else quadraticCoefficient a p.2

/-- Every global translate is an explicit combination of the same twenty features. -/
theorem translate_eq_feature_sum (a : GaussianPair) :
    translate readout a = ∑ p : FeatureIndex, translateCoefficient a p • feature p := by
  classical
  funext z
  simp only [translate, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (rho z)]
  · unfold readout
    rw [rho_add]
    by_cases h : rho z + rho a = 0
    · simp [translateCoefficient, h]
    · simp [translateCoefficient, feature, h, quadraticCoefficient, quadraticFeature,
        Fin.sum_univ_succ, normSq, Prod.fst_add, Prod.snd_add]
      ring
  · intro r _ hr
    apply Finset.sum_eq_zero
    intro j _
    simp [feature, Ne.symm hr]
  · simp

private def featureSpan : Submodule ℝ (GaussianPair → ℝ) :=
  Submodule.span ℝ (Set.range feature)

private instance featureSpan_finiteDimensional : FiniteDimensional ℝ featureSpan := by
  exact FiniteDimensional.span_of_finite ℝ (Set.finite_range feature)

private theorem translate_mem_featureSpan (a : GaussianPair) :
    translate readout a ∈ featureSpan := by
  rw [translate_eq_feature_sum]
  apply Submodule.sum_mem
  intro p _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

private theorem translateSpan_le_featureSpan : translateSpan readout ≤ featureSpan := by
  apply Submodule.span_le.mpr
  rintro g ⟨a, rfl⟩
  exact translate_mem_featureSpan a

/-- Finiteness follows from the global feature identity, independently of the certificate. -/
instance translateSpan_finiteDimensional : FiniteDimensional ℝ (translateSpan readout) :=
  Submodule.finiteDimensional_of_le translateSpan_le_featureSpan

private theorem featureSpan_finrank_le : Module.finrank ℝ featureSpan ≤ 20 := by
  have h := finrank_range_le_card (R := ℝ) feature
  simpa [Set.finrank, featureSpan, FeatureIndex] using h

/-- The global upper bound holds for every integer translate. -/
theorem translateSpan_finrank_le_twenty : Module.finrank ℝ (translateSpan readout) ≤ 20 :=
  (Submodule.finrank_mono translateSpan_le_featureSpan).trans featureSpan_finrank_le

/-- Fixed order, supplied before inspecting the matrix residuals. -/
def sample : Fin 20 → GaussianPair :=
  ![(0, 0), (5, 0), (-5, 0), (2, 1), (1, 0), (6, 0), (-4, 0), (3, 1), (2, 0), (7, 0), (-3, 0), (4, 1), (3, 0), (8, 0), (-2, 0), (5, 1), (4, 0), (9, 0), (-1, 0), (6, 1)]

private def sampleMatrix : Matrix (Fin 20) (Fin 20) ℝ :=
  fun i j => readout (sample i + sample j)

/-- Exact integer entries in the prescribed sample and translation order. -/
private def certificateMatrix : Matrix (Fin 20) (Fin 20) ℝ :=
  ![![0, 0, 0, 0, 1, 36, 16, 10, 4, 49, 9, 17, 9, 64, 4, 26, 16, 81, 1, 37],
    ![0, 0, 0, 0, 36, 121, 1, 65, 49, 144, 4, 82, 64, 169, 9, 101, 81, 196, 16, 122],
    ![0, 0, 0, 0, 16, 1, 81, 5, 9, 4, 64, 2, 4, 9, 49, 1, 1, 16, 36, 2],
    ![0, 0, 0, 0, 10, 65, 5, 29, 17, 82, 2, 40, 26, 101, 1, 53, 37, 122, 2, 68],
    ![1, 36, 16, 10, 4, 49, 9, 17, 9, 64, 4, 26, 16, 81, 1, 37, 0, 0, 0, 0],
    ![36, 121, 1, 65, 49, 144, 4, 82, 64, 169, 9, 101, 81, 196, 16, 122, 0, 0, 0, 0],
    ![16, 1, 81, 5, 9, 4, 64, 2, 4, 9, 49, 1, 1, 16, 36, 2, 0, 0, 0, 0],
    ![10, 65, 5, 29, 17, 82, 2, 40, 26, 101, 1, 53, 37, 122, 2, 68, 0, 0, 0, 0],
    ![4, 49, 9, 17, 9, 64, 4, 26, 16, 81, 1, 37, 0, 0, 0, 0, 36, 121, 1, 65],
    ![49, 144, 4, 82, 64, 169, 9, 101, 81, 196, 16, 122, 0, 0, 0, 0, 121, 256, 36, 170],
    ![9, 4, 64, 2, 4, 9, 49, 1, 1, 16, 36, 2, 0, 0, 0, 0, 1, 36, 16, 10],
    ![17, 82, 2, 40, 26, 101, 1, 53, 37, 122, 2, 68, 0, 0, 0, 0, 65, 170, 10, 104],
    ![9, 64, 4, 26, 16, 81, 1, 37, 0, 0, 0, 0, 36, 121, 1, 65, 49, 144, 4, 82],
    ![64, 169, 9, 101, 81, 196, 16, 122, 0, 0, 0, 0, 121, 256, 36, 170, 144, 289, 49, 197],
    ![4, 9, 49, 1, 1, 16, 36, 2, 0, 0, 0, 0, 1, 36, 16, 10, 4, 49, 9, 17],
    ![26, 101, 1, 53, 37, 122, 2, 68, 0, 0, 0, 0, 65, 170, 10, 104, 82, 197, 17, 125],
    ![16, 81, 1, 37, 0, 0, 0, 0, 36, 121, 1, 65, 49, 144, 4, 82, 64, 169, 9, 101],
    ![81, 196, 16, 122, 0, 0, 0, 0, 121, 256, 36, 170, 144, 289, 49, 197, 169, 324, 64, 226],
    ![1, 16, 36, 2, 0, 0, 0, 0, 1, 36, 16, 10, 4, 49, 9, 17, 9, 64, 4, 26],
    ![37, 122, 2, 68, 0, 0, 0, 0, 65, 170, 10, 104, 82, 197, 17, 125, 101, 226, 26, 148]]

/-- Exact rational left inverse supplied by the immutable finite witness. -/
private def inverseMatrix : Matrix (Fin 20) (Fin 20) ℝ :=
  ![![-9/50, -21/200, 3/200, 3/10, 151/2500, 179/5000, -31/5000, -1/10, 77/1250, 181/5000, -39/5000, -1/10, 159/2500, 181/5000, -49/5000, -1/10, 83/1250, 179/5000, -61/5000, -1/10],
    ![-21/200, -3/80, 3/200, 9/80, 179/5000, 29/2500, -49/10000, -3/80, 181/5000, 109/10000, -23/5000, -3/80, 181/5000, 13/1250, -41/10000, -3/80, 179/5000, 101/10000, -17/5000, -3/80],
    ![3/200, 3/200, -3/400, -3/80, -31/5000, -49/10000, 9/2500, 1/80, -39/5000, -23/5000, 49/10000, 1/80, -49/5000, -41/10000, 4/625, 1/80, -61/5000, -17/5000, 81/10000, 1/80],
    ![3/10, 9/80, -3/80, -3/8, -1/10, -3/80, 1/80, 1/8, -1/10, -3/80, 1/80, 1/8, -1/10, -3/80, 1/80, 1/8, -1/10, -3/80, 1/80, 1/8],
    ![151/2500, 179/5000, -31/5000, -1/10, 77/1250, 181/5000, -39/5000, -1/10, 159/2500, 181/5000, -49/5000, -1/10, 83/1250, 179/5000, -61/5000, -1/10, -21/100, -21/200, 9/200, 3/10],
    ![179/5000, 29/2500, -49/10000, -3/80, 181/5000, 109/10000, -23/5000, -3/80, 181/5000, 13/1250, -41/10000, -3/80, 179/5000, 101/10000, -17/5000, -3/80, -21/200, -3/100, 3/400, 9/80],
    ![-31/5000, -49/10000, 9/2500, 1/80, -39/5000, -23/5000, 49/10000, 1/80, -49/5000, -41/10000, 4/625, 1/80, -61/5000, -17/5000, 81/10000, 1/80, 9/200, 3/400, -3/100, -3/80],
    ![-1/10, -3/80, 1/80, 1/8, -1/10, -3/80, 1/80, 1/8, -1/10, -3/80, 1/80, 1/8, -1/10, -3/80, 1/80, 1/8, 3/10, 9/80, -3/80, -3/8],
    ![77/1250, 181/5000, -39/5000, -1/10, 159/2500, 181/5000, -49/5000, -1/10, 83/1250, 179/5000, -61/5000, -1/10, -21/100, -21/200, 9/200, 3/10, 93/1250, 169/5000, -91/5000, -1/10],
    ![181/5000, 109/10000, -23/5000, -3/80, 181/5000, 13/1250, -41/10000, -3/80, 179/5000, 101/10000, -17/5000, -3/80, -21/200, -3/100, 3/400, 9/80, 169/5000, 101/10000, -7/5000, -3/80],
    ![-39/5000, -23/5000, 49/10000, 1/80, -49/5000, -41/10000, 4/625, 1/80, -61/5000, -17/5000, 81/10000, 1/80, 9/200, 3/400, -3/100, -3/80, -91/5000, -7/5000, 121/10000, 1/80],
    ![-1/10, -3/80, 1/80, 1/8, -1/10, -3/80, 1/80, 1/8, -1/10, -3/80, 1/80, 1/8, 3/10, 9/80, -3/80, -3/8, -1/10, -3/80, 1/80, 1/8],
    ![159/2500, 181/5000, -49/5000, -1/10, 83/1250, 179/5000, -61/5000, -1/10, -21/100, -21/200, 9/200, 3/10, 93/1250, 169/5000, -91/5000, -1/10, 199/2500, 161/5000, -109/5000, -1/10],
    ![181/5000, 13/1250, -41/10000, -3/80, 179/5000, 101/10000, -17/5000, -3/80, -21/200, -3/100, 3/400, 9/80, 169/5000, 101/10000, -7/5000, -3/80, 161/5000, 13/1250, -1/10000, -3/80],
    ![-49/5000, -41/10000, 4/625, 1/80, -61/5000, -17/5000, 81/10000, 1/80, 9/200, 3/400, -3/100, -3/80, -91/5000, -7/5000, 121/10000, 1/80, -109/5000, -1/10000, 9/625, 1/80],
    ![-1/10, -3/80, 1/80, 1/8, -1/10, -3/80, 1/80, 1/8, 3/10, 9/80, -3/80, -3/8, -1/10, -3/80, 1/80, 1/8, -1/10, -3/80, 1/80, 1/8],
    ![83/1250, 179/5000, -61/5000, -1/10, -21/100, -21/200, 9/200, 3/10, 93/1250, 169/5000, -91/5000, -1/10, 199/2500, 161/5000, -109/5000, -1/10, 107/1250, 151/5000, -129/5000, -1/10],
    ![179/5000, 101/10000, -17/5000, -3/80, -21/200, -3/100, 3/400, 9/80, 169/5000, 101/10000, -7/5000, -3/80, 161/5000, 13/1250, -1/10000, -3/80, 151/5000, 109/10000, 7/5000, -3/80],
    ![-61/5000, -17/5000, 81/10000, 1/80, 9/200, 3/400, -3/100, -3/80, -91/5000, -7/5000, 121/10000, 1/80, -109/5000, -1/10000, 9/625, 1/80, -129/5000, 7/5000, 169/10000, 1/80],
    ![-1/10, -3/80, 1/80, 1/8, 3/10, 9/80, -3/80, -3/8, -1/10, -3/80, 1/80, 1/8, -1/10, -3/80, 1/80, 1/8, -1/10, -3/80, 1/80, 1/8]]

private theorem sampleMatrix_eq_certificateMatrix : sampleMatrix = certificateMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sampleMatrix, sample, certificateMatrix, readout, rho_eq_zero_iff, normSq]

/-- Every entry of the rational identity is checked by ordinary Lean arithmetic tactics. -/
private theorem inverseMatrix_mul_certificateMatrix :
    inverseMatrix * certificateMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [inverseMatrix, certificateMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem inverseMatrix_mul_sampleMatrix : inverseMatrix * sampleMatrix = 1 := by
  rw [sampleMatrix_eq_certificateMatrix, inverseMatrix_mul_certificateMatrix]

/-- Evaluating at the same twenty points proves independence of twenty global translates. -/
theorem fixed_translates_linearIndependent :
    LinearIndependent ℝ (fun i : Fin 20 => translate readout (sample i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hkernel : sampleMatrix *ᵥ c = 0 := by
    funext j
    have hj := congrFun hc (sample j)
    simpa [sampleMatrix, translate, Matrix.mulVec, dotProduct, mul_comm] using hj
  have hzero : c = 0 := by
    calc
      c = (1 : Matrix (Fin 20) (Fin 20) ℝ) *ᵥ c := (Matrix.one_mulVec c).symm
      _ = (inverseMatrix * sampleMatrix) *ᵥ c := by
        rw [inverseMatrix_mul_sampleMatrix]
      _ = inverseMatrix *ᵥ (sampleMatrix *ᵥ c) :=
        (Matrix.mulVec_mulVec c inverseMatrix sampleMatrix).symm
      _ = 0 := by rw [hkernel, Matrix.mulVec_zero]
  exact congrFun hzero i

private theorem fixed_span_le_translateSpan :
    Submodule.span ℝ (Set.range (fun i : Fin 20 => translate readout (sample i))) ≤
      translateSpan readout := by
  apply Submodule.span_le.mpr
  rintro g ⟨i, rfl⟩
  exact Submodule.subset_span ⟨sample i, rfl⟩

/-- The fixed evaluation certificate gives the matching global lower bound. -/
theorem twenty_le_translateSpan_finrank : 20 ≤ Module.finrank ℝ (translateSpan readout) := by
  have hfixed := finrank_span_eq_card fixed_translates_linearIndependent
  calc
    20 = Module.finrank ℝ
        (Submodule.span ℝ (Set.range (fun i : Fin 20 => translate readout (sample i)))) := by
      simpa using hfixed.symm
    _ ≤ Module.finrank ℝ (translateSpan readout) :=
      Submodule.finrank_mono fixed_span_le_translateSpan

/-- Exact dimension of the span of all translates on the full integer carrier. -/
theorem translateSpan_finrank_eq_twenty : Module.finrank ℝ (translateSpan readout) = 20 :=
  le_antisymm translateSpan_finrank_le_twenty twenty_le_translateSpan_finrank

/-- The control retains the explicit calibration and multiplicativity while differing from the norm. -/
theorem mod5_filter_control :
    (∀ z, 0 ≤ readout z) ∧
    (∀ z w, readout (gmul z w) = readout z * readout w) ∧
    readout (1, 0) = 1 ∧ readout (2, 0) = 4 ∧
    readout (0, 1) = 1 ∧ readout (1, 1) = 2 ∧
    readout ≠ normSq ∧
    Module.finrank ℝ (translateSpan readout) = 20 :=
  ⟨readout_nonnegative, readout_gmul, readout_one, readout_two,
    readout_imaginary_unit, readout_one_add_imaginary_unit,
    readout_not_normSq, translateSpan_finrank_eq_twenty⟩

end

end IDT.QMClosure.FiniteRankReadoutFilter
