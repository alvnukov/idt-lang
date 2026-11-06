import Proofs.QMClosure.NativeMixerInfiniteOrder
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The three-wire selected-row stabilizer under explicit matrix invariants

This is an abstract complex-matrix theorem conditional on the displayed
invariant contract. A separate adapter must prove that an actual native
circuit has these invariants. The result concerns all complex inputs at fixed
width three; it does not classify compressed input profiles, mixtures, higher
widths, physical probabilities, continuous dynamics, or full QM.
-/

namespace IDT.QMClosure.NativeThreeWireStabilizer

noncomputable section

open scoped Matrix BigOperators

abbrev Mat3 := NativeMixerInfiniteOrder.Mat3
abbrev spectator := NativeMixerInfiniteOrder.B

def uniform : Fin 3 → ℂ := fun _ => 1

def IsUnitary (U : Mat3) : Prop :=
  U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1

def FixesUniform (U : Mat3) : Prop := U.mulVec uniform = uniform

def FourthRoot (z : ℂ) : Prop :=
  z = 1 ∨ z = Complex.I ∨ z = -1 ∨ z = -Complex.I

structure Invariants (U : Mat3) : Prop where
  unitary : IsUnitary U
  uniform : FixesUniform U
  det_fourthRoot : FourthRoot U.det

def SameSelectedReadout (U V : Mat3) : Prop :=
  ∀ x : Fin 3 → ℂ,
    Complex.normSq (U.mulVec x 0) = Complex.normSq (V.mulVec x 0)

theorem fourthRoot_mul {z w : ℂ} (hz : FourthRoot z) (hw : FourthRoot w) :
    FourthRoot (z * w) := by
  rcases hz with hz | hz | hz | hz <;>
    rcases hw with hw | hw | hw | hw <;>
    subst z <;> subst w <;> norm_num [FourthRoot]

theorem fourthRoot_star {z : ℂ} (hz : FourthRoot z) : FourthRoot (star z) := by
  rcases hz with hz | hz | hz | hz <;> subst z <;> norm_num [FourthRoot]

theorem invariants_one : Invariants (1 : Mat3) := by
  constructor
  · constructor <;> simp
  · simp [FixesUniform]
  · simp [FourthRoot]

theorem invariants_mul {U V : Mat3} (hU : Invariants U) (hV : Invariants V) :
    Invariants (U * V) := by
  constructor
  · constructor
    · rw [Matrix.conjTranspose_mul]
      calc
        V.conjTranspose * U.conjTranspose * (U * V) =
            V.conjTranspose * (U.conjTranspose * U) * V := by
              simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hU.unitary.1]; simpa using hV.unitary.1
    · rw [Matrix.conjTranspose_mul]
      calc
        U * V * (V.conjTranspose * U.conjTranspose) =
            U * (V * V.conjTranspose) * U.conjTranspose := by
              simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hV.unitary.2]; simpa using hU.unitary.2
  · change (U * V).mulVec uniform = uniform
    rw [← Matrix.mulVec_mulVec, hV.uniform, hU.uniform]
  · rw [Matrix.det_mul]
    exact fourthRoot_mul hU.det_fourthRoot hV.det_fourthRoot

theorem invariants_conjTranspose {U : Mat3} (hU : Invariants U) :
    Invariants U.conjTranspose := by
  constructor
  · constructor
    · simpa using hU.unitary.2
    · simpa using hU.unitary.1
  · change U.conjTranspose.mulVec uniform = uniform
    have hu : U.mulVec uniform = uniform := hU.uniform
    have h := congrArg (fun x => U.conjTranspose.mulVec x) hu
    simpa only [Matrix.mulVec_mulVec, hU.unitary.1, Matrix.one_mulVec] using h.symm
  · rw [Matrix.det_conjTranspose]
    exact fourthRoot_star hU.det_fourthRoot

theorem spectator_invariants : Invariants spectator := by
  constructor
  · constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      norm_num [spectator, NativeMixerInfiniteOrder.B, NativeMixerInfiniteOrder.a,
        NativeMixerInfiniteOrder.b, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im,
        Complex.div_re, Complex.div_im]
  · ext i
    fin_cases i <;> apply Complex.ext <;>
      norm_num [FixesUniform, uniform, spectator, NativeMixerInfiniteOrder.B,
        NativeMixerInfiniteOrder.a, NativeMixerInfiniteOrder.b, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im,
        Complex.div_re, Complex.div_im]
  · right; left
    apply Complex.ext <;>
      norm_num [spectator, NativeMixerInfiniteOrder.B, NativeMixerInfiniteOrder.a,
        NativeMixerInfiniteOrder.b, Matrix.det_fin_three, Matrix.cons_val_two, Complex.mul_re,
        Complex.mul_im, Complex.div_re, Complex.div_im]

theorem spectator_pow_row_zero (n : ℕ) :
    ∀ j : Fin 3, (spectator ^ n) 0 j = (1 : Mat3) 0 j := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro j
    simp only [pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, ih]
    fin_cases j <;> simp [spectator, NativeMixerInfiniteOrder.B, Matrix.one_apply]

theorem complex_eq_of_three_norms {z w : ℂ}
    (h0 : Complex.normSq z = Complex.normSq w)
    (h1 : Complex.normSq (z + 1) = Complex.normSq (w + 1))
    (hi : Complex.normSq (z + Complex.I) = Complex.normSq (w + Complex.I)) :
    z = w := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im] at h0 h1 hi
  apply Complex.ext <;> nlinarith

theorem selected_rows_equal {U V : Mat3}
    (hU : FixesUniform U) (hV : FixesUniform V)
    (hread : SameSelectedReadout U V) : ∀ j, U 0 j = V 0 j := by
  intro j
  apply complex_eq_of_three_norms
  · simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using
      hread (Pi.single j 1)
  · have h := hread (Pi.single j 1 + uniform)
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_single_one,
      Matrix.mulVec_single_one, hU, hV] at h
    simpa [uniform] using h
  · have h := hread (Pi.single j 1 + Complex.I • uniform)
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Matrix.mulVec_single_one,
      Matrix.mulVec_single_one, hU, hV] at h
    simpa [uniform] using h

def stabilizerBlock (z : ℂ) : Mat3 :=
  !![1, 0, 0; 0, z, 1 - z; 0, 1 - z, z]

theorem stabilizer_classification {R : Mat3} (hR : Invariants R)
    (hrow : ∀ j, R 0 j = (1 : Mat3) 0 j) :
    ∃ r : Fin 4, R = spectator ^ r.val := by
  have h00 : R 0 0 = 1 := by simpa using hrow 0
  have h01 : R 0 1 = 0 := by simpa using hrow 1
  have h02 : R 0 2 = 0 := by simpa using hrow 2
  have hcol (i : Fin 3) : R i 0 = (1 : Mat3) i 0 := by
    have h := congrArg (fun M : Mat3 => M i 0) hR.unitary.2
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      h00, h01, h02] using h
  have h10 : R 1 0 = 0 := by simpa using hcol 1
  have h20 : R 2 0 = 0 := by simpa using hcol 2
  have hrowsum (i : Fin 3) : R i 0 + R i 1 + R i 2 = 1 := by
    have hu : R.mulVec uniform = uniform := hR.uniform
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, uniform, add_assoc] using
      congrFun hu i
  have hcolsum (j : Fin 3) : R 0 j + R 1 j + R 2 j = 1 := by
    have hu : R.conjTranspose.mulVec uniform = uniform :=
      (invariants_conjTranspose hR).uniform
    have h := congrArg star (congrFun hu j)
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, uniform,
      Matrix.conjTranspose_apply, add_assoc] using h
  have h12 : R 1 2 = 1 - R 1 1 := by
    have h := hrowsum 1
    rw [h10, zero_add] at h
    linear_combination h
  have h21 : R 2 1 = 1 - R 1 1 := by
    have h := hcolsum 1
    rw [h01, zero_add] at h
    linear_combination h
  have h22 : R 2 2 = R 1 1 := by
    have h := hrowsum 2
    rw [h20, zero_add, h21] at h
    linear_combination h
  have hblock : R = stabilizerBlock (R 1 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [stabilizerBlock, h00, h01, h02, h10, h20, h12, h21, h22]
  have hdet : R.det = 2 * R 1 1 - 1 := by
    calc
      R.det = (stabilizerBlock (R 1 1)).det := congrArg Matrix.det hblock
      _ = 2 * R 1 1 - 1 := by simp [stabilizerBlock, Matrix.det_fin_three]; ring
  rcases hR.det_fourthRoot with hr | hr | hr | hr
  · refine ⟨0, ?_⟩
    have hz : R 1 1 = 1 := by linear_combination (1 / 2 : ℂ) * (hdet.symm.trans hr)
    rw [hblock]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [stabilizerBlock, hz]
  · refine ⟨1, ?_⟩
    have hz : R 1 1 = NativeMixerInfiniteOrder.a := by
      dsimp [NativeMixerInfiniteOrder.a]
      linear_combination (1 / 2 : ℂ) * (hdet.symm.trans hr)
    rw [hblock]
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [stabilizerBlock, hz, spectator, NativeMixerInfiniteOrder.B,
        NativeMixerInfiniteOrder.a, NativeMixerInfiniteOrder.b, Complex.div_re,
        Complex.div_im]
  · refine ⟨2, ?_⟩
    have hz : R 1 1 = 0 := by linear_combination (1 / 2 : ℂ) * (hdet.symm.trans hr)
    rw [hblock]
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [stabilizerBlock, hz, spectator, NativeMixerInfiniteOrder.B,
        NativeMixerInfiniteOrder.a, NativeMixerInfiniteOrder.b, pow_succ,
        Matrix.mul_apply, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im,
        Complex.div_re, Complex.div_im]
  · refine ⟨3, ?_⟩
    have hz : R 1 1 = NativeMixerInfiniteOrder.b := by
      dsimp [NativeMixerInfiniteOrder.b]
      linear_combination (1 / 2 : ℂ) * (hdet.symm.trans hr)
    rw [hblock]
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [stabilizerBlock, hz, spectator, NativeMixerInfiniteOrder.B,
        NativeMixerInfiniteOrder.a, NativeMixerInfiniteOrder.b, pow_succ,
        Matrix.mul_apply, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im,
        Complex.div_re, Complex.div_im]

theorem selected_readout_iff_suffix {U V : Mat3}
    (hU : Invariants U) (hV : Invariants V) :
    SameSelectedReadout U V ↔ ∃ r : Fin 4, V = spectator ^ r.val * U := by
  constructor
  · intro hread
    have hrows := selected_rows_equal hU.uniform hV.uniform hread
    let R : Mat3 := V * U.conjTranspose
    have hR : Invariants R := invariants_mul hV (invariants_conjTranspose hU)
    have hrow : ∀ j, R 0 j = (1 : Mat3) 0 j := by
      intro j
      have h := congrArg (fun M : Mat3 => M 0 j) hU.unitary.2
      simpa only [R, Matrix.mul_apply, ← hrows] using h
    obtain ⟨r, hr⟩ := stabilizer_classification hR hrow
    refine ⟨r, ?_⟩
    calc
      V = R * U := by
        dsimp [R]
        rw [Matrix.mul_assoc, hU.unitary.1, Matrix.mul_one]
      _ = spectator ^ r.val * U := by rw [hr]
  · rintro ⟨r, rfl⟩ x
    congr 1
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ,
      spectator_pow_row_zero]

end

end IDT.QMClosure.NativeThreeWireStabilizer
