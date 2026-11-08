import Proofs.QMClosure.RawSparsePhaseTwistControl

/-!
# Continuous phase transports of the three-coordinate native operation

Every fixed parameter gives a weight-preserving conjugate of the supplied
native complex mixer. All results concern this explicit mathematical model.
-/

namespace IDT.QMClosure.RawPlanePhaseFamily

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

open RawSparseConservationSelection
open Filter
open scoped Topology

abbrev Vec := Fin 3 → ℂ

def W (x : Vec) : ℝ :=
  Complex.normSq (x 0) + Complex.normSq (x 1) + Complex.normSq (x 2)

abbrev phase := RawSparsePhaseTwistControl.phase
abbrev a := NativeAttenuationCircuit.a
abbrev b := NativeAttenuationCircuit.b

def ratio (x : Vec) : ℝ := Complex.normSq (x 0) / W x
def H (t : ℝ) (x : Vec) : Vec := phase (t * ratio x) • x
def native (x y : Vec) : Vec := a • x + b • y
def familyM (t : ℝ) (x y : Vec) : Vec := H t (native (H (-t) x) (H (-t) y))
def familyOperation (t : ℝ) (p : Vec × Vec) : Vec × Vec :=
  (familyM t p.1 p.2, familyM t p.2 p.1)

theorem W_nonnegative (x : Vec) : 0 ≤ W x := by
  exact add_nonneg (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
    (Complex.normSq_nonneg _)

@[simp] theorem W_zero : W 0 = 0 := by simp [W]

theorem W_eq_zero_iff (x : Vec) : W x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have h0 := Complex.normSq_nonneg (x 0)
    have h1 := Complex.normSq_nonneg (x 1)
    have h2 := Complex.normSq_nonneg (x 2)
    have hz0 : x 0 = 0 := Complex.normSq_eq_zero.mp (by unfold W at hx; linarith)
    have hz1 : x 1 = 0 := Complex.normSq_eq_zero.mp (by unfold W at hx; linarith)
    have hz2 : x 2 = 0 := Complex.normSq_eq_zero.mp (by unfold W at hx; linarith)
    funext i
    fin_cases i <;> assumption
  · rintro rfl
    exact W_zero

theorem W_smul (c : ℂ) (x : Vec) : W (c • x) = Complex.normSq c * W x := by
  simp only [W, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]
  ring

@[simp] theorem ratio_zero : ratio 0 = 0 := by simp [ratio]

theorem ratio_smul (c : ℂ) (hc : c ≠ 0) (x : Vec) : ratio (c • x) = ratio x := by
  have hn : Complex.normSq c ≠ 0 := (Complex.normSq_pos.mpr hc).ne'
  simp only [ratio, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, W_smul]
  exact mul_div_mul_left _ _ hn

@[simp] theorem H_zero (t : ℝ) : H t 0 = 0 := by simp [H]

@[simp] theorem H_zero_parameter (x : Vec) : H 0 x = x := by
  simp [H, phase, RawSparsePhaseTwistControl.phase]

theorem ratio_H (t : ℝ) (x : Vec) : ratio (H t x) = ratio x :=
  ratio_smul _ (RawSparsePhaseTwistControl.phase_ne_zero _) x

theorem W_H (t : ℝ) (x : Vec) : W (H t x) = W x := by
  rw [H, W_smul, RawSparsePhaseTwistControl.phase_normSq, one_mul]

theorem H_smul (t : ℝ) (c : ℂ) (x : Vec) : H t (c • x) = c • H t x := by
  by_cases hc : c = 0
  · subst c
    simp
  · rw [H, ratio_smul c hc, H, smul_smul, smul_smul, mul_comm]

@[simp] theorem H_neg_H (t : ℝ) (x : Vec) : H (-t) (H t x) = x := by
  simp only [H, ratio_smul _ (RawSparsePhaseTwistControl.phase_ne_zero _),
    smul_smul, neg_mul, RawSparsePhaseTwistControl.phase_neg_mul, one_smul]

@[simp] theorem H_H_neg (t : ℝ) (x : Vec) : H t (H (-t) x) = x := by
  simpa only [neg_neg] using H_neg_H (-t) x

theorem H_injective (t : ℝ) : Function.Injective (H t) := by
  intro x y h
  have hh := congrArg (H (-t)) h
  simpa only [H_neg_H] using hh

theorem H_surjective (t : ℝ) : Function.Surjective (H t) := by
  intro x
  exact ⟨H (-t) x, H_H_neg t x⟩

theorem H_coordinate_norm (t : ℝ) (x : Vec) (i : Fin 3) : ‖H t x i‖ = ‖x i‖ := by
  have he : Complex.normSq (H t x i) = Complex.normSq (x i) := by
    simp only [H, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
      RawSparsePhaseTwistControl.phase_normSq, one_mul]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at he
  nlinarith [norm_nonneg (H t x i), norm_nonneg (x i)]

theorem continuous_W : Continuous W := by
  exact ((Complex.continuous_normSq.comp (continuous_apply 0)).add
    (Complex.continuous_normSq.comp (continuous_apply 1))).add
    (Complex.continuous_normSq.comp (continuous_apply 2))

theorem continuousAt_ratio {x : Vec} (hx : x ≠ 0) : ContinuousAt ratio x := by
  exact (Complex.continuous_normSq.comp (continuous_apply 0)).continuousAt.div
    continuous_W.continuousAt (fun h => hx ((W_eq_zero_iff x).mp h))

theorem continuous_H : Continuous (fun p : ℝ × Vec => H p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hx : p.2 = 0
  · apply continuousAt_pi.mpr
    intro i
    have hn : Tendsto (fun q : ℝ × Vec => ‖H q.1 q.2 i‖) (𝓝 p) (𝓝 0) := by
      have hc := ((continuous_apply i).comp continuous_snd).norm.tendsto p
      simpa only [H_coordinate_norm, Function.comp_apply, hx, Pi.zero_apply, norm_zero]
        using hc
    have ht := tendsto_zero_iff_norm_tendsto_zero.mpr hn
    simpa only [ContinuousAt, hx, H_zero, Pi.zero_apply] using ht
  · have hr := (continuousAt_ratio hx).comp continuous_snd.continuousAt
    have hp := RawSparsePhaseTwistControl.continuous_phase.continuousAt.comp
      (continuous_fst.continuousAt.mul hr)
    exact hp.smul continuous_snd.continuousAt

theorem native_apply (x y : Vec) (i : Fin 3) : native x y i = a * x i + b * y i := rfl

theorem native_diagonal (x : Vec) : native x x = x := by
  funext i
  apply Complex.ext <;>
    norm_num [native_apply, a, b, NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring

theorem native_square (x y : Vec) : native (native x y) (native y x) = y := by
  funext i
  apply Complex.ext <;>
    norm_num [native_apply, a, b, NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring

theorem native_smul (c : ℂ) (x y : Vec) :
    native (c • x) (c • y) = c • native x y := by
  funext i
  simp only [native_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem native_conserved (x y : Vec) :
    W (native x y) + W (native y x) = W x + W y := by
  have h0 := NativeMixerEventConeExclusion.mixer_conserves (x 0) (y 0)
  have h1 := NativeMixerEventConeExclusion.mixer_conserves (x 1) (y 1)
  have h2 := NativeMixerEventConeExclusion.mixer_conserves (x 2) (y 2)
  simp only [NativeAttenuationCircuit.mixer_fst, NativeAttenuationCircuit.mixer_snd]
    at h0 h1 h2
  simp only [W, native_apply, a, b]
  rw [add_comm (NativeAttenuationCircuit.a * y 0),
    add_comm (NativeAttenuationCircuit.a * y 1),
    add_comm (NativeAttenuationCircuit.a * y 2)]
  linarith

theorem native_sparse (x y z : Vec) :
    W (native (native x y) (a • z)) + W (native (native y x) (b • z)) =
      W (native x z) + W (a • y) := by
  have hi (i : Fin 3) := RawSparsePhaseTwistControl.native_sparse_identity (x i) (y i) (z i)
  simp only [RawSparsePhaseTwistControl.N, NativeAttenuationCircuit.mixer_fst,
    NativeAttenuationCircuit.mixer_snd] at hi
  have h0 := hi 0
  have h1 := hi 1
  have h2 := hi 2
  simp only [W, native_apply, Pi.smul_apply, smul_eq_mul, a, b]
  rw [add_comm (NativeAttenuationCircuit.a * y 0),
    add_comm (NativeAttenuationCircuit.a * y 1),
    add_comm (NativeAttenuationCircuit.a * y 2)]
  linarith

theorem familyM_H (t : ℝ) (x y : Vec) :
    familyM t (H t x) (H t y) = H t (native x y) := by
  simp only [familyM, H_neg_H]

@[simp] theorem familyM_zero (x y : Vec) : familyM 0 x y = native x y := by
  simp only [familyM, neg_zero, H_zero_parameter]

theorem W_familyM_of_ratio_eq (t : ℝ) (x y : Vec) (hr : ratio x = ratio y) :
    W (familyM t x y) = W (native x y) := by
  rw [familyM, W_H]
  simp only [H, hr, native_smul, W_smul,
    RawSparsePhaseTwistControl.phase_normSq, one_mul]

theorem familyM_diagonal (t : ℝ) (x : Vec) : familyM t x x = x := by
  rw [familyM, native_diagonal, H_H_neg]

theorem familyM_smul (t : ℝ) (c : ℂ) (x y : Vec) :
    familyM t (c • x) (c • y) = c • familyM t x y := by
  simp only [familyM, H_smul, native_smul]

theorem familyOperation_square (t : ℝ) (p : Vec × Vec) :
    familyOperation t (familyOperation t p) = p.swap := by
  rcases p with ⟨x, y⟩
  apply Prod.ext <;>
    simp only [familyOperation, familyM, H_neg_H, native_square, H_H_neg, Prod.swap]

theorem familyOperation_transparent (t : ℝ) (x : Vec) :
    familyOperation t (x, x) = (x, x) := by
  simp only [familyOperation, familyM_diagonal]

def familyContract (t : ℝ) : Contract Vec where
  chosenZero := 0
  operation := familyOperation t
  weight := W
  vacuum := W_zero
  square := familyOperation_square t
  transparent := familyOperation_transparent t

theorem family_m (t : ℝ) (x y : Vec) : m (familyContract t) x y = familyM t x y := rfl

theorem family_A (t : ℝ) (x : Vec) : A (familyContract t) x = a • x := by
  change H t (native (H (-t) x) (H (-t) 0)) = a • x
  simp only [H_zero, native, smul_zero, add_zero, H_smul, H_H_neg]

theorem family_B (t : ℝ) (x : Vec) : B (familyContract t) x = b • x := by
  change H t (native (H (-t) 0) (H (-t) x)) = b • x
  simp only [H_zero, native, smul_zero, zero_add, H_smul, H_H_neg]

theorem family_A_H (t : ℝ) (x : Vec) : A (familyContract t) (H t x) = H t (a • x) := by
  rw [family_A, H_smul]

theorem family_B_H (t : ℝ) (x : Vec) : B (familyContract t) (H t x) = H t (b • x) := by
  rw [family_B, H_smul]

theorem familySparse (t : ℝ) : SparseMarginalLaw (familyContract t) := by
  intro x y z
  obtain ⟨x, rfl⟩ := H_surjective t x
  obtain ⟨y, rfl⟩ := H_surjective t y
  obtain ⟨z, rfl⟩ := H_surjective t z
  change W (familyM t (familyM t (H t x) (H t y)) (A (familyContract t) (H t z))) +
      W (familyM t (familyM t (H t y) (H t x)) (B (familyContract t) (H t z))) =
    W (familyM t (H t x) (H t z)) + W (A (familyContract t) (H t y))
  simp only [familyM_H, family_A_H, family_B_H, W_H]
  exact native_sparse x y z

theorem familyTests (t : ℝ) : RawSparseConservationTests.Tests (familyContract t) :=
  RawSparseConservationTests.of_sparse _ (familySparse t)

theorem family_conserved (t : ℝ) : PairConserved (familyContract t) := by
  intro x y
  change W (familyM t x y) + W (familyM t y x) = W x + W y
  simp only [familyM, W_H]
  simpa only [W_H] using native_conserved (H (-t) x) (H (-t) y)

theorem continuous_native : Continuous (fun p : Vec × Vec => native p.1 p.2) :=
  (continuous_const.smul continuous_fst).add (continuous_const.smul continuous_snd)

theorem continuous_familyM : Continuous (fun p : ℝ × (Vec × Vec) =>
    familyM p.1 p.2.1 p.2.2) := by
  have hxin : Continuous (fun p : ℝ × (Vec × Vec) => (-p.1, p.2.1)) :=
    continuous_fst.neg.prodMk (continuous_fst.comp continuous_snd)
  have hyin : Continuous (fun p : ℝ × (Vec × Vec) => (-p.1, p.2.2)) :=
    continuous_fst.neg.prodMk (continuous_snd.comp continuous_snd)
  have hx : Continuous (fun p : ℝ × (Vec × Vec) => H (-p.1) p.2.1) :=
    continuous_H.comp' (f := fun p : ℝ × (Vec × Vec) => (-p.1, p.2.1)) hxin
  have hy : Continuous (fun p : ℝ × (Vec × Vec) => H (-p.1) p.2.2) :=
    continuous_H.comp' (f := fun p : ℝ × (Vec × Vec) => (-p.1, p.2.2)) hyin
  have hn : Continuous (fun p : ℝ × (Vec × Vec) =>
      native (H (-p.1) p.2.1) (H (-p.1) p.2.2)) :=
    (continuous_const.smul hx).add (continuous_const.smul hy)
  have hin : Continuous (fun p : ℝ × (Vec × Vec) =>
      (p.1, native (H (-p.1) p.2.1) (H (-p.1) p.2.2))) :=
    continuous_fst.prodMk hn
  exact continuous_H.comp' (f := fun p : ℝ × (Vec × Vec) =>
    (p.1, native (H (-p.1) p.2.1) (H (-p.1) p.2.2))) hin

theorem jointcontinuous_family : Continuous (fun p : ℝ × (Vec × Vec) =>
    familyOperation p.1 p.2) := by
  have hs : Continuous (fun p : ℝ × (Vec × Vec) => (p.1, (p.2.2, p.2.1))) :=
    continuous_fst.prodMk
      ((continuous_snd.comp continuous_snd).prodMk (continuous_fst.comp continuous_snd))
  exact continuous_familyM.prodMk
    (continuous_familyM.comp' (f := fun p : ℝ × (Vec × Vec) =>
      (p.1, (p.2.2, p.2.1))) hs)

theorem continuous_familyOperation (t : ℝ) : Continuous (familyOperation t) :=
  jointcontinuous_family.comp' (f := fun p : Vec × Vec => (t, p))
    (continuous_const.prodMk continuous_id)

end
end IDT.QMClosure.RawPlanePhaseFamily
