import Proofs.QMClosure.NativeMixerEventConeExclusion
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# An infinite-order word in the supplied native mixer model

The fixed three-wire native word (12,12,12,01) has no positive power equal
to identity. This is a universal exact algebraic result in the supplied complex
coordinate model. It does not establish density, continuous physical dynamics,
physical port availability, a probability law, or full QM closure.
-/

namespace IDT.QMClosure.NativeMixerInfiniteOrder

noncomputable section

open NativeMixerEventConeExclusion MixerGeneratedProcessWall
open scoped Matrix BigOperators

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℂ

def a : ℂ := (1 + Complex.I) / 2
def b : ℂ := (1 - Complex.I) / 2
def A : Mat3 := !![a, b, 0; b, a, 0; 0, 0, 1]
def B : Mat3 := !![1, 0, 0; 0, a, b; 0, b, a]

/-- Matrix composition is reverse chronological order. -/
def K : Mat3 := A * B ^ 3

/-- This is a word in the existing syntax, using only the existing mixer. -/
def cK : NativeCircuit := .seq (.seq (.seq gate12 gate12) gate12) gate01

theorem gate01_action (v : Fin 3 → ℂ) : gate01.eval v = A.mulVec v := by
  ext k
  fin_cases k <;> apply Complex.ext <;>
    norm_num [gate01, Circuit.eval, pairGate, pairReplace, mixer, Raw,
      CompositeProductControls.RawSign.N, CompositeProductControls.RawSign.n,
      A, a, b, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.ext_iff,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> first | rfl | ring

theorem gate12_action (v : Fin 3 → ℂ) : gate12.eval v = B.mulVec v := by
  ext k
  fin_cases k <;> apply Complex.ext <;>
    norm_num [gate12, Circuit.eval, pairGate, pairReplace, mixer, Raw,
      CompositeProductControls.RawSign.N, CompositeProductControls.RawSign.n,
      B, a, b, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.ext_iff,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> first | rfl | ring

theorem native_word_action (v : Fin 3 → ℂ) : cK.eval v = K.mulVec v := by
  change gate01.eval (gate12.eval (gate12.eval (gate12.eval v))) = _
  rw [gate01_action, gate12_action, gate12_action, gate12_action]
  simp [K, pow_succ, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- The zero-coherent-sum plane and its coordinate left inverse. -/
def W : Matrix (Fin 3) (Fin 2) ℂ := !![1, 0; 0, 1; -1, -1]
def D : Matrix (Fin 2) (Fin 3) ℂ := !![1, 0, 0; 0, 1, 0]
def M : Mat2 := !![Complex.I / 2, -a; 1 / 2 - Complex.I, b]
def C : Mat2 := !![Complex.I, -1 - Complex.I; 1 - 2 * Complex.I, 1 - Complex.I]

theorem left_inverse : D * W = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, W, Matrix.mul_apply, Fin.sum_univ_succ]

theorem intertwines : K * W = W * M := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [K, A, B, W, M, a, b, pow_succ, Matrix.mul_apply,
      Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im]

theorem C_eq_two_smul : C = (2 : ℂ) • M := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [C, M, a, b, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im]

theorem C_quadratic : C ^ 2 = C - (4 : ℂ) • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [C, pow_two, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im]

theorem trace_C : Matrix.trace C = 1 := by
  norm_num [Matrix.trace, Matrix.diag, C, Fin.sum_univ_succ]

def traceSequence : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => traceSequence (n + 1) - 4 * traceSequence n

theorem traceSequence_odd (n : ℕ) : traceSequence (n + 1) % 2 = 1 := by
  induction n with
  | zero => norm_num [traceSequence]
  | succ n ih =>
      rw [show n.succ + 1 = n + 2 by omega, traceSequence]
      omega

theorem C_pow_recurrence (n : ℕ) :
    C ^ (n + 2) = C ^ (n + 1) - (4 : ℂ) • C ^ n := by
  calc
    C ^ (n + 2) = C ^ n * C ^ 2 := pow_add _ _ _
    _ = C ^ n * (C - (4 : ℂ) • (1 : Mat2)) := by rw [C_quadratic]
    _ = C ^ (n + 1) - (4 : ℂ) • C ^ n := by
      rw [mul_sub, Matrix.mul_smul, mul_one, ← pow_succ]

theorem trace_C_pow (n : ℕ) : Matrix.trace (C ^ n) = (traceSequence n : ℂ) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [traceSequence, Matrix.trace_one]
  | one => simpa [traceSequence] using trace_C
  | more n ih₀ ih₁ =>
      rw [C_pow_recurrence, Matrix.trace_sub, Matrix.trace_smul, ih₀, ih₁]
      simp [traceSequence]

theorem C_pow_scale (n : ℕ) : C ^ n = (2 : ℂ) ^ n • M ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, C_eq_two_smul, Matrix.smul_mul, Matrix.mul_smul]
      simp [smul_smul, pow_succ]

theorem M_pow_ne_one (n : ℕ) (hn : 0 < n) : M ^ n ≠ 1 := by
  intro h
  have ht := trace_C_pow n
  rw [C_pow_scale, h, Matrix.trace_smul] at ht
  have he : (traceSequence n : ℂ) = ((2 : ℤ) ^ (n + 1) : ℤ) := by
    norm_num [Matrix.trace_one, pow_succ] at ht ⊢
    exact ht.symm
  have hz : traceSequence n = (2 : ℤ) ^ (n + 1) := by exact_mod_cast he
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have ho := traceSequence_odd m
  rw [hz] at ho
  have heven : ((2 : ℤ) ^ (m + 1 + 1)) % 2 = 0 := by
    rw [pow_succ]
    omega
  omega

theorem K_pow_intertwines (n : ℕ) : K ^ n * W = W * M ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Matrix.mul_assoc, intertwines, ← Matrix.mul_assoc, ih,
        Matrix.mul_assoc, ← pow_succ]

/-- Every positive power of this one fixed native word is nonidentity. -/
theorem native_word_infinite_order (n : ℕ) (hn : 0 < n) : K ^ n ≠ 1 := by
  intro h
  have hw := K_pow_intertwines n
  rw [h, Matrix.one_mul] at hw
  have hd : D * W = D * (W * M ^ n) := congrArg (fun X => D * X) hw
  simp only [← Matrix.mul_assoc, left_inverse, one_mul] at hd
  exact M_pow_ne_one n hn hd.symm

end

end IDT.QMClosure.NativeMixerInfiniteOrder
