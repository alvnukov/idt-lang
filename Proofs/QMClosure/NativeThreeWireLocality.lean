import Proofs.QMClosure.NativeThreeWireStabilizer
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Exact three-wire native spectator locality

The matrix representation below covers every constructor of the existing native
circuit grammar. A supplied readout invariant under complete evaluation equality
and a final spectator mixer descends along the full selected-weight profile on
all complex three-wire inputs. Spectator locality remains a supplied physical
premise; the complex matrix model is a mathematical representation.

The separate compressed-input counterexample is an arbitrary real probe readout,
not a normalized probability model. It excludes inferring compressed-profile
descent from these same generic premises. No wider-wire, mixture, attenuation,
physical preparation, norm-control, or full-QM conclusion is asserted.
-/

namespace IDT.QMClosure.NativeThreeWireLocality

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

open MixerGeneratedProcessWall NativeMixerEventConeExclusion
open NativeThreeWireStabilizer
open scoped Matrix BigOperators

abbrev a := NativeMixerInfiniteOrder.a
abbrev b := NativeMixerInfiniteOrder.b

/-- Literal matrix of an ordered pair generator; the two ports are distinct. -/
def pairMatrix (i j : Fin 3) : Mat3 := fun k l =>
  if k = i then (if l = i then a else if l = j then b else 0)
  else if k = j then (if l = i then b else if l = j then a else 0)
  else if k = l then 1 else 0

/-- The syntax's permutation convention is `v ↦ v ∘ e`. -/
abbrev permutationMatrix (e : Equiv.Perm (Fin 3)) : Mat3 := e.permMatrix ℂ

/-- Matrix multiplication is reverse chronological order. -/
def circuitMatrix : NativeCircuit → Mat3
  | .identity => 1
  | .pair i j _ => pairMatrix i j
  | .permute e => permutationMatrix e
  | .seq c d => circuitMatrix d * circuitMatrix c

theorem pair_action (i j : Fin 3) (hij : i ≠ j) (x : Fin 3 → ℂ) :
    (Circuit.pair i j hij : NativeCircuit).eval x = (pairMatrix i j).mulVec x := by
  ext k
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals
    fin_cases k <;>
      simp [Circuit.eval, pairGate, pairReplace, pairMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ]
  all_goals
    apply Complex.ext <;>
      norm_num [mixer, Raw,
        CompositeProductControls.RawSign.N, CompositeProductControls.RawSign.n,
        a, b, NativeMixerInfiniteOrder.a, NativeMixerInfiniteOrder.b,
        Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring

/-- Exact action on all vectors, not only on basis columns. -/
theorem circuit_action (c : NativeCircuit) (x : Fin 3 → ℂ) :
    c.eval x = (circuitMatrix c).mulVec x := by
  induction c generalizing x with
  | identity => simp [Circuit.eval, circuitMatrix]
  | pair i j hij => exact pair_action i j hij x
  | permute e =>
      simpa [Circuit.eval, circuitMatrix, permutationMatrix] using
        (Matrix.permMatrix_mulVec e (v := x)).symm
  | seq c d hc hd =>
      change d.eval (c.eval x) = _
      rw [hc, hd]
      simp only [circuitMatrix, Matrix.mulVec_mulVec]

theorem pair_unitary (i j : Fin 3) (hij : i ≠ j) : IsUnitary (pairMatrix i j) := by
  constructor <;> ext k l
  all_goals
    fin_cases i <;> fin_cases j <;> try contradiction
  all_goals
    fin_cases k <;> fin_cases l <;>
      simp [pairMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_succ]
  all_goals
    apply Complex.ext <;>
      norm_num [a, b, NativeMixerInfiniteOrder.a, NativeMixerInfiniteOrder.b,
        Complex.mul_re, Complex.mul_im, Complex.div_re,
        Complex.div_im]

theorem pair_fixes_uniform (i j : Fin 3) (hij : i ≠ j) :
    FixesUniform (pairMatrix i j) := by
  change (pairMatrix i j).mulVec uniform = uniform
  ext k
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals
    fin_cases k <;>
      simp [pairMatrix, uniform, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals
    apply Complex.ext <;>
      norm_num [a, b, NativeMixerInfiniteOrder.a,
        NativeMixerInfiniteOrder.b, Complex.div_re, Complex.div_im]

/-- Each actual pair generator has determinant `i`. -/
theorem pair_determinant (i j : Fin 3) (hij : i ≠ j) :
    (pairMatrix i j).det = Complex.I := by
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals
    simp [Matrix.det_fin_three, pairMatrix]
  all_goals
    apply Complex.ext <;>
      norm_num [a, b,
        NativeMixerInfiniteOrder.a, NativeMixerInfiniteOrder.b,
        Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem pair_invariants (i j : Fin 3) (hij : i ≠ j) :
    Invariants (pairMatrix i j) := by
  exact ⟨pair_unitary i j hij, pair_fixes_uniform i j hij,
    by rw [pair_determinant i j hij]; simp [FourthRoot]⟩

theorem permutation_invariants (e : Equiv.Perm (Fin 3)) :
    Invariants (permutationMatrix e) := by
  constructor
  · constructor
    · simp only [permutationMatrix, Matrix.conjTranspose_permMatrix,
        ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]
    · simp only [permutationMatrix, Matrix.conjTranspose_permMatrix,
        ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]
  · ext k
    simp [permutationMatrix, Matrix.permMatrix_mulVec, uniform]
  · rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h
    · simp [h, FourthRoot]
    · simp [h, FourthRoot]

/-- Invariants are derived from actual finite generators, never assumed. -/
theorem circuit_invariants (c : NativeCircuit) : Invariants (circuitMatrix c) := by
  induction c with
  | identity => exact invariants_one
  | pair i j hij => exact pair_invariants i j hij
  | permute e => exact permutation_invariants e
  | seq c d hc hd => exact invariants_mul hd hc

theorem gate12_matrix : circuitMatrix gate12 = spectator := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circuitMatrix, gate12, pairMatrix, spectator, NativeMixerInfiniteOrder.B]

/-- An actual circuit appending `n` spectator gates. -/
def appendSpectator (c : NativeCircuit) : ℕ → NativeCircuit
  | 0 => c
  | n + 1 => .seq (appendSpectator c n) gate12

theorem appendSpectator_matrix (c : NativeCircuit) (n : ℕ) :
    circuitMatrix (appendSpectator c n) = spectator ^ n * circuitMatrix c := by
  induction n with
  | zero => simp [appendSpectator]
  | succ n ih =>
      simp only [appendSpectator, circuitMatrix, gate12_matrix, ih]
      rw [pow_succ', Matrix.mul_assoc]

theorem matrix_eq_complete_eval {c d : NativeCircuit}
    (h : circuitMatrix c = circuitMatrix d) : ∀ x, c.eval x = d.eval x := by
  intro x
  rw [circuit_action, circuit_action, h]

/-- Generic readout premises: complete-evaluation equality and post-spectator locality. -/
structure ReadoutPremises {A : Type*} (pi : NativeCircuit → A) : Prop where
  complete_eval : ∀ c d, (∀ x, c.eval x = d.eval x) → pi c = pi d
  spectator_local : ∀ c, pi (.seq c gate12) = pi c

theorem appendSpectator_readout {A : Type*} {pi : NativeCircuit → A}
    (hpi : ReadoutPremises pi) (c : NativeCircuit) (n : ℕ) :
    pi (appendSpectator c n) = pi c := by
  induction n with
  | zero => rfl
  | succ n ih => exact (hpi.spectator_local (appendSpectator c n)).trans ih

/-- Full three-wire selected-weight equality suffices for any such readout. -/
theorem full_selected_profile_readout {A : Type*} {pi : NativeCircuit → A}
    (hpi : ReadoutPremises pi) (c d : NativeCircuit)
    (hprofile : ∀ x : Fin 3 → ℂ,
      Complex.normSq (c.eval x 0) = Complex.normSq (d.eval x 0)) : pi c = pi d := by
  have hm : ∀ x : Fin 3 → ℂ,
      Complex.normSq ((circuitMatrix c).mulVec x 0) =
        Complex.normSq ((circuitMatrix d).mulVec x 0) := by
    intro x
    simpa only [← circuit_action] using hprofile x
  obtain ⟨r, hr⟩ := (selected_readout_iff_suffix
    (circuit_invariants c) (circuit_invariants d)).mp hm
  have he : ∀ x, d.eval x = (appendSpectator c r.val).eval x :=
    matrix_eq_complete_eval (hr.trans (appendSpectator_matrix c r.val).symm)
  exact ((hpi.complete_eval d (appendSpectator c r.val) he).trans
    (appendSpectator_readout hpi c r.val)).symm

/-- The compressed-input test compares a gate with its third power. -/
def gate02Cubed : NativeCircuit := .seq (.seq gate02 gate02) gate02

theorem compressed_gate02_weight (z w : ℂ) :
    Complex.normSq (gate02.eval (input z w) 0) = Complex.normSq z / 2 := by
  change Complex.normSq (CompositeProductControls.RawSign.n z 0) = _
  norm_num [
    CompositeProductControls.RawSign.N, CompositeProductControls.RawSign.n_re,
    CompositeProductControls.RawSign.n_im,
    Complex.normSq_apply]
  ring

theorem compressed_gate02Cubed_weight (z w : ℂ) :
    Complex.normSq (gate02Cubed.eval (input z w) 0) = Complex.normSq z / 2 := by
  simp [gate02Cubed, gate02, input, Circuit.eval, pairGate, pairReplace]
  norm_num [gate02Cubed, gate02, input, Circuit.eval, pairGate, pairReplace, mixer, Raw,
    CompositeProductControls.RawSign.N, CompositeProductControls.RawSign.n_re,
    CompositeProductControls.RawSign.n_im,
    Complex.normSq_apply]
  ring

theorem compressed_profile_equal (z w : ℂ) :
    Complex.normSq (gate02.eval (input z w) 0) =
      Complex.normSq (gate02Cubed.eval (input z w) 0) := by
  rw [compressed_gate02_weight, compressed_gate02Cubed_weight]

/-- A real phase probe, expressly not a normalized probability readout. -/
def probeReadout (c : NativeCircuit) : ℝ := (c.eval ![0, 0, 1] 0).im

theorem probeReadout_premises : ReadoutPremises probeReadout := by
  constructor
  · intro c d h
    unfold probeReadout
    rw [h]
  · intro c
    simp [probeReadout, Circuit.eval, gate12, pairGate, pairReplace]

theorem probeReadout_gate02 : probeReadout gate02 = -1 / 2 := by
  change (CompositeProductControls.RawSign.n 0 1).im = _
  norm_num [probeReadout, gate02, Circuit.eval, pairGate, pairReplace, mixer, Raw,
    CompositeProductControls.RawSign.N, CompositeProductControls.RawSign.n_re,
    CompositeProductControls.RawSign.n_im]

theorem probeReadout_gate02Cubed : probeReadout gate02Cubed = 1 / 2 := by
  simp [probeReadout, gate02Cubed, gate02, Circuit.eval, pairGate, pairReplace]
  norm_num [probeReadout, gate02Cubed, gate02, Circuit.eval, pairGate, pairReplace,
    mixer, Raw, CompositeProductControls.RawSign.N, CompositeProductControls.RawSign.n_re,
    CompositeProductControls.RawSign.n_im]

/-- The generic readout premises do not imply descent on compressed inputs. -/
theorem compressed_profile_descent_not_forced :
    ¬ (∀ (A : Type) (pi : NativeCircuit → A), ReadoutPremises pi →
      ∀ c d, (∀ z w : ℂ, Complex.normSq (c.eval (input z w) 0) =
        Complex.normSq (d.eval (input z w) 0)) → pi c = pi d) := by
  intro h
  have hp := h ℝ probeReadout probeReadout_premises gate02 gate02Cubed
    compressed_profile_equal
  rw [probeReadout_gate02, probeReadout_gate02Cubed] at hp
  norm_num at hp

end

end IDT.QMClosure.NativeThreeWireLocality
