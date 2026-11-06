import Proofs.QMClosure.NativeDyadicGaussianArithmetic
import Proofs.QMClosure.NativeThreeWireLocality

/-!
# Exact native synthesis of legal dyadic three-coordinate vectors

This module concerns the supplied complex scalar representation of the existing
finite native circuit syntax. The hypotheses are exact Gaussian dyadic
coordinates, coherent sum one, and squared norm one. No physical preparation,
readout actualization, arbitrary-width synthesis, or QM closure is asserted.
-/

namespace IDT.QMClosure.NativeDyadicThreeVectorSynthesis

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

open NativeDyadicGaussianArithmetic MixerGeneratedProcessWall
open NativeMixerEventConeExclusion
open scoped BigOperators

def piC : ℂ := 1 + Complex.I

@[simp] theorem cast_pi : (pi : ℂ) = piC := by
  simp [GaussianInt.toComplex_def, pi, piC]

@[simp] theorem cast_ii : (ii : ℂ) = Complex.I := by
  simp [GaussianInt.toComplex_def, ii]

theorem piC_ne_zero : piC ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [piC] at this

def vector (k : ℕ) (x y z : G) : Fin 3 → ℂ :=
  ![(x : ℂ) / piC ^ k, (y : ℂ) / piC ^ k, (z : ℂ) / piC ^ k]

theorem mixer_formula (z w : ℂ) :
    mixer (z, w) = ((Complex.I * z + w) / piC,
      (z + Complex.I * w) / piC) := by
  apply Prod.ext <;> apply Complex.ext <;>
    norm_num [mixer, Raw, CompositeProductControls.RawSign.N,
      CompositeProductControls.RawSign.n_re,
      CompositeProductControls.RawSign.n_im, piC,
      Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,
      Complex.normSq_apply] <;> ring

theorem scalar_down (k : ℕ) (x x' : G) (h : pi * x' = x) :
    (x : ℂ) / piC ^ (k + 1) = (x' : ℂ) / piC ^ k := by
  have hc := congrArg GaussianInt.toComplex h
  simp only [map_mul, cast_pi] at hc
  rw [← hc, pow_succ]
  field_simp [piC_ne_zero]

theorem scalar_down_two (k : ℕ) (x x' : G) (h : pi ^ 2 * x' = x) :
    (x : ℂ) / piC ^ (k + 2) = (x' : ℂ) / piC ^ k := by
  have hc := congrArg GaussianInt.toComplex h
  simp only [map_mul, map_pow, cast_pi] at hc
  rw [← hc, pow_add]
  field_simp [piC_ne_zero]

theorem mixer_down (k : ℕ) (x y x' y' : G)
    (hx : pi ^ 2 * x' = ii * x + y) (hy : pi ^ 2 * y' = x + ii * y) :
    mixer ((x : ℂ) / piC ^ (k + 1), (y : ℂ) / piC ^ (k + 1)) =
      ((x' : ℂ) / piC ^ k, (y' : ℂ) / piC ^ k) := by
  rw [mixer_formula]
  apply Prod.ext
  · calc
      _ = ((ii * x + y : G) : ℂ) / piC ^ (k + 2) := by
        simp only [map_add, map_mul, cast_ii]
        rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
        field_simp [piC_ne_zero]
        ring
      _ = _ := scalar_down_two k _ _ hx
  · calc
      _ = ((x + ii * y : G) : ℂ) / piC ^ (k + 2) := by
        simp only [map_add, map_mul, cast_ii]
        rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
        field_simp [piC_ne_zero]
        ring
      _ = _ := scalar_down_two k _ _ hy

theorem all_even_action (k : ℕ) (x y z : G)
    (hx : EvenPi x) (hy : EvenPi y) (hz : EvenPi z) :
    vector (k + 1) x y z = vector k (halfPi x) (halfPi y) (halfPi z) := by
  ext j
  fin_cases j
  · exact scalar_down k _ _ (mul_halfPi x hx)
  · exact scalar_down k _ _ (mul_halfPi y hy)
  · exact scalar_down k _ _ (mul_halfPi z hz)

theorem gate01_down (k : ℕ) (x y z x' y' z' : G)
    (hx : pi ^ 2 * x' = ii * x + y) (hy : pi ^ 2 * y' = x + ii * y)
    (hz : pi * z' = z) :
    gate01.eval (vector (k + 1) x y z) = vector k x' y' z' := by
  have hm := mixer_down k x y x' y' hx hy
  ext j
  fin_cases j <;>
    simp [gate01, Circuit.eval, pairGate, pairReplace, vector, hm,
      scalar_down k z z' hz]

theorem gate02_down (k : ℕ) (x y z x' y' z' : G)
    (hx : pi ^ 2 * x' = ii * x + z) (hz : pi ^ 2 * z' = x + ii * z)
    (hy : pi * y' = y) :
    gate02.eval (vector (k + 1) x y z) = vector k x' y' z' := by
  have hm := mixer_down k x z x' z' hx hz
  ext j
  fin_cases j <;>
    simp [gate02, Circuit.eval, pairGate, pairReplace, vector, hm,
      scalar_down k y y' hy]

theorem gate12_down (k : ℕ) (x y z x' y' z' : G)
    (hy : pi ^ 2 * y' = ii * y + z) (hz : pi ^ 2 * z' = y + ii * z)
    (hx : pi * x' = x) :
    gate12.eval (vector (k + 1) x y z) = vector k x' y' z' := by
  have hm := mixer_down k y z y' z' hy hz
  ext j
  fin_cases j <;>
    simp [gate12, Circuit.eval, pairGate, pairReplace, vector, hm,
      scalar_down k x x' hx]

def Reduces (k : ℕ) (x y z : G) : Prop :=
  ∃ c : NativeCircuit, ∃ j : Fin 3, c.eval (vector k x y z) = single j 1

theorem zero_reduces (x y z : G) (h : LegalTriple 0 x y z) : Reduces 0 x y z := by
  obtain ⟨hs, hn⟩ := h
  simp only [pow_zero] at hs hn
  rcases sum_one_norm_one x y z hs hn with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact ⟨.identity, 0, by ext j; fin_cases j <;> simp [Circuit.eval, vector, single]⟩
  · exact ⟨.identity, 1, by ext j; fin_cases j <;> simp [Circuit.eval, vector, single]⟩
  · exact ⟨.identity, 2, by ext j; fin_cases j <;> simp [Circuit.eval, vector, single]⟩

theorem one_reduces (x y z : G) (h : LegalTriple 1 x y z) : Reduces 1 x y z := by
  obtain ⟨hs, hn⟩ := h
  simp only [pow_one] at hs hn
  rcases sum_pi_norm_two x y z hs hn with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine ⟨.identity, 0, ?_⟩
    ext j; fin_cases j <;> simp [Circuit.eval, vector, single, piC_ne_zero]
  · refine ⟨.identity, 1, ?_⟩
    ext j; fin_cases j <;> simp [Circuit.eval, vector, single, piC_ne_zero]
  · refine ⟨.identity, 2, ?_⟩
    ext j; fin_cases j <;> simp [Circuit.eval, vector, single, piC_ne_zero]
  · refine ⟨gate01, 0, ?_⟩
    refine (gate01_down 0 1 ii 0 1 0 0 (by decide) (by decide) (by decide)).trans ?_
    ext j; fin_cases j <;> simp [vector, single]
  · refine ⟨gate01, 1, ?_⟩
    refine (gate01_down 0 ii 1 0 0 1 0 (by decide) (by decide) (by decide)).trans ?_
    ext j; fin_cases j <;> simp [vector, single]
  · refine ⟨gate02, 0, ?_⟩
    refine (gate02_down 0 1 0 ii 1 0 0 (by decide) (by decide) (by decide)).trans ?_
    ext j; fin_cases j <;> simp [vector, single]
  · refine ⟨gate02, 2, ?_⟩
    refine (gate02_down 0 ii 0 1 0 0 1 (by decide) (by decide) (by decide)).trans ?_
    ext j; fin_cases j <;> simp [vector, single]
  · refine ⟨gate12, 1, ?_⟩
    refine (gate12_down 0 0 1 ii 0 1 0 (by decide) (by decide) (by decide)).trans ?_
    ext j; fin_cases j <;> simp [vector, single]
  · refine ⟨gate12, 2, ?_⟩
    refine (gate12_down 0 0 ii 1 0 0 1 (by decide) (by decide) (by decide)).trans ?_
    ext j; fin_cases j <;> simp [vector, single]

/-- The step witness is either the identity or a single existing pair generator. -/
theorem denominator_descent (k : ℕ) (x y z : G) (h : LegalTriple (k + 2) x y z) :
    ∃ c : NativeCircuit, ∃ x' y' z' : G, LegalTriple (k + 1) x' y' z' ∧
      c.eval (vector (k + 2) x y z) = vector (k + 1) x' y' z' := by
  have hp := three_parity x y z (by rw [h.1]; exact (pow_pi_even k).1)
    (by rw [h.1]; exact (pow_pi_even k).2) (by rw [h.2]; exact pow_two_mod_four k)
  rcases hp with ⟨hx, hy, hz⟩ | ⟨ho, hz⟩ | ⟨ho, hy⟩ | ⟨ho, hx⟩
  · exact ⟨.identity, halfPi x, halfPi y, halfPi z,
      divide_all (k + 1) x y z h hx hy hz, all_even_action (k + 1) x y z hx hy hz⟩
  · obtain ⟨x', y', z', hl, hx', hy', hz'⟩ := divide_pair (k + 1) x y z h ho hz
    exact ⟨gate01, x', y', z', hl, gate01_down (k + 1) x y z x' y' z' hx' hy' hz'⟩
  · have hr : LegalTriple (k + 2) x z y := by
      simpa [LegalTriple, add_comm, add_left_comm, add_assoc] using h
    obtain ⟨x', z', y', hl, hx', hz', hy'⟩ := divide_pair (k + 1) x z y hr ho hy
    refine ⟨gate02, x', y', z', ?_, gate02_down (k + 1) x y z x' y' z' hx' hz' hy'⟩
    simpa [LegalTriple, add_comm, add_left_comm, add_assoc] using hl
  · have hr : LegalTriple (k + 2) y z x := by
      simpa [LegalTriple, add_comm, add_left_comm, add_assoc] using h
    obtain ⟨y', z', x', hl, hy', hz', hx'⟩ := divide_pair (k + 1) y z x hr ho hx
    refine ⟨gate12, x', y', z', ?_, gate12_down (k + 1) x y z x' y' z' hy' hz' hx'⟩
    simpa [LegalTriple, add_comm, add_left_comm, add_assoc] using hl

/-- Every exact legal triple admits a finite native word reducing it to a basis vector. -/
theorem legal_triple_reduces (k : ℕ) (x y z : G) (h : LegalTriple k x y z) :
    Reduces k x y z := by
  induction k using Nat.strong_induction_on generalizing x y z with
  | h k ih =>
    rcases k with _ | k
    · exact zero_reduces x y z h
    rcases k with _ | k
    · exact one_reduces x y z h
    obtain ⟨c, x', y', z', hl, hc⟩ := denominator_descent k x y z h
    obtain ⟨d, j, hd⟩ := ih (k + 1) (by omega) x' y' z' hl
    refine ⟨.seq c d, j, ?_⟩
    change d.eval (c.eval (vector (k + 2) x y z)) = _
    rw [hc, hd]

/-- Function-form interface for matrix-column adapters. -/
theorem legal_three_vector_reduces (k : ℕ) (u : Fin 3 → G)
    (hs : ∑ j, u j = pi ^ k) (hn : ∑ j, (u j).norm = (2 : ℤ) ^ k) :
    ∃ c : NativeCircuit, ∃ j : Fin 3,
      c.eval (fun i => (u i : ℂ) / piC ^ k) = single j 1 := by
  have h : LegalTriple k (u 0) (u 1) (u 2) := by
    constructor
    · simpa [Fin.sum_univ_succ, add_assoc] using hs
    · simpa [Fin.sum_univ_succ, add_assoc] using hn
  obtain ⟨c, j, hc⟩ := legal_triple_reduces k (u 0) (u 1) (u 2) h
  refine ⟨c, j, ?_⟩
  have hv : (fun i => (u i : ℂ) / piC ^ k) = vector k (u 0) (u 1) (u 2) := by
    ext i; fin_cases i <;> rfl
  rw [hv]
  exact hc

/-- An inverse is another literal word: each pair inverse is its third power. -/
def inverseCircuit : NativeCircuit → NativeCircuit
  | .identity => .identity
  | .pair i j h => .seq (.seq (.pair i j h) (.pair i j h)) (.pair i j h)
  | .permute e => .permute e.symm
  | .seq c d => .seq (inverseCircuit d) (inverseCircuit c)

theorem pair_four (i j : Fin 3) (hij : i ≠ j) (v : Fin 3 → ℂ) :
    let p : NativeCircuit := .pair i j hij
    p.eval (p.eval (p.eval (p.eval v))) = v := by
  have hm : mixer (mixer (mixer (mixer (v i, v j)))) = (v i, v j) := by
    rw [mixer_square, mixer_square]
    rfl
  ext k
  by_cases hi : k = i
  · subst k
    simpa [Circuit.eval, pairGate, pairReplace, hij, Ne.symm hij] using congrArg Prod.fst hm
  by_cases hj : k = j
  · subst k
    simpa [Circuit.eval, pairGate, pairReplace, hij, Ne.symm hij] using congrArg Prod.snd hm
  · simp [Circuit.eval, pairGate, pairReplace, hi, hj]

theorem inverseCircuit_left (c : NativeCircuit) (v : Fin 3 → ℂ) :
    (inverseCircuit c).eval (c.eval v) = v := by
  induction c generalizing v with
  | identity => rfl
  | pair i j hij => exact pair_four i j hij v
  | permute e =>
    ext k
    simp [inverseCircuit, Circuit.eval]
  | seq c d hc hd =>
    change (inverseCircuit c).eval ((inverseCircuit d).eval (d.eval (c.eval v))) = v
    rw [hd, hc]

/-- Synthesis uses actual finite native syntax, not an invariant-certified map. -/
theorem legal_three_vector_synthesizes (k : ℕ) (u : Fin 3 → G)
    (hs : ∑ j, u j = pi ^ k) (hn : ∑ j, (u j).norm = (2 : ℤ) ^ k) :
    ∃ c : NativeCircuit, ∃ j : Fin 3,
      c.eval (single j 1) = (fun i => (u i : ℂ) / piC ^ k) := by
  obtain ⟨c, j, hc⟩ := legal_three_vector_reduces k u hs hn
  refine ⟨inverseCircuit c, j, ?_⟩
  rw [← hc, inverseCircuit_left]

theorem legal_three_vector_synthesizes_from_zero (k : ℕ) (u : Fin 3 → G)
    (hs : ∑ j, u j = pi ^ k) (hn : ∑ j, (u j).norm = (2 : ℤ) ^ k) :
    ∃ c : NativeCircuit,
      c.eval (single (0 : Fin 3) 1) = (fun i => (u i : ℂ) / piC ^ k) := by
  obtain ⟨c, j, hc⟩ := legal_three_vector_synthesizes k u hs hn
  let p : NativeCircuit := .permute (Equiv.swap 0 j)
  have hp : p.eval (single (0 : Fin 3) 1) = single j 1 := by
    ext i
    fin_cases j <;> fin_cases i <;> simp [p, Circuit.eval, single, Equiv.swap_apply_def]
  refine ⟨.seq p c, ?_⟩
  change c.eval (p.eval (single (0 : Fin 3) 1)) = _
  rw [hp, hc]

@[simp] theorem norm_piC : Complex.normSq piC = 2 := by
  norm_num [piC, Complex.normSq_apply]

/-- The numerator hypotheses are exactly the represented vector's two normalizations. -/
theorem numerator_normalization (k : ℕ) (u : Fin 3 → G)
    (hs : (∑ j, (u j : ℂ) / piC ^ k) = 1)
    (hn : (∑ j, Complex.normSq ((u j : ℂ) / piC ^ k)) = 1) :
    (∑ j, u j = pi ^ k) ∧ (∑ j, (u j).norm = (2 : ℤ) ^ k) := by
  constructor
  · apply GaussianInt.toComplex_injective
    simp only [map_sum, map_pow, cast_pi]
    rw [← Finset.sum_div] at hs
    exact (div_eq_one_iff_eq (pow_ne_zero k piC_ne_zero)).mp hs
  · have hh : (∑ j, ((u j).norm : ℝ)) / (2 : ℝ) ^ k = 1 := by
      simpa only [Complex.normSq_div, map_pow, norm_piC,
        ← GaussianInt.intCast_real_norm, Finset.sum_div] using hn
    have hh' := (div_eq_one_iff_eq (pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0))).mp hh
    exact_mod_cast hh'

/-- A direct vector-facing synthesis theorem with exact dyadic data and normalizations. -/
theorem normalized_three_vector_synthesizes (k : ℕ) (u : Fin 3 → G)
    (hs : (∑ j, (u j : ℂ) / piC ^ k) = 1)
    (hn : (∑ j, Complex.normSq ((u j : ℂ) / piC ^ k)) = 1) :
    ∃ c : NativeCircuit,
      c.eval (single (0 : Fin 3) 1) = (fun i => (u i : ℂ) / piC ^ k) := by
  obtain ⟨hs', hn'⟩ := numerator_normalization k u hs hn
  exact legal_three_vector_synthesizes_from_zero k u hs' hn'

end
end IDT.QMClosure.NativeDyadicThreeVectorSynthesis
