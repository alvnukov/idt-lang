import Proofs.QMClosure.FiniteReadoutRecurrence
import Proofs.QMClosure.NativeFiniteStochasticReadoutWall
import Proofs.QMClosure.NativeThreeWireNondecay
import Mathlib.Tactic.ComputeDegree

/-!
# An exact finite window for a bounded fixed stochastic preparation model

For the supplied native weight, a fixed finite row-stochastic preparation
kernel with `d` states and arbitrary fixed complex initial/readout vectors must
disagree at some word depth `n < d + 4`. Cayley--Hamilton and the native forced
fourth-order recurrence make agreement on that window imply agreement forever,
contradicting the existing exact stochastic readout obstruction.

The state bound and the uniform compositional hidden preparation contract are
supplied. Depth is not repeated-trial time. This is an exact algebraic witness,
not a finite-precision margin, physical memory bound, detector frequency law,
experimental confidence claim, or derivation of QM.
-/

namespace IDT.QMClosure.NativeFixedStateFiniteWindow

open Polynomial Finset
open FiniteReadoutRecurrence NativeFiniteStochasticReadoutWall
open NativeThreeWireProbabilityDenominator

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- A linear functional giving the fixed readout of one matrix. -/
def matrixReadout (μ r : S → ℂ) : Matrix S S ℂ →ₗ[ℂ] ℂ where
  toFun A := ∑ i, μ i * A.mulVec r i
  map_add' A B := by
    simp [Matrix.add_mulVec, mul_add, sum_add_distrib]
  map_smul' c A := by
    simp [Matrix.smul_mulVec, Finset.mul_sum, mul_left_comm]

theorem prediction_eq_matrixReadout (P : Matrix S S ℝ) (μ r : S → ℂ) (n : ℕ) :
    prediction P μ r n = matrixReadout μ r (FiniteStochasticPeripheral.complexify P ^ n) :=
  rfl

/-- The complexified matrix characteristic polynomial annihilates the readout. -/
theorem charpoly_prediction (P : Matrix S S ℝ) (μ r : S → ℂ) :
    applyPolynomial (FiniteStochasticPeripheral.complexify P).charpoly
      (prediction P μ r) = 0 :=
  charpoly_annihilates _ (matrixReadout μ r)

private theorem complexify_mulVec_one {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) :
    (FiniteStochasticPeripheral.complexify P).mulVec (fun _ => 1) = fun _ => 1 := by
  funext i
  simp only [FiniteStochasticPeripheral.complexify, Matrix.mulVec, dotProduct, mul_one]
  exact_mod_cast Matrix.sum_row_of_mem_rowStochastic hP i

private theorem complexify_pow_mulVec_one {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) (n : ℕ) :
    (FiniteStochasticPeripheral.complexify P ^ n).mulVec (fun _ => 1) = fun _ => 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, complexify_mulVec_one hP, ih]

/-- A nonempty row-stochastic matrix has characteristic root one. -/
theorem charpoly_eval_one [Nonempty S] {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) :
    (FiniteStochasticPeripheral.complexify P).charpoly.eval 1 = 0 := by
  let i : S := Classical.choice inferInstance
  have hseq : prediction P (Pi.single i 1) (fun _ => 1) = fun _ => (1 : ℂ) := by
    funext n
    simp [prediction, complexify_pow_mulVec_one hP]
  have hzero := charpoly_prediction P (Pi.single i 1) (fun _ => 1)
  rw [hseq, applyPolynomial_const] at hzero
  simpa using congrFun hzero 0

/-- The monic fourth-order polynomial in the native forced recurrence. -/
def nativePolynomial : ℂ[X] :=
  X ^ 4 + C (5 / 4) * X ^ 3 + C (9 / 8) * X ^ 2 + C (5 / 4) * X + C 1

theorem nativePolynomial_monic : nativePolynomial.Monic := by
  unfold nativePolynomial
  monicity!

theorem nativePolynomial_natDegree : nativePolynomial.natDegree = 4 := by
  unfold nativePolynomial
  compute_degree!

/-- The native recurrence produces a constant forcing term, not zero. -/
theorem nativePolynomial_forcing :
    applyPolynomial nativePolynomial (fun n => (selectedWeight n : ℂ)) =
      fun _ => (21 / 8 : ℂ) := by
  funext n
  have hc : (8 : ℂ) * (selectedWeight (n + 4) : ℂ) +
      10 * (selectedWeight (n + 3) : ℂ) + 9 * (selectedWeight (n + 2) : ℂ) +
      10 * (selectedWeight (n + 1) : ℂ) + 8 * (selectedWeight n : ℂ) = 21 := by
    exact_mod_cast NativeThreeWireNondecay.selectedWeight_recurrence n
  have hX (u : ℕ → ℂ) (k : ℕ) : applyPolynomial X u k = u (k + 1) := by
    simpa only [pow_one] using applyPolynomial_X_pow 1 u k
  simp only [nativePolynomial, applyPolynomial_add, Pi.add_apply,
    applyPolynomial_mul, applyPolynomial_C, applyPolynomial_X_pow, hX, one_mul]
  linear_combination (1 / 8 : ℂ) * hc

/-- Both sequences have a common monic annihilator of degree `card S + 4`. -/
theorem common_annihilator [Nonempty S] {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) (μ r : S → ℂ) :
    let p := (FiniteStochasticPeripheral.complexify P).charpoly * nativePolynomial
    p.Monic ∧ p.natDegree = Fintype.card S + 4 ∧
      applyPolynomial p (prediction P μ r) = 0 ∧
      applyPolynomial p (fun n => (selectedWeight n : ℂ)) = 0 := by
  dsimp only
  refine ⟨(Matrix.charpoly_monic _).mul nativePolynomial_monic, ?_, ?_, ?_⟩
  · rw [(Matrix.charpoly_monic _).natDegree_mul nativePolynomial_monic,
      Matrix.charpoly_natDegree_eq_dim, nativePolynomial_natDegree]
  · rw [mul_comm, applyPolynomial_mul, charpoly_prediction, applyPolynomial_zero_sequence]
  · rw [applyPolynomial_mul, nativePolynomial_forcing, applyPolynomial_const,
      charpoly_eval_one hP]
    funext n
    simp

/-- A fixed finite row-stochastic preparation model must fail in this exact window. -/
theorem exists_mismatch_before_card_add_four {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) (μ r : S → ℂ) :
    ∃ n : ℕ, n < Fintype.card S + 4 ∧ prediction P μ r n ≠ (selectedWeight n : ℂ) := by
  classical
  rcases isEmpty_or_nonempty S with hS | hS
  · refine ⟨0, by omega, ?_⟩
    simp [prediction, selectedWeight, selectedAmplitude_zero]
  · by_contra h
    push Not at h
    let p := (FiniteStochasticPeripheral.complexify P).charpoly * nativePolynomial
    obtain ⟨hmonic, hdegree, ha, hb⟩ := common_annihilator hP μ r
    change p.natDegree = Fintype.card S + 4 at hdegree
    have hrec : applyPolynomial p
        (prediction P μ r - fun n => (selectedWeight n : ℂ)) = 0 := by
      change (aeval (shift : Module.End ℂ (ℕ → ℂ)) p)
        (prediction P μ r - fun n => (selectedWeight n : ℂ)) = 0
      rw [map_sub]
      change applyPolynomial p (prediction P μ r) -
        applyPolynomial p (fun n => (selectedWeight n : ℂ)) = 0
      rw [ha, hb, sub_self]
    have heq := eq_zero_of_initial p hmonic _ hrec (by
      intro n hn
      change prediction P μ r n - (selectedWeight n : ℂ) = 0
      exact sub_eq_zero.mpr (h n (by simpa only [hdegree] using hn)))
    apply no_exact_representation hP μ r
    intro n
    exact sub_eq_zero.mp (congrFun heq n)

/-- An externally supplied upper bound on the state count gives a common window. -/
theorem exists_mismatch_before_bound_add_four {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) (μ r : S → ℂ) (M : ℕ)
    (hcard : Fintype.card S ≤ M) :
    ∃ n : ℕ, n < M + 4 ∧ prediction P μ r n ≠ (selectedWeight n : ℂ) := by
  obtain ⟨n, hn, hne⟩ := exists_mismatch_before_card_add_four hP μ r
  exact ⟨n, lt_of_lt_of_le hn (Nat.add_le_add_right hcard 4), hne⟩

/-- Matching a prefix of length `N` requires at least `N - 3` states. -/
theorem match_prefix_requires_states {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) (μ r : S → ℂ) (N : ℕ)
    (hmatch : ∀ n < N, prediction P μ r n = (selectedWeight n : ℂ)) :
    N ≤ Fintype.card S + 3 := by
  obtain ⟨n, hn, hne⟩ := exists_mismatch_before_card_add_four hP μ r
  by_contra hN
  exact hne (hmatch n (by omega))

/-- The natural-number lower bound, with truncated subtraction for short prefixes. -/
theorem prefix_state_lower_bound {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) (μ r : S → ℂ) (N : ℕ)
    (hmatch : ∀ n < N, prediction P μ r n = (selectedWeight n : ℂ)) :
    N - 3 ≤ Fintype.card S := by
  have := match_prefix_requires_states hP μ r N hmatch
  omega

end

end IDT.QMClosure.NativeFixedStateFiniteWindow
