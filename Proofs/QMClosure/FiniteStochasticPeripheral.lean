import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Data.Complex.BigOperators
import Proofs.QMClosure.FiniteDeterministicRecordFrequency

/-!
# Peripheral eigenvalues of finite stochastic matrices

For a real finite row-stochastic matrix, every complex eigenvalue of squared
modulus one is a root of unity with a positive exponent at most the number of
states. The entries may be arbitrary real numbers; neither irreducibility nor
rational transition probabilities are assumed.

The proof derives phase alignment along positive transitions from a weighted
squared-distance identity, then finds a finite cycle in the maximal-modulus
support of the eigenvector. This is a mathematical matrix theorem, not a
stochastic preparation theorem or a physical exclusion claim.
-/

namespace IDT.QMClosure.FiniteStochasticPeripheral

open Finset Function

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Entrywise complexification of a real transition matrix. -/
def complexify (P : Matrix S S ℝ) : Matrix S S ℂ :=
  fun i j => (P i j : ℂ)

omit [DecidableEq S] in
private theorem weighted_normSq_sub (p : S → ℝ) (v : S → ℂ) (w : ℂ)
    (hp : ∑ j, p j = 1) (hm : ∑ j, (p j : ℂ) * v j = w) :
    ∑ j, p j * Complex.normSq (v j - w) =
      (∑ j, p j * Complex.normSq (v j)) - Complex.normSq w := by
  have hre : ∑ j, p j * (v j).re = w.re := by
    simpa [Complex.re_sum, Complex.mul_re] using congrArg Complex.re hm
  have him : ∑ j, p j * (v j).im = w.im := by
    simpa [Complex.im_sum, Complex.mul_im] using congrArg Complex.im hm
  have hpoint (j : S) :
      p j * Complex.normSq (v j - w) =
        p j * Complex.normSq (v j) + p j * Complex.normSq w -
          (p j * (v j).re) * (2 * w.re) -
          (p j * (v j).im) * (2 * w.im) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  simp_rw [hpoint]
  rw [sum_sub_distrib, sum_sub_distrib, sum_add_distrib]
  rw [← sum_mul, ← sum_mul, ← sum_mul, hp, hre, him]
  rw [Complex.normSq_apply]
  ring

/-- Every positive transition from a component of maximal squared modulus
advances its value by the peripheral eigenvalue. Alignment is derived from
the stochastic and eigenvector equations. -/
theorem aligned_of_positive_edge {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) {v : S → ℂ} {ζ : ℂ}
    (heig : (complexify P).mulVec v = ζ • v) (hζ : Complex.normSq ζ = 1)
    {i j : S} (hmax : ∀ k, Complex.normSq (v k) ≤ Complex.normSq (v i))
    (hij : 0 < P i j) : v j = ζ * v i := by
  have hrow : ∑ k, P i k = 1 := Matrix.sum_row_of_mem_rowStochastic hP i
  have hm : ∑ k, (P i k : ℂ) * v k = ζ * v i := by
    simpa [complexify, Matrix.mulVec, dotProduct] using congrFun heig i
  have hsum_le : (∑ k, P i k * Complex.normSq (v k)) ≤ Complex.normSq (v i) := by
    calc
      _ ≤ ∑ k, P i k * Complex.normSq (v i) :=
        sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hmax k) (hP.1 i k)
      _ = Complex.normSq (v i) := by rw [← sum_mul, hrow, one_mul]
  have hdist := weighted_normSq_sub (P i) v (ζ * v i) hrow hm
  rw [Complex.normSq_mul, hζ, one_mul] at hdist
  have htotal : (∑ k, P i k * Complex.normSq (v k - ζ * v i)) ≤ 0 := by
    linarith
  have hterm : P i j * Complex.normSq (v j - ζ * v i) ≤ 0 :=
    (single_le_sum
      (fun k _ => mul_nonneg (hP.1 i k) (Complex.normSq_nonneg (v k - ζ * v i)))
      (mem_univ j)).trans htotal
  have hz : Complex.normSq (v j - ζ * v i) = 0 := by
    have hnonneg := Complex.normSq_nonneg (v j - ζ * v i)
    nlinarith
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp hz)

private theorem exists_positive_edge {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) (i : S) : ∃ j, 0 < P i j := by
  by_contra h
  push Not at h
  have hz : ∑ j, P i j = 0 := sum_eq_zero fun j _ => le_antisymm (h j) (hP.1 i j)
  have ho := Matrix.sum_row_of_mem_rowStochastic hP i
  linarith

/-- A peripheral eigenvalue of a finite real row-stochastic matrix is a root
of unity, with a positive exponent bounded by the number of states. -/
theorem exists_bounded_pow_eq_one {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) {v : S → ℂ} {ζ : ℂ}
    (hv : v ≠ 0) (heig : (complexify P).mulVec v = ζ • v)
    (hζ : Complex.normSq ζ = 1) :
    ∃ q : ℕ, 0 < q ∧ q ≤ Fintype.card S ∧ ζ ^ q = 1 := by
  classical
  obtain ⟨s, hs⟩ : ∃ s, v s ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨i, _, hmax⟩ := exists_max_image univ (fun k => Complex.normSq (v k))
    ⟨s, mem_univ s⟩
  have hmax' (k : S) : Complex.normSq (v k) ≤ Complex.normSq (v i) :=
    hmax k (mem_univ k)
  have hR : 0 < Complex.normSq (v i) :=
    (Complex.normSq_pos.mpr hs).trans_le (hmax' s)
  let M := {k : S // Complex.normSq (v k) = Complex.normSq (v i)}
  have hnext (k : M) : ∃ l : M, v l = ζ * v k := by
    obtain ⟨l, hl⟩ := exists_positive_edge hP k
    have halign : v l = ζ * v k := aligned_of_positive_edge hP heig hζ
      (fun m => by rw [k.property]; exact hmax' m) hl
    refine ⟨⟨l, ?_⟩, halign⟩
    rw [halign, Complex.normSq_mul, hζ, one_mul, k.property]
  let step : M → M := fun k => Classical.choose (hnext k)
  have hstep (k : M) : v (step k) = ζ * v k := Classical.choose_spec (hnext k)
  have hiter (n : ℕ) (k : M) : v ((step^[n]) k) = ζ ^ n * v k := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iterate_succ_apply', hstep, ih, pow_succ]
      ring
  obtain ⟨T, q, hq, hcard, hp⟩ :=
    FiniteDeterministicRecordFrequency.exists_periodic_tail step (⟨i, rfl⟩ : M)
  let k : M := (step^[T]) (⟨i, rfl⟩ : M)
  have hk : v k ≠ 0 := by
    apply Complex.normSq_pos.mp
    rw [k.property]
    exact hR
  have heq : ζ ^ q * v k = 1 * v k := by
    rw [← hiter, hp.eq]
    exact (one_mul (v k)).symm
  exact ⟨q, hq, hcard.trans (Fintype.card_subtype_le _), mul_right_cancel₀ hk heq⟩

end IDT.QMClosure.FiniteStochasticPeripheral
