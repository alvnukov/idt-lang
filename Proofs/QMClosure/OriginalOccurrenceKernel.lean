import Proofs.QMClosure.NativeGeneratorMixtureReadout
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Sum
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Nat.Choose.Cast

/-!
# Finite original-occurrence kernel compiler

An original occurrence is a tagged member of `Fin n ⊕ Fin m`. The compiler sums
once over unordered selected subsets of those original occurrences. Its fixed
real kernel depends only on the two type counts. The finite order K and the
same coefficients are used for every input size. A finite bound on original
ancestry says nothing here about how many selected subsets use one occurrence.

`CompatibleOriginalKernel` is an additional readout premise. No physical
preparation cost, detector event interpretation, positivity, continuity,
global multiplication law, or pair-congruence law is asserted by this premise.
-/

noncomputable section

namespace IDT.QMClosure.OriginalOccurrenceKernel

open scoped BigOperators
open NativeInitialHistoryPresentation
open NativeGeneratorMixtureReadout
open MvPolynomial

attribute [local instance] presentationCommRing presentationCharZero

abbrev Kernel := ℕ → ℕ → ℝ
abbrev Occurrence (n m : ℕ) := Fin n ⊕ Fin m

/-- Evaluation of the bag of original a and b occurrences. -/
def bagEval (n m : ℕ) : Presentation := (n : Presentation) * a + (m : Presentation) * b

/-- Each original tagged occurrence has one fixed native generator value. -/
def occurrenceValue {n m : ℕ} : Occurrence n m → Presentation
  | Sum.inl _ => a
  | Sum.inr _ => b

/-- The bag evaluation is the coherent sum of its original occurrence values. -/
theorem sum_occurrenceValue (n m : ℕ) :
    (∑ t : Occurrence n m, occurrenceValue t) = bagEval n m := by
  simp [Fintype.sum_sum_type, occurrenceValue, bagEval, nsmul_eq_mul]

/-- Each unordered original subset is used once. Its empty subset is included. -/
def originalSubsetCount (K : ℕ) (κ : Kernel) (n m : ℕ) : ℝ :=
  ∑ s : Finset (Occurrence n m),
    if s.card ≤ K then κ s.toLeft.card s.toRight.card else 0

/-- A rectangular finite sum with the triangular order cutoff. -/
def binomialSum (K : ℕ) (κ : Kernel) (n m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (K + 1), ∑ k ∈ Finset.range (K + 1),
    if j + k ≤ K then κ j k * (n.choose j : ℝ) * (m.choose k : ℝ) else 0

/-- Compatibility is supplied for all finite bags, with one fixed kernel. -/
def CompatibleOriginalKernel (W : Presentation → ℝ) (K : ℕ) (κ : Kernel) : Prop :=
  ∀ n m : ℕ, W (bagEval n m) = originalSubsetCount K κ n m

private theorem sum_finset_card_eq (n j : ℕ) (v : ℝ) :
    (∑ s : Finset (Fin n), if s.card = j then v else 0) =
      (n.choose j : ℝ) * v := by
  classical
  rw [← Finset.sum_filter]
  simp [Finset.univ_filter_card_eq, Finset.card_powersetCard, nsmul_eq_mul]

private theorem sum_finset_card_pair (n m j k : ℕ) (v : ℝ) :
    (∑ s : Finset (Fin n), ∑ t : Finset (Fin m),
      if s.card = j then (if t.card = k then v else 0) else 0) =
        (n.choose j : ℝ) * (m.choose k : ℝ) * v := by
  classical
  calc
    _ = ∑ s : Finset (Fin n), if s.card = j then (m.choose k : ℝ) * v else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hj : s.card = j
      · simp only [hj, if_true]
        exact sum_finset_card_eq m k v
      · simp [hj]
    _ = _ := by
      rw [sum_finset_card_eq]
      ring

private theorem cardinal_kernel_expansion (K : ℕ) (κ : Kernel) (s t : ℕ) :
    (if s + t ≤ K then κ s t else 0) =
      ∑ j ∈ Finset.range (K + 1), ∑ k ∈ Finset.range (K + 1),
        if s = j then (if t = k then (if j + k ≤ K then κ j k else 0) else 0)
        else 0 := by
  classical
  by_cases h : s + t ≤ K
  · have hs : s ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by omega)
    have ht : t ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by omega)
    symm
    rw [Finset.sum_eq_single s]
    · rw [Finset.sum_eq_single t]
      · simp [h]
      · intro k hk hkt
        simp [Ne.symm hkt]
      · exact fun hnot => False.elim (hnot ht)
    · intro j hj hjs
      simp [Ne.symm hjs]
    · exact fun hnot => False.elim (hnot hs)
  · simp only [if_neg h]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hs : s = j
    · by_cases ht : t = k
      · have h' : ¬j + k ≤ K := by simpa [hs, ht] using h
        simp [hs, ht, h']
      · simp [ht]
    · simp [hs]

private theorem swap_four_sums
    {α β γ δ : Type*} (s : Finset α) (t : Finset β)
    (u : Finset γ) (v : Finset δ) (f : α → β → γ → δ → ℝ) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, f a b c d) =
      ∑ c ∈ u, ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t, f a b c d := by
  calc
    _ = ∑ a ∈ s, ∑ c ∈ u, ∑ b ∈ t, ∑ d ∈ v, f a b c d := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, ∑ d ∈ v, f a b c d :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      calc
        _ = ∑ a ∈ s, ∑ d ∈ v, ∑ b ∈ t, f a b c d := by
          apply Finset.sum_congr rfl
          intro a ha
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

/-- Grouping the actual unordered tagged subsets gives the binomial formula. -/
theorem originalSubsetCount_eq_binomialSum (K : ℕ) (κ : Kernel) (n m : ℕ) :
    originalSubsetCount K κ n m = binomialSum K κ n m := by
  classical
  have hpairs : originalSubsetCount K κ n m =
      ∑ s : Finset (Fin n), ∑ t : Finset (Fin m),
        if s.card + t.card ≤ K then κ s.card t.card else 0 := by
    unfold originalSubsetCount
    calc
      _ = ∑ p : Finset (Fin n) × Finset (Fin m),
          if p.1.card + p.2.card ≤ K then κ p.1.card p.2.card else 0 := by
        apply Fintype.sum_equiv (Finset.sumEquiv.toEquiv) _ _
        intro s
        change (if s.card ≤ K then κ s.toLeft.card s.toRight.card else 0) =
          (if s.toLeft.card + s.toRight.card ≤ K then κ s.toLeft.card s.toRight.card else 0)
        rw [Finset.card_toLeft_add_card_toRight]
      _ = _ := Fintype.sum_prod_type _
  have hexpand :
      (∑ s : Finset (Fin n), ∑ t : Finset (Fin m),
        if s.card + t.card ≤ K then κ s.card t.card else 0) =
      ∑ s : Finset (Fin n), ∑ t : Finset (Fin m),
        ∑ j ∈ Finset.range (K + 1), ∑ k ∈ Finset.range (K + 1),
          if s.card = j then
            (if t.card = k then (if j + k ≤ K then κ j k else 0) else 0)
          else 0 := by
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro t ht
    exact cardinal_kernel_expansion K κ s.card t.card
  rw [hpairs, hexpand, swap_four_sums]
  unfold binomialSum
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [sum_finset_card_pair]
  by_cases h : j + k ≤ K <;> simp [h] <;> ring

/-- Lift a univariate polynomial to one specified coordinate. -/
private def coordinatePolynomial (i : Fin 2) (p : Polynomial ℂ) :
    MvPolynomial (Fin 2) ℂ :=
  p.eval₂ MvPolynomial.C (MvPolynomial.X i)

private theorem eval_coordinatePolynomial
    (i : Fin 2) (p : Polynomial ℂ) (x : Fin 2 → ℂ) :
    MvPolynomial.eval x (coordinatePolynomial i p) = p.eval (x i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [coordinatePolynomial, Polynomial.eval₂_add, map_add,
        Polynomial.eval_add] at hp hq ⊢
      rw [hp, hq]
  | monomial n a =>
      simp [coordinatePolynomial, Polynomial.eval₂_monomial, Polynomial.eval_monomial]

/-- The falling-factorial polynomial divided by the factorial, on one coordinate. -/
def chooseCoordinate (i : Fin 2) (j : ℕ) : MvPolynomial (Fin 2) ℂ :=
  coordinatePolynomial i
    (Polynomial.C ((j.factorial : ℂ)⁻¹) * descPochhammer ℂ j)

private theorem eval_chooseCoordinate (i : Fin 2) (j : ℕ)
    (x : Fin 2 → ℂ) (n : ℕ) (hx : x i = n) :
    MvPolynomial.eval x (chooseCoordinate i j) = (n.choose j : ℂ) := by
  rw [chooseCoordinate, eval_coordinatePolynomial]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, hx]
  rw [Nat.cast_choose_eq_descPochhammer_div]
  ring

/-- A supplied finite kernel determines one global bivariate polynomial. -/
def kernelPolynomial (K : ℕ) (κ : Kernel) : MvPolynomial (Fin 2) ℂ :=
  ∑ j ∈ Finset.range (K + 1), ∑ k ∈ Finset.range (K + 1),
    if j + k ≤ K then C (κ j k : ℂ) * chooseCoordinate 0 j * chooseCoordinate 1 k
    else 0

/-- Evaluation is valid for every natural input, including counts below an index. -/
theorem eval_kernelPolynomial (K : ℕ) (κ : Kernel) (n m : ℕ) :
    MvPolynomial.eval ![(n : ℂ), (m : ℂ)] (kernelPolynomial K κ) =
      (binomialSum K κ n m : ℂ) := by
  classical
  unfold kernelPolynomial binomialSum
  simp only [map_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : j + k ≤ K
  · simp only [h, if_true, map_mul, eval_C]
    rw [eval_chooseCoordinate 0 j _ n (by simp),
      eval_chooseCoordinate 1 k _ m (by simp)]
    simp
  · simp [h]

/-- The compatibility premise supplies the polynomial representation. -/
theorem compatible_polynomial_eval
    {W : Presentation → ℝ} {K : ℕ} {κ : Kernel}
    (H : CompatibleOriginalKernel W K κ) (n m : ℕ) :
    MvPolynomial.eval ![(n : ℂ), (m : ℂ)] (kernelPolynomial K κ) =
      (W (bagEval n m) : ℂ) := by
  rw [eval_kernelPolynomial, H, originalSubsetCount_eq_binomialSum]

/-- The normalized positive order-two witness. Its mixed coefficient is zero. -/
def pairKernel (j k : ℕ) : ℝ :=
  if (j = 1 ∧ k = 0) ∨ (j = 0 ∧ k = 1) then 1 / 2
  else if (j = 2 ∧ k = 0) ∨ (j = 0 ∧ k = 2) then 1 else 0

theorem pairKernel_nonnegative (j k : ℕ) : 0 ≤ pairKernel j k := by
  unfold pairKernel
  split_ifs <;> norm_num

theorem binomialSum_pairKernel (n m : ℕ) :
    binomialSum 2 pairKernel n m = ((n : ℝ) ^ 2 + (m : ℝ) ^ 2) / 2 := by
  simp [binomialSum, Finset.sum_range_succ, pairKernel, Nat.cast_choose_two]
  ring

end IDT.QMClosure.OriginalOccurrenceKernel
