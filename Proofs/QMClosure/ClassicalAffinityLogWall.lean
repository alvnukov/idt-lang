import Mathlib
import Proofs.QMClosure.RawProcessComparisonBridge
import Proofs.QMClosure.PairComparisonReconstruction

/-!
# A finite classical-affinity logarithm boundary

Three explicitly supplied Bernoulli distributions have an entrywise strictly
positive, positive-semidefinite affinity matrix. Its negative logarithm fails conditional
negative definiteness, and its entrywise square root fails positive
semidefiniteness. The finite distribution data are mathematical countercontrols.
No detector realization or globally covariant gate is constructed here.
-/

namespace IDT.QMClosure.ClassicalAffinityLogWall

noncomputable section

open scoped BigOperators

def probabilityRow : Fin 3 → Fin 2 → ℝ :=
  ![![1 / 5, 4 / 5], ![1 / 2, 1 / 2], ![4 / 5, 1 / 5]]

theorem probabilityRow_positive (i : Fin 3) (r : Fin 2) :
    0 < probabilityRow i r := by
  fin_cases i <;> fin_cases r <;> norm_num [probabilityRow]

theorem probabilityRow_nonnegative (i : Fin 3) (r : Fin 2) :
    0 ≤ probabilityRow i r := (probabilityRow_positive i r).le

theorem probabilityRow_normalized (i : Fin 3) :
    ∑ r, probabilityRow i r = 1 := by
  fin_cases i <;> norm_num [probabilityRow, Fin.sum_univ_succ]

/-- The ordinary finite classical affinity, evaluated on the supplied rows. -/
def affinity (i j : Fin 3) : ℝ :=
  ∑ r, Real.sqrt (probabilityRow i r * probabilityRow j r)

def adjacent : ℝ := 3 * Real.sqrt (1 / 10)

theorem adjacent_positive : 0 < adjacent := by
  unfold adjacent
  positivity

theorem adjacent_sq : adjacent ^ 2 = 9 / 10 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 10 by norm_num)
  unfold adjacent
  nlinarith

theorem adjacent_lt_one : adjacent < 1 := by
  nlinarith [adjacent_sq, adjacent_positive]

theorem adjacent_eq_three_div_sqrt_ten : adjacent = 3 / Real.sqrt 10 := by
  rw [adjacent, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
  norm_num
  ring

private theorem sqrt_two_fifths :
    Real.sqrt (2 / 5 : ℝ) = 2 * Real.sqrt (1 / 10 : ℝ) := by
  apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).2
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 10 by norm_num)
  nlinarith

/-- An explicit formula for all nine actual affinities. -/
theorem affinity_matrix : affinity =
    ![![1, adjacent, 4 / 5], ![adjacent, 1, adjacent],
      ![4 / 5, adjacent, 1]] := by
  have htwo := sqrt_two_fifths
  norm_num at htwo
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [affinity, probabilityRow, Fin.sum_univ_succ, adjacent] <;>
      nlinarith [htwo]

theorem affinity_positive (i j : Fin 3) : 0 < affinity i j := by
  rw [affinity_matrix]
  fin_cases i <;> fin_cases j <;> norm_num [adjacent_positive]

theorem affinity_le_one (i j : Fin 3) : affinity i j ≤ 1 := by
  rw [affinity_matrix]
  fin_cases i <;> fin_cases j <;> norm_num [adjacent_lt_one.le]

theorem affinity_symmetric (i j : Fin 3) : affinity i j = affinity j i := by
  unfold affinity
  congr 1
  funext r
  rw [mul_comm]

theorem affinity_self (i : Fin 3) : affinity i i = 1 := by
  rw [affinity_matrix]
  fin_cases i <;> norm_num

def sqrtFeatures : Matrix (Fin 2) (Fin 3) ℝ :=
  fun r i => Real.sqrt (probabilityRow i r)

/-- Positivity is supplied by a genuine Gram factorization of square-root rows. -/
theorem affinity_eq_gram :
    affinity = sqrtFeatures.conjTranspose * sqrtFeatures := by
  ext i j
  simp only [affinity, Matrix.mul_apply, Matrix.conjTranspose_apply,
    sqrtFeatures, star_trivial]
  apply Finset.sum_congr rfl
  intro r hr
  exact Real.sqrt_mul (probabilityRow_nonnegative i r) _

theorem affinity_posSemidef : Matrix.PosSemidef affinity := by
  rw [affinity_eq_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

def quadraticForm (K : Fin 3 → Fin 3 → ℝ) (c : Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * K i j * c j

def ConditionallyNegative (K : Fin 3 → Fin 3 → ℝ) : Prop :=
  ∀ c : Fin 3 → ℝ, (∑ i, c i) = 0 → quadraticForm K c ≤ 0

def logComparison (i j : Fin 3) : ℝ := -Real.log (affinity i j)

theorem logComparison_nonnegative (i j : Fin 3) : 0 ≤ logComparison i j := by
  exact neg_nonneg.mpr (Real.log_nonpos (affinity_positive i j).le
    (affinity_le_one i j))

theorem logComparison_symmetric (i j : Fin 3) :
    logComparison i j = logComparison j i := by
  simp only [logComparison, affinity_symmetric i j]

theorem logComparison_self (i : Fin 3) : logComparison i i = 0 := by
  simp [logComparison, affinity_self]

def logWitness : Fin 3 → ℝ := ![1, -2, 1]

theorem logWitness_zero_sum : ∑ i, logWitness i = 0 := by
  norm_num [logWitness, Fin.sum_univ_succ]

theorem logWitness_quadraticForm :
    quadraticForm logComparison logWitness = 2 * Real.log (81 / 80) := by
  have hfour : adjacent ^ 4 = (81 / 100 : ℝ) := by
    calc
      adjacent ^ 4 = (adjacent ^ 2) ^ 2 := by ring
      _ = 81 / 100 := by rw [adjacent_sq]; norm_num
  have hlog : 4 * Real.log adjacent = Real.log (81 / 100 : ℝ) := by
    calc
      4 * Real.log adjacent = Real.log (adjacent ^ 4) := by
        exact (Real.log_pow adjacent 4).symm
      _ = Real.log (81 / 100 : ℝ) := by rw [hfour]
  have hratio : Real.log (81 / 80 : ℝ) =
      Real.log (81 / 100 : ℝ) - Real.log (4 / 5 : ℝ) := by
    rw [← Real.log_div (by norm_num : (81 / 100 : ℝ) ≠ 0)
      (by norm_num : (4 / 5 : ℝ) ≠ 0)]
    norm_num
  simp [quadraticForm, logComparison, affinity_matrix, logWitness,
    Fin.sum_univ_succ]
  rw [hratio]
  linarith

theorem logWitness_positive : 0 < quadraticForm logComparison logWitness := by
  rw [logWitness_quadraticForm]
  exact mul_pos (by norm_num) (Real.log_pos (by norm_num))

/-- Ordinary affinity Gram positivity does not imply CND of its negative log. -/
theorem logComparison_not_conditionallyNegative :
    ¬ ConditionallyNegative logComparison := by
  intro h
  exact (not_le_of_gt logWitness_positive) (h logWitness logWitness_zero_sum)

def rootAffinity (i j : Fin 3) : ℝ := Real.sqrt (affinity i j)

def rootWitness : Fin 3 → ℝ := ![1, -2 * Real.sqrt adjacent, 1]

theorem rootWitness_quadraticForm :
    quadraticForm rootAffinity rootWitness =
      2 * (1 + Real.sqrt (4 / 5 : ℝ) - 2 * adjacent) := by
  have hs := Real.sq_sqrt adjacent_positive.le
  simp [quadraticForm, rootAffinity, affinity_matrix, rootWitness,
    Fin.sum_univ_succ]
  nlinarith

theorem rootWitness_negative : quadraticForm rootAffinity rootWitness < 0 := by
  rw [rootWitness_quadraticForm]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 4 / 5 by norm_num)
  have hn := Real.sqrt_nonneg (4 / 5 : ℝ)
  have hsmall : Real.sqrt (4 / 5 : ℝ) < 9 / 10 := by nlinarith
  have ha := adjacent_positive
  have hgap : 1 + Real.sqrt (4 / 5 : ℝ) < 2 * adjacent := by
    by_contra h
    have hprod := mul_nonneg
      (show 0 ≤ 1 + Real.sqrt (4 / 5 : ℝ) - 2 * adjacent by linarith)
      (show 0 ≤ 1 + Real.sqrt (4 / 5 : ℝ) + 2 * adjacent by positivity)
    nlinarith [adjacent_sq]
  linarith

private theorem matrix_quadraticForm (K : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) :
    star c ⬝ᵥ (Matrix.mulVec K c) = quadraticForm K c := by
  simp [dotProduct, Matrix.mulVec, quadraticForm, Finset.mul_sum, mul_assoc]

/-- The square root is an explicit failed positive-semidefinite entrywise power. -/
theorem rootAffinity_not_posSemidef : ¬ Matrix.PosSemidef rootAffinity := by
  intro h
  have hnonneg := h.dotProduct_mulVec_nonneg rootWitness
  rw [matrix_quadraticForm] at hnonneg
  exact (not_le_of_gt rootWitness_negative) hnonneg

section SuppliedAffinityLaws

variable {V : Type*}

/-- A comparison defined from an arbitrary supplied affinity. -/
def negativeLog (A : V → V → ℝ) (x y : V) : ℝ := -Real.log (A x y)

theorem negativeLog_symmetric (A : V → V → ℝ)
    (hsym : ∀ x y, A x y = A y x) (x y : V) :
    negativeLog A x y = negativeLog A y x := by
  simp only [negativeLog, hsym x y]

theorem negativeLog_self (A : V → V → ℝ)
    (hself : ∀ x, A x x = 1) (x : V) : negativeLog A x x = 0 := by
  simp [negativeLog, hself]

theorem negativeLog_nonnegative (A : V → V → ℝ)
    (hpositive : ∀ x y, 0 < A x y) (hbound : ∀ x y, A x y ≤ 1)
    (x y : V) : 0 ≤ negativeLog A x y := by
  exact neg_nonneg.mpr (Real.log_nonpos (hpositive x y).le (hbound x y))

/-- This is an implication between supplied laws. No Markov-processing theorem
or gate-compatible detector realization is asserted. -/
theorem negativeLog_pair_nonexpanding (A : V → V → ℝ)
    (hpositive : ∀ x y, 0 < A x y) (F : V × V → V × V)
    (hproduct : ∀ p q, A p.1 q.1 * A p.2 q.2 ≤
      A (F p).1 (F q).1 * A (F p).2 (F q).2) :
    RawProcessComparisonBridge.PairComparisonNonexpanding (negativeLog A) F := by
  intro p q
  have hlog := Real.log_le_log
    (mul_pos (hpositive p.1 q.1) (hpositive p.2 q.2)) (hproduct p q)
  rw [Real.log_mul (hpositive p.1 q.1).ne' (hpositive p.2 q.2).ne',
    Real.log_mul (hpositive (F p).1 (F q).1).ne'
      (hpositive (F p).2 (F q).2).ne'] at hlog
  unfold RawProcessComparisonBridge.pairComparison negativeLog
  linarith

/-- Assemble only the supplied affinity and gate laws into the reconstruction
contract. Physical availability and Markov-processing origin remain separate. -/
def affinityContract (o : V) (F : V × V → V × V)
    (hsquare : ∀ p, F (F p) = p.swap)
    (htransparent : ∀ x, F (x, x) = (x, x))
    (A : V → V → ℝ) (hpositive : ∀ x y, 0 < A x y)
    (hbound : ∀ x y, A x y ≤ 1) (hsym : ∀ x y, A x y = A y x)
    (hself : ∀ x, A x x = 1)
    (hproduct : ∀ p q, A p.1 q.1 * A p.2 q.2 ≤
      A (F p).1 (F q).1 * A (F p).2 (F q).2) :
    PairComparisonReconstruction.Contract V where
  chosenZero := o
  operation := F
  comparison := negativeLog A
  square := hsquare
  transparent := htransparent
  symmetric := negativeLog_symmetric A hsym
  nonnegative := negativeLog_nonnegative A hpositive hbound
  diagonal := negativeLog_self A hself
  nonexpanding := negativeLog_pair_nonexpanding A hpositive F hproduct

/-- End-to-end mathematical reconstruction under the complete supplied laws. -/
theorem negativeLog_distance (o : V) (F : V × V → V × V)
    (hsquare : ∀ p, F (F p) = p.swap)
    (htransparent : ∀ x, F (x, x) = (x, x))
    (A : V → V → ℝ) (hpositive : ∀ x y, 0 < A x y)
    (hbound : ∀ x y, A x y ≤ 1) (hsym : ∀ x y, A x y = A y x)
    (hself : ∀ x, A x x = 1)
    (hproduct : ∀ p q, A p.1 q.1 * A p.2 q.2 ≤
      A (F p).1 (F q).1 * A (F p).2 (F q).2) (x y : V) :
    let D := affinityContract o F hsquare htransparent A hpositive hbound hsym
      hself hproduct
    negativeLog A x y = ‖D.feature x - D.feature y‖ ^ 2 := by
  exact (affinityContract o F hsquare htransparent A hpositive hbound hsym
    hself hproduct).comparison_eq_norm_sub_sq x y

end SuppliedAffinityLaws

end

end IDT.QMClosure.ClassicalAffinityLogWall
