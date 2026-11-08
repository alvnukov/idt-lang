import Proofs.QMClosure.RawProcessComparisonBridge
import Proofs.QMClosure.RationalFiniteDistribution
import Mathlib.Algebra.Field.GeomSum

/-!
# Bounded comparison and total reference preparation

A total reference right inverse and exact half attenuation force every
nonnegative comparison to vanish when its inverse-reference orbit has one
uniform finite upper bound. The bound may depend on the fixed input pair.
Finite depth supplies a quantitative bound without a total inverse-reference
orbit. Uniform one-step errors leave the sharp residual ceiling twice the
error. Pointwise preparation closeness is not a comparison-error hypothesis.

These statements concern supplied real comparisons. They do not establish a
metric, a quadratic comparison, Born readout, or quantum mechanics. A resource
indexed comparison and a map between distinct resource carriers do not satisfy
the single-carrier, uniform-orbit-bound hypotheses merely by being finite at
each resource level.
-/

namespace IDT.QMClosure.BoundedComparisonReferenceWall

open scoped BigOperators
open RawDyadicMidpointGram

noncomputable section

variable {V : Type*}

/-- Only the first N recurrence inequalities are used. -/
theorem finite_recurrence_bound (f : ℕ → ℝ) (c ε M : ℝ) (N : ℕ)
    (hc : 0 ≤ c) (hstep : ∀ n, n < N → f n ≤ c * f (n + 1) + ε)
    (hterminal : f N ≤ M) :
    f 0 ≤ c ^ N * M + ε * ∑ j ∈ Finset.range N, c ^ j := by
  have hprefix : ∀ n : ℕ, n ≤ N →
      f 0 ≤ c ^ n * f n + ε * ∑ j ∈ Finset.range n, c ^ j := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
        intro hn
        have hprev := ih (by omega)
        have hnext := mul_le_mul_of_nonneg_left (hstep n (by omega))
          (pow_nonneg hc n)
        rw [Finset.sum_range_succ, pow_succ]
        nlinarith
  have hlast := mul_le_mul_of_nonneg_left hterminal (pow_nonneg hc N)
  exact (hprefix N le_rfl).trans (by linarith)

theorem finite_half_recurrence_bound (f : ℕ → ℝ) (ε M : ℝ) (N : ℕ)
    (hstep : ∀ n, n < N → f n ≤ (1 / 2 : ℝ) * f (n + 1) + ε)
    (hterminal : f N ≤ M) :
    f 0 ≤ (1 / 2 : ℝ) ^ N * M +
      2 * ε * (1 - (1 / 2 : ℝ) ^ N) := by
  have h := finite_recurrence_bound f (1 / 2) ε M N (by norm_num) hstep hterminal
  rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)] at h
  convert h using 1
  ring

/-- Signed terminal bounds and signed error parameters are allowed. -/
theorem bounded_recurrence_bound (f : ℕ → ℝ) (c ε M : ℝ)
    (hc : 0 ≤ c) (hc_one : c < 1)
    (hstep : ∀ n, f n ≤ c * f (n + 1) + ε)
    (hbound : ∀ n, f n ≤ M) : f 0 ≤ ε / (1 - c) := by
  let L := ε / (1 - c)
  have hden : 1 - c ≠ 0 := by linarith
  have hfixed : L = c * L + ε := by
    dsimp [L]
    field_simp [hden]
    ring
  have hshift (n : ℕ) : f n - L ≤ c * (f (n + 1) - L) := by
    linarith [hstep n]
  have hfinite (n : ℕ) : f 0 - L ≤ c ^ n * (M - L) := by
    have h := finite_recurrence_bound (fun n => f n - L) c 0 (M - L) n hc
      (fun k _ => by simpa using hshift k) (by linarith [hbound n])
    simpa using h
  by_contra hnot
  have hpos : 0 < f 0 - L := by dsimp [L] at *; linarith
  by_cases hM : 0 < M - L
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hpos hM) hc_one
    have hsmall : c ^ n * (M - L) < f 0 - L := (lt_div_iff₀ hM).mp hn
    linarith [hfinite n]
  · have hzero := hfinite 0
    norm_num at hzero
    linarith

theorem bounded_half_recurrence_bound (f : ℕ → ℝ) (ε M : ℝ)
    (hstep : ∀ n, f n ≤ (1 / 2 : ℝ) * f (n + 1) + ε)
    (hbound : ∀ n, f n ≤ M) : f 0 ≤ 2 * ε := by
  have h := bounded_recurrence_bound f (1 / 2) ε M (by norm_num) (by norm_num)
    hstep hbound
  convert h using 1
  ring

/-- A per-pair bound must be uniform in the reference iteration index. -/
theorem comparison_le_twice_error_of_orbit_bound
    (D : V → V → ℝ) (R : V → V) (ε : ℝ)
    (hstep : ∀ x y, D x y ≤ (1 / 2 : ℝ) * D (R x) (R y) + ε)
    (hbound : ∀ x y, ∃ M : ℝ, ∀ n,
      D (halfIterate R n x) (halfIterate R n y) ≤ M) (x y : V) :
    D x y ≤ 2 * ε := by
  obtain ⟨M, hM⟩ := hbound x y
  exact bounded_half_recurrence_bound
    (fun n => D (halfIterate R n x) (halfIterate R n y)) ε M
    (fun n => by
      simpa only [halfIterate] using hstep (halfIterate R n x) (halfIterate R n y)) hM

/-- Comparison reconstruction error is supplied explicitly in comparison units. -/
theorem comparison_le_twice_combined_error
    (D : V → V → ℝ) (B R : V → V) (ε η : ℝ)
    (hatten : ∀ x y, D (B x) (B y) ≤ (1 / 2 : ℝ) * D x y + ε)
    (hreference : ∀ x y, |D (B (R x)) (B (R y)) - D x y| ≤ η)
    (hbound : ∀ x y, ∃ M : ℝ, ∀ n,
      D (halfIterate R n x) (halfIterate R n y) ≤ M) (x y : V) :
    D x y ≤ 2 * (ε + η) := by
  apply comparison_le_twice_error_of_orbit_bound D R (ε + η) ?_ hbound x y
  intro u v
  have hlower := (abs_le.mp (hreference u v)).1
  linarith [hatten (R u) (R v)]

theorem comparison_eq_zero_of_exact_half_reference
    (D : V → V → ℝ) (B R : V → V)
    (hnonneg : ∀ x y, 0 ≤ D x y)
    (hhalf : ∀ x y, D (B x) (B y) = D x y / 2)
    (hreference : ∀ x, B (R x) = x)
    (hbound : ∀ x y, ∃ M : ℝ, ∀ n,
      D (halfIterate R n x) (halfIterate R n y) ≤ M) (x y : V) :
    D x y = 0 := by
  have hupper := comparison_le_twice_error_of_orbit_bound D R 0 (by
    intro u v
    have h := hhalf (R u) (R v)
    rw [hreference u, hreference v] at h
    linarith) hbound x y
  linarith [hnonneg x y]

theorem comparison_eq_zero_of_global_bound
    (D : V → V → ℝ) (B R : V → V) (M : ℝ)
    (hnonneg : ∀ x y, 0 ≤ D x y)
    (hhalf : ∀ x y, D (B x) (B y) = D x y / 2)
    (hreference : ∀ x, B (R x) = x)
    (hbound : ∀ x y, D x y ≤ M) (x y : V) : D x y = 0 := by
  exact comparison_eq_zero_of_exact_half_reference D B R hnonneg hhalf hreference
    (fun _ _ => ⟨M, fun _ => hbound _ _⟩) x y

/-- This adapter uses precisely the reference preparation in the process bridge.
No complete-gate conservation or order-four identity enters this wall. -/
theorem process_reference_comparison_eq_zero
    (D : V → V → ℝ) (F : V × V → V × V) (J B : V → V) (M : ℝ)
    (hnonneg : ∀ x y, 0 ≤ D x y)
    (hhalf : ∀ x y, D (B x) (B y) = D x y / 2)
    (hreference : ∀ z, B (F (z, J z)).1 = z)
    (hbound : ∀ x y, D x y ≤ M) (x y : V) : D x y = 0 := by
  exact comparison_eq_zero_of_global_bound D B (fun z => (F (z, J z)).1) M
    hnonneg hhalf hreference hbound x y

/-- A bounded two-point comparison attains the robust ceiling. -/
def twoPointComparison (ε : ℝ) (x y : Bool) : ℝ := if x = y then 0 else 2 * ε

theorem twoPointComparison_nonnegative (ε : ℝ) (hε : 0 ≤ ε) (x y : Bool) :
    0 ≤ twoPointComparison ε x y := by
  unfold twoPointComparison
  split_ifs <;> linarith

theorem twoPointComparison_symmetric (ε : ℝ) (x y : Bool) :
    twoPointComparison ε x y = twoPointComparison ε y x := by
  simp [twoPointComparison, eq_comm]

theorem twoPointComparison_eq_zero_iff (ε : ℝ) (hε : 0 < ε) (x y : Bool) :
    twoPointComparison ε x y = 0 ↔ x = y := by
  unfold twoPointComparison
  split_ifs with h
  · simp [h]
  · constructor
    · intro hz; linarith
    · exact fun hxy => (h hxy).elim

theorem twoPointComparison_triangle (ε : ℝ) (hε : 0 ≤ ε) (x y z : Bool) :
    twoPointComparison ε x z ≤ twoPointComparison ε x y +
      twoPointComparison ε y z := by
  cases x <;> cases y <;> cases z <;> simp [twoPointComparison] <;> linarith

theorem twoPointComparison_bounded (ε : ℝ) (hε : 0 ≤ ε) (x y : Bool) :
    twoPointComparison ε x y ≤ 2 * ε := by
  unfold twoPointComparison
  split_ifs <;> linarith

theorem twoPointComparison_half_error (ε : ℝ) (hε : 0 ≤ ε) (x y : Bool) :
    |twoPointComparison ε (id x) (id y) - twoPointComparison ε x y / 2| ≤ ε := by
  simp only [id_eq, twoPointComparison]
  split_ifs <;> rw [abs_of_nonneg (by linarith)] <;> linarith

theorem twoPointComparison_attains_error_ceiling (ε : ℝ) :
    twoPointComparison ε false true = 2 * ε := by
  simp [twoPointComparison]

/-- This is a finite chain, whose admissible range ends at N. -/
def finiteSharpChain (M : ℝ) (N n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (N - n) * M

theorem finiteSharpChain_step (M : ℝ) (N n : ℕ) (hn : n < N) :
    finiteSharpChain M N n = (1 / 2 : ℝ) * finiteSharpChain M N (n + 1) := by
  have hexp : N - n = (N - (n + 1)) + 1 := by omega
  unfold finiteSharpChain
  rw [hexp, pow_succ]
  ring

theorem finiteSharpChain_admissible (M : ℝ) (hM : 0 ≤ M) (N n : ℕ) :
    0 ≤ finiteSharpChain M N n ∧ finiteSharpChain M N n ≤ M := by
  have hpow : (1 / 2 : ℝ) ^ (N - n) ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  constructor
  · exact mul_nonneg (pow_nonneg (by norm_num) _) hM
  · exact (mul_le_mul_of_nonneg_right hpow hM).trans_eq (one_mul M)

theorem finiteSharpChain_attainment (M : ℝ) (N : ℕ) :
    finiteSharpChain M N N = M ∧ finiteSharpChain M N 0 = (1 / 2 : ℝ) ^ N * M := by
  simp [finiteSharpChain]

section ClassicalTotalVariation

open RationalFiniteDistribution

/-- Normalized rational distributions give one global real comparison bound. -/
theorem real_tv_bounds (μ ν : FinDist V) :
    0 ≤ (tv μ ν : ℝ) ∧ (tv μ ν : ℝ) ≤ 1 := by
  have hneg : l1 (-ν.coeff) = l1 ν.coeff := by
    simpa using l1_smul (-1) ν.coeff
  have hsum := l1_add_le μ.coeff (-ν.coeff)
  rw [l1_of_nonneg μ.coeff μ.nonneg, μ.mass_one, hneg,
    l1_of_nonneg ν.coeff ν.nonneg, ν.mass_one] at hsum
  have hupper : tv μ ν ≤ 1 := by
    unfold tv
    rw [sub_eq_add_neg]
    linarith
  have hlower : 0 ≤ tv μ ν := div_nonneg (l1_nonneg _) (by norm_num)
  exact ⟨by exact_mod_cast hlower, by exact_mod_cast hupper⟩

theorem real_tv_dirac_of_ne (u v : V) (huv : u ≠ v) :
    (tv (dirac u) (dirac v) : ℝ) = 1 := by
  classical
  let d := (dirac u).coeff - (dirac v).coeff
  have hs : d.support ⊆ {u, v} := by
    intro w hw
    by_cases hwu : w = u
    · simp [hwu]
    by_cases hwv : w = v
    · simp [hwv]
    have hzero : d w = 0 := by simp [d, dirac, hwu, hwv]
    exact False.elim ((Finsupp.mem_support_iff.mp hw) hzero)
  have hrat : tv (dirac u) (dirac v) = 1 := by
    change l1 d / 2 = 1
    rw [l1, Finsupp.sum_of_support_subset d hs _ (by simp)]
    norm_num [d, dirac, huv, Ne.symm huv]
  exact_mod_cast hrat

/-- Exact half calibration and a total reference retract cannot coexist on
the entire nontrivial normalized classical distribution carrier. -/
theorem no_total_tv_half_reference [Nontrivial V]
    (B R : FinDist V → FinDist V)
    (hhalf : ∀ μ ν, (tv (B μ) (B ν) : ℝ) = (tv μ ν : ℝ) / 2)
    (hreference : ∀ μ, B (R μ) = μ) : False := by
  obtain ⟨u, v, huv⟩ := exists_pair_ne V
  have hzero := comparison_eq_zero_of_global_bound
    (fun μ ν : FinDist V => (tv μ ν : ℝ)) B R 1
    (fun μ ν => (real_tv_bounds μ ν).1) hhalf hreference
    (fun μ ν => (real_tv_bounds μ ν).2) (dirac u) (dirac v)
  rw [real_tv_dirac_of_ne u v huv] at hzero
  norm_num at hzero

end ClassicalTotalVariation

end
end IDT.QMClosure.BoundedComparisonReferenceWall
