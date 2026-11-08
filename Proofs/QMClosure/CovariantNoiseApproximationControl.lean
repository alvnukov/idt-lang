import Proofs.QMClosure.FiniteCovariantNoiseWall
import Proofs.QMClosure.RawNetworkMedialWall

/-!
# Approximation control for finite covariant-noise rigidity

This finite stochastic family separates exact product covariance from small
coefficient and total-variation defects. Its strictly positive floor tends to
zero with the noise parameter. The statements concern raw finite kernels and
their explicitly defined error norms.
-/

namespace IDT.QMClosure.CovariantNoiseApproximationControl

noncomputable section

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Identity readout mixed with uniform noise of total weight `t`. -/
def noisyIdentityKernel (t : ℝ) (x r : V) : ℝ :=
  (1 - t) * (if r = x then 1 else 0) + t / Fintype.card V

/-- Total variation between two finite rows. -/
def rowTV (K : V → V → ℝ) (x y : V) : ℝ :=
  (∑ r, |K x r - K y r|) / 2

/-- Signed defect of a single product-covariance coefficient. -/
def coefficientCovarianceDefect (K : V → V → ℝ)
    (F : V × V → V × V) (x y r s : V) : ℝ :=
  K (F (x, y)).1 (F (r, s)).1 * K (F (x, y)).2 (F (r, s)).2 -
    K x r * K y s

/-- Half the summed absolute pulled-back coefficient defects for one input pair.
For bijective `F`, this equals the TV distance of the two output channels. -/
def channelCovarianceTV (K : V → V → ℝ)
    (F : V × V → V × V) (x y : V) : ℝ :=
  (∑ p : V × V, |coefficientCovarianceDefect K F x y p.1 p.2|) / 2

private def coordinateMatches (x y r s : V) : ℝ :=
  (if r = x then 1 else 0) + (if s = y then 1 else 0)

private theorem card_pos [Nonempty V] : (0 : ℝ) < Fintype.card V := by
  exact_mod_cast Fintype.card_pos

/-- The family has the explicit positive uniform lower bound `t / card V`. -/
theorem positivity_floor [Nonempty V] {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (x r : V) : 0 < t / Fintype.card V ∧
      t / Fintype.card V ≤ noisyIdentityKernel t x r := by
  constructor
  · exact div_pos ht card_pos
  · unfold noisyIdentityKernel
    have : 0 ≤ (1 - t) * (if r = x then (1 : ℝ) else 0) :=
      mul_nonneg (by linarith) (by split_ifs <;> norm_num)
    linarith

/-- Each row is exactly normalized. -/
theorem row_sum [Nonempty V] (t : ℝ) (x : V) :
    ∑ r, noisyIdentityKernel t x r = 1 := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := ne_of_gt card_pos
  simp [noisyIdentityKernel, sum_add_distrib, ← mul_sum, hn]
  field_simp
  <;> ring

/-- The positive normalized entries are bounded above by one. -/
theorem entry_le_one [Nonempty V] {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (x r : V) : noisyIdentityKernel t x r ≤ 1 := by
  rw [← row_sum t x]
  exact single_le_sum (fun s _ => le_trans (le_of_lt (positivity_floor ht ht1 x s).1)
    (positivity_floor ht ht1 x s).2) (mem_univ r)

/-- Every distinct pair of rows retains exactly `1 - t` total variation. -/
theorem rowTV_distinct {t : ℝ} (ht1 : t ≤ 1) {x y : V} (hxy : x ≠ y) :
    rowTV (noisyIdentityKernel t) x y = 1 - t := by
  have hA : 0 ≤ 1 - t := by linarith
  have hpoint : ∀ r, |noisyIdentityKernel t x r - noisyIdentityKernel t y r| =
      (1 - t) * ((if r = x then 1 else 0) + (if r = y then 1 else 0)) := by
    intro r
    by_cases hx : r = x <;> by_cases hy : r = y
    all_goals simp_all [noisyIdentityKernel, abs_of_nonneg hA,
      abs_of_nonpos (sub_nonpos.mpr ht1), abs_neg]
  simp [rowTV, hpoint, mul_add, sum_add_distrib, ← mul_sum]

private theorem pair_matches_iff (F : V × V → V × V) (hinj : Function.Injective F)
    (x y r s : V) :
    ((F (r, s)).1 = (F (x, y)).1 ∧ (F (r, s)).2 = (F (x, y)).2) ↔
      (r = x ∧ s = y) := by
  constructor
  · intro h
    have hh := hinj (Prod.ext h.1 h.2)
    exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

private theorem coefficient_defect_eq (t : ℝ) (F : V × V → V × V)
    (hinj : Function.Injective F) (x y r s : V) :
    coefficientCovarianceDefect (noisyIdentityKernel t) F x y r s =
      ((1 - t) * (t / Fintype.card V)) *
        (coordinateMatches (F (x, y)).1 (F (x, y)).2 (F (r, s)).1 (F (r, s)).2 -
          coordinateMatches x y r s) := by
  have hp := pair_matches_iff F hinj x y r s
  by_cases h₁ : (F (r, s)).1 = (F (x, y)).1 <;>
    by_cases h₂ : (F (r, s)).2 = (F (x, y)).2 <;>
    by_cases h₃ : r = x <;> by_cases h₄ : s = y
  all_goals simp_all [coefficientCovarianceDefect, noisyIdentityKernel, coordinateMatches]
  all_goals ring

private theorem match_difference_bound (F : V × V → V × V)
    (hinj : Function.Injective F) (x y r s : V) :
    |coordinateMatches (F (x, y)).1 (F (x, y)).2 (F (r, s)).1 (F (r, s)).2 -
      coordinateMatches x y r s| ≤ 1 := by
  have hp := pair_matches_iff F hinj x y r s
  by_cases h₁ : (F (r, s)).1 = (F (x, y)).1 <;>
    by_cases h₂ : (F (r, s)).2 = (F (x, y)).2 <;>
    by_cases h₃ : r = x <;> by_cases h₄ : s = y
  all_goals simp_all [coordinateMatches]

/-- Injectivity alone gives this uniform coefficient bound. -/
theorem coefficient_defect_bound [Nonempty V] {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (F : V × V → V × V) (hinj : Function.Injective F) (x y r s : V) :
    |coefficientCovarianceDefect (noisyIdentityKernel t) F x y r s| ≤
      (1 - t) * (t / Fintype.card V) := by
  have hAB : 0 ≤ (1 - t) * (t / Fintype.card V) :=
    mul_nonneg (by linarith) (div_nonneg ht (le_of_lt card_pos))
  rw [coefficient_defect_eq t F hinj, abs_mul, abs_of_nonneg hAB]
  exact mul_le_of_le_one_right hAB (match_difference_bound F hinj x y r s)

private theorem absent_endpoint (F : V × V → V × V)
    (hsquare : ∀ p, F (F p) = p.swap)
    {a b : V} (hab : a ≠ b) :
    ((F (a, b)).1 ≠ a ∧ (F (a, b)).2 ≠ a) ∨
      ((F (a, b)).1 ≠ b ∧ (F (a, b)).2 ≠ b) := by
  have hroute := FiniteCovariantNoiseWall.mixed_output_not_routing F hsquare hab
  by_cases hua : (F (a, b)).1 = a <;> by_cases hva : (F (a, b)).2 = a
  · right
    exact ⟨fun h => hab (hua.symm.trans h), fun h => hab (hva.symm.trans h)⟩
  · right
    exact ⟨fun h => hab (hua.symm.trans h), fun h => hroute.1 (Prod.ext hua h)⟩
  · right
    exact ⟨fun h => hroute.2 (Prod.ext h hva), fun h => hab (hva.symm.trans h)⟩
  · exact Or.inl ⟨hua, hva⟩

/-- Under square-swap and diagonal fixing, the coefficient bound is attained. -/
theorem coefficient_bound_attained [Nontrivial V] {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (F : V × V → V × V) (hsquare : ∀ p, F (F p) = p.swap)
    (hdiag : ∀ x, F (x, x) = (x, x)) :
    ∃ x y r s, |coefficientCovarianceDefect (noisyIdentityKernel t) F x y r s| =
      (1 - t) * (t / Fintype.card V) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne V
  have hAB : 0 ≤ (1 - t) * (t / Fintype.card V) :=
    mul_nonneg (by linarith) (div_nonneg ht (le_of_lt card_pos))
  rcases absent_endpoint F hsquare hab with ha | hb
  · refine ⟨a, b, a, a, ?_⟩
    rw [coefficient_defect_eq t F (FiniteCovariantNoiseWall.square_swap_injective F hsquare)]
    simp [coordinateMatches, hdiag, Ne.symm ha.1, Ne.symm ha.2, hab, Ne.symm hab,
      abs_of_nonneg hAB]
  · refine ⟨a, b, b, b, ?_⟩
    rw [coefficient_defect_eq t F (FiniteCovariantNoiseWall.square_swap_injective F hsquare)]
    simp [coordinateMatches, hdiag, Ne.symm hb.1, Ne.symm hb.2, hab, Ne.symm hab,
      abs_of_nonneg hAB]

private theorem coordinateMatches_nonneg (x y r s : V) :
    0 ≤ coordinateMatches x y r s := by
  unfold coordinateMatches
  positivity

private theorem sum_coordinateMatches (x y : V) :
    ∑ p : V × V, coordinateMatches x y p.1 p.2 = 2 * Fintype.card V := by
  rw [Fintype.sum_prod_type]
  have hleft : (∑ r : V, ∑ _s : V, if r = x then (1 : ℝ) else 0) =
      Fintype.card V := by
    rw [sum_comm]
    simp
  have hright : (∑ _r : V, ∑ s : V, if s = y then (1 : ℝ) else 0) =
      Fintype.card V := by simp
  simp only [coordinateMatches, sum_add_distrib]
  rw [hleft, hright]
  ring

/-- The full output-pair TV defect obeys a dimension-free bound. -/
theorem channel_covariance_TV_bound [Nonempty V] {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (F : V × V → V × V)
    (hinj : Function.Injective F) (x y : V) :
    channelCovarianceTV (noisyIdentityKernel t) F x y ≤ 2 * t * (1 - t) := by
  let A : ℝ := (1 - t) * (t / Fintype.card V)
  have hA : 0 ≤ A := mul_nonneg (by linarith) (div_nonneg ht (le_of_lt card_pos))
  have hpoint : ∀ p : V × V,
      |coefficientCovarianceDefect (noisyIdentityKernel t) F x y p.1 p.2| ≤
        A * (coordinateMatches (F (x, y)).1 (F (x, y)).2 (F p).1 (F p).2 +
          coordinateMatches x y p.1 p.2) := by
    intro p
    rw [coefficient_defect_eq t F hinj, abs_mul, abs_of_nonneg hA]
    apply mul_le_mul_of_nonneg_left _ hA
    apply abs_le.mpr
    constructor <;> linarith [coordinateMatches_nonneg (F (x, y)).1 (F (x, y)).2
      (F p).1 (F p).2, coordinateMatches_nonneg x y p.1 p.2]
  have hbij : Function.Bijective F := ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hout : ∑ p : V × V,
      coordinateMatches (F (x, y)).1 (F (x, y)).2 (F p).1 (F p).2 =
        2 * Fintype.card V := by
    exact (hbij.sum_comp (fun p : V × V =>
      coordinateMatches (F (x, y)).1 (F (x, y)).2 p.1 p.2)).trans
        (sum_coordinateMatches (F (x, y)).1 (F (x, y)).2)
  have hsum := sum_le_sum (fun p (_ : p ∈ (univ : Finset (V × V))) => hpoint p)
  have htotal : ∑ p : V × V,
      A * (coordinateMatches (F (x, y)).1 (F (x, y)).2 (F p).1 (F p).2 +
        coordinateMatches x y p.1 p.2) = 4 * A * Fintype.card V := by
    rw [← mul_sum, sum_add_distrib, hout, sum_coordinateMatches]
    ring
  rw [htotal] at hsum
  have hn : (Fintype.card V : ℝ) ≠ 0 := ne_of_gt card_pos
  have hvalue : 4 * A * Fintype.card V = 4 * t * (1 - t) := by
    dsimp [A]
    field_simp
    <;> ring
  rw [hvalue] at hsum
  unfold channelCovarianceTV
  linarith

/-- Arbitrarily small covariance defects coexist with almost disjoint rows
when the positive floor is allowed to vanish. -/
theorem arbitrarily_small_covariance_defects [Nonempty V]
    (F : V × V → V × V) (hinj : Function.Injective F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      (∀ x r : V, 0 < noisyIdentityKernel t x r) ∧
      (∀ x : V, ∑ r, noisyIdentityKernel t x r = 1) ∧
      (∀ x y : V, x ≠ y → 1 - ε ≤ rowTV (noisyIdentityKernel t) x y) ∧
      (∀ x y r s, |coefficientCovarianceDefect (noisyIdentityKernel t) F x y r s| ≤ ε) ∧
      (∀ x y, channelCovarianceTV (noisyIdentityKernel t) F x y ≤ ε) := by
  let t : ℝ := min (ε / 4) (1 / 2)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have htε : t ≤ ε / 4 := min_le_left _ _
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hn : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hden : t / Fintype.card V ≤ t := (div_le_self (le_of_lt ht) hn)
  refine ⟨t, ht, ht1, ?_, row_sum t, ?_, ?_, ?_⟩
  · intro x r
    exact lt_of_lt_of_le (positivity_floor ht ht1 x r).1 (positivity_floor ht ht1 x r).2
  · intro x y hxy
    rw [rowTV_distinct (le_of_lt ht1) hxy]
    linarith
  · intro x y r s
    have hb := coefficient_defect_bound (le_of_lt ht) (le_of_lt ht1) F hinj x y r s
    have hprod : (1 - t) * (t / Fintype.card V) ≤ t := by
      nlinarith [div_nonneg (le_of_lt ht) (le_of_lt (card_pos (V := V)))]
    linarith
  · intro x y
    have hb := channel_covariance_TV_bound (le_of_lt ht) (le_of_lt ht1) F hinj x y
    nlinarith

/-- On a nontrivial carrier the approximation family has a genuinely distinct
pair of almost maximally distinguishable rows. -/
theorem nontrivial_near_distinguishable_family [Nontrivial V]
    (F : V × V → V × V) (hinj : Function.Injective F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, ∃ x y : V, 0 < t ∧ t < 1 ∧ x ≠ y ∧
      (∀ u r : V, 0 < noisyIdentityKernel t u r) ∧
      (∀ u : V, ∑ r, noisyIdentityKernel t u r = 1) ∧
      1 - ε ≤ rowTV (noisyIdentityKernel t) x y ∧
      (∀ u v r s, |coefficientCovarianceDefect (noisyIdentityKernel t) F u v r s| ≤ ε) ∧
      (∀ u v, channelCovarianceTV (noisyIdentityKernel t) F u v ≤ ε) := by
  obtain ⟨t, ht, ht1, hpos, hnorm, hrows, hcoeff, hchannel⟩ :=
    arbitrarily_small_covariance_defects F hinj hε
  obtain ⟨x, y, hxy⟩ := exists_pair_ne V
  exact ⟨t, x, y, ht, ht1, hxy, hpos, hnorm, hrows x y hxy, hcoeff, hchannel⟩

/-- The existing checked four-state square-swap gate realizes the approximation
family with a genuinely distinct pair of rows. -/
theorem four_state_near_distinguishable_family {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, ∃ x y : RawNetworkMedialWall.State, 0 < t ∧ t < 1 ∧ x ≠ y ∧
      (∀ u r : RawNetworkMedialWall.State, 0 < noisyIdentityKernel t u r) ∧
      (∀ u : RawNetworkMedialWall.State, ∑ r, noisyIdentityKernel t u r = 1) ∧
      1 - ε ≤ rowTV (noisyIdentityKernel t) x y ∧
      (∀ u v r s, |coefficientCovarianceDefect (noisyIdentityKernel t)
        RawNetworkMedialWall.gate u v r s| ≤ ε) ∧
      (∀ u v, channelCovarianceTV (noisyIdentityKernel t)
        RawNetworkMedialWall.gate u v ≤ ε) := by
  exact nontrivial_near_distinguishable_family RawNetworkMedialWall.gate
    (FiniteCovariantNoiseWall.square_swap_injective _ RawNetworkMedialWall.gate_square) hε

end
end IDT.QMClosure.CovariantNoiseApproximationControl
