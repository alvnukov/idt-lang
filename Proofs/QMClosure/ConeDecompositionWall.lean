import Mathlib.Tactic
import Proofs.QMClosure.SorkinGradeIffPairwiseGeneration
import Proofs.QMClosure.ConeGluingIsPositive

namespace IDT
namespace QMClosure

/-!
# A wall for the cone-plus-zero-mass decomposition route

A natural route to UNIVERSAL positive gluing of equal-mass pairs is the
decomposition conjecture: every nonnegative pairwise weight μ of
positive total mass M admits a positively generated C (singleton and
ordered-pair coefficients all nonnegative) with C ≤ μ pointwise and
C(univ) = M; then R = μ − C is nonnegative of mass zero, and the pair
(μ, ν) glues by kernel-coupling the cone parts and mass-zero-coupling
the residues, then summing.

This file REFUTES that conjecture on a 4-point context with an explicit
machine-checked witness and a hand-readable certificate:

  μ* = δ₃ + (x₀x₁ + x₀x₂ + x₁x₂) − (x₀x₃ + x₁x₃ + x₂x₃),

with values {3} = 1, {01} = {02} = {12} = 1, {012} = 3, every proper
triple containing 3 equal to 0, and μ*(univ) = 1. The certificate: the
three zero-valued triples {0,1,3}, {0,2,3}, {1,2,3} cover every point
and every ordered pair, so any data-nonneg C ≤ μ* pointwise vanishes on
all three triples, hence has all coefficients zero, hence mass 0 ≠ 1.

Scope, stated honestly: this kills the cone+zero ROUTE to universal
gluing beyond 3-point contexts (on Fin 3 the conjecture holds: pairs
are the maximal proper subsets and Σ_{i<j} μ{ij} = 2Σa + Σq ≥ μ(univ)
always certifies). It does NOT refute universal gluing itself: the
gluing feasibility of μ* with equal-mass partners is a separate
question (probed by exact LP in the session record).
-/

/-- Sum over the off-diagonal as a double sum with an `if`. -/
theorem offDiag_sum_eq {α : Type} [DecidableEq α] (s : Finset α)
    (f : α → α → ℚ) :
    ∑ p ∈ s.offDiag, f p.1 p.2
      = ∑ i ∈ s, ∑ j ∈ s, if i ≠ j then f i j else 0 := by
  classical
  have hmono : s.offDiag ⊆ s ×ˢ s := by
    intro p hp
    obtain ⟨h1, h2, -⟩ := Finset.mem_offDiag.mp hp
    exact Finset.mem_product.mpr ⟨h1, h2⟩
  have hcompl : ∀ p ∈ s ×ˢ s, p ∉ s.offDiag →
      (if p.1 ≠ p.2 then f p.1 p.2 else 0) = 0 := by
    intro p hp hnp
    rw [if_neg]
    intro hne
    exact hnp (Finset.mem_offDiag.mpr
      ⟨(Finset.mem_product.mp hp).1, (Finset.mem_product.mp hp).2, hne⟩)
  have hL : ∑ p ∈ s.offDiag, f p.1 p.2
      = ∑ p ∈ s.offDiag, (if p.1 ≠ p.2 then f p.1 p.2 else 0) :=
    Finset.sum_congr rfl fun p hp =>
      (if_pos (Finset.mem_offDiag.mp hp).2.2).symm
  have hR : ∑ p ∈ s.offDiag, (if p.1 ≠ p.2 then f p.1 p.2 else 0)
      = ∑ p ∈ s ×ˢ s, (if p.1 ≠ p.2 then f p.1 p.2 else 0) :=
    Finset.sum_subset hmono hcompl
  rw [hL, hR, Finset.sum_product]

/-- The counterexample's singleton data: a point mass at `3`. -/
def muStarA : Fin 4 → ℚ := fun i => if i = 3 then 1 else 0

/-- The counterexample's ordered-pair data: the positive triangle on
`{0,1,2}` and the negative star from `3`, each carried on the
ascending order only. -/
def muStarB : Fin 4 → Fin 4 → ℚ := fun i j =>
  match i, j with
  | 0, 1 | 0, 2 | 1, 2 => 1
  | 0, 3 | 1, 3 | 2, 3 => -1
  | _, _ => 0

/-- The counterexample weight. -/
def muStar (S : Finset (Fin 4)) : ℚ :=
  (∑ i ∈ S, muStarA i) + ∑ p ∈ S.offDiag, muStarB p.1 p.2

theorem muStar_two_decomposable : TwoDecomposable muStar :=
  ⟨muStarA, muStarB, fun _ => rfl⟩

theorem muStar_mass : muStar (Finset.univ : Finset (Fin 4)) = 1 := by
  have hu : (Finset.univ : Finset (Fin 4))
      = ({0, 1, 2, 3} : Finset (Fin 4)) := by
    ext x
    fin_cases x <;> simp
  rw [muStar, hu, offDiag_sum_eq]
  simp [muStarA, muStarB, Finset.sum_insert, Finset.sum_singleton]

/-- The witness is nonnegative on every event, by exhaustive evaluation
of all 16 events (values lie in {0, 1, 3}). -/
theorem muStar_nonneg (S : Finset (Fin 4)) : 0 ≤ muStar S := by
  classical
  have hS : S ∈ ({∅, {0}, {1}, {2}, {3}, {0, 1}, {0, 2}, {0, 3}, {1, 2},
    {1, 3}, {2, 3}, {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3},
    ({0, 1, 2, 3} : Finset (Fin 4))} : Finset (Finset (Fin 4))) := by
    have h1 : S ∈ (Finset.univ : Finset (Fin 4)).powerset :=
      Finset.mem_powerset.mpr (Finset.subset_univ S)
    have h2 : (Finset.univ : Finset (Fin 4)).powerset
        = ({∅, {0}, {1}, {2}, {3}, {0, 1}, {0, 2}, {0, 3}, {1, 2},
          {1, 3}, {2, 3}, {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3},
          ({0, 1, 2, 3} : Finset (Fin 4))} : Finset (Finset (Fin 4))) := by
      decide
    rw [h2] at h1
    exact h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [muStar, offDiag_sum_eq]
    simp [muStarA, muStarB, Finset.sum_insert, Finset.sum_singleton]
  all_goals norm_num

/-- The three zero-valued triples that cover every point and every
ordered pair. -/
def wallTriples : List (Finset (Fin 4)) :=
  [{0, 1, 3}, {0, 2, 3}, {1, 2, 3}]

theorem muStar_triple_zero_1 : muStar ({0, 1, 3} : Finset (Fin 4)) = 0 := by
  rw [muStar, offDiag_sum_eq]
  simp [muStarA, muStarB, Finset.sum_insert, Finset.sum_singleton]

theorem muStar_triple_zero_2 : muStar ({0, 2, 3} : Finset (Fin 4)) = 0 := by
  rw [muStar, offDiag_sum_eq]
  simp [muStarA, muStarB, Finset.sum_insert, Finset.sum_singleton]

theorem muStar_triple_zero_3 : muStar ({1, 2, 3} : Finset (Fin 4)) = 0 := by
  rw [muStar, offDiag_sum_eq]
  simp [muStarA, muStarB, Finset.sum_insert, Finset.sum_singleton]

theorem muStar_triple_zero (T : Finset (Fin 4)) (hT : T ∈ wallTriples) :
    muStar T = 0 := by
  have h1 : T = {0, 1, 3} ∨ T = {0, 2, 3} ∨ T = {1, 2, 3} := by
    simpa [wallTriples] using hT
  rcases h1 with rfl | rfl | rfl
  · exact muStar_triple_zero_1
  · exact muStar_triple_zero_2
  · exact muStar_triple_zero_3

/-- Every point of the context lies in some wall triple. -/
theorem wallTriples_cover_points :
    ∀ i : Fin 4, ∃ T ∈ wallTriples, i ∈ T := by decide

/-- Every ordered pair of distinct points lies in some wall triple's
off-diagonal. -/
theorem wallTriples_cover_pairs :
    ∀ i j : Fin 4, i ≠ j → ∃ T ∈ wallTriples, (i, j) ∈ T.offDiag := by
  decide

/-- **The wall.** No positively generated weight sits below `muStar`
pointwise with the same total mass: the three zero triples force every
nonnegative coefficient to vanish, so the cone part has mass 0 while
`muStar` has mass 1. -/
theorem no_cone_below_muStar :
    ¬ ∃ (ca : Fin 4 → ℚ) (cb : Fin 4 → Fin 4 → ℚ),
      (∀ i, 0 ≤ ca i) ∧ (∀ i j, 0 ≤ cb i j) ∧
      (∀ S : Finset (Fin 4),
        (∑ i ∈ S, ca i) + ∑ p ∈ S.offDiag, cb p.1 p.2 ≤ muStar S) ∧
      ((∑ i ∈ (Finset.univ : Finset (Fin 4)), ca i)
        + ∑ p ∈ (Finset.univ : Finset (Fin 4)).offDiag, cb p.1 p.2 = 1) := by
  rintro ⟨ca, cb, hca, hcb, hbelow, hmass⟩
  -- each wall triple forces the cone data sum to be exactly zero
  have hzero : ∀ T ∈ wallTriples,
      (∑ i ∈ T, ca i) + ∑ p ∈ T.offDiag, cb p.1 p.2 = 0 := by
    intro T hT
    have h1 := hbelow T
    rw [muStar_triple_zero T hT] at h1
    have h2 : 0 ≤ (∑ i ∈ T, ca i) + ∑ p ∈ T.offDiag, cb p.1 p.2 :=
      add_nonneg (Finset.sum_nonneg fun i _ => hca i)
        (Finset.sum_nonneg fun p _ => hcb p.1 p.2)
    linarith
  -- hence every singleton coefficient vanishes
  have hcaz : ∀ i : Fin 4, ca i = 0 := by
    intro i
    obtain ⟨T, hT, hiT⟩ := wallTriples_cover_points i
    have hs0 : ∑ i ∈ T, ca i = 0 := by
      have := hzero T hT
      have hnn : 0 ≤ ∑ i ∈ T, ca i := Finset.sum_nonneg fun i _ => hca i
      have hnn2 : 0 ≤ ∑ p ∈ T.offDiag, cb p.1 p.2 :=
        Finset.sum_nonneg fun p _ => hcb p.1 p.2
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => hca i)).mp hs0 i hiT
  -- hence every off-diagonal ordered-pair coefficient vanishes (the
  -- diagonal entries never enter any event or the mass equation)
  have hcbz : ∀ i j : Fin 4, i ≠ j → cb i j = 0 := by
    intro i j hij
    obtain ⟨T, hT, hpT⟩ := wallTriples_cover_pairs i j hij
    have hs0 : ∑ p ∈ T.offDiag, cb p.1 p.2 = 0 := by
      have := hzero T hT
      have hnn : 0 ≤ ∑ i ∈ T, ca i := Finset.sum_nonneg fun i _ => hca i
      have hnn2 : 0 ≤ ∑ p ∈ T.offDiag, cb p.1 p.2 :=
        Finset.sum_nonneg fun p _ => hcb p.1 p.2
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun p _ => hcb p.1 p.2)).mp hs0 (i, j) hpT
  -- the cone part is identically zero, so its total mass is zero
  have e1 : (∑ i ∈ (Finset.univ : Finset (Fin 4)), ca i) = 0 :=
    Finset.sum_eq_zero fun i _ => hcaz i
  have e2 : (∑ p ∈ (Finset.univ : Finset (Fin 4)).offDiag, cb p.1 p.2)
      = 0 :=
    Finset.sum_eq_zero fun p hp =>
      hcbz p.1 p.2 (Finset.mem_offDiag.mp hp).2.2
  rw [e1, e2] at hmass
  norm_num at hmass

/-- The refutation, packaged: a legitimate nonnegative pairwise weight
of positive mass for which no positively generated part can carry the
full mass below it. -/
theorem cone_decomposition_refuted_on_fin4 :
    ∃ mu : Finset (Fin 4) → ℚ,
      TwoDecomposable mu ∧ (∀ S, 0 ≤ mu S) ∧
      0 < mu (Finset.univ : Finset (Fin 4)) ∧
      ¬ ∃ (ca : Fin 4 → ℚ) (cb : Fin 4 → Fin 4 → ℚ),
        (∀ i, 0 ≤ ca i) ∧ (∀ i j, 0 ≤ cb i j) ∧
        (∀ S : Finset (Fin 4),
          (∑ i ∈ S, ca i) + ∑ p ∈ S.offDiag, cb p.1 p.2 ≤ mu S) ∧
        ((∑ i ∈ (Finset.univ : Finset (Fin 4)), ca i)
          + ∑ p ∈ (Finset.univ : Finset (Fin 4)).offDiag, cb p.1 p.2
          = mu (Finset.univ : Finset (Fin 4))) := by
  refine ⟨muStar, muStar_two_decomposable, muStar_nonneg,
    by rw [muStar_mass]; norm_num, ?_⟩
  rintro ⟨ca, cb, h1, h2, h3, h4⟩
  rw [muStar_mass] at h4
  exact no_cone_below_muStar ⟨ca, cb, h1, h2, h3, h4⟩

end QMClosure
end IDT
