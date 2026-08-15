import Mathlib.Tactic
import Proofs.QMClosure.SorkinGradeIffPairwiseGeneration
import Proofs.QMClosure.TwoSidedCylinderGluing

namespace IDT
namespace QMClosure

/-!
# Column embedding: every nonnegative pairwise weight couples with a point

`ConeGluingIsPositive` glues two cone weights (nonnegative generating
coefficients) via the product kernel. `DiagonalSelfGluing` glues any
nonnegative-valued pairwise weight with itself. This file adds a third
universal positive-coupling class with a two-line mechanism: carry the
whole left weight on a single right-hand alternative `t₀`,

  W U = mu {i | (i, t₀) ∈ U}.

The right cylinder marginal of this composite is the point mass
`mu univ · δ_{t₀}` and the left cylinder marginal is `mu` exactly;
pairwise generation is inherited (the data lives on one column, exactly
the `sliceWeightTop` shape of `TwoSidedCylinderGluing`), and nonnegativity
is inherited because every column projection of an event is a legitimate
event of the left context.

Two consequences. (1) Any nonnegative pairwise weight of total mass `M`
positively couples with the pure point mass `M · δ_{t₀}`. (2) Any
nonnegative pairwise weight of total mass ZERO positively couples with
the zero weight: the column marginal `M · δ_{t₀}` vanishes identically.
No cone condition and no context nonemptiness is needed.

What this does NOT give: couplings of two arbitrary distinct weights of
equal mass. The column embedding produces one degenerate right marginal
(a point mass, or zero); extending beyond it remains open.
-/

section
variable {α β : Type} [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β]

/-- Column projection of an event at `t₀`: the left indices whose point in
column `t₀` is present in `U`. -/
def sliceProj (t₀ : β) (U : Finset (α × β)) : Finset α :=
  (U.filter fun x => x.2 = t₀).image Prod.fst

/-- The horizontal slice weight is the base weight read on the column
projection. -/
theorem sliceWeightTop_eq (a : α → ℚ) (b : α → α → ℚ) (t₀ : β)
    (U : Finset (α × β)) :
    sliceWeightTop a b t₀ U
      = (∑ i ∈ sliceProj t₀ U, a i) + ∑ p ∈ (sliceProj t₀ U).offDiag, b p.1 p.2 := by
  classical
  set S : Finset (α × β) := U.filter fun x => x.2 = t₀ with hSdef
  have hmono : S.offDiag ⊆ U.offDiag := by
    intro p hp
    obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp hp
    exact Finset.mem_offDiag.mpr
      ⟨(Finset.mem_filter.mp h1).1, (Finset.mem_filter.mp h2).1, hne⟩
  have hcond : ∀ p ∈ U.offDiag,
      (p.1.2 = t₀ ∧ p.2.2 = t₀) ↔ p ∈ S.offDiag := by
    intro p hp
    obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp hp
    constructor
    · intro ⟨hd1, hd2⟩
      exact Finset.mem_offDiag.mpr
        ⟨Finset.mem_filter.mpr ⟨h1, hd1⟩, Finset.mem_filter.mpr ⟨h2, hd2⟩, hne⟩
    · intro hmem
      obtain ⟨k1, k2, -⟩ := Finset.mem_offDiag.mp hmem
      exact ⟨(Finset.mem_filter.mp k1).2, (Finset.mem_filter.mp k2).2⟩
  have e0 : (∑ p ∈ U.offDiag,
        if p.1.2 = t₀ ∧ p.2.2 = t₀ then b p.1.1 p.2.1 else 0)
      = ∑ p ∈ U.offDiag, (if p ∈ S.offDiag then b p.1.1 p.2.1 else 0) :=
    Finset.sum_congr rfl fun p hp => by
      by_cases h : p ∈ S.offDiag
      · rw [if_pos h, if_pos ((hcond p hp).mpr h)]
      · rw [if_neg h, if_neg fun hc => h ((hcond p hp).mp hc)]
  have e1 : (∑ p ∈ U.offDiag, (if p ∈ S.offDiag then b p.1.1 p.2.1 else 0))
      = ∑ p ∈ S.offDiag, b p.1.1 p.2.1 := by
    rw [← Finset.sum_subset hmono fun p _ hnp => if_neg hnp]
    exact Finset.sum_congr rfl fun p hp => if_pos hp
  have hcol : ∀ p ∈ S.offDiag, p.1 = (p.1.1, t₀) ∧ p.2 = (p.2.1, t₀) := by
    intro p hp
    obtain ⟨k1, k2, -⟩ := Finset.mem_offDiag.mp hp
    exact ⟨Prod.ext rfl (Finset.mem_filter.mp k1).2,
      Prod.ext rfl (Finset.mem_filter.mp k2).2⟩
  have himg : (S.offDiag).image (fun p : (α × β) × (α × β) => (p.1.1, p.2.1))
      = ((S.image Prod.fst).offDiag : Finset (α × α)) := by
    ext q
    simp only [Finset.mem_image, Finset.mem_offDiag]
    constructor
    · rintro ⟨p, ⟨k1, k2, kne⟩, hpq⟩
      obtain ⟨hq1, hq2⟩ := Prod.ext_iff.mp hpq
      dsimp only at hq1 hq2
      refine ⟨⟨p.1, k1, hq1⟩, ⟨p.2, k2, hq2⟩, ?_⟩
      intro hqq
      obtain ⟨hd1, hd2⟩ := hcol p (Finset.mem_offDiag.mpr ⟨k1, k2, kne⟩)
      exact kne (by rw [hd1, hd2, hq1, hq2, hqq])
    · rintro ⟨h1, h2, hne⟩
      obtain ⟨x, hx, hxq⟩ := h1
      obtain ⟨y, hy, hyq⟩ := h2
      refine ⟨(x, y), ⟨hx, hy, ?_⟩, ?_⟩
      · intro hcc
        exact hne (by rw [← hxq, ← hyq]; exact congrArg Prod.fst hcc)
      · simp only
        exact Prod.ext hxq hyq
  have hinj : ∀ p ∈ S.offDiag, ∀ p' ∈ S.offDiag,
      (fun p : (α × β) × (α × β) => (p.1.1, p.2.1)) p
        = (fun p : (α × β) × (α × β) => (p.1.1, p.2.1)) p' → p = p' := by
    intro p hp p' hp' hcc
    simp only at hcc
    obtain ⟨hf, hs⟩ := Prod.ext_iff.mp hcc
    obtain ⟨k1, k2, -⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨k1', k2', -⟩ := Finset.mem_offDiag.mp hp'
    have e2' : p.1 = p'.1 :=
      Prod.ext hf ((Finset.mem_filter.mp k1).2.trans
        (Finset.mem_filter.mp k1').2.symm)
    have e3' : p.2 = p'.2 :=
      Prod.ext hs ((Finset.mem_filter.mp k2).2.trans
        (Finset.mem_filter.mp k2').2.symm)
    exact Prod.ext e2' e3'
  have hsing : (∑ x ∈ U, if x.2 = t₀ then a x.1 else 0) = ∑ i ∈ sliceProj t₀ U, a i := by
    rw [← Finset.sum_filter]
    unfold sliceProj
    refine (Finset.sum_image ?_).symm
    intro x hx y hy hxy
    exact Prod.ext hxy
      ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
  unfold sliceWeightTop
  rw [hsing, e0, e1]
  unfold sliceProj
  rw [← hSdef, ← himg, Finset.sum_image hinj]

/-- Nonnegativity of the column embedding: the slice weight reads the base
weight on a legitimate event. -/
theorem sliceWeightTop_nonneg {mu : Finset α → ℚ}
    (hpos : ∀ S, 0 ≤ mu S) (a : α → ℚ) (b : α → α → ℚ)
    (hmu' : ∀ S : Finset α,
      mu S = (∑ i ∈ S, a i) + ∑ p ∈ S.offDiag, b p.1 p.2)
    (t₀ : β) (U : Finset (α × β)) :
    0 ≤ sliceWeightTop a b t₀ U := by
  rw [sliceWeightTop_eq, ← hmu' (sliceProj t₀ U)]
  exact hpos (sliceProj t₀ U)

/-- **Column embedding.** Every nonnegative-valued pairwise weight couples
positively with the point mass of its own total mass: the composite carries
the whole left weight on one right-hand alternative, is pairwise, and is
nonnegative on every event. -/
theorem column_embedding_gluing (mu : Finset α → ℚ)
    (hmu : TwoDecomposable mu) (hpos : ∀ S, 0 ≤ mu S) (t₀ : β) :
    ∃ W : Finset (α × β) → ℚ, TwoDecomposable W ∧
      (∀ S, W (S ×ˢ (Finset.univ : Finset β)) = mu S) ∧
      (∀ T, W ((Finset.univ : Finset α) ×ˢ T)
        = if t₀ ∈ T then mu (Finset.univ : Finset α) else 0) ∧
      (∀ U, 0 ≤ W U) := by
  obtain ⟨a, b, hmu'⟩ := hmu
  refine ⟨sliceWeightTop a b t₀, sliceWeightTop_two_decomposable a b t₀,
    ?_, ?_, ?_⟩
  · intro S
    rw [sliceTop_section S (Finset.univ : Finset β) t₀
      (Finset.mem_univ t₀) a b, ← hmu' S]
  · intro T
    by_cases hT : t₀ ∈ T
    · rw [sliceTop_section (Finset.univ : Finset α) T t₀ hT a b,
        ← hmu' (Finset.univ : Finset α), if_pos hT]
    · rw [sliceWeightTop_of_not_mem (Finset.univ : Finset α) T t₀ hT a b,
        if_neg hT]
  · exact sliceWeightTop_nonneg hpos a b hmu' t₀

/-- Specialization to zero total mass: a mass-zero nonnegative pairwise
weight positively couples with the zero weight on any nonempty right
context. -/
theorem column_embedding_gluing_zero_mass (mu : Finset α → ℚ)
    (hmu : TwoDecomposable mu) (hpos : ∀ S, 0 ≤ mu S)
    (hmass : mu (Finset.univ : Finset α) = 0) (t₀ : β) :
    ∃ W : Finset (α × β) → ℚ, TwoDecomposable W ∧
      (∀ S, W (S ×ˢ (Finset.univ : Finset β)) = mu S) ∧
      (∀ T, W ((Finset.univ : Finset α) ×ˢ T) = 0) ∧
      (∀ U, 0 ≤ W U) := by
  obtain ⟨W, hW, hR, hL, hpos'⟩ := column_embedding_gluing mu hmu hpos t₀
  refine ⟨W, hW, hR, ?_, hpos'⟩
  intro T
  rw [hL T]
  by_cases hT : t₀ ∈ T
  · rw [if_pos hT, hmass]
  · rw [if_neg hT]

end

inductive ColumnEmbeddingFinding where
  | everyNonnegativePairwiseWeightCouplesWithAPointMass
  | massZeroWeightsCoupleWithTheZeroWeight
  | theMechanismIsCarryingTheLeftWeightOnOneColumn
  deriving DecidableEq, Repr

def columnEmbeddingFindings : List ColumnEmbeddingFinding :=
  [ .everyNonnegativePairwiseWeightCouplesWithAPointMass,
    .massZeroWeightsCoupleWithTheZeroWeight,
    .theMechanismIsCarryingTheLeftWeightOnOneColumn ]

theorem column_embedding_records_three_findings :
    columnEmbeddingFindings.length = 3 := by
  rfl

inductive ColumnEmbeddingOpenObligation where
  | extendBeyondPointMassRightMarginalsToGeneralDistinctWeights
  | extractAndGeneralizeTheMechanismBehindLpFeasibleAdversarialPairs
  deriving DecidableEq, Repr

def columnEmbeddingOpenObligations : List ColumnEmbeddingOpenObligation :=
  [ .extendBeyondPointMassRightMarginalsToGeneralDistinctWeights,
    .extractAndGeneralizeTheMechanismBehindLpFeasibleAdversarialPairs ]

theorem column_embedding_keeps_two_open_obligations :
    columnEmbeddingOpenObligations.length = 2 := by
  rfl

def columnEmbeddingClaimBoundary : String :=
  "For set-function weights over ℚ on finite contexts: for every nonnegative-valued pairwise generated weight mu and every right-hand alternative t0, the slice weight sliceWeightTop a b t0 (the generating data carried on the column t0) is pairwise generated, nonnegative on every event (it equals mu on the column projection of the event), has left cylinder marginal mu exactly, and right cylinder marginal the point mass (mu univ) at t0. Hence mu positively couples with the pure point mass of its own total mass, and a mass-zero nonnegative pairwise weight positively couples with the zero weight. No nonemptiness, mass, or coefficient-cone condition is used. Not covered: couplings of two arbitrary distinct weights of equal mass (open; exact adversarial LP probes on Fin 3 x Fin 3 found all tested equal-mass pairs feasible, but no general construction is known beyond cone pairs, self-couplings, and point-mass/zero right marginals). Nothing here is uniqueness, nothing concerns entangled or interference-optimal couplings, and nothing derives complex amplitudes, a Hilbert carrier, purification, or the Born rule."

end QMClosure
end IDT
