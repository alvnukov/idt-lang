import Mathlib.Tactic
import Proofs.QMClosure.SorkinGradeIffPairwiseGeneration

namespace IDT
namespace QMClosure

/-!
# Diagonal self-gluing: positivity never obstructs self-coupling

`ConeGluingIsPositive` proved that two weights in the positive generation
cone (nonnegative singleton and kernel coefficients) always admit a
nonnegative pairwise composite. But the cone is a coefficient-level notion,
strictly smaller than the cone of nonnegative-valued weights: already on
`Fin 3` there are nonnegative pairwise weights whose every pairwise
decomposition carries negative kernel coefficients (mass-zero "partition"
rays such as the indicator of `x₁(1−x₂)(1−x₃)` plus the indicator of
`(1−x₁)x₂x₃`, whose third-order terms cancel). For those weights the
kernel-product coupling of the cone file says nothing.

This file closes one large diagonal of that gap unconditionally: EVERY
nonnegative-valued pairwise weight couples with ITSELF. The construction is
the diagonal (perfectly correlated) composite: evaluate the weight on the
diagonal projection of the event,

  W U = mu {i | (i, i) ∈ U}.

Both cylinder marginals of the diagonal composite reproduce `mu` on the nose
(the diagonal points of `S ×ˢ univ` are exactly the lifts of `S`), pairwise
generation is inherited because the singleton and kernel parts are simply
re-carried on the diagonal points, and nonnegativity is inherited because
every diagonal projection is a legitimate event of the base context. No
nonemptiness, mass, or cone-side condition is needed: even mass-zero weights
self-couple.

What this does NOT give: a coupling of two DISTINCT nonnegative weights.
Whether positive gluing is universally unobstructed for arbitrary pairs
remains open (recorded below); the diagonal composite only covers `nu = mu`.
-/

section
variable {α : Type} [DecidableEq α] [Fintype α]

/-- Diagonal projection of a product event: the indices whose diagonal
point is present in `U`. -/
def diagProj (U : Finset (α × α)) : Finset α :=
  (U.filter fun x => x.1 = x.2).image Prod.fst

/-- The diagonal composite: carry the singleton part of the decomposition on
the diagonal points, and the ordered-pair kernel part on ordered pairs of
diagonal points. -/
def diagonalWeight (a : α → ℚ) (b : α → α → ℚ) (U : Finset (α × α)) : ℚ :=
  (∑ x ∈ U, if x.1 = x.2 then a x.1 else 0)
    + ∑ p ∈ U.offDiag,
        if p.1.1 = p.1.2 ∧ p.2.1 = p.2.2 then b p.1.1 p.2.1 else 0

/-- The singleton part of the diagonal composite is the singleton part of
the base weight, read on the diagonal projection. -/
theorem diagonalWeight_single (a : α → ℚ) (U : Finset (α × α)) :
    (∑ x ∈ U, if x.1 = x.2 then a x.1 else 0) = ∑ i ∈ diagProj U, a i := by
  rw [← Finset.sum_filter]
  unfold diagProj
  refine (Finset.sum_image ?_).symm
  intro x hx y hy hxy
  exact Prod.ext hxy
    (((Finset.mem_filter.mp hx).2.symm.trans hxy).trans
      (Finset.mem_filter.mp hy).2)

/-- The kernel part of the diagonal composite is the kernel part of the
base weight, read on the diagonal projection. -/
theorem diagonalWeight_pair (b : α → α → ℚ) (U : Finset (α × α)) :
    (∑ p ∈ U.offDiag,
        if p.1.1 = p.1.2 ∧ p.2.1 = p.2.2 then b p.1.1 p.2.1 else 0)
      = ∑ p ∈ (diagProj U).offDiag, b p.1 p.2 := by
  classical
  set S : Finset (α × α) := U.filter fun x => x.1 = x.2 with hSdef
  have hmono : S.offDiag ⊆ U.offDiag := by
    intro p hp
    obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp hp
    exact Finset.mem_offDiag.mpr
      ⟨(Finset.mem_filter.mp h1).1, (Finset.mem_filter.mp h2).1, hne⟩
  have hcond : ∀ p ∈ U.offDiag,
      (p.1.1 = p.1.2 ∧ p.2.1 = p.2.2) ↔ p ∈ S.offDiag := by
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
        if p.1.1 = p.1.2 ∧ p.2.1 = p.2.2 then b p.1.1 p.2.1 else 0)
      = ∑ p ∈ U.offDiag, (if p ∈ S.offDiag then b p.1.1 p.2.1 else 0) :=
    Finset.sum_congr rfl fun p hp => by
      by_cases h : p ∈ S.offDiag
      · rw [if_pos h, if_pos ((hcond p hp).mpr h)]
      · rw [if_neg h, if_neg fun hc => h ((hcond p hp).mp hc)]
  have e1 : (∑ p ∈ U.offDiag, (if p ∈ S.offDiag then b p.1.1 p.2.1 else 0))
      = ∑ p ∈ S.offDiag, b p.1.1 p.2.1 := by
    rw [← Finset.sum_subset hmono fun p _ hnp => if_neg hnp]
    exact Finset.sum_congr rfl fun p hp => if_pos hp
  rw [e0, e1]
  have hdiag : ∀ p ∈ S.offDiag, p.1 = (p.1.1, p.1.1) ∧ p.2 = (p.2.1, p.2.1) := by
    intro p hp
    obtain ⟨k1, k2, -⟩ := Finset.mem_offDiag.mp hp
    exact ⟨Prod.ext rfl (Finset.mem_filter.mp k1).2.symm,
      Prod.ext rfl (Finset.mem_filter.mp k2).2.symm⟩
  have himg : (S.offDiag).image (fun p : (α × α) × (α × α) => (p.1.1, p.2.1))
      = ((S.image Prod.fst).offDiag : Finset (α × α)) := by
    ext q
    simp only [Finset.mem_image, Finset.mem_offDiag]
    constructor
    · rintro ⟨p, ⟨k1, k2, kne⟩, hpq⟩
      obtain ⟨hq1, hq2⟩ := Prod.ext_iff.mp hpq
      refine ⟨⟨p.1, k1, hq1⟩, ⟨p.2, k2, hq2⟩, ?_⟩
      intro hqq
      obtain ⟨hd1, hd2⟩ := hdiag p (Finset.mem_offDiag.mpr ⟨k1, k2, kne⟩)
      exact kne (by rw [hd1, hq1, hqq, ← hq2, ← hd2])
    · rintro ⟨h1, h2, hne⟩
      obtain ⟨x, hx, hxq⟩ := h1
      obtain ⟨y, hy, hyq⟩ := h2
      refine ⟨(x, y), ⟨hx, hy, ?_⟩, ?_⟩
      · intro hcc
        exact hne (by rw [← hxq, ← hyq]; exact congrArg Prod.fst hcc)
      · simp only
        exact Prod.ext hxq hyq
  have hinj : ∀ p ∈ S.offDiag, ∀ p' ∈ S.offDiag,
      (fun p : (α × α) × (α × α) => (p.1.1, p.2.1)) p
        = (fun p : (α × α) × (α × α) => (p.1.1, p.2.1)) p' → p = p' := by
    intro p hp p' hp' hcc
    simp only at hcc
    obtain ⟨hf, hs⟩ := Prod.ext_iff.mp hcc
    obtain ⟨k1, k2, -⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨k1', k2', -⟩ := Finset.mem_offDiag.mp hp'
    have e2' : p.1 = p'.1 :=
      Prod.ext hf ((Finset.mem_filter.mp k1).2.symm.trans
        (hf.trans (Finset.mem_filter.mp k1').2))
    have e3' : p.2 = p'.2 :=
      Prod.ext hs ((Finset.mem_filter.mp k2).2.symm.trans
        (hs.trans (Finset.mem_filter.mp k2').2))
    exact Prod.ext e2' e3'
  unfold diagProj
  rw [← hSdef, ← himg, Finset.sum_image hinj]

/-- The diagonal composite of a decomposition is the base weight read on
the diagonal projection. -/
theorem diagonalWeight_eq (a : α → ℚ) (b : α → α → ℚ) (U : Finset (α × α)) :
    diagonalWeight a b U
      = (∑ i ∈ diagProj U, a i) + ∑ p ∈ (diagProj U).offDiag, b p.1 p.2 := by
  unfold diagonalWeight
  rw [diagonalWeight_single, diagonalWeight_pair]

/-- The diagonal composite is pairwise generated by construction: its
singleton and kernel coefficients are the base ones, masked to the diagonal
points. -/
theorem diagonalWeight_two_decomposable (a : α → ℚ) (b : α → α → ℚ) :
    TwoDecomposable (diagonalWeight a b) :=
  ⟨fun x => if x.1 = x.2 then a x.1 else 0,
   fun x y => if x.1 = x.2 ∧ y.1 = y.2 then b x.1 y.1 else 0,
   fun _ => rfl⟩

/-- The diagonal projection of a right cylinder is the base event. -/
theorem diagProj_top (S : Finset α) :
    diagProj (S ×ˢ (Finset.univ : Finset α)) = S := by
  ext i
  unfold diagProj
  constructor
  · intro h
    rw [Finset.mem_image] at h
    obtain ⟨x, hx, hxq⟩ := h
    rw [Finset.mem_filter] at hx
    have hmem : x.1 ∈ S := (Finset.mem_product.mp hx.1).1
    rw [← hxq]
    exact hmem
  · intro hi
    refine Finset.mem_image.mpr ⟨(i, i), ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨hi, Finset.mem_univ i⟩, rfl⟩

/-- The diagonal projection of a left cylinder is the base event. -/
theorem diagProj_left (T : Finset α) :
    diagProj ((Finset.univ : Finset α) ×ˢ T) = T := by
  ext i
  unfold diagProj
  constructor
  · intro h
    rw [Finset.mem_image] at h
    obtain ⟨x, hx, hxq⟩ := h
    rw [Finset.mem_filter] at hx
    have hmem : x.2 ∈ T := (Finset.mem_product.mp hx.1).2
    have hxi : x.2 = i := by rw [← hx.2]; exact hxq
    rw [← hxi]
    exact hmem
  · intro hi
    refine Finset.mem_image.mpr ⟨(i, i), ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩

/-- The diagonal composite depends only on the weight, not on the chosen
pairwise decomposition of that weight. -/
theorem diagonalWeight_well_defined (a a' : α → ℚ) (b b' : α → α → ℚ)
    (h : ∀ S : Finset α,
      (∑ i ∈ S, a i) + ∑ p ∈ S.offDiag, b p.1 p.2
        = (∑ i ∈ S, a' i) + ∑ p ∈ S.offDiag, b' p.1 p.2) :
    diagonalWeight a b = diagonalWeight a' b' := by
  funext U
  rw [diagonalWeight_eq, diagonalWeight_eq, h (diagProj U)]

/-- **Diagonal self-gluing.** Every nonnegative-valued pairwise weight
admits a pairwise composite on the product context that is nonnegative on
every event and reproduces the weight in BOTH cylinder marginals. No
nonemptiness, mass, or cone-coefficient condition is required. -/
theorem diagonal_self_gluing_positive (mu : Finset α → ℚ)
    (hmu : TwoDecomposable mu) (hpos : ∀ S, 0 ≤ mu S) :
    ∃ W : Finset (α × α) → ℚ, TwoDecomposable W ∧
      (∀ S, W (S ×ˢ (Finset.univ : Finset α)) = mu S) ∧
      (∀ T, W ((Finset.univ : Finset α) ×ˢ T) = mu T) ∧
      (∀ U, 0 ≤ W U) := by
  obtain ⟨a, b, hmu'⟩ := hmu
  have hval : ∀ U : Finset (α × α), diagonalWeight a b U = mu (diagProj U) := by
    intro U
    rw [diagonalWeight_eq, hmu' (diagProj U)]
  refine ⟨diagonalWeight a b, diagonalWeight_two_decomposable a b, ?_, ?_, ?_⟩
  · intro S
    rw [hval, diagProj_top]
  · intro T
    rw [hval, diagProj_left]
  · intro U
    rw [hval]
    exact hpos (diagProj U)

end

inductive DiagonalSelfGluingFinding where
  | everyNonnegativePairwiseWeightCouplesWithItself
  | theCouplingIsTheDiagonalCorrelatedComposite
  | selfCouplingNeedsNoMassOrConeSideCondition
  deriving DecidableEq, Repr

def diagonalSelfGluingFindings : List DiagonalSelfGluingFinding :=
  [ .everyNonnegativePairwiseWeightCouplesWithItself,
    .theCouplingIsTheDiagonalCorrelatedComposite,
    .selfCouplingNeedsNoMassOrConeSideCondition ]

theorem diagonal_self_gluing_records_three_findings :
    diagonalSelfGluingFindings.length = 3 := by
  rfl

inductive DiagonalSelfGluingOpenObligation where
  | decideUniversalPositiveGluingForDistinctWeights
  | formalizeThatTheNonnegativeConeStrictlyExceedsTheGuardCone
  | classifyMassZeroRaysAndTheirCouplings
  | relateDiagonalCouplingsToSpectralQuantumCouplings
  deriving DecidableEq, Repr

def diagonalSelfGluingOpenObligations : List DiagonalSelfGluingOpenObligation :=
  [ .decideUniversalPositiveGluingForDistinctWeights,
    .formalizeThatTheNonnegativeConeStrictlyExceedsTheGuardCone,
    .classifyMassZeroRaysAndTheirCouplings,
    .relateDiagonalCouplingsToSpectralQuantumCouplings ]

theorem diagonal_self_gluing_keeps_four_open_obligations :
    diagonalSelfGluingOpenObligations.length = 4 := by
  rfl

def diagonalSelfGluingClaimBoundary : String :=
  "For set-function weights over ℚ on finite contexts: every nonnegative-valued pairwise generated weight mu admits a pairwise generated composite W on the product context, nonnegative on every event, whose right cylinder marginal S x univ and left cylinder marginal univ x T both equal mu exactly; the witness is the diagonal composite W U = mu {i | (i, i) in U}, the perfectly correlated coupling, and pairwise generation and nonnegativity are both inherited by construction, with no nonemptiness, mass, or coefficient-cone side condition (mass-zero weights included). The value W U depends only on mu, not on the chosen decomposition. This closes only the nu = mu diagonal: whether two DISTINCT nonnegative pairwise weights of equal total mass always admit such a composite remains open; exact rational LP evidence (two-phase simplex over the Farkas alternative, certificates verified by direct arithmetic) found no obstruction on the adversarial mass-zero sector tested, and the nonnegative cone is known by the same exact computation to strictly exceed the guard cone on Fin 3, so the kernel-product theorem does not cover the general case. Nothing here is uniqueness of a positive coupling, nothing concerns interference-optimal or entangled couplings, and nothing here derives complex amplitudes, a Hilbert carrier, purification, or the Born rule."

end QMClosure
end IDT
