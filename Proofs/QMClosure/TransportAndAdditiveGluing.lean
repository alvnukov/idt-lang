import Mathlib.Tactic
import Proofs.QMClosure.SorkinGradeIffPairwiseGeneration
import Proofs.QMClosure.TwoSidedCylinderGluing
import Proofs.QMClosure.ColumnEmbeddingGluing
import Proofs.QMClosure.ConeGluingIsPositive

namespace IDT
namespace QMClosure

/-!
# Transport and additive gluing: two new universal positive-coupling classes

This file adds two constructions that substantially enlarge the class of
pairs known to admit a positive pairwise coupling.

**Transport gluing.** For any map `σ : α → β` (no injectivity, no context
condition) and any nonnegative-valued pairwise weight `mu`, the weight

  W U = mu { i | (i, σ i) ∈ U }

carried on the graph of `σ` is pairwise generated, nonnegative on every
event, has left cylinder marginal `mu` exactly, and right cylinder marginal
the transport `σ∗ mu := T ↦ mu { i | σ i ∈ T }`. Special cases: `σ = id` is
the diagonal self-gluing of `DiagonalSelfGluing`; a constant `σ` is the
column embedding of `ColumnEmbeddingGluing` (right marginal = point mass of
the total mass, or the zero weight for mass-zero `mu`). Non-injective `σ`
glues `mu` with genuinely new right marginals: fiber-merged transports.

**Additive gluing.** If the left weight is additive with nonnegative
coefficients (`mu S = ∑ i ∈ S, a i`) and the right weight `nu` is any
nonnegative-valued pairwise weight of the same positive total mass, the
row-copy mixture

  W U = ∑ i, (a i / M) * nu { t | (i, t) ∈ U }

(each row of the product carries an independent scaled copy of `nu`) is
pairwise generated, nonnegative, and has cylinder marginals `mu` and `nu`.
Together with the sum lemma below, any weight that decomposes as an
additive part plus a mass-zero nonnegative pairwise residue couples with
every equal-mass nonnegative pairwise weight. The exact rational LP probes
on `Fin 3 × Fin 3` (Farkas feasibility plus verified witnesses) closed
every probed adversarial pair by these mechanisms: the XOR ray `f` with its
relabel `f2`, `H12` with `H13`, `P12` with `P13` (transports), `2f + E1`
with `P12` (additive part `E1` plus mass-zero residue `2f`).

**Sum composition.** Positive couplings compose by sums: if `W₁` couples
`(mu₁, nu₁)` and `W₂` couples `(mu₂, nu₂)`, all values nonnegative, then
`W₁ + W₂` couples `(mu₁ + mu₂, nu₁ + nu₂)`.

What remains open: pairs where both weights are non-additive and related
neither by transport nor by an additive-plus-zero-mass decomposition, for
example two distinct mass-zero XOR-type weights that are not relabels of
each other.
-/

section
variable {α β : Type} [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β]

/-! ## Transport gluing -/

/-- Preimage of a right-hand event under `σ`. -/
def transportPreimage (σ : α → β) (T : Finset β) : Finset α :=
  (Finset.univ : Finset α).filter fun i => σ i ∈ T

/-- Projection of a product event onto the graph of `σ`. -/
def transportProj (σ : α → β) (U : Finset (α × β)) : Finset α :=
  (U.filter fun x => x.2 = σ x.1).image Prod.fst

/-- Generating data carried on the graph of `σ`. -/
def transportWeight (a : α → ℚ) (b : α → α → ℚ) (σ : α → β)
    (U : Finset (α × β)) : ℚ :=
  (∑ x ∈ U, if x.2 = σ x.1 then a x.1 else 0)
    + ∑ p ∈ U.offDiag, if p.1.2 = σ p.1.1 ∧ p.2.2 = σ p.2.1 then b p.1.1 p.2.1 else 0

theorem transportWeight_two_decomposable (a : α → ℚ) (b : α → α → ℚ)
    (σ : α → β) :
    TwoDecomposable (transportWeight a b σ) :=
  ⟨fun x => if x.2 = σ x.1 then a x.1 else 0,
    fun x y => if x.2 = σ x.1 ∧ y.2 = σ y.1 then b x.1 y.1 else 0,
    fun _ => rfl⟩

/-- The transport weight reads the base weight on the graph projection. -/
theorem transportWeight_eq (a : α → ℚ) (b : α → α → ℚ) (σ : α → β)
    (U : Finset (α × β)) :
    transportWeight a b σ U
      = (∑ i ∈ transportProj σ U, a i) + ∑ p ∈ (transportProj σ U).offDiag, b p.1 p.2 := by
  classical
  set S : Finset (α × β) := U.filter fun x => x.2 = σ x.1 with hSdef
  have hmono : S.offDiag ⊆ U.offDiag := by
    intro p hp
    obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp hp
    exact Finset.mem_offDiag.mpr
      ⟨(Finset.mem_filter.mp h1).1, (Finset.mem_filter.mp h2).1, hne⟩
  have hcond : ∀ p ∈ U.offDiag,
      (p.1.2 = σ p.1.1 ∧ p.2.2 = σ p.2.1) ↔ p ∈ S.offDiag := by
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
        if p.1.2 = σ p.1.1 ∧ p.2.2 = σ p.2.1 then b p.1.1 p.2.1 else 0)
      = ∑ p ∈ U.offDiag, (if p ∈ S.offDiag then b p.1.1 p.2.1 else 0) :=
    Finset.sum_congr rfl fun p hp => by
      by_cases h : p ∈ S.offDiag
      · rw [if_pos h, if_pos ((hcond p hp).mpr h)]
      · rw [if_neg h, if_neg fun hc => h ((hcond p hp).mp hc)]
  have e1 : (∑ p ∈ U.offDiag, (if p ∈ S.offDiag then b p.1.1 p.2.1 else 0))
      = ∑ p ∈ S.offDiag, b p.1.1 p.2.1 := by
    rw [← Finset.sum_subset hmono fun p _ hnp => if_neg hnp]
    exact Finset.sum_congr rfl fun p hp => if_pos hp
  have hcol : ∀ p ∈ S.offDiag, p.1 = (p.1.1, σ p.1.1) ∧ p.2 = (p.2.1, σ p.2.1) := by
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
    dsimp only at hf hs
    obtain ⟨k1, k2, -⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨k1', k2', -⟩ := Finset.mem_offDiag.mp hp'
    have e2' : p.1 = p'.1 := by
      apply Prod.ext hf
      have g1 := (Finset.mem_filter.mp k1).2
      have g1' := (Finset.mem_filter.mp k1').2
      rw [g1, hf, ← g1']
    have e3' : p.2 = p'.2 := by
      apply Prod.ext hs
      have g2 := (Finset.mem_filter.mp k2).2
      have g2' := (Finset.mem_filter.mp k2').2
      rw [g2, hs, ← g2']
    exact Prod.ext e2' e3'
  have hsing : (∑ x ∈ U, if x.2 = σ x.1 then a x.1 else 0)
      = ∑ i ∈ transportProj σ U, a i := by
    rw [← Finset.sum_filter]
    unfold transportProj
    refine (Finset.sum_image ?_).symm
    intro x hx y hy hxy
    have g1 := (Finset.mem_filter.mp hx).2
    have g2 := (Finset.mem_filter.mp hy).2
    have hxy' : x.1 = y.1 := hxy
    apply Prod.ext hxy'
    rw [g1, hxy', ← g2]
  unfold transportWeight
  rw [hsing, e0, e1]
  unfold transportProj
  rw [← hSdef, ← himg, Finset.sum_image hinj]

/-- Nonnegativity of the transport weight: it reads the base weight on a
legitimate event. -/
theorem transportWeight_nonneg {mu : Finset α → ℚ}
    (hpos : ∀ S, 0 ≤ mu S) (a : α → ℚ) (b : α → α → ℚ)
    (hmu' : ∀ S : Finset α,
      mu S = (∑ i ∈ S, a i) + ∑ p ∈ S.offDiag, b p.1 p.2)
    (σ : α → β) (U : Finset (α × β)) :
    0 ≤ transportWeight a b σ U := by
  rw [transportWeight_eq, ← hmu' (transportProj σ U)]
  exact hpos (transportProj σ U)

theorem transportProj_product_left (σ : α → β) (S : Finset α) :
    transportProj σ (S ×ˢ (Finset.univ : Finset β)) = S := by
  ext i
  constructor
  · intro hi
    obtain ⟨x, hx, hxi⟩ := Finset.mem_image.mp hi
    obtain ⟨hmem, -⟩ := Finset.mem_filter.mp hx
    rw [Finset.mem_product] at hmem
    exact hxi ▸ hmem.1
  · intro hi
    refine Finset.mem_image.mpr ⟨(i, σ i), ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hi, Finset.mem_univ _⟩, rfl⟩

theorem transportProj_product_right (σ : α → β) (T : Finset β) :
    transportProj σ ((Finset.univ : Finset α) ×ˢ T) = transportPreimage σ T := by
  ext i
  constructor
  · intro hi
    obtain ⟨x, hx, hxi⟩ := Finset.mem_image.mp hi
    obtain ⟨hmem, hgate⟩ := Finset.mem_filter.mp hx
    rw [Finset.mem_product] at hmem
    rw [hxi] at hgate
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
    exact hgate ▸ hmem.2
  · intro hi
    obtain ⟨-, hT⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_image.mpr ⟨(i, σ i), ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, hT⟩, rfl⟩

/-- **Transport gluing.** Every nonnegative-valued pairwise weight couples
positively with every transport of itself: for any map `σ : α → β` (no
injectivity required), the graph-carried weight is pairwise, nonnegative on
every event, has left cylinder marginal `mu` exactly, and right cylinder
marginal `T ↦ mu {i | σ i ∈ T}`. -/
theorem transport_gluing (mu : Finset α → ℚ)
    (hmu : TwoDecomposable mu) (hpos : ∀ S, 0 ≤ mu S) (σ : α → β) :
    ∃ W : Finset (α × β) → ℚ, TwoDecomposable W ∧
      (∀ S, W (S ×ˢ (Finset.univ : Finset β)) = mu S) ∧
      (∀ T, W ((Finset.univ : Finset α) ×ˢ T)
        = mu (transportPreimage σ T)) ∧
      (∀ U, 0 ≤ W U) := by
  obtain ⟨a, b, hmu'⟩ := hmu
  refine ⟨transportWeight a b σ, transportWeight_two_decomposable a b σ,
    ?_, ?_, ?_⟩
  · intro S
    rw [transportWeight_eq, transportProj_product_left, ← hmu' S]
  · intro T
    rw [transportWeight_eq, transportProj_product_right,
      ← hmu' (transportPreimage σ T)]
  · exact transportWeight_nonneg hpos a b hmu' σ

/-! ## Additive gluing: the row-copy mixture -/

/-- Row projection of a product event: the right indices present in row
`i`. -/
def rowProj (i : α) (U : Finset (α × β)) : Finset β :=
  (U.filter fun x => x.1 = i).image Prod.snd

/-- The row-copy mixture: row `i` carries a scaled copy `a i / M` of the
right weight, and rows do not interact (all cross-row pairs vanish). -/
def rowMixWeight (a : α → ℚ) (c : β → ℚ) (d : β → β → ℚ) (M : ℚ)
    (U : Finset (α × β)) : ℚ :=
  (∑ x ∈ U, a x.1 * c x.2 / M)
    + ∑ p ∈ U.offDiag, if p.1.1 = p.2.1 then a p.1.1 * d p.1.2 p.2.2 / M else 0

theorem rowMixWeight_two_decomposable (a : α → ℚ) (c : β → ℚ)
    (d : β → β → ℚ) (M : ℚ) :
    TwoDecomposable (rowMixWeight a c d M) :=
  ⟨fun x => a x.1 * c x.2 / M,
    fun x y => if x.1 = y.1 then a x.1 * d x.2 y.2 / M else 0,
    fun _ => rfl⟩

theorem rowProj_product_top (i : α) (S : Finset α) :
    rowProj i (S ×ˢ (Finset.univ : Finset β))
      = if i ∈ S then (Finset.univ : Finset β) else ∅ := by
  ext t
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    constructor
    · intro _
      exact Finset.mem_univ t
    · intro _
      exact Finset.mem_image.mpr ⟨(i, t),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, Finset.mem_univ t⟩, rfl⟩,
        rfl⟩
  · rw [if_neg hi]
    constructor
    · intro h
      obtain ⟨x, hx, -⟩ := Finset.mem_image.mp h
      obtain ⟨hmem, hgate⟩ := Finset.mem_filter.mp hx
      rw [Finset.mem_product] at hmem
      exact absurd (hgate ▸ hmem.1) hi
    · intro h
      simp at h

theorem rowProj_top_product (i : α) (T : Finset β) :
    rowProj i ((Finset.univ : Finset α) ×ˢ T) = T := by
  ext t
  constructor
  · intro hi
    obtain ⟨x, hx, hxt⟩ := Finset.mem_image.mp hi
    obtain ⟨hmem, -⟩ := Finset.mem_filter.mp hx
    rw [Finset.mem_product] at hmem
    exact hxt ▸ hmem.2
  · intro ht
    exact Finset.mem_image.mpr ⟨(i, t),
      Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, ht⟩, rfl⟩, rfl⟩

/-- Fiberwise representation of the row-copy mixture: it is the sum over
rows of `(a i / M)` times the right weight read on the row section. -/
theorem rowMixWeight_eq (a : α → ℚ) (c : β → ℚ) (d : β → β → ℚ) (M : ℚ)
    (U : Finset (α × β)) :
    rowMixWeight a c d M U
      = ∑ i ∈ (Finset.univ : Finset α), (a i / M) *
          ((∑ t ∈ rowProj i U, c t) + ∑ p ∈ (rowProj i U).offDiag, d p.1 p.2) := by
  classical
  -- singles: partition by row
  have hsing : (∑ x ∈ U, a x.1 * c x.2 / M)
      = ∑ i ∈ (Finset.univ : Finset α),
          (a i / M) * ∑ t ∈ rowProj i U, c t := by
    have hmaps : ∀ x ∈ U, Prod.fst x ∈ (Finset.univ : Finset α) :=
      fun _ _ => Finset.mem_univ _
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => a x.1 * c x.2 / M)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hterm : ∀ x ∈ U.filter fun x => x.1 = i,
        a x.1 * c x.2 / M = (a i / M) * c x.2 := by
      intro x hx
      have hxi : x.1 = i := (Finset.mem_filter.mp hx).2
      rw [hxi]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have h2 : ∑ x ∈ U.filter fun x => x.1 = i, c x.2
        = ∑ t ∈ rowProj i U, c t := by
      unfold rowProj
      refine (Finset.sum_image ?_).symm
      intro x hx y hy hxy
      have hfst : x.1 = y.1 :=
        (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
      have hsnd : x.2 = y.2 := hxy
      exact Prod.ext hfst hsnd
    rw [h2]
  -- pairs: split by row equality, transfer to row sections
  have hpair : (∑ p ∈ U.offDiag,
        if p.1.1 = p.2.1 then a p.1.1 * d p.1.2 p.2.2 / M else 0)
      = ∑ i ∈ (Finset.univ : Finset α),
          (a i / M) * ∑ p ∈ (rowProj i U).offDiag, d p.1 p.2 := by
    have hpt : ∀ p ∈ U.offDiag,
        (if p.1.1 = p.2.1 then a p.1.1 * d p.1.2 p.2.2 / M else 0)
          = ∑ i ∈ (Finset.univ : Finset α),
              if p.1.1 = i ∧ p.2.1 = i then (a i / M) * d p.1.2 p.2.2 else 0 := by
      intro p _
      by_cases hp : p.1.1 = p.2.1
      · rw [if_pos hp,
          Finset.sum_eq_single p.1.1
            (fun j _ hj => if_neg fun hc => hj hc.1.symm)
            (fun hj => absurd (Finset.mem_univ p.1.1) hj),
          if_pos ⟨rfl, hp.symm⟩]
        ring
      · rw [if_neg hp,
          Finset.sum_eq_zero fun i _ =>
            if_neg fun hc => hp (hc.1.trans hc.2.symm)]
    rw [Finset.sum_congr rfl hpt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    set F : Finset (α × β) := U.filter fun x => x.1 = i with hF
    have hfilter : (U.offDiag).filter fun p => p.1.1 = i ∧ p.2.1 = i
        = F.offDiag := by
      ext p
      constructor
      · intro hp
        obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
        obtain ⟨k1, k2, hne⟩ := Finset.mem_offDiag.mp h1
        exact Finset.mem_offDiag.mpr
          ⟨Finset.mem_filter.mpr ⟨k1, h2.1⟩,
            Finset.mem_filter.mpr ⟨k2, h2.2⟩, hne⟩
      · intro hp
        obtain ⟨k1, k2, hne⟩ := Finset.mem_offDiag.mp hp
        refine Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr
          ⟨(Finset.mem_filter.mp k1).1, (Finset.mem_filter.mp k2).1, hne⟩, ?_⟩
        exact ⟨(Finset.mem_filter.mp k1).2, (Finset.mem_filter.mp k2).2⟩
    have hrow : (∑ p ∈ U.offDiag,
        if p.1.1 = i ∧ p.2.1 = i then (a i / M) * d p.1.2 p.2.2 else 0)
        = (a i / M) * ∑ p ∈ F.offDiag, d p.1.2 p.2.2 := by
      rw [← Finset.sum_filter, hfilter, ← Finset.mul_sum]
    rw [hrow]
    have himg : (F.offDiag).image (fun p : (α × β) × (α × β) => (p.1.2, p.2.2))
        = ((F.image Prod.snd).offDiag : Finset (β × β)) := by
      ext q
      simp only [Finset.mem_image, Finset.mem_offDiag]
      constructor
      · rintro ⟨p, ⟨k1, k2, kne⟩, hpq⟩
        obtain ⟨hq1, hq2⟩ := Prod.ext_iff.mp hpq
        dsimp only at hq1 hq2
        refine ⟨⟨p.1, k1, hq1⟩, ⟨p.2, k2, hq2⟩, ?_⟩
        intro hqq
        have e1 : p.1 = (i, p.1.2) := Prod.ext (Finset.mem_filter.mp k1).2 rfl
        have e2 : p.2 = (i, p.2.2) := Prod.ext (Finset.mem_filter.mp k2).2 rfl
        exact kne (by rw [e1, e2, hq1, hq2, hqq])
      · rintro ⟨h1, h2, hne⟩
        obtain ⟨x, hx, hxq⟩ := h1
        obtain ⟨y, hy, hyq⟩ := h2
        refine ⟨(x, y), ⟨hx, hy, ?_⟩, ?_⟩
        · intro hcc
          exact hne (by rw [← hxq, ← hyq]; exact congrArg Prod.snd hcc)
        · simp only
          exact Prod.ext hxq hyq
    have hinj : ∀ p ∈ F.offDiag, ∀ p' ∈ F.offDiag,
        (fun p : (α × β) × (α × β) => (p.1.2, p.2.2)) p
          = (fun p : (α × β) × (α × β) => (p.1.2, p.2.2)) p' → p = p' := by
      intro p hp p' hp' hcc
      simp only at hcc
      obtain ⟨hf, hs⟩ := Prod.ext_iff.mp hcc
      obtain ⟨k1, k2, -⟩ := Finset.mem_offDiag.mp hp
      obtain ⟨k1', k2', -⟩ := Finset.mem_offDiag.mp hp'
      have e2' : p.1 = p'.1 :=
        Prod.ext ((Finset.mem_filter.mp k1).2.trans
          (Finset.mem_filter.mp k1').2.symm) hf
      have e3' : p.2 = p'.2 :=
        Prod.ext ((Finset.mem_filter.mp k2).2.trans
          (Finset.mem_filter.mp k2').2.symm) hs
      exact Prod.ext e2' e3'
    unfold rowProj
    rw [← himg, Finset.sum_image hinj]
  unfold rowMixWeight
  rw [hsing, hpair, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => (mul_add (a i / M) _ _).symm

/-- Nonnegativity of the row-copy mixture: every row term is a nonnegative
scalar times the right weight read on a legitimate event. -/
theorem rowMixWeight_nonneg {nu : Finset β → ℚ}
    (hposnu : ∀ T, 0 ≤ nu T) (a : α → ℚ) (c : β → ℚ) (d : β → β → ℚ)
    (hnu' : ∀ T : Finset β,
      nu T = (∑ t ∈ T, c t) + ∑ p ∈ T.offDiag, d p.1 p.2)
    (ha : ∀ i, 0 ≤ a i) (hM : 0 < M) (U : Finset (α × β)) :
    0 ≤ rowMixWeight a c d M U := by
  rw [rowMixWeight_eq]
  refine Finset.sum_nonneg fun i _ => ?_
  exact mul_nonneg (div_nonneg (ha i) hM.le)
    (by rw [← hnu' (rowProj i U)]; exact hposnu (rowProj i U))

theorem rowMixWeight_left (a : α → ℚ) (c : β → ℚ) (d : β → β → ℚ) (M : ℚ)
    (hM : M ≠ 0)
    (hmass : (∑ t ∈ (Finset.univ : Finset β), c t)
      + ∑ p ∈ (Finset.univ : Finset β).offDiag, d p.1 p.2 = M)
    (S : Finset α) :
    rowMixWeight a c d M (S ×ˢ (Finset.univ : Finset β)) = ∑ i ∈ S, a i := by
  rw [rowMixWeight_eq]
  have hread : ∀ i ∈ (Finset.univ : Finset α),
      (a i / M) * ((∑ t ∈ rowProj i (S ×ˢ (Finset.univ : Finset β)), c t)
        + ∑ p ∈ (rowProj i (S ×ˢ (Finset.univ : Finset β))).offDiag, d p.1 p.2)
      = if i ∈ S then a i else 0 := by
    intro i _
    rw [rowProj_product_top i S]
    by_cases hi : i ∈ S
    · rw [if_pos hi, hmass, div_mul_cancel₀ _ hM, if_pos hi]
    · simp [hi, Finset.offDiag_empty]
  rw [Finset.sum_congr rfl hread]
  have hset : (Finset.univ : Finset α).filter (fun i => i ∈ S) = S := by
    ext i
    simp
  rw [← Finset.sum_filter, hset]

theorem rowMixWeight_right (a : α → ℚ) (c : β → ℚ) (d : β → β → ℚ) (M : ℚ)
    (hM : M ≠ 0) (hsum : ∑ i ∈ (Finset.univ : Finset α), a i = M)
    (T : Finset β) :
    rowMixWeight a c d M ((Finset.univ : Finset α) ×ˢ T)
      = (∑ t ∈ T, c t) + ∑ p ∈ T.offDiag, d p.1 p.2 := by
  rw [rowMixWeight_eq]
  simp only [rowProj_top_product]
  rw [← Finset.sum_mul, ← Finset.sum_div, hsum, div_self hM, one_mul]

/-- **Additive gluing.** Every additive weight with nonnegative
coefficients couples positively with every nonnegative-valued pairwise
weight of the same positive total mass: the row-copy mixture does it, with
left cylinder marginal `S ↦ ∑ i ∈ S, a i` and right cylinder marginal the
given weight exactly. -/
theorem additive_weight_gluing (a : α → ℚ) (ha : ∀ i, 0 ≤ a i)
    (nu : Finset β → ℚ) (hnu : TwoDecomposable nu) (hposnu : ∀ T, 0 ≤ nu T)
    (hposmass : 0 < nu (Finset.univ : Finset β))
    (hmass : ∑ i ∈ (Finset.univ : Finset α), a i = nu (Finset.univ : Finset β)) :
    ∃ W : Finset (α × β) → ℚ, TwoDecomposable W ∧
      (∀ S, W (S ×ˢ (Finset.univ : Finset β)) = ∑ i ∈ S, a i) ∧
      (∀ T, W ((Finset.univ : Finset α) ×ˢ T) = nu T) ∧
      (∀ U, 0 ≤ W U) := by
  obtain ⟨c, d, hnu'⟩ := hnu
  have hM : nu (Finset.univ : Finset β) ≠ 0 := ne_of_gt hposmass
  refine ⟨rowMixWeight a c d (nu (Finset.univ : Finset β)),
    rowMixWeight_two_decomposable a c d _, ?_, ?_, ?_⟩
  · intro S
    exact rowMixWeight_left a c d _ hM
      (by rw [hnu' (Finset.univ : Finset β)]) S
  · intro T
    rw [rowMixWeight_right a c d _ hM hmass T, ← hnu' T]
  · exact rowMixWeight_nonneg hposnu a c d hnu' ha hposmass

/-! ## Zero weight on the left: the left-slice embedding -/

/-- Left projection of a product event: the right indices whose point in
row `s₀` is present in `U`. -/
def sliceProjLeft (s₀ : α) (U : Finset (α × β)) : Finset β :=
  (U.filter fun x => x.1 = s₀).image Prod.snd

/-- The left slice weight reads the carried right weight on the row
projection. -/
theorem sliceWeightLeft_eq (c : β → ℚ) (d : β → β → ℚ) (s₀ : α)
    (U : Finset (α × β)) :
    sliceWeightLeft c d s₀ U
      = (∑ t ∈ sliceProjLeft s₀ U, c t)
        + ∑ p ∈ (sliceProjLeft s₀ U).offDiag, d p.1 p.2 := by
  classical
  set S : Finset (α × β) := U.filter fun x => x.1 = s₀ with hSdef
  have hmono : S.offDiag ⊆ U.offDiag := by
    intro p hp
    obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp hp
    exact Finset.mem_offDiag.mpr
      ⟨(Finset.mem_filter.mp h1).1, (Finset.mem_filter.mp h2).1, hne⟩
  have hcond : ∀ p ∈ U.offDiag,
      (p.1.1 = s₀ ∧ p.2.1 = s₀) ↔ p ∈ S.offDiag := by
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
        if p.1.1 = s₀ ∧ p.2.1 = s₀ then d p.1.2 p.2.2 else 0)
      = ∑ p ∈ U.offDiag, (if p ∈ S.offDiag then d p.1.2 p.2.2 else 0) :=
    Finset.sum_congr rfl fun p hp => by
      by_cases h : p ∈ S.offDiag
      · rw [if_pos h, if_pos ((hcond p hp).mpr h)]
      · rw [if_neg h, if_neg fun hc => h ((hcond p hp).mp hc)]
  have e1 : (∑ p ∈ U.offDiag, (if p ∈ S.offDiag then d p.1.2 p.2.2 else 0))
      = ∑ p ∈ S.offDiag, d p.1.2 p.2.2 := by
    rw [← Finset.sum_subset hmono fun p _ hnp => if_neg hnp]
    exact Finset.sum_congr rfl fun p hp => if_pos hp
  have hcol : ∀ p ∈ S.offDiag, p.1 = (s₀, p.1.2) ∧ p.2 = (s₀, p.2.2) := by
    intro p hp
    obtain ⟨k1, k2, -⟩ := Finset.mem_offDiag.mp hp
    exact ⟨Prod.ext (Finset.mem_filter.mp k1).2 rfl,
      Prod.ext (Finset.mem_filter.mp k2).2 rfl⟩
  have himg : (S.offDiag).image (fun p : (α × β) × (α × β) => (p.1.2, p.2.2))
      = ((S.image Prod.snd).offDiag : Finset (β × β)) := by
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
        exact hne (by rw [← hxq, ← hyq]; exact congrArg Prod.snd hcc)
      · simp only
        exact Prod.ext hxq hyq
  have hinj : ∀ p ∈ S.offDiag, ∀ p' ∈ S.offDiag,
      (fun p : (α × β) × (α × β) => (p.1.2, p.2.2)) p
        = (fun p : (α × β) × (α × β) => (p.1.2, p.2.2)) p' → p = p' := by
    intro p hp p' hp' hcc
    simp only at hcc
    obtain ⟨hf, hs⟩ := Prod.ext_iff.mp hcc
    dsimp only at hf hs
    obtain ⟨k1, k2, -⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨k1', k2', -⟩ := Finset.mem_offDiag.mp hp'
    have e2' : p.1 = p'.1 := by
      apply Prod.ext _ hf
      have g1 := (Finset.mem_filter.mp k1).2
      have g1' := (Finset.mem_filter.mp k1').2
      rw [g1, ← g1']
    have e3' : p.2 = p'.2 := by
      apply Prod.ext _ hs
      have g2 := (Finset.mem_filter.mp k2).2
      have g2' := (Finset.mem_filter.mp k2').2
      rw [g2, ← g2']
    exact Prod.ext e2' e3'
  have hsing : (∑ x ∈ U, if x.1 = s₀ then c x.2 else 0)
      = ∑ t ∈ sliceProjLeft s₀ U, c t := by
    rw [← Finset.sum_filter]
    unfold sliceProjLeft
    refine (Finset.sum_image ?_).symm
    intro x hx y hy hxy
    have g1 := (Finset.mem_filter.mp hx).2
    have g2 := (Finset.mem_filter.mp hy).2
    have hsnd : x.2 = y.2 := hxy
    exact Prod.ext (g1.trans g2.symm) hsnd
  unfold sliceWeightLeft
  rw [hsing, e0, e1]
  unfold sliceProjLeft
  rw [← hSdef, ← himg, Finset.sum_image hinj]

/-- Nonnegativity of the left slice weight: it reads the carried weight on
a legitimate event. -/
theorem sliceWeightLeft_nonneg {nu : Finset β → ℚ}
    (hposnu : ∀ T, 0 ≤ nu T) (c : β → ℚ) (d : β → β → ℚ)
    (hnu' : ∀ T : Finset β,
      nu T = (∑ t ∈ T, c t) + ∑ p ∈ T.offDiag, d p.1 p.2)
    (s₀ : α) (U : Finset (α × β)) :
    0 ≤ sliceWeightLeft c d s₀ U := by
  rw [sliceWeightLeft_eq, ← hnu' (sliceProjLeft s₀ U)]
  exact hposnu (sliceProjLeft s₀ U)

/-- **Zero weight on the left.** The zero weight couples positively with
every nonnegative-valued pairwise weight of total mass zero (which may be
nonzero itself, e.g. XOR-type weights): the left slice carries the whole
right weight on one row, the left cylinder marginal vanishes identically
because the total mass vanishes. -/
theorem zero_weight_gluing (nu : Finset β → ℚ)
    (hnu : TwoDecomposable nu) (hposnu : ∀ T, 0 ≤ nu T)
    (hzero : nu (Finset.univ : Finset β) = 0) (s₀ : α) :
    ∃ W : Finset (α × β) → ℚ, TwoDecomposable W ∧
      (∀ S, W (S ×ˢ (Finset.univ : Finset β)) = 0) ∧
      (∀ T, W ((Finset.univ : Finset α) ×ˢ T) = nu T) ∧
      (∀ U, 0 ≤ W U) := by
  obtain ⟨c, d, hnu'⟩ := hnu
  refine ⟨sliceWeightLeft c d s₀, sliceWeightLeft_two_decomposable c d s₀,
    ?_, ?_, ?_⟩
  · intro S
    by_cases hS : s₀ ∈ S
    · rw [sliceLeft_section S (Finset.univ : Finset β) s₀ hS c d,
        ← hnu' (Finset.univ : Finset β), hzero]
    · rw [sliceWeightLeft_of_not_mem S (Finset.univ : Finset β) s₀ hS c d]
  · intro T
    rw [sliceLeft_section (Finset.univ : Finset α) T s₀
      (Finset.mem_univ s₀) c d, ← hnu' T]
  · exact sliceWeightLeft_nonneg hposnu c d hnu' s₀

/-! ## Sum composition and the decomposition corollary -/

/-- **Sum composition.** Positive couplings compose by sums: gluing
`(mu₁, nu₁)` and gluing `(mu₂, nu₂)` yields a gluing of
`(mu₁ + mu₂, nu₁ + nu₂)`. -/
theorem gluing_sum_composition (W₁ W₂ : Finset (α × β) → ℚ)
    (h₁ : TwoDecomposable W₁) (h₂ : TwoDecomposable W₂)
    (hp₁ : ∀ U, 0 ≤ W₁ U) (hp₂ : ∀ U, 0 ≤ W₂ U)
    (mu₁ mu₂ : Finset α → ℚ) (nu₁ nu₂ : Finset β → ℚ)
    (hL₁ : ∀ S, W₁ (S ×ˢ (Finset.univ : Finset β)) = mu₁ S)
    (hL₂ : ∀ S, W₂ (S ×ˢ (Finset.univ : Finset β)) = mu₂ S)
    (hR₁ : ∀ T, W₁ ((Finset.univ : Finset α) ×ˢ T) = nu₁ T)
    (hR₂ : ∀ T, W₂ ((Finset.univ : Finset α) ×ˢ T) = nu₂ T) :
    ∃ W : Finset (α × β) → ℚ, TwoDecomposable W ∧
      (∀ S, W (S ×ˢ (Finset.univ : Finset β)) = mu₁ S + mu₂ S) ∧
      (∀ T, W ((Finset.univ : Finset α) ×ˢ T) = nu₁ T + nu₂ T) ∧
      (∀ U, 0 ≤ W U) := by
  refine ⟨fun U => W₁ U + W₂ U, twoDecomposable_add W₁ W₂ h₁ h₂, ?_, ?_, ?_⟩
  · intro S
    show W₁ (S ×ˢ (Finset.univ : Finset β))
      + W₂ (S ×ˢ (Finset.univ : Finset β)) = _
    rw [hL₁ S, hL₂ S]
  · intro T
    show W₁ ((Finset.univ : Finset α) ×ˢ T)
      + W₂ ((Finset.univ : Finset α) ×ˢ T) = _
    rw [hR₁ T, hR₂ T]
  · intro U
    exact add_nonneg (hp₁ U) (hp₂ U)

/-- **Additive part plus mass-zero residue.** Any weight that decomposes as
an additive nonnegative part (carrying the whole positive total mass) plus a
nonnegative pairwise residue of total mass zero couples positively with
every nonnegative-valued pairwise weight of the same total mass: glue the
additive part by the row-copy mixture and the residue by the column
embedding (whose right marginal is the point mass of zero total mass). -/
theorem additive_plus_zeromass_gluing (a : α → ℚ) (ha : ∀ i, 0 ≤ a i)
    (R : Finset α → ℚ) (hR : TwoDecomposable R) (hposR : ∀ S, 0 ≤ R S)
    (hR0 : R (Finset.univ : Finset α) = 0)
    (nu : Finset β → ℚ) (hnu : TwoDecomposable nu) (hposnu : ∀ T, 0 ≤ nu T)
    (hposmass : 0 < nu (Finset.univ : Finset β))
    (hmass : ∑ i ∈ (Finset.univ : Finset α), a i
      = nu (Finset.univ : Finset β)) (t₀ : β) :
    ∃ W : Finset (α × β) → ℚ, TwoDecomposable W ∧
      (∀ S, W (S ×ˢ (Finset.univ : Finset β)) = (∑ i ∈ S, a i) + R S) ∧
      (∀ T, W ((Finset.univ : Finset α) ×ˢ T) = nu T) ∧
      (∀ U, 0 ≤ W U) := by
  obtain ⟨Wmix, hmix, hmixL, hmixR, hmixpos⟩ :=
    additive_weight_gluing a ha nu hnu hposnu hposmass hmass
  obtain ⟨Wcol, hcol, hcolL, hcolR, hcolpos⟩ :=
    column_embedding_gluing R hR hposR t₀
  obtain ⟨W, hW, hL, hRsum, hpos⟩ :=
    gluing_sum_composition Wmix Wcol hmix hcol hmixpos hcolpos
      (fun S => ∑ i ∈ S, a i) R nu (fun _ => (0 : ℚ)) hmixL hcolL hmixR
      (fun T => by
        rw [hcolR T]
        by_cases hT : t₀ ∈ T
        · rw [if_pos hT, hR0]
        · rw [if_neg hT])
  refine ⟨W, hW, hL, ?_, hpos⟩
  intro T
  rw [hRsum T, add_zero]

/-- **The whole mass-zero sector.** Any two nonnegative-valued pairwise
weights of total mass zero glue positively: carry the left weight on one
column (its column marginal is the point mass of zero total mass, i.e. the
zero weight) and the right weight on one row (its left cylinder marginal is
zero), then compose by sums. -/
theorem mass_zero_sector_gluing (mu : Finset α → ℚ)
    (hmu : TwoDecomposable mu) (hpos : ∀ S, 0 ≤ mu S)
    (hmass : mu (Finset.univ : Finset α) = 0)
    (nu : Finset β → ℚ) (hnu : TwoDecomposable nu) (hposnu : ∀ T, 0 ≤ nu T)
    (hmassnu : nu (Finset.univ : Finset β) = 0) (t₀ : β) (s₀ : α) :
    ∃ W : Finset (α × β) → ℚ, TwoDecomposable W ∧
      (∀ S, W (S ×ˢ (Finset.univ : Finset β)) = mu S) ∧
      (∀ T, W ((Finset.univ : Finset α) ×ˢ T) = nu T) ∧
      (∀ U, 0 ≤ W U) := by
  obtain ⟨Wc, hc1, hcL, hcR, hcp⟩ :=
    column_embedding_gluing_zero_mass mu hmu hpos hmass t₀
  obtain ⟨Wl, hl1, hlL, hlR, hlp⟩ :=
    zero_weight_gluing nu hnu hposnu hmassnu s₀
  obtain ⟨W, hW, hL, hR, hp⟩ :=
    gluing_sum_composition Wc Wl hc1 hl1 hcp hlp mu (fun _ => (0 : ℚ))
      (fun _ => (0 : ℚ)) nu hcL hlL hcR hlR
  refine ⟨W, hW, ?_, ?_, hp⟩
  · intro S
    rw [hL S]
    exact add_zero (mu S)
  · intro T
    rw [hR T]
    exact zero_add (nu T)

/-- **Transport marginals are pairwise weights.** The right cylinder
marginal produced by transport gluing is itself pairwise generated (it is
the left cylinder marginal of a pairwise composite). -/
theorem transport_marginal_two_decomposable (mu : Finset α → ℚ)
    (hmu : TwoDecomposable mu) (hpos : ∀ S, 0 ≤ mu S) (σ : α → β) :
    TwoDecomposable (fun T => mu (transportPreimage σ T)) := by
  obtain ⟨W, hW, -, hR, -⟩ := transport_gluing mu hmu hpos σ
  have heq : (fun T => mu (transportPreimage σ T))
      = (fun T => W ((Finset.univ : Finset α) ×ˢ T)) :=
    funext fun T => (hR T).symm
  rw [heq]
  exact cylinder_left_two_decomposable hW

/-- **Cone couplings compose by sums.** If both sides split into
positively generated pieces with matching masses, the pair glues: kernel
couple the pieces and sum. Canonical covered case on Fin 3:
`2·P₁₂ ⊗ (P₁₂ + P₁₃)` via `(P₁₂ ⊗ P₁₂) + (P₁₂ ⊗ P₁₃)`. -/
theorem cone_pair_sum_gluing (mu₁ mu₂ : Finset α → ℚ)
    (nu₁ nu₂ : Finset β → ℚ)
    (h₁ : PositivelyGenerated mu₁) (h₂ : PositivelyGenerated mu₂)
    (hn₁ : PositivelyGenerated nu₁) (hn₂ : PositivelyGenerated nu₂)
    (hm₁ : mu₁ (Finset.univ : Finset α) = nu₁ (Finset.univ : Finset β))
    (hm₂ : mu₂ (Finset.univ : Finset α) = nu₂ (Finset.univ : Finset β)) :
    ∃ W : Finset (α × β) → ℚ, TwoDecomposable W ∧
      (∀ S, W (S ×ˢ (Finset.univ : Finset β)) = mu₁ S + mu₂ S) ∧
      (∀ T, W ((Finset.univ : Finset α) ×ˢ T) = nu₁ T + nu₂ T) ∧
      (∀ U, 0 ≤ W U) := by
  obtain ⟨W₁, hW₁, hL₁, hR₁, hp₁⟩ := cone_gluing_positive mu₁ nu₁ h₁ hn₁ hm₁
  obtain ⟨W₂, hW₂, hL₂, hR₂, hp₂⟩ := cone_gluing_positive mu₂ nu₂ h₂ hn₂ hm₂
  exact gluing_sum_composition W₁ W₂ hW₁ hW₂ hp₁ hp₂ mu₁ mu₂ nu₁ nu₂
    hL₁ hL₂ hR₁ hR₂

end

inductive TransportAdditiveFinding where
  | anyNonnegativePairwiseWeightCouplesWithEveryTransportOfItself
  | diagonalAndColumnEmbeddingAreTheIdentityAndConstantTransports
  | additiveWeightsCoupleWithEveryEqualMassPositiveWeight
  | zeroWeightsCoupleWithEveryMassZeroWeightFromTheLeft
  | positiveCouplingsComposeBySums
  | additivePartPlusMassZeroResidueCouplesWithEverything
  | theWholeMassZeroSectorGlues
  | transportMarginalsArePairwiseWeights
  | coneCouplingsAlsoComposeBySums
  deriving DecidableEq, Repr

def transportAdditiveFindings : List TransportAdditiveFinding :=
  [ .anyNonnegativePairwiseWeightCouplesWithEveryTransportOfItself,
    .diagonalAndColumnEmbeddingAreTheIdentityAndConstantTransports,
    .additiveWeightsCoupleWithEveryEqualMassPositiveWeight,
    .zeroWeightsCoupleWithEveryMassZeroWeightFromTheLeft,
    .positiveCouplingsComposeBySums,
    .additivePartPlusMassZeroResidueCouplesWithEverything,
    .theWholeMassZeroSectorGlues,
    .transportMarginalsArePairwiseWeights,
    .coneCouplingsAlsoComposeBySums ]

theorem transport_additive_records_nine_findings :
    transportAdditiveFindings.length = 9 := by
  rfl

inductive TransportAdditiveOpenObligation where
  | proveOrRefuteTheConePlusZeroMassDecompositionConjecture
  | closeOrCounterexampleTheRemainingNonTransportPositiveMassPairs
  deriving DecidableEq, Repr

def transportAdditiveOpenObligations : List TransportAdditiveOpenObligation :=
  [ .proveOrRefuteTheConePlusZeroMassDecompositionConjecture,
    .closeOrCounterexampleTheRemainingNonTransportPositiveMassPairs ]

theorem transport_additive_keeps_two_open_obligations :
    transportAdditiveOpenObligations.length = 2 := by
  rfl

def transportAdditiveClaimBoundary : String :=
  "For set-function weights over Q on finite contexts: (1) for every nonnegative-valued pairwise generated weight mu and EVERY map sigma : alpha -> beta (no injectivity), the graph-carried transport weight is pairwise generated, nonnegative on every event, has left cylinder marginal mu exactly, and right cylinder marginal T |-> mu {i | sigma i in T}, and that transport marginal is itself pairwise generated; sigma = id recovers the diagonal self-gluing and constant sigma recovers the column embedding. (2) Every additive weight with nonnegative coefficients couples positively with every nonnegative-valued pairwise weight of the same positive total mass via the row-copy mixture. (3) Positive couplings compose by sums; consequently any additive-nonnegative part carrying the whole positive mass plus a mass-zero nonnegative pairwise residue couples with every equal-mass nonnegative pairwise weight, ANY two nonnegative-valued pairwise weights of total mass zero couple (the whole mass-zero sector), and pairs whose two sides split into positively generated pieces with matching masses couple (cone pair sums; e.g. 2*P12 with P12+P13). Machine status beyond the theorems: exhaustive transport-relatedness over all 27 maps on Fin 3 confirms f2, H13, P13, P23, H21 and f2+P13 as transports of f, H12, P12, P12, H12 and f+P12 respectively, while 2f+E1 vs 2f2+E2 and f+P12 vs f2+P23 are NOT transport-related. The cone-plus-zero-mass decomposition (mu = positively generated C of full mass + nonneg mass-zero residue), which would have implied universal positive gluing by kernel-coupling the cone parts and mass-zero-coupling the residues, holds on Fin 2 (hand proof) and on ALL 2385 positive-mass grid weights on Fin 3 (exact LP), but is REFUTED on Fin 4: ConeDecompositionWall gives an explicit nonnegative pairwise weight of mass 1 (delta_3 + positive triangle on 012 - star from 3) for which no positively generated part can carry the mass below it, with a machine-checked Lean proof. Open: whether that witness still couples with equal-mass partners (the refutation kills the route, not the gluing), and the remaining non-transport positive-mass pairs. Nothing here is uniqueness, nothing concerns entangled or interference-optimal couplings, and nothing derives complex amplitudes, a Hilbert carrier, purification, or the Born rule."

end QMClosure
end IDT
