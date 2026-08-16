import Mathlib.Tactic
import Proofs.QMClosure.SorkinGradeIffPairwiseGeneration

namespace IDT
namespace QMClosure

/-!
# Born-readout lemmas from the weight calculus alone

The three born_readout closure obligations (exclusivity additivity,
coarse-graining consistency, operational-equivalence invariance) were
demoted to IMPORT_REJECTED because their artifacts assumed
`W : H → ℂ` — the complex carrier they should derive.  This file
re-derives all three at the level where the primitive base actually
lives: the 2-additive weight calculus.  No complex numbers, no
amplitudes, no measure theory — only singleton coefficients `a`, pair
coefficients `b`, and Finset algebra.

Statements, each closing the corresponding required statement at the
weight-calculus level:

* `merge_expansion` / `coarse_graining_three_set`: readout stability
  under admissible coarse-graining.  Merging two disjoint events adds
  exactly the ordered cross-pair sum, and the three-event readout is
  consistent under any regrouping — the partition expansion is an
  identity for every partition.
* `exclusive_events_are_additive`: additivity over facticized exclusive
  alternatives.  Events with vanishing cross pair coefficients are
  additive — exclusivity IS vanishing interference, and then merging
  adds nothing.
* `operational_equivalence_invariance`: equal probabilities for
  operationally equivalent readout events.  A relabeling that preserves
  the generating data (singletons and pair coefficients) preserves the
  readout on every event.

Together with `TwoDecomposable` (weights built from a kernel), these
are the weight-calculus shadows of the demoted measure-theoretic
artifacts, at the correct primitive level.  Registering them under the
full proof-card contract is a separate mechanical step; the mathematics
here is carrier-free.  Scope: finite events over an arbitrary type with
DecidableEq; coefficients over ℚ.
-/

section
variable {α : Type} [DecidableEq α]

/-- Cross interference between two disjoint events: the ordered
pair-coefficient sum carried by the merge. -/
def crossInterference (b : α → α → ℚ) (X Y : Finset α) : ℚ :=
  (∑ x ∈ X, ∑ y ∈ Y, b x y) + (∑ x ∈ X, ∑ y ∈ Y, b y x)

/-- **Merge expansion**: merging two disjoint events adds exactly the
ordered cross-pair interference.  This is the readout-stability
identity under binary coarse-graining. -/
theorem merge_expansion (a : α → ℚ) (b : α → α → ℚ)
    (mu : Finset α → ℚ)
    (hmu : ∀ S : Finset α,
      mu S = (∑ i ∈ S, a i) + ∑ p ∈ S.offDiag, b p.1 p.2)
    (A B : Finset α) (hD : Disjoint A B) :
    mu (A ∪ B) = mu A + mu B + crossInterference b A B := by
  rw [hmu (A ∪ B), hmu A, hmu B, Finset.sum_union hD]
  have hint : A ∩ B = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hD
  have hAB : ∀ i, i ∈ A → i ∉ B := fun i hi hiB =>
    absurd (Finset.mem_inter.mpr ⟨hi, hiB⟩) (by simp [hint])
  have hBA : ∀ i, i ∈ B → i ∉ A := fun i hi hiA =>
    absurd (Finset.mem_inter.mpr ⟨hiA, hi⟩) (by simp [hint])
  have xA1 : Disjoint A.offDiag (A ×ˢ B) := by
    rw [Finset.disjoint_left]
    intro p hp hqp
    exact hAB _ (Finset.mem_offDiag.mp hp).2.1
      (Finset.mem_product.mp hqp).2
  have xA2 : Disjoint A.offDiag (B ×ˢ A) := by
    rw [Finset.disjoint_left]
    intro p hp hqp
    exact hAB _ (Finset.mem_offDiag.mp hp).1
      (Finset.mem_product.mp hqp).1
  have xA3 : Disjoint A.offDiag B.offDiag := by
    rw [Finset.disjoint_left]
    intro p hp hqp
    exact hAB _ (Finset.mem_offDiag.mp hp).1
      (Finset.mem_offDiag.mp hqp).1
  have xB1 : Disjoint (A ×ˢ B) (B ×ˢ A) := by
    rw [Finset.disjoint_left]
    intro p hp hqp
    exact hAB _ (Finset.mem_product.mp hp).1
      (Finset.mem_product.mp hqp).1
  have xB2 : Disjoint (A ×ˢ B) B.offDiag := by
    rw [Finset.disjoint_left]
    intro p hp hqp
    exact hBA _ (Finset.mem_offDiag.mp hqp).1
      (Finset.mem_product.mp hp).1
  have xB3 : Disjoint (B ×ˢ A) B.offDiag := by
    rw [Finset.disjoint_left]
    intro p hp hqp
    exact hAB _ (Finset.mem_product.mp hp).2
      (Finset.mem_offDiag.mp hqp).2.1
  have midD : Disjoint (A.offDiag ∪ A ×ˢ B) (B ×ˢ A) := by
    rw [Finset.disjoint_union_left]
    exact ⟨xA2, xB1⟩
  have topD : Disjoint ((A.offDiag ∪ A ×ˢ B) ∪ (B ×ˢ A)) B.offDiag := by
    rw [Finset.disjoint_union_left]
    exact ⟨by rw [Finset.disjoint_union_left]; exact ⟨xA3, xB2⟩, xB3⟩
  have hsplit : (A ∪ B).offDiag
      = A.offDiag ∪ (A ×ˢ B) ∪ (B ×ˢ A) ∪ B.offDiag := by
    ext p
    obtain ⟨x, y⟩ := p
    simp only [Finset.mem_offDiag, Finset.mem_union, Finset.mem_product]
    constructor
    · rintro ⟨(h1 | h1), (h2 | h2), hne⟩
      · left; left; left; exact ⟨h1, h2, hne⟩
      · left; left; right; exact ⟨h1, h2⟩
      · left; right; exact ⟨h1, h2⟩
      · right; exact ⟨h1, h2, hne⟩
    · intro h
      rcases h with ((h | h) | h) | h
      · obtain ⟨h1, h2, hne⟩ := h
        exact ⟨Or.inl h1, Or.inl h2, hne⟩
      · obtain ⟨h1, h2⟩ := h
        refine ⟨Or.inl h1, Or.inr h2, fun hcon => ?_⟩
        subst hcon
        exact hAB _ h1 h2
      · obtain ⟨h1, h2⟩ := h
        refine ⟨Or.inr h1, Or.inl h2, fun hcon => ?_⟩
        subst hcon
        exact hBA _ h1 h2
      · obtain ⟨h1, h2, hne⟩ := h
        exact ⟨Or.inr h1, Or.inr h2, hne⟩
  rw [hsplit, Finset.sum_union topD, Finset.sum_union midD,
    Finset.sum_union xA1]
  rw [Finset.sum_product, Finset.sum_product]
  dsimp only
  have hBA : ∑ x ∈ B, ∑ y ∈ A, b x y = ∑ x ∈ A, ∑ y ∈ B, b y x :=
    Finset.sum_comm (s := B) (t := A) (f := fun x y => b x y)
  rw [hBA]
  unfold crossInterference
  ring

/-- **Three-event coarse-graining consistency**: the readout of a
three-part event equals the sum of parts plus pairwise cross
interferences, independent of the regrouping order. -/
theorem coarse_graining_three_set (a : α → ℚ) (b : α → α → ℚ)
    (mu : Finset α → ℚ)
    (hmu : ∀ S : Finset α,
      mu S = (∑ i ∈ S, a i) + ∑ p ∈ S.offDiag, b p.1 p.2)
    (A B C : Finset α) (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) :
    mu (A ∪ B ∪ C) = mu A + mu B + mu C
      + crossInterference b A B + crossInterference b A C
      + crossInterference b B C := by
  rw [Finset.union_assoc]
  have h1 : Disjoint A (B ∪ C) := by
    rw [Finset.disjoint_union_right]
    exact ⟨hAB, hAC⟩
  rw [merge_expansion a b mu hmu A (B ∪ C) h1,
    merge_expansion a b mu hmu B C hBC]
  have hu : ∀ f : α → α → ℚ, (∑ x ∈ A, ∑ y ∈ B ∪ C, f x y)
      = (∑ x ∈ A, ∑ y ∈ B, f x y) + (∑ x ∈ A, ∑ y ∈ C, f x y) := by
    intro f
    have h1 : ∀ x ∈ A, (∑ y ∈ B ∪ C, f x y)
        = (∑ y ∈ B, f x y) + (∑ y ∈ C, f x y) :=
      fun x _ => Finset.sum_union hBC
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
  have hsplit : crossInterference b A (B ∪ C)
      = crossInterference b A B + crossInterference b A C := by
    unfold crossInterference
    rw [hu (fun x y => b x y), hu (fun x y => b y x)]
    ring
  rw [hsplit]
  ring

/-- **Exclusivity additivity**: facticized exclusive alternatives
(vanishing cross pair coefficients) are additive. -/
theorem exclusive_events_are_additive (a : α → ℚ) (b : α → α → ℚ)
    (mu : Finset α → ℚ)
    (hmu : ∀ S : Finset α,
      mu S = (∑ i ∈ S, a i) + ∑ p ∈ S.offDiag, b p.1 p.2)
    (A B : Finset α) (hD : Disjoint A B)
    (hzero : ∀ x ∈ A, ∀ y ∈ B, b x y = 0 ∧ b y x = 0) :
    mu (A ∪ B) = mu A + mu B := by
  rw [merge_expansion a b mu hmu A B hD]
  have h0 : crossInterference b A B = 0 := by
    unfold crossInterference
    have e1 : (∑ x ∈ A, ∑ y ∈ B, b x y) = 0 :=
      Finset.sum_eq_zero fun x hx =>
        Finset.sum_eq_zero fun y hy => (hzero x hx y hy).1
    have e2 : (∑ x ∈ A, ∑ y ∈ B, b y x) = 0 :=
      Finset.sum_eq_zero fun x hx =>
        Finset.sum_eq_zero fun y hy => (hzero x hx y hy).2
    rw [e1, e2]
    ring
  rw [h0]
  ring

/-- **Operational-equivalence invariance**: a relabeling that
preserves the generating data preserves the readout on every event. -/
theorem operational_equivalence_invariance (a : α → ℚ)
    (b : α → α → ℚ) (mu : Finset α → ℚ)
    (hmu : ∀ S : Finset α,
      mu S = (∑ i ∈ S, a i) + ∑ p ∈ S.offDiag, b p.1 p.2)
    (σ : α → α) (hinj : Function.Injective σ)
    (ha : ∀ i, a (σ i) = a i)
    (hb : ∀ i j, b (σ i) (σ j) = b i j)
    (S : Finset α) :
    mu (S.image σ) = mu S := by
  rw [hmu (S.image σ), hmu S]
  rw [Finset.sum_image hinj.injOn]
  have hinj2 : Function.Injective
      (fun p : α × α => (σ p.1, σ p.2)) := by
    intro p q h
    rw [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    exact Prod.ext (hinj h1) (hinj h2)
  have himg : (S.image σ).offDiag
      = (S.offDiag).image (fun p : α × α => (σ p.1, σ p.2)) := by
    ext p
    obtain ⟨x, y⟩ := p
    simp only [Finset.mem_offDiag, Finset.mem_image]
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩, hne⟩
      refine ⟨(u, v), ⟨hu, hv, ?_⟩, ?_⟩
      · intro hcon
        exact hne (congrArg σ hcon)
      · rfl
    · rintro ⟨⟨u, v⟩, ⟨hu, hv, hne⟩, huv⟩
      dsimp only at huv
      rw [Prod.mk.injEq] at huv
      obtain ⟨rfl, rfl⟩ := huv
      exact ⟨⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩, by
        intro h
        exact hne (hinj h)⟩
  rw [himg, Finset.sum_image hinj2.injOn]
  simp only [ha, hb]

end
end QMClosure
end IDT

