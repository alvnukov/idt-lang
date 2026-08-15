import Mathlib.Tactic
import Proofs.QMClosure.SorkinGradeIffPairwiseGeneration

namespace IDT
namespace QMClosure

/-!
# Cylinder gluing forces binary arity (one-sided)

The C-arity research hypothesis, recorded in the task ledger on 2026-08-15,
says: composition closure forces binary arity. Its decisive test was the
two-context ternary composability probe -- the H1 kill construction of
section 174.80 only ever tested a ternary witness inside a single context.
This file runs the probe at the weight-calculus level and returns a partial
THEOREM: the literature prediction holds for cylinder marginals.

Setup. A composite of two contexts with alternative sets α and β carries
weights on the product selection algebra, `W : Finset (α × β) → ℚ`. The
cylinder marginal on the first context is `fun S => W (S ×ˢ univ)`: the
composite's readout of the cylinder event "select S on the left, anything on
the right". Cylinder consistency -- the composite extends the local readout
-- is the natural minimal gluing demand.

Main theorem. The cylinder marginal of a pairwise generated (second-order)
composite is pairwise generated. The proof goes through the grade
equivalence of `SorkinGradeIffPairwiseGeneration` with no sum manipulations
at all: products distribute over unions, so the cylinder image of a pairwise
disjoint nonempty triple is again a pairwise disjoint nonempty triple of
cylinder events, and the third-order term of the marginal is the third-order
term of the composite on those cylinders.

No-gluing. Contrapositive, a weight with genuine third-order content on some
triple -- a ternary discipline -- has NO second-order composite with
consistent cylinder marginal. This is the arithmetic shadow of the
literature: density cubes have third-order interference and violate local
tomography (Dakic-Paterek-Brukner 2014), and any Born-rule modification that
changes the interference order violates purification or local tomography
(Galley-Masanes 2018). A concrete witness instantiates the no-go: the cubic
weight `S ↦ |S|³`, whose third-order term on three singletons is 6.

Non-vacuity. Every second-order local weight does admit a second-order
composite with consistent cylinder marginal (an explicit lift concentrating
the kernel on one right-hand alternative), so the theorem does not ban
gluing outright: it bans gluing exactly of ternary residues.

What remains of C-arity after this file. (1) The top-level demand that
composites be second-order at all is an input here, not a derivation; the
no-gluing theorem says ternary locals cannot be glued INTO a second-order
composite, which is the direction the literature predicts. (2) Two-sided
gluing -- one composite extending BOTH local weights on their cylinders --
is left open and is genuinely constrained: the additive lift below cannot be
made two-sided without extra structure, which is a signal that composites
carry amplitude-level, not weight-level, information. (3) Stronger gluing
demands (conditioning, no-signalling on non-cylinder events, local
tomography degree counting) are not yet formalised.

Scope. Set-function weights over ℚ on selection algebras; the composite
lives on the product selection algebra, where the quantum composite weight
is second order (it is a squared sum over product selections). This is a
different degree notion from the per-particle mask parameterisation used in
many-body interference experiments, which reaches order 2M; no claim is made
about that parameterisation. Nothing here derives complex amplitudes, a
Hilbert carrier, purification, or the Born rule, and the primitive base
still has no semantics.
-/

variable {α β : Type} [DecidableEq α] [Fintype β] [DecidableEq β] [Nonempty β]

theorem disjoint_product_univ {s t : Finset α} (h : Disjoint s t) :
    Disjoint (s ×ˢ (Finset.univ : Finset β)) (t ×ˢ Finset.univ) :=
  disjoint_intro _ _ fun x hx1 hx2 =>
    disjoint_notMem _ _ h (Finset.mem_product.mp hx1).1
      (Finset.mem_product.mp hx2).1

theorem product_univ_nonempty {s : Finset α} (hs : s.Nonempty) :
    (s ×ˢ (Finset.univ : Finset β)).Nonempty := by
  obtain ⟨x, hx⟩ := hs
  obtain ⟨y⟩ : Nonempty β := ‹_›
  exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, Finset.mem_univ y⟩⟩

/--
The main theorem, one direction of the C-arity prediction: the cylinder
marginal of a pairwise generated composite is pairwise generated.
-/
theorem cylinder_two_decomposable {W : Finset (α × β) → ℚ}
    (hW : TwoDecomposable W) :
    TwoDecomposable (fun S => W (S ×ˢ (Finset.univ : Finset β))) := by
  have hWempty : W ∅ = 0 := by
    obtain ⟨a, b, hb⟩ := hW
    rw [hb ∅]
    simp
  refine vanishing_i3_is_two_decomposable _ ?_ ?_
  · show W ((∅ : Finset α) ×ˢ (Finset.univ : Finset β)) = 0
    rw [Finset.empty_product]
    exact hWempty
  · intro A B C hA hB hC hAB hAC hBC
    have hmain := twoDecomposable_sorkinI3 W hW
      (A ×ˢ (Finset.univ : Finset β)) (B ×ˢ Finset.univ) (C ×ˢ Finset.univ)
      (disjoint_product_univ hAB) (disjoint_product_univ hAC)
      (disjoint_product_univ hBC)
    have hU1 : (A ∪ B ∪ C) ×ˢ (Finset.univ : Finset β)
        = (A ×ˢ (Finset.univ : Finset β)) ∪ (B ×ˢ Finset.univ) ∪ (C ×ˢ Finset.univ) := by
      rw [Finset.union_product, Finset.union_product]
    have hU2 : (A ∪ B) ×ˢ (Finset.univ : Finset β)
        = (A ×ˢ (Finset.univ : Finset β)) ∪ (B ×ˢ Finset.univ) := Finset.union_product
    have hU3 : (A ∪ C) ×ˢ (Finset.univ : Finset β)
        = (A ×ˢ (Finset.univ : Finset β)) ∪ (C ×ˢ Finset.univ) := Finset.union_product
    have hU4 : (B ∪ C) ×ˢ (Finset.univ : Finset β)
        = (B ×ˢ (Finset.univ : Finset β)) ∪ (C ×ˢ Finset.univ) := Finset.union_product
    unfold sorkinI3 at hmain ⊢
    simp only []
    rw [hU1, hU2, hU3, hU4]
    exact hmain

/--
The no-gluing theorem: a weight with genuine third-order content on some
disjoint triple has no second-order composite whose cylinder marginal is
that weight. Ternary residues cannot be glued into second-order composites.
-/
theorem no_ternary_cylinder_gluing (mu : Finset α → ℚ)
    (htriple : ∃ A B C : Finset α, A.Nonempty ∧ B.Nonempty ∧ C.Nonempty ∧
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧ sorkinI3 mu A B C ≠ 0) :
    ¬ ∃ W : Finset (α × β) → ℚ,
      TwoDecomposable W ∧ ∀ S, W (S ×ˢ (Finset.univ : Finset β)) = mu S := by
  rintro ⟨W, hW, hcyl⟩
  obtain ⟨A, B, C, h1, h2, h3, d1, d2, d3, hI3⟩ := htriple
  rw [(funext hcyl).symm] at hI3
  exact hI3 (twoDecomposable_sorkinI3 _ (cylinder_two_decomposable hW)
    A B C d1 d2 d3)

theorem one_hot_sum {c : ℚ} (j₀ : β) :
    ∑ j : β, (if j = j₀ then c else 0) = c := by
  classical
  rw [Finset.sum_eq_single j₀
    (fun j _ hj => by simp [hj])
    (fun hj => absurd (Finset.mem_univ j₀) hj)]
  simp

/--
Non-vacuity: every pairwise generated local weight admits a pairwise
generated composite with consistent cylinder marginal, by concentrating the
singleton and kernel data on one right-hand alternative.
-/
theorem cylinder_gluing_lift (mu : Finset α → ℚ) (hmu : TwoDecomposable mu) :
    ∃ W : Finset (α × β) → ℚ,
      TwoDecomposable W ∧ ∀ S, W (S ×ˢ (Finset.univ : Finset β)) = mu S := by
  classical
  obtain ⟨a₀, b₀, hmu'⟩ := hmu
  obtain ⟨j₀⟩ : Nonempty β := ‹_›
  refine ⟨fun E => (∑ x ∈ E, if x.2 = j₀ then a₀ x.1 else 0)
      + ∑ p ∈ E.offDiag,
          if p.1.2 = j₀ ∧ p.2.2 = j₀ then b₀ p.1.1 p.2.1 else 0,
    ⟨fun x => if x.2 = j₀ then a₀ x.1 else 0,
      fun x y => if x.2 = j₀ ∧ y.2 = j₀ then b₀ x.1 y.1 else 0,
      fun E => rfl⟩, ?_⟩
  intro S
  -- singleton part
  have hsing : (∑ x ∈ S ×ˢ (Finset.univ : Finset β),
        if x.2 = j₀ then a₀ x.1 else 0) = ∑ i ∈ S, a₀ i := by
    rw [Finset.sum_product S Finset.univ
      (fun x => if x.2 = j₀ then a₀ x.1 else 0)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have heq : ∑ j : β, (if ((i, j) : α × β).2 = j₀ then a₀ ((i, j) : α × β).1 else 0)
        = ∑ j : β, (if j = j₀ then a₀ i else 0) :=
      Finset.sum_congr rfl fun j _ => by
        by_cases hj : j = j₀ <;> simp [hj]
    rw [heq, one_hot_sum]
  -- kernel part: reduce to the j₀-section and transfer along the section
  have hmono : (S ×ˢ ({j₀} : Finset β)).offDiag ⊆ (S ×ˢ (Finset.univ : Finset β)).offDiag := by
    intro p hp
    obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp hp
    rw [Finset.mem_product] at h1 h2
    exact Finset.mem_offDiag.mpr
      ⟨Finset.mem_product.mpr ⟨h1.1, Finset.mem_univ _⟩,
        Finset.mem_product.mpr ⟨h2.1, Finset.mem_univ _⟩, hne⟩
  have hsupport : ∀ p ∈ (S ×ˢ (Finset.univ : Finset β)).offDiag,
      p ∉ (S ×ˢ ({j₀} : Finset β)).offDiag →
      (if p.1.2 = j₀ ∧ p.2.2 = j₀ then b₀ p.1.1 p.2.1 else 0) = 0 := by
    intro p hp hnp
    by_cases hcond : p.1.2 = j₀ ∧ p.2.2 = j₀
    · exfalso
      obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp hp
      rw [Finset.mem_product] at h1 h2
      exact hnp (Finset.mem_offDiag.mpr
        ⟨Finset.mem_product.mpr ⟨h1.1, Finset.mem_singleton.mpr hcond.1⟩,
          Finset.mem_product.mpr ⟨h2.1, Finset.mem_singleton.mpr hcond.2⟩,
          hne⟩)
    · simp [hcond]
  have himg : (S ×ˢ ({j₀} : Finset β)).offDiag
      = (S.offDiag).image (fun p : α × α => ((p.1, j₀), (p.2, j₀))) := by
    ext q
    constructor
    · intro hq
      obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp hq
      rw [Finset.mem_product, Finset.mem_singleton] at h1 h2
      refine Finset.mem_image.mpr ⟨(q.1.1, q.2.1),
        Finset.mem_offDiag.mpr ⟨h1.1, h2.1, fun hcc =>
          hne (Prod.ext hcc (h1.2.trans (h2.2.symm)))⟩, ?_⟩
      exact Prod.ext (Prod.ext rfl h1.2.symm) (Prod.ext rfl h2.2.symm)
    · intro hq
      rw [Finset.mem_image] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp hp
      refine Finset.mem_offDiag.mpr
        ⟨Finset.mem_product.mpr ⟨h1, Finset.mem_singleton.mpr rfl⟩,
          Finset.mem_product.mpr ⟨h2, Finset.mem_singleton.mpr rfl⟩,
          fun hcc => hne (Prod.ext_iff.mp hcc).1⟩
  have hker : (∑ p ∈ (S ×ˢ (Finset.univ : Finset β)).offDiag,
        if p.1.2 = j₀ ∧ p.2.2 = j₀ then b₀ p.1.1 p.2.1 else 0)
      = ∑ p ∈ S.offDiag, b₀ p.1 p.2 := by
    rw [← Finset.sum_subset hmono hsupport, himg,
      Finset.sum_image fun p₁ _ p₂ _ h => Prod.ext
        ((Prod.ext_iff.mp (Prod.ext_iff.mp h).1).1)
        ((Prod.ext_iff.mp (Prod.ext_iff.mp h).2).1)]
    exact Finset.sum_congr rfl fun p _ => by simp
  simp only []
  rw [hsing, hker, ← hmu' S]

/--
The witness: the cubic weight `S ↦ |S|³` has third-order term 6 on the
three singletons, the arithmetic shadow of the density-cube construction.
-/
theorem cubic_weight_i3 :
    sorkinI3 (fun T : Finset (Fin 3) => (T.card : ℚ) ^ 3)
      ({0} : Finset (Fin 3)) ({1} : Finset (Fin 3)) ({2} : Finset (Fin 3)) = 6 := by
  unfold sorkinI3
  simp
  norm_num

/--
The density-cube shadow cannot be glued: the cubic weight on three
alternatives has no second-order composite on any product context with a
consistent cylinder marginal.
-/
theorem cubic_weight_has_no_second_order_composite :
    ¬ ∃ W : Finset (Fin 3 × Fin 2) → ℚ,
      TwoDecomposable W ∧
        ∀ S, W (S ×ˢ (Finset.univ : Finset (Fin 2)))
          = (fun T => (T.card : ℚ) ^ 3) S :=
  no_ternary_cylinder_gluing _ ⟨{0}, {1}, {2},
    ⟨⟨0, Finset.mem_singleton_self 0⟩, ⟨1, Finset.mem_singleton_self 1⟩,
      ⟨2, Finset.mem_singleton_self 2⟩,
      Finset.disjoint_singleton.mpr (by decide),
      Finset.disjoint_singleton.mpr (by decide),
      Finset.disjoint_singleton.mpr (by decide),
      by rw [cubic_weight_i3]; norm_num⟩⟩

inductive CylinderFinding where
  | cylinderMarginalOfASecondOrderCompositeIsSecondOrder
  | ternaryResiduesHaveNoSecondOrderComposite
  | secondOrderLocalsAlwaysAdmitASecondOrderComposite
  | theCubicWeightWitnessInstantiatesTheNoGluing
  deriving DecidableEq, Repr

def cylinderFindings : List CylinderFinding :=
  [ .cylinderMarginalOfASecondOrderCompositeIsSecondOrder,
    .ternaryResiduesHaveNoSecondOrderComposite,
    .secondOrderLocalsAlwaysAdmitASecondOrderComposite,
    .theCubicWeightWitnessInstantiatesTheNoGluing ]

theorem cylinder_records_four_findings :
    cylinderFindings.length = 4 := by
  rfl

inductive CylinderOpenObligation where
  | deriveThatCompositesMustBeSecondOrderRatherThanAssumeIt
  | twoSidedGluingFromWeightDataAlone
  | formalizeStrongerGluingDemandsThanCylinderConsistency
  | connectTheNoGluingToDensityCubeLocalTomographyCounts
  deriving DecidableEq, Repr

def cylinderOpenObligations : List CylinderOpenObligation :=
  [ .deriveThatCompositesMustBeSecondOrderRatherThanAssumeIt,
    .twoSidedGluingFromWeightDataAlone,
    .formalizeStrongerGluingDemandsThanCylinderConsistency,
    .connectTheNoGluingToDensityCubeLocalTomographyCounts ]

theorem cylinder_keeps_four_open_obligations :
    cylinderOpenObligations.length = 4 := by
  rfl

def cylinderClaimBoundary : String :=
  "For set-function weights over ℚ: the cylinder marginal of a pairwise generated composite weight is pairwise generated (via the grade equivalence, since products distribute over unions), so a weight with nonzero third-order term on some disjoint triple has no pairwise generated composite with a consistent cylinder marginal, while every pairwise generated local weight does admit such a composite. The cubic weight |S|^3 instantiates the no-gluing. The demand that composites be second-order at all is an input here, not a derivation; two-sided gluing and stronger gluing demands are open; the per-particle mask degree notion of many-body interference is a different parameterisation about which nothing is claimed. Nothing here derives complex amplitudes, a Hilbert carrier, purification, or the Born rule."

end QMClosure
end IDT
