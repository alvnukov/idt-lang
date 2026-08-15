import Mathlib.Tactic
import Proofs.QMClosure.SorkinGradeIffPairwiseGeneration
import Proofs.QMClosure.CompositionForcesBinaryArity
import Proofs.QMClosure.CylinderGluingForcesBinaryArity
import Proofs.QMClosure.TwoSidedCylinderGluing

namespace IDT
namespace QMClosure

/-!
# Conditioned gluing is unobstructed

`TwoSidedCylinderGluing` characterized two-sided cylinder gluing: second-order
locals with equal total mass always glue. The natural stronger demand is
conditioning: prescribe, for EVERY right-hand alternative `y`, the full
conditional readout `mu y` that the composite must give on the events
`S ×ˢ {y}` ("select S on the left, y on the right"), together with the left
cylinder marginal `nu`. Bell-type obstructions, if any live at the weight
level, should surface here.

They do not. Main theorem `conditioned_gluing_iff`: such a second-order
composite exists exactly when every `mu y` and `nu` are second order and the
overlap values agree, `nu {y} = mu y univ` -- the identification of the event
`univ ×ˢ {y}`, read once as a conditioned event and once as a left cylinder
event. No other constraint exists.

The witness is the slice family plus a left-over correction: carry each
`mu y` on its own horizontal slice `α × {y}` (slices do not interact, since a
pair of points in two different slices never lies in a single `S ×ˢ {y}`),
then carry the left-over `nu - (additive mass table)` on one vertical slice.
The overlap hypothesis makes the left-over vanish on singletons, so the
vertical slice never disturbs the conditioned family.

Two companion observations sharpen the reading.

First, `rectangle_marginal_two_decomposable`: for ANY fixed `T` (not just
`univ`), the rectangle marginal `fun S => W (S ×ˢ T)` of a second-order
composite is second order. The cylinder theorem is the case `T = univ`.

Second, `additive_table_two_decomposable`: any additive table -- and every
joint outcome table of a box, classical, quantum, or PR, is one at fixed
settings -- is pairwise generated with zero kernel, grade at most one. So
interference grade cannot see nonlocality: it separates quantum from
classical readouts (that is the exponent-selection route), but a PR box is
as acceptable to the grade machinery as a classical table. Whatever excludes
boxworld must enter through demands this layer does not express.

Conclusion of the gluing cluster (`SorkinGradeIffPairwiseGeneration`,
`CylinderGluingForcesBinaryArity`, `TwoSidedCylinderGluing`, this file): the
entire linear layer of the weight calculus -- cylinder, two-sided, and
conditioned gluing -- is obstruction-free up to linear consistency. The first
gates that can carry physical selection content must be non-linear:
positivity of weights or of the generating kernel. That is recorded as the
leading open obligation, along with prescribing the unconditioned right
marginal on top of the family: an exact linear-algebra check over ℚ,
independent of Lean, found no further constraints there either on contexts
up to 4 × 2 and 3 × 3 (for at least two right-hand alternatives), and a
cross-kernel witness is sketched but not yet formalized.

Scope. Set-function weights over ℚ on finite contexts; nonemptiness of α is
required only for sufficiency (the vertical-slice anchor); conditioning on
single alternatives only, no multi-alternative conditioning beyond the left
cylinder; no positivity anywhere, so no probability interpretation is forced;
nothing here derives complex amplitudes, a Hilbert carrier, purification, or
the Born rule, and the second-orderness of composites remains an input, not a
derivation.
-/

variable {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]

/-! ## Rectangle marginals -/

theorem disjoint_product_gen {s t : Finset α} (T : Finset β) (h : Disjoint s t) :
    Disjoint (s ×ˢ T) (t ×ˢ T) :=
  disjoint_intro _ _ fun x hx1 hx2 =>
    disjoint_notMem _ _ h (Finset.mem_product.mp hx1).1
      (Finset.mem_product.mp hx2).1

/--
For ANY fixed right-hand event `T`, the rectangle marginal of a pairwise
generated composite is pairwise generated. The cylinder theorem
`cylinder_two_decomposable` is the case `T = univ`.
-/
theorem rectangle_marginal_two_decomposable {W : Finset (α × β) → ℚ}
    (hW : TwoDecomposable W) (T : Finset β) :
    TwoDecomposable (fun S => W (S ×ˢ T)) := by
  have hWempty : W ∅ = 0 := by
    obtain ⟨a, b, hb⟩ := hW
    rw [hb ∅]
    simp
  refine vanishing_i3_is_two_decomposable _ ?_ ?_
  · show W ((∅ : Finset α) ×ˢ T) = 0
    rw [Finset.empty_product]
    exact hWempty
  · intro A B C hA hB hC hAB hAC hBC
    have hmain := twoDecomposable_sorkinI3 W hW
      (A ×ˢ T) (B ×ˢ T) (C ×ˢ T)
      (disjoint_product_gen T hAB) (disjoint_product_gen T hAC)
      (disjoint_product_gen T hBC)
    have hU1 : (A ∪ B ∪ C) ×ˢ T = (A ×ˢ T) ∪ (B ×ˢ T) ∪ (C ×ˢ T) := by
      rw [Finset.union_product, Finset.union_product]
    have hU2 : (A ∪ B) ×ˢ T = (A ×ˢ T) ∪ (B ×ˢ T) := Finset.union_product
    have hU3 : (A ∪ C) ×ˢ T = (A ×ˢ T) ∪ (C ×ˢ T) := Finset.union_product
    have hU4 : (B ∪ C) ×ˢ T = (B ×ˢ T) ∪ (C ×ˢ T) := Finset.union_product
    unfold sorkinI3 at hmain ⊢
    simp only []
    rw [hU1, hU2, hU3, hU4]
    exact hmain

/-! ## Additive tables -/

/--
Any additive table is pairwise generated with zero kernel: grade at most one.
Every joint outcome table of a box at fixed settings -- classical, quantum,
or PR -- is such a table, so interference grade cannot see nonlocality.
-/
theorem additive_table_two_decomposable {γ : Type} [DecidableEq γ]
    (w : γ → ℚ) :
    TwoDecomposable (fun S => ∑ i ∈ S, w i) :=
  ⟨w, fun _ _ => 0, fun S => by simp⟩

/-! ## Finite sums of pairwise generated weights -/

theorem twoDecomposable_univ_sum {γ : Type} [DecidableEq γ]
    {δ : Type} [Fintype δ] [DecidableEq δ]
    (F : δ → Finset γ → ℚ) (hF : ∀ y, TwoDecomposable (F y)) :
    TwoDecomposable (fun S => ∑ y : δ, F y S) := by
  classical
  choose a b hb using hF
  refine ⟨fun x => ∑ y : δ, a y x, fun x z => ∑ y : δ, b y x z, fun S => ?_⟩
  simp only []
  have e1 : ∑ y : δ, F y S
      = ∑ y : δ, ((∑ i ∈ S, a y i) + ∑ p ∈ S.offDiag, b y p.1 p.2) :=
    Finset.sum_congr rfl fun y _ => hb y S
  rw [e1, Finset.sum_add_distrib]
  have e2 : ∑ y : δ, ∑ i ∈ S, a y i = ∑ i ∈ S, ∑ y : δ, a y i := Finset.sum_comm
  have e3 : ∑ y : δ, ∑ p ∈ S.offDiag, b y p.1 p.2
      = ∑ p ∈ S.offDiag, ∑ y : δ, b y p.1 p.2 := Finset.sum_comm
  rw [e2, e3]

/-! ## The conditioned characterization -/

/--
Necessity: a second-order composite realizing a conditioned family and the
left cylinder forces every family member and the left marginal to be second
order, and the overlap values to agree.
-/
theorem conditioned_gluing_necessity (mufam : β → Finset α → ℚ)
    (nu : Finset β → ℚ) {W : Finset (α × β) → ℚ} (hW : TwoDecomposable W)
    (hFam : ∀ (S : Finset α) (y : β), W (S ×ˢ ({y} : Finset β)) = mufam y S)
    (hL : ∀ T : Finset β, W ((Finset.univ : Finset α) ×ˢ T) = nu T) :
    (∀ y : β, TwoDecomposable (mufam y)) ∧ TwoDecomposable nu ∧
      (∀ y : β, nu {y} = mufam y (Finset.univ : Finset α)) := by
  refine ⟨fun y => ?_, ?_, fun y => ?_⟩
  · have hfun : mufam y = fun S => W (S ×ˢ ({y} : Finset β)) :=
      (funext fun S => hFam S y).symm
    rw [hfun]
    exact rectangle_marginal_two_decomposable hW _
  · have hfun : nu = fun T => W ((Finset.univ : Finset α) ×ˢ T) :=
      (funext hL).symm
    rw [hfun]
    exact cylinder_left_two_decomposable hW
  · rw [← hL {y}, hFam (Finset.univ : Finset α) y]

/--
Sufficiency: any second-order conditioned family with a second-order left
marginal consistent on overlaps is realized by a second-order composite.
The witness carries each family member on its own horizontal slice and the
left-over `nu - (mass table)` on one vertical slice.
-/
theorem conditioned_gluing_sufficiency (mufam : β → Finset α → ℚ)
    (nu : Finset β → ℚ) [Nonempty α]
    (hfam : ∀ y : β, TwoDecomposable (mufam y)) (hnu : TwoDecomposable nu)
    (hone : ∀ y : β, nu {y} = mufam y (Finset.univ : Finset α)) :
    ∃ W : Finset (α × β) → ℚ, TwoDecomposable W ∧
      (∀ (S : Finset α) (y : β), W (S ×ˢ ({y} : Finset β)) = mufam y S) ∧
      (∀ T : Finset β, W ((Finset.univ : Finset α) ×ˢ T) = nu T) := by
  classical
  obtain ⟨s₀⟩ : Nonempty α := ‹_›
  choose a b hb using hfam
  have hadd : TwoDecomposable
      (fun T => ∑ y ∈ T, mufam y (Finset.univ : Finset α)) :=
    additive_table_two_decomposable _
  obtain ⟨c, d, hcred⟩ := twoDecomposable_sub nu _ hnu hadd
  have hc0 : ∀ y : β, c y = 0 := by
    intro y
    have h1 := hcred {y}
    simp only [] at h1
    rw [Finset.sum_singleton, Finset.sum_singleton, offDiag_singleton,
      Finset.sum_empty] at h1
    linarith [h1, hone y]
  refine ⟨fun U => (∑ y : β, sliceWeightTop (a y) (b y) y U)
      + sliceWeightLeft c d s₀ U, ?_, ?_, ?_⟩
  · exact twoDecomposable_add _ _
      (twoDecomposable_univ_sum (fun y => sliceWeightTop (a y) (b y) y)
        (fun y => sliceWeightTop_two_decomposable (a y) (b y) y))
      (sliceWeightLeft_two_decomposable c d s₀)
  · intro S y
    simp only []
    have hslice : ∀ y' : β,
        sliceWeightTop (a y') (b y') y' (S ×ˢ ({y} : Finset β))
          = if y' = y then mufam y' S else 0 := by
      intro y'
      by_cases hy : y' = y
      · rw [if_pos hy,
          sliceTop_section S ({y} : Finset β) y' (Finset.mem_singleton.mpr hy)
            (a y') (b y'),
          ← hb y' S]
      · rw [sliceWeightTop_of_not_mem S ({y} : Finset β) y'
          (fun hmem => hy (Finset.mem_singleton.mp hmem)) (a y') (b y'),
        if_neg hy]
    have hleft : sliceWeightLeft c d s₀ (S ×ˢ ({y} : Finset β)) = 0 := by
      by_cases hs : s₀ ∈ S
      · rw [sliceLeft_section S ({y} : Finset β) s₀ hs c d,
          Finset.sum_singleton, offDiag_singleton, Finset.sum_empty, hc0 y]
        ring
      · exact sliceWeightLeft_of_not_mem S ({y} : Finset β) s₀ hs c d
    rw [hleft, Finset.sum_congr rfl (fun y' _ => hslice y'),
      Finset.sum_eq_single y (fun y' _ hy' => by simp [hy'])
        (fun hy => absurd (Finset.mem_univ y) hy)]
    simp
  · intro T
    simp only []
    have hslice : ∀ y : β,
        sliceWeightTop (a y) (b y) y ((Finset.univ : Finset α) ×ˢ T)
          = if y ∈ T then mufam y (Finset.univ : Finset α) else 0 := by
      intro y
      by_cases hy : y ∈ T
      · rw [if_pos hy,
          sliceTop_section (Finset.univ : Finset α) T y hy (a y) (b y),
          hb y (Finset.univ : Finset α)]
      · rw [sliceWeightTop_of_not_mem (Finset.univ : Finset α) T y hy
          (a y) (b y), if_neg hy]
    have hleft : sliceWeightLeft c d s₀ ((Finset.univ : Finset α) ×ˢ T)
        = nu T - ∑ y ∈ T, mufam y (Finset.univ : Finset α) := by
      rw [sliceLeft_section (Finset.univ : Finset α) T s₀
        (Finset.mem_univ s₀) c d]
      exact (hcred T).symm
    have hsum : ∑ y : β,
        (if y ∈ T then mufam y (Finset.univ : Finset α) else 0)
        = ∑ y ∈ T, mufam y (Finset.univ : Finset α) := by
      have hf : (Finset.univ : Finset β).filter (fun y => y ∈ T) = T := by
        ext y
        simp [Finset.mem_filter]
      rw [← Finset.sum_filter, hf]
    rw [hleft, Finset.sum_congr rfl (fun y _ => hslice y), hsum]
    ring

/-- The conditioned characterization: second-order composites realize
exactly the second-order families consistent on overlaps. -/
theorem conditioned_gluing_iff (mufam : β → Finset α → ℚ) (nu : Finset β → ℚ)
    [Nonempty α] :
    (∃ W : Finset (α × β) → ℚ, TwoDecomposable W ∧
      (∀ (S : Finset α) (y : β), W (S ×ˢ ({y} : Finset β)) = mufam y S) ∧
      (∀ T : Finset β, W ((Finset.univ : Finset α) ×ˢ T) = nu T))
  ↔ (∀ y : β, TwoDecomposable (mufam y)) ∧ TwoDecomposable nu ∧
      (∀ y : β, nu {y} = mufam y (Finset.univ : Finset α)) := by
  constructor
  · rintro ⟨W, hW, hFam, hL⟩
    exact conditioned_gluing_necessity mufam nu hW hFam hL
  · rintro ⟨hfam, hnu, hone⟩
    exact conditioned_gluing_sufficiency mufam nu hfam hnu hone

inductive ConditionedFinding where
  | rectangleMarginalsAreSecondOrder
  | conditionedFamiliesGlueExactlyOnOverlapConsistency
  | additiveTablesAreAtMostFirstOrder
  | gradeCannotSeeNonlocality
  | theLinearGluingLayerIsObstructionFree
  deriving DecidableEq, Repr

def conditionedFindings : List ConditionedFinding :=
  [ .rectangleMarginalsAreSecondOrder,
    .conditionedFamiliesGlueExactlyOnOverlapConsistency,
    .additiveTablesAreAtMostFirstOrder,
    .gradeCannotSeeNonlocality,
    .theLinearGluingLayerIsObstructionFree ]

theorem conditioned_records_five_findings :
    conditionedFindings.length = 5 := by
  rfl

inductive ConditionedOpenObligation where
  | formalizeThePositivityGateWhereTheFirstRealObstructionMustAppear
  | characterizePrescribingTheUnconditionedRightMarginalToo
  | liftTheSetupToMultipleSettingsPerPartyForGenuineBellStructure
  deriving DecidableEq, Repr

def conditionedOpenObligations : List ConditionedOpenObligation :=
  [ .formalizeThePositivityGateWhereTheFirstRealObstructionMustAppear,
    .characterizePrescribingTheUnconditionedRightMarginalToo,
    .liftTheSetupToMultipleSettingsPerPartyForGenuineBellStructure ]

theorem conditioned_keeps_three_open_obligations :
    conditionedOpenObligations.length = 3 := by
  rfl

def conditionedClaimBoundary : String :=
  "For set-function weights over ℚ on finite contexts: for every fixed right-hand event T the rectangle marginal of a pairwise generated composite is pairwise generated; a second-order composite realizing a conditioned family (mu y on every S x {y}) together with the left cylinder marginal nu exists exactly when every mu y and nu are pairwise generated and nu {y} = mu y univ for every y (the overlap identification); and every additive table, hence every joint outcome table of a box at fixed settings, is pairwise generated with zero kernel. Consequences: interference grade cannot see nonlocality (a PR table is as acceptable as a classical one), and the linear gluing layer is obstruction-free up to linear consistency, so the first gate able to carry physical selection content must be non-linear, positivity above all. Prescribing the unconditioned right marginal on top of the family was checked by exact linear algebra over ℚ on small contexts (no further constraints for at least two right-hand alternatives) but is not formalized here; multi-setting Bell structure is not formalized either. Nonemptiness of the left context is needed for sufficiency only. Nothing here derives complex amplitudes, a Hilbert carrier, purification, or the Born rule, and the second-orderness of composites remains an input."

end QMClosure
end IDT
