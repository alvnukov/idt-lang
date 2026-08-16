import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation
import Proofs.QMClosure.V7PositiveGeometryGeneral

namespace IDT
namespace QMClosure

/-!
# The facticization-stability route to the visibility cap is either a
# disguise or vacuous

Section 174.37 proposed the bridge "finite facticization stability →
positive comparison geometry": if every negative quadratic direction
generated a finite refinement or spectator extension with a negative
facticization weight, stability would forbid the direction, and the
Cauchy-Schwarz cap (the exact gap between event-nonneg weights and
Born weights, see `BornConeGap`) would be derived from a primitive
demand.  This file kills both available readings of that bridge on two
alternatives:

1. **The disguise.** `FacticizationStability` as formalized in
   `V7PositiveGeometryGeneral` is `∀ v, quadForm G v ≥ 0` — PSD of the
   comparison form.  `form_psd_iff_cap` proves this is EXACTLY the cap
   `a ≥ 0 ∧ c ≥ 0 ∧ ac ≥ b²` (V7 proved the forward direction; the
   backward direction is completed here by completing the square).
   As a demand it assumes the visibility bound; it derives nothing.

2. **The vacuous reading.** If instead facticization witnesses are
   generated freely — any four-cell pairwise table that coarsens back
   to the weight counts as a refinement — then stability demands all
   such refinements be nonnegative.  `free_refinement_stability_is_vacuous`
   proves this reading is satisfied by NO weight at all: for every
   two-alternative weight `(a0, a1, q)` there is a coarsening-compatible
   refinement with a strictly negative event (uniform witness: halve
   each alternative, zero the intra fibers, put `−t` with
   `t = (a0+a1)/2 + 1` on one mixed pair and distribute the rest).
   Even additive, Born-representable weights fail it.

The third route (spectator extensions) cannot help either: direct-sum
and product composites preserve event-nonnegativity componentwise
(arithmetic observation, not formalized here), so no spectator ever
realizes a signed direction as a negative event.

**Consequence.**  The bridge from facticity stability to the visibility
cap has no construction at either reading.  What is missing is the
WITNESS-ADMISSIBILITY RULE: which refinements count as facticization
witnesses.  Any rule that does the job must admit refinements that kill
super-visibility weights while excluding refinements that kill additive
weights — and the two are separated by exactly the Cauchy-Schwarz
bound, so the rule must encode the bound it was supposed to derive.
The super-visibility countermodel of `BornConeGap` therefore survives
every currently formalizable reading of the F-family, and the
representation bridge remains un-closable from the current base.
-/

section disguise

/-- **The disguise**: PSD of the 2×2 comparison form is exactly the cap.
The forward direction is `psd_conditions` from
`V7PositiveGeometryGeneral`; the backward direction completes the
square. -/
theorem form_psd_iff_cap (G : CompForm2) :
    (∀ v : Dir2, quadForm G v ≥ 0) ↔
      (G.a ≥ 0 ∧ G.c ≥ 0 ∧ G.a * G.c ≥ G.b * G.b) := by
  constructor
  · exact psd_conditions G
  · rintro ⟨ha, hc, hdet⟩ v
    by_cases hap : G.a > 0
    · have key : G.a * quadForm G v
          = (G.a * v.x + G.b * v.y) ^ 2
            + (G.a * G.c - G.b * G.b) * v.y ^ 2 := by
        unfold quadForm
        ring
      have hs : (G.a * v.x + G.b * v.y) ^ 2 ≥ 0 := sq_nonneg _
      have hy : v.y ^ 2 ≥ 0 := sq_nonneg _
      nlinarith
    · have haz : G.a = 0 := by linarith
      have hb : G.b = 0 := by nlinarith
      unfold quadForm
      rw [haz, hb]
      nlinarith [sq_nonneg v.y]

end disguise

section refinements

/-- Weight of an event in a four-cell refined context: singleton
coefficients `a'` and pair coefficients `q'` summed over ordered pairs
(the convention of `TwoDecomposable`; symmetric `q'` counts each pair
twice). -/
def refinedWeight (a' : Fin 4 → ℝ) (q' : Fin 4 → Fin 4 → ℝ)
    (S : Finset (Fin 4)) : ℝ :=
  (∑ i ∈ S, a' i) + ∑ i ∈ S, ∑ j ∈ S, if i = j then 0 else q' i j

/-- The refinement coarsens back to the two-alternative weight
`(a0, a1, q)`: each half-fiber reproduces its alternative, and the
total reproduces the merged weight. -/
def CoarsensTo (a' : Fin 4 → ℝ) (q' : Fin 4 → Fin 4 → ℝ)
    (a0 a1 q : ℝ) : Prop :=
  refinedWeight a' q' {0, 1} = a0 ∧
    refinedWeight a' q' {2, 3} = a1 ∧
    refinedWeight a' q' Finset.univ = a0 + a1 + q

/-- **The vacuous reading**: no event-nonnegative two-alternative
weight whatsoever is stable under freely generated refinements.  For
every `(a0, a1, q)` with `0 ≤ a0`, `0 ≤ a1` there is a
coarsening-compatible refinement with a strictly negative event. -/
theorem free_refinement_stability_is_vacuous (a0 a1 q : ℝ)
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) :
    ∃ a' : Fin 4 → ℝ, ∃ q' : Fin 4 → Fin 4 → ℝ,
      CoarsensTo a' q' a0 a1 q ∧ ∃ S : Finset (Fin 4),
        refinedWeight a' q' S < 0 := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (a0 + a1) / 2 + 1 := ⟨_, rfl⟩
  refine ⟨![a0 / 2, a0 / 2, a1 / 2, a1 / 2],
    !![0, 0, (q + 2 * t) / 6, -t;
       0, 0, (q + 2 * t) / 6, (q + 2 * t) / 6;
       (q + 2 * t) / 6, (q + 2 * t) / 6, 0, 0;
       -t, (q + 2 * t) / 6, 0, 0],
    ⟨?_, ?_, ?_⟩, {(0 : Fin 4), 3}, ?_⟩
  · simp [refinedWeight]
  · simp [refinedWeight]
  · simp [refinedWeight, Fin.sum_univ_four]
    field_simp
    ring
  · simp [refinedWeight]
    linarith [ht, ha0, ha1]

end refinements

end QMClosure
end IDT


