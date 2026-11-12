import Proofs.QMClosure.PauliOrientationObstruction

namespace IDT.QMClosure.PauliOrientationCompletion

open PauliOrientationObstruction PauliOrientationObstruction.Pauli

/-!
Finite completion of the supplied four-sign table classification. The triangle
uses exactly the previously supplied ordered-pair gates and product readouts.
The finite positivity characterization below concerns the two supplied two-wire
test families and this one three-wire circuit. It establishes no positivity
claim for every state in either surviving table's generated grammar.
-/

/-- Chronological H₂, G₂₁, G₁₃, G₂₁, G₁₃, G₂₃ for a supplied sign table.
Wire indices in the implementation are zero-based. -/
def triangle (s : Signs) : State3 :=
  gate3 s 1 2 (gate3 s 0 2 (gate3 s 1 0
    (gate3 s 0 2 (gate3 s 1 0 (hSecond zeroThree)))))

/-- Binary X₂/Z₃ product readout, with the first wire ignored. -/
def triangleReadout (s : Signs) (u v : Bool) : ℚ :=
  productReadout2 (fun w => triangle s (I, w.1, w.2)) X Z u v

/-- The four supplied binary X₂/Z₃ events on this single triangle circuit. -/
def TrianglePositive (s : Signs) : Prop :=
  ∀ u v : Bool, 0 ≤ triangleReadout s u v

instance (s : Signs) : Decidable (TrianglePositive s) :=
  inferInstanceAs (Decidable (∀ u v : Bool, 0 ≤ triangleReadout s u v))

theorem triangle_mirror_eq : triangle mirror = mirrorTriangle := rfl

theorem triangle_readout_true_true (s : Signs) :
    triangleReadout s true true = negativeTriangleReadout (triangle s) := rfl

/-- Both residual mirror tables produce the same negative product event. -/
theorem mirrorZ_triangle_negative :
    negativeTriangleReadout (triangle mirrorZ) = -1/2 := by
  decide +kernel

theorem mirror_triangle_negative :
    negativeTriangleReadout (triangle mirror) = -1/2 := by
  exact PauliOrientationObstruction.mirror_triangle_negative

theorem ordinary_triangle_negative_event :
    negativeTriangleReadout (triangle ordinary) = 0 := by
  decide +kernel

theorem ordinaryZ_triangle_negative_event :
    negativeTriangleReadout (triangle ordinaryZ) = 0 := by
  decide +kernel

theorem ordinary_triangle_positive : TrianglePositive ordinary := by
  decide +kernel

theorem ordinaryZ_triangle_positive : TrianglePositive ordinaryZ := by
  decide +kernel

theorem mirror_triangle_not_positive : ¬ TrianglePositive mirror := by
  intro h
  have hp := h true true
  rw [triangle_readout_true_true, mirror_triangle_negative] at hp
  norm_num at hp

theorem mirrorZ_triangle_not_positive : ¬ TrianglePositive mirrorZ := by
  intro h
  have hp := h true true
  rw [triangle_readout_true_true, mirrorZ_triangle_negative] at hp
  norm_num at hp

/-- The additional triangle test removes both mirrors from the four previously
classified choices. Sufficiency here is limited to the stated finite tests. -/
theorem tested_positive_and_triangle_positive_iff (s : Signs) :
    TestedPositive s ∧ TrianglePositive s ↔ s = ordinary ∨ s = ordinaryZ := by
  constructor
  · rintro ⟨ht, hp⟩
    rcases (tested_positive_iff_four_choices s).mp ht with ho | hoZ | hm | hmZ
    · exact Or.inl ho
    · exact Or.inr hoZ
    · subst s
      exact False.elim (mirror_triangle_not_positive hp)
    · subst s
      exact False.elim (mirrorZ_triangle_not_positive hp)
  · rintro (rfl | rfl)
    · exact ⟨(tested_positive_iff_four_choices ordinary).mpr (Or.inl rfl),
        ordinary_triangle_positive⟩
    · exact ⟨(tested_positive_iff_four_choices ordinaryZ).mpr
          (Or.inr (Or.inl rfl)), ordinaryZ_triangle_positive⟩

/-- Reachability under precisely the supplied initial state, H₂ and distinct
ordered-pair gates, with the sign table held fixed through the entire circuit. -/
inductive Generated (s : Signs) : State3 → Prop
  | initial : Generated s zeroThree
  | hSecond {r} : Generated s r → Generated s (hSecond r)
  | pair {r} (i j : Fin 3) :
      i ≠ j → Generated s r → Generated s (gate3 s i j r)

theorem triangle_generated (s : Signs) : Generated s (triangle s) := by
  apply Generated.pair 1 2 (by decide +kernel)
  apply Generated.pair 0 2 (by decide +kernel)
  apply Generated.pair 1 0 (by decide +kernel)
  apply Generated.pair 0 2 (by decide +kernel)
  apply Generated.pair 1 0 (by decide +kernel)
  exact Generated.hSecond Generated.initial

/-- Nonnegativity of the single specified product event on every generated
state. This is a hypothesis on the supplied grammar. -/
def AllGeneratedReadoutNonnegative (s : Signs) : Prop :=
  ∀ r : State3, Generated s r → 0 ≤ negativeTriangleReadout r

theorem mirror_generated_nonnegativity_impossible :
    ¬ AllGeneratedReadoutNonnegative mirror := by
  intro h
  have hp := h (triangle mirror) (triangle_generated mirror)
  rw [mirror_triangle_negative] at hp
  norm_num at hp

theorem mirrorZ_generated_nonnegativity_impossible :
    ¬ AllGeneratedReadoutNonnegative mirrorZ := by
  intro h
  have hp := h (triangle mirrorZ) (triangle_generated mirrorZ)
  rw [mirrorZ_triangle_negative] at hp
  norm_num at hp

/-- Necessary orientation choice if both the supplied two-wire tests and the
all-generated specified-event positivity hypothesis are imposed. -/
theorem tested_and_generated_nonnegativity_forces_ordinary (s : Signs)
    (ht : TestedPositive s) (hg : AllGeneratedReadoutNonnegative s) :
    s = ordinary ∨ s = ordinaryZ := by
  rcases (tested_positive_iff_four_choices s).mp ht with ho | hoZ | hm | hmZ
  · exact Or.inl ho
  · exact Or.inr hoZ
  · subst s
    exact False.elim (mirror_generated_nonnegativity_impossible hg)
  · subst s
    exact False.elim (mirrorZ_generated_nonnegativity_impossible hg)

end IDT.QMClosure.PauliOrientationCompletion
