import Proofs.QMClosure.FourthRejoinIdempotentControls

/-!
# An additively cancellative zero-divisor-free semiring with a nontrivial idempotent

The ambient product ring is used to describe a subsemiring and missing elements. The restricted
carrier supplies no additive-inverse operation. The generated-subsemiring
image characterization remains an analytic research note outside these proofs.
-/

noncomputable section

namespace IDT.FourthRejoinIdempotent.Controls

/-- The zero element together with all pairs having positive real coordinate. -/
def positiveSecond : Subsemiring (ℂ × ℝ) where
  carrier := {x | x = 0 ∨ 0 < x.2}
  zero_mem' := Or.inl rfl
  one_mem' := Or.inr (by norm_num)
  add_mem' := by
    intro x y hx hy
    rcases hx with rfl | hx
    · simpa using hy
    rcases hy with rfl | hy
    · simpa using (Or.inr hx : x = 0 ∨ 0 < x.2)
    exact Or.inr (add_pos hx hy)
  mul_mem' := by
    intro x y hx hy
    rcases hx with rfl | hx
    · exact Or.inl (zero_mul y)
    rcases hy with rfl | hy
    · exact Or.inl (mul_zero x)
    exact Or.inr (mul_pos hx hy)

/-- Additive cancellation is inherited through the carrier inclusion. -/
theorem positive_add_right_cancel (x y z : positiveSecond)
    (h : x + z = y + z) : x = y := by
  apply Subtype.ext
  exact add_right_cancel (congrArg (fun t : positiveSecond => t.val) h)

theorem positive_add_left_cancel (x y z : positiveSecond)
    (h : z + x = z + y) : x = y := by
  apply Subtype.ext
  exact add_left_cancel (congrArg (fun t : positiveSecond => t.val) h)

/-- Every nonzero element has a strictly positive second coordinate. -/
theorem positive_second_of_ne_zero (x : positiveSecond) (hx : x ≠ 0) :
    0 < x.val.2 := by
  rcases x.property with hz | hp
  · exact False.elim (hx (Subtype.ext hz))
  · exact hp

/-- The restricted semiring has no nonzero zero-product pair. -/
theorem positive_mul_eq_zero (x y : positiveSecond) (h : x * y = 0) :
    x = 0 ∨ y = 0 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  by_cases hy : y = 0
  · exact Or.inr hy
  have hxy : 0 < x.val.2 * y.val.2 :=
    mul_pos (positive_second_of_ne_zero x hx) (positive_second_of_ne_zero y hy)
  have hz := congrArg (fun t : positiveSecond => t.val.2) h
  change x.val.2 * y.val.2 = 0 at hz
  exact False.elim ((ne_of_gt hxy) hz)

instance positiveNoZeroDivisors : NoZeroDivisors positiveSecond where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro x y h
    exact positive_mul_eq_zero x y h

/-- The mixed coefficients belong to the restricted full semiring grammar. -/
def positiveA : positiveSecond :=
  ⟨mixedA, Or.inr (by norm_num [mixedA, realA])⟩

def positiveB : positiveSecond :=
  ⟨mixedB, Or.inr (by norm_num [mixedB, realB])⟩

theorem positive_contract : Contract positiveA positiveB := by
  refine ⟨?_, ?_, ?_⟩
  · change positiveA * positiveB = positiveB * positiveA
    apply Subtype.ext
    exact mixed_contract.commute.eq
  · apply Subtype.ext
    exact mixed_contract.sum
  · apply Subtype.ext
    exact mixed_contract.fourthRejoin

theorem positive_defect_value :
    (defect positiveA positiveB).val = (0, (1 / 2 : ℝ)) := by
  exact mixed_defect

theorem positive_sector_value :
    (sector positiveA positiveB).val = (0, (1 : ℝ)) := by
  exact mixed_sector

theorem positive_pair_ne : positiveA ≠ positiveB := by
  intro hab
  exact mixed_pair_ne (congrArg (fun x : positiveSecond => x.val) hab)

theorem positive_defect_ne_zero : defect positiveA positiveB ≠ 0 := by
  intro hT
  have hs := congrArg (fun x : positiveSecond => x.val.2) hT
  change (defect positiveA positiveB).val.2 = 0 at hs
  rw [positive_defect_value] at hs
  norm_num at hs

/-- This zero-divisor-free additively cancellative semiring has a nontrivial idempotent. -/
theorem positive_nontrivial_idempotent :
    sector positiveA positiveB * sector positiveA positiveB = sector positiveA positiveB ∧
      sector positiveA positiveB ≠ 0 ∧ sector positiveA positiveB ≠ 1 :=
  nontrivial_sector positive_contract positive_pair_ne positive_defect_ne_zero

/-- All inverse words remain inside the restricted semiring. -/
theorem positive_inverse_contexts : InverseContexts positiveA positiveB :=
  inverse_contexts positive_contract

/-- NoZeroDivisors together with additive cancellation does not imply purity. -/
theorem positive_coefficient_purity_fails :
    ¬ CoefficientIdempotentPurity positiveSecond := by
  intro hpure
  exact positive_defect_ne_zero
    (destructive_of_coefficient_purity positive_contract hpure positive_pair_ne)

/-- The ambient complementary idempotent is absent from the restricted carrier. -/
theorem complementary_pair_absent : ((1 : ℂ), (0 : ℝ)) ∉ positiveSecond := by
  intro hx
  rcases hx with hz | hp
  · have hf := congrArg Prod.fst hz
    norm_num at hf
  · norm_num at hp

/-- The ambient coefficient difference is also absent. -/
theorem difference_pair_absent : (Complex.I, (0 : ℝ)) ∉ positiveSecond := by
  intro hx
  rcases hx with hz | hp
  · have hi := congrArg (fun z : ℂ × ℝ => z.1.im) hz
    norm_num at hi
  · norm_num at hp

/-- Ambient subtraction identifies the missing complement. -/
theorem ambient_complement_value :
    (1 : ℂ × ℝ) - (sector positiveA positiveB).val = ((1 : ℂ), (0 : ℝ)) := by
  rw [positive_sector_value]
  apply Prod.ext <;> norm_num

/-- Ambient subtraction identifies the missing coefficient difference. -/
theorem ambient_difference_value :
    positiveA.val - positiveB.val = (Complex.I, (0 : ℝ)) := by
  apply Prod.ext
  · apply Complex.ext <;> norm_num [positiveA, positiveB, mixedA, mixedB, complexA, complexB]
  · norm_num [positiveA, positiveB, mixedA, mixedB, realA, realB]

/-- The full restricted carrier is nontrivial. -/
theorem positive_nontrivial : (0 : positiveSecond) ≠ 1 := by
  intro h
  have hs := congrArg (fun x : positiveSecond => x.val.2) h
  norm_num at hs

end IDT.FourthRejoinIdempotent.Controls
