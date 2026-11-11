import Proofs.QMClosure.FourthRejoinIdempotentCore

/-!
# Three fourth-rejoin controls

The project import is the Mathlib-only core. The models are explicit coefficient
algebras. All inverse-context certificates use their full semiring grammar.
They supply no physical interpretation or available experimental operation.
-/

noncomputable section

namespace IDT.FourthRejoinIdempotent.Controls

/-- Standard complex destructive coefficient (1+i)/2 in Cartesian form. -/
def complexA : ℂ := ⟨1 / 2, 1 / 2⟩

/-- The conjugate coefficient (1-i)/2. -/
def complexB : ℂ := ⟨1 / 2, -(1 / 2)⟩

theorem complexA_standard : complexA = (1 + Complex.I) / 2 := by
  apply Complex.ext <;>
    norm_num [complexA, Complex.div_re, Complex.div_im, Complex.normSq_apply]

theorem complexB_standard : complexB = (1 - Complex.I) / 2 := by
  apply Complex.ext <;>
    norm_num [complexB, Complex.div_re, Complex.div_im, Complex.normSq_apply]

theorem complex_contract : Contract complexA complexB := by
  refine ⟨Commute.all _ _, ?_, ?_⟩
  · apply Complex.ext <;> norm_num [complexA, complexB]
  · apply Complex.ext <;>
      norm_num [complexA, complexB, pow_succ, Complex.mul_re, Complex.mul_im]

theorem complex_defect : defect complexA complexB = 0 := by
  apply Complex.ext <;>
    norm_num [defect, complexA, complexB, pow_succ, Complex.mul_re, Complex.mul_im]

theorem complex_sector : sector complexA complexB = 0 :=
  (sector_eq_zero_iff complex_contract).mpr complex_defect

theorem complex_pair_ne : complexA ≠ complexB := by
  intro hab
  have hi := congrArg Complex.im hab
  norm_num [complexA, complexB] at hi

/-- Nontriviality belongs to the full complex semiring. -/
theorem complex_nontrivial : (0 : ℂ) ≠ 1 := zero_ne_one

/-- Every operation in the finite certificate is interpreted in ℂ. -/
theorem complex_inverse_contexts : InverseContexts complexA complexB :=
  inverse_contexts complex_contract

/-- The destructive words reduce to the expected pair inverses and return two. -/
theorem complex_inverse_words :
    (2 : ℂ) * complexB + sector complexA complexB = (2 : ℂ) * complexB ∧
      (2 : ℂ) * complexA + sector complexA complexB = (2 : ℂ) * complexA ∧
      (2 : ℂ) + (2 : ℂ) * sector complexA complexB = (2 : ℂ) :=
  destructive_inverse_words complex_defect

/-- Equal real half coefficients give the classical alternative. -/
def realA : ℝ := 1 / 2

def realB : ℝ := 1 / 2

theorem real_contract : Contract realA realB := by
  refine ⟨Commute.all _ _, ?_, ?_⟩
  · norm_num [realA, realB]
  · rfl

theorem real_pair_eq : realA = realB := rfl

theorem real_defect : defect realA realB = (1 / 2 : ℝ) := by
  norm_num [defect, realA, realB]

theorem real_defect_ne_zero : defect realA realB ≠ 0 := by
  rw [real_defect]
  norm_num

theorem real_sector : sector realA realB = 1 :=
  (sector_eq_one_iff real_contract).mpr real_pair_eq

/-- Nontriviality belongs to the full real semiring. -/
theorem real_nontrivial : (0 : ℝ) ≠ 1 := zero_ne_one

theorem real_inverse_contexts : InverseContexts realA realB :=
  inverse_contexts real_contract

/-- The two pair inverses equal two and the classical cross return equals four. -/
theorem real_inverse_words :
    (2 : ℝ) * realB + sector realA realB = 2 ∧
      (2 : ℝ) * realA + sector realA realB = 2 ∧
      (2 : ℝ) + (2 : ℝ) * sector realA realB = 4 := by
  rw [real_sector]
  norm_num [realA, realB]

/-- A direct product realizes both alternatives in one coefficient algebra. -/
def mixedA : ℂ × ℝ := (complexA, realA)

def mixedB : ℂ × ℝ := (complexB, realB)

theorem mixed_contract : Contract mixedA mixedB := by
  refine ⟨Commute.all _ _, ?_, ?_⟩
  · apply Prod.ext
    · exact complex_contract.sum
    · exact real_contract.sum
  · apply Prod.ext
    · exact complex_contract.fourthRejoin
    · exact real_contract.fourthRejoin

theorem mixed_defect : defect mixedA mixedB = (0, (1 / 2 : ℝ)) := by
  apply Prod.ext
  · exact complex_defect
  · exact real_defect

theorem mixed_sector : sector mixedA mixedB = (0, (1 : ℝ)) := by
  rw [sector, mixed_defect]
  apply Prod.ext
  · norm_num
  · norm_num

theorem mixed_pair_ne : mixedA ≠ mixedB := by
  intro hab
  exact complex_pair_ne (congrArg Prod.fst hab)

theorem mixed_defect_ne_zero : defect mixedA mixedB ≠ 0 := by
  intro hT
  have hs := congrArg Prod.snd hT
  rw [mixed_defect] at hs
  norm_num at hs

theorem mixed_sector_ne_zero : sector mixedA mixedB ≠ 0 := by
  intro he
  have hs := congrArg Prod.snd he
  rw [mixed_sector] at hs
  norm_num at hs

theorem mixed_sector_ne_one : sector mixedA mixedB ≠ 1 := by
  intro he
  have hf := congrArg Prod.fst he
  rw [mixed_sector] at hf
  norm_num at hf

/-- Nontriviality belongs to the full product semiring. -/
theorem mixed_nontrivial : (0 : ℂ × ℝ) ≠ 1 := zero_ne_one

/-- The mixed alternative realizes the full nontrivial-idempotent conclusion. -/
theorem mixed_idempotent :
    sector mixedA mixedB * sector mixedA mixedB = sector mixedA mixedB ∧
      sector mixedA mixedB ≠ 0 ∧ sector mixedA mixedB ≠ 1 :=
  nontrivial_sector mixed_contract mixed_pair_ne mixed_defect_ne_zero

theorem mixed_inverse_contexts : InverseContexts mixedA mixedB :=
  inverse_contexts mixed_contract

/-- Corrected mixed inverse words retain the real-sector contribution. -/
theorem mixed_inverse_words :
    (2 : ℂ × ℝ) * mixedB + sector mixedA mixedB =
        ((2 : ℂ) * complexB, (2 : ℝ)) ∧
      (2 : ℂ × ℝ) * mixedA + sector mixedA mixedB =
        ((2 : ℂ) * complexA, (2 : ℝ)) ∧
      (2 : ℂ × ℝ) + (2 : ℂ × ℝ) * sector mixedA mixedB =
        ((2 : ℂ), (4 : ℝ)) := by
  rw [mixed_sector]
  constructor
  · apply Prod.ext
    · simp [mixedB]
    · norm_num [mixedB, realB]
  · constructor
    · apply Prod.ext
      · simp [mixedA]
      · norm_num [mixedA, realA]
    · apply Prod.ext <;> norm_num

/-- The generated inverse of natural two evaluates to one half in both factors. -/
theorem mixed_two_inverse_word :
    mixedA * mixedB + (defect mixedA mixedB) ^ 2 =
      ((1 / 2 : ℂ), (1 / 2 : ℝ)) := by
  rw [mixed_defect]
  apply Prod.ext
  · apply Complex.ext <;>
      norm_num [mixedA, mixedB, complexA, complexB,
        Complex.mul_re, Complex.mul_im]
  · norm_num [mixedA, mixedB, realA, realB]

/-- Global coefficient purity genuinely fails in the mixed algebra. -/
theorem mixed_coefficient_purity_fails :
    ¬ CoefficientIdempotentPurity (ℂ × ℝ) := by
  intro hpure
  rcases hpure (sector mixedA mixedB) (sector_idempotent mixed_contract) with he | he
  · exact mixed_sector_ne_zero he
  · exact mixed_sector_ne_one he

end IDT.FourthRejoinIdempotent.Controls
