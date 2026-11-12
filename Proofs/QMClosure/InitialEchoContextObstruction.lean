import Proofs.QMClosure.TransparentFourthReflectionEcho
import Proofs.QMClosure.InitialEchoCoordinates
import Mathlib.Data.ZMod.Basic

/-!
# Two-point obstruction for finite arithmetic expressions on the initial carrier

The expression language contains an input, fixed carrier constants, addition,
and multiplication. Its syntax permits arbitrarily many occurrences of the
input. Each expression preserves every fibre of every semiring homomorphism.
One homomorphism to ZMod 5 then separates the desired outputs at two inputs
whose images coincide. This yields two-point and global exact-output
obstructions for the canonical generator swap and algebraic echo.

The auxiliary norm-square control records the observational scope precisely.
Squaring matches the echo's norm-square at every input. Adding the fixed
reference one separates their norm-square responses at the generator a.

Physical operation availability, unknown-input semantics, and the choice of
response-comparison contexts are recorded as open data below. All theorem
conclusions refer to the declared finite expression language and initial
semiring. The ZMod homomorphism is an algebraic proof witness.
-/

namespace IDT.QMClosure.InitialEchoContextObstruction

noncomputable section

open TransparentFourthInitialHistoryPresentation
open TransparentFourthReflectionEcho

/-- Finite arithmetic syntax with fixed carrier constants and repeated input use. -/
inductive Expr (S : Type*) where
  | input : Expr S
  | const (value : S) : Expr S
  | add (left right : Expr S) : Expr S
  | mul (left right : Expr S) : Expr S

namespace Expr

variable {S T : Type*} [Semiring S] [Semiring T]

/-- Every constant belongs to the chosen expression before evaluation. -/
def eval : Expr S → S → S
  | .input, p => p
  | .const value, _ => value
  | .add left right, p => eval left p + eval right p
  | .mul left right, p => eval left p * eval right p

/-- Structural induction covers every finite nesting and input multiplicity. -/
theorem eval_preserves_fibres (f : S →+* T) (expression : Expr S)
    {p q : S} (h : f p = f q) :
    f (expression.eval p) = f (expression.eval q) := by
  induction expression with
  | input => exact h
  | const value => rfl
  | add left right hleft hright =>
      simpa only [eval, map_add, hleft, hright]
  | mul left right hleft hright =>
      simpa only [eval, map_mul, hleft, hright]

/-- A prescribed single input/output pair admits a fixed constant expression. -/
theorem one_point_representation (p target : S) :
    ∃ expression : Expr S, expression.eval p = target :=
  ⟨.const target, rfl⟩

end Expr

/-- The universal presentation map at the two solutions 2 and 4 modulo five. -/
def χ : Presentation →+* ZMod 5 :=
  TransparentFourthInitialHistoryPresentation.eval (2 : ZMod 5) 4
    (by decide) (by decide)

@[simp] theorem chi_a : χ a = 2 := by simp [χ]

@[simp] theorem chi_b : χ b = 4 := by simp [χ]

@[simp] theorem chi_two : χ (2 : Presentation) = 2 := by
  simp only [map_ofNat]

/-- These are two inputs in one algebraic fibre. -/
theorem two_a_same_fibre : χ (2 : Presentation) = χ a := by
  rw [chi_two, chi_a]

@[simp] theorem chi_J_two : χ (J (2 : Presentation)) = 2 := by
  simp only [map_ofNat]

@[simp] theorem chi_J_a : χ (J a) = 4 := by
  rw [J_a, chi_b]

@[simp] theorem chi_echo_two : χ (echo (2 : Presentation)) = 4 := by
  rw [echo, map_mul, chi_two, chi_J_two]
  norm_num

@[simp] theorem chi_echo_a : χ (echo a) = 3 := by
  rw [echo, map_mul, chi_a, chi_J_a]
  decide

theorem J_outputs_distinct : J (2 : Presentation) ≠ J a := by
  intro h
  have hh := congrArg χ h
  rw [chi_J_two, chi_J_a] at hh
  exact (by decide : (2 : ZMod 5) ≠ 4) hh

theorem echo_outputs_distinct : echo (2 : Presentation) ≠ echo a := by
  intro h
  have hh := congrArg χ h
  rw [chi_echo_two, chi_echo_a] at hh
  exact (by decide : (4 : ZMod 5) ≠ 3) hh

/-- The obstruction uses two distinct inputs of the fixed language. -/
theorem two_ne_a : (2 : Presentation) ≠ a := by
  intro h
  exact J_outputs_distinct (congrArg J h)

theorem no_two_point_J (expression : Expr Presentation) :
    ¬ (expression.eval 2 = J 2 ∧ expression.eval a = J a) := by
  rintro ⟨htwo, ha⟩
  have h := Expr.eval_preserves_fibres χ expression two_a_same_fibre
  rw [htwo, ha, chi_J_two, chi_J_a] at h
  exact (by decide : (2 : ZMod 5) ≠ 4) h

theorem no_two_point_echo (expression : Expr Presentation) :
    ¬ (expression.eval 2 = echo 2 ∧ expression.eval a = echo a) := by
  rintro ⟨htwo, ha⟩
  have h := Expr.eval_preserves_fibres χ expression two_a_same_fibre
  rw [htwo, ha, chi_echo_two, chi_echo_a] at h
  exact (by decide : (4 : ZMod 5) ≠ 3) h

theorem no_global_J_expression :
    ¬ ∃ expression : Expr Presentation, ∀ p, expression.eval p = J p := by
  rintro ⟨expression, h⟩
  exact no_two_point_J expression ⟨h 2, h a⟩

theorem no_global_echo_expression :
    ¬ ∃ expression : Expr Presentation, ∀ p, expression.eval p = echo p := by
  rintro ⟨expression, h⟩
  exact no_two_point_echo expression ⟨h 2, h a⟩

/-- Each singleton test of the swap admits a preselected fixed constant. -/
theorem one_point_J (p : Presentation) :
    ∃ expression : Expr Presentation, expression.eval p = J p :=
  Expr.one_point_representation p (J p)

/-- Each singleton test of the echo admits a preselected fixed constant. -/
theorem one_point_echo (p : Presentation) :
    ∃ expression : Expr Presentation, expression.eval p = echo p :=
  Expr.one_point_representation p (echo p)

/-- One expression uses its input twice by multiplication. -/
def squareExpression : Expr Presentation := .mul .input .input

@[simp] theorem eval_squareExpression (p : Presentation) :
    squareExpression.eval p = p * p := rfl

/-- Exact equality of this single norm-square statistic holds for every input. -/
theorem square_matches_echo_normSq (p : Presentation) :
    InitialEchoCoordinates.N (squareExpression.eval p) =
      InitialEchoCoordinates.N (echo p) := by
  change InitialCountGeometry.normSq (p * p) = InitialCountGeometry.normSq (echo p)
  calc
    InitialCountGeometry.normSq (p * p) =
        InitialCountGeometry.normSq p * InitialCountGeometry.normSq p :=
      InitialCountGeometry.normSq_mul p p
    _ = InitialCountGeometry.normSq (echo p) := by
      simpa only [pow_two] using (InitialEchoCoordinates.N_echo p).symm

/-- The fixed reference one distinguishes square from echo at a. -/
theorem reference_square_a_normSq :
    InitialEchoCoordinates.N (1 + squareExpression.eval a) = (5 / 4 : ℝ) := by
  change Complex.normSq
    (TransparentFourthInitialNormalForm.complexEvaluation (1 + a * a)) = _
  rw [map_add, map_one, map_mul, InitialCountGeometry.evaluation_a]
  norm_num [TransparentFourthInitialNormalForm.complexA, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem reference_echo_a_normSq :
    InitialEchoCoordinates.N (1 + echo a) = (9 / 4 : ℝ) := by
  change Complex.normSq
    (TransparentFourthInitialNormalForm.complexEvaluation (1 + echo a)) = _
  rw [echo_a, map_add, map_one, map_mul,
    InitialCountGeometry.evaluation_a, InitialCountGeometry.evaluation_b]
  norm_num [TransparentFourthInitialNormalForm.complexA,
    TransparentFourthInitialNormalForm.complexB, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem fixed_reference_separates_square_echo :
    InitialEchoCoordinates.N (1 + squareExpression.eval a) ≠
      InitialEchoCoordinates.N (1 + echo a) := by
  rw [reference_square_a_normSq, reference_echo_a_normSq]
  norm_num

/-- This algebraic norm-square statistic can exceed one. -/
theorem normSq_two : InitialEchoCoordinates.N (2 : Presentation) = 4 := by
  change Complex.normSq
    (TransparentFourthInitialNormalForm.complexEvaluation (2 : Presentation)) = _
  rw [map_ofNat]
  norm_num [Complex.normSq_apply]

/-- Research questions are data and introduce no theorem premises. -/
structure OpenObligation where
  id : String
  question : String
  deriving DecidableEq, Repr

def openObligations : List OpenObligation := [
  { id := "physical-operation-library"
    question := "Which physically available operations, fixed resources, and input uses are represented by a finite arithmetic expression, and which require a richer language?" },
  { id := "known-recipe-versus-unknown-input"
    question := "What operational contract distinguishes access to a known preparation recipe from receiving an unknown carrier input, and how is generator interchange implemented under each contract?" },
  { id := "response-comparison"
    question := "Which readout and comparison contexts define the intended operational equivalence, and which physical contract relates them to the constructed norm-square coordinate?" }
]

end

end IDT.QMClosure.InitialEchoContextObstruction
