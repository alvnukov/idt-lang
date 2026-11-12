import Proofs.QMClosure.FiniteRejoinReversibleQuadraticReadout
import Mathlib.Data.NNReal.Basic

/-!
# Nonzero model and premise controls for finite-rejoin quadratic readout

The canonical complex model satisfies the complete finite-rejoin contract and
has a normalized nonzero norm-square readout. Its computations provide a
consistency witness for the conditional reconstruction theorem.

Separate readouts on this same gate show the roles of vacuum normalization
and global nonnegativity. A nonnegative-real model satisfies the remaining
period-one laws while its diagonal two-port map fails surjectivity and its
original monoid lacks an inverse for one.

These controls concern the exact listed algebraic contracts. They supply no
physical-origin, accessibility, or full-QM conclusion. The null-sector
full-carrier fourth-power example is outside this source's scope.
-/

noncomputable section

namespace IDT.QMClosure.FiniteRejoinQuadraticReadoutControls

open FiniteRejoinReversibleQuadraticReadout
open scoped NNReal

namespace CanonicalComplex

/-- The visible canonical first-branch coefficient. -/
def alpha : ℂ := ⟨1 / 2, 1 / 2⟩

/-- The visible canonical second-branch coefficient. -/
def beta : ℂ := ⟨1 / 2, -(1 / 2)⟩

/-- Multiplication by a fixed complex number as an additive endomorphism. -/
def scalarEnd (c : ℂ) : AddMonoid.End ℂ where
  toFun z := c * z
  map_zero' := mul_zero c
  map_add' z w := mul_add c z w

def A : AddMonoid.End ℂ := scalarEnd alpha

def B : AddMonoid.End ℂ := scalarEnd beta

theorem coefficient_laws : alpha + beta = 1 ∧
    alpha * alpha + beta * beta = 0 ∧ alpha * beta + beta * alpha = 1 := by
  constructor
  · apply Complex.ext <;> norm_num [alpha, beta]
  constructor <;> apply Complex.ext <;>
    norm_num [alpha, beta, Complex.mul_re, Complex.mul_im]

theorem coefficient_fourth : alpha ^ 4 = beta ^ 4 := by
  apply Complex.ext <;>
    norm_num [alpha, beta, pow_succ, Complex.mul_re, Complex.mul_im]

theorem transparent : A + B = 1 := by
  apply DFunLike.ext
  intro z
  change alpha * z + beta * z = z
  rw [← add_mul, coefficient_laws.1, one_mul]

theorem rejoin : A ^ 4 = B ^ 4 := by
  apply DFunLike.ext
  intro z
  change alpha * (alpha * (alpha * (alpha * z))) =
    beta * (beta * (beta * (beta * z)))
  calc
    alpha * (alpha * (alpha * (alpha * z))) = alpha ^ 4 * z := by ring
    _ = beta ^ 4 * z := by rw [coefficient_fourth]
    _ = beta * (beta * (beta * (beta * z))) := by ring

/-- The complete symmetric two-port operation used by the witness. -/
def F : (ℂ × ℂ) → (ℂ × ℂ) := twoPort A B

theorem square (p : ℂ × ℂ) : F (F p) = p.swap := by
  apply Prod.ext
  · change alpha * (alpha * p.1 + beta * p.2) +
        beta * (beta * p.1 + alpha * p.2) = p.2
    calc
      _ = (alpha * alpha + beta * beta) * p.1 +
          (alpha * beta + beta * alpha) * p.2 := by ring
      _ = p.2 := by rw [coefficient_laws.2.1, coefficient_laws.2.2]; simp
  · change beta * (alpha * p.1 + beta * p.2) +
        alpha * (beta * p.1 + alpha * p.2) = p.1
    calc
      _ = (alpha * beta + beta * alpha) * p.1 +
          (alpha * alpha + beta * beta) * p.2 := by ring
      _ = p.1 := by rw [coefficient_laws.2.1, coefficient_laws.2.2]; simp

theorem fourth (p : ℂ × ℂ) : F (F (F (F p))) = p := by
  calc
    F (F (F (F p))) = (F (F p)).swap := square (F (F p))
    _ = p.swap.swap := congrArg Prod.swap (square p)
    _ = p := by cases p; rfl

theorem onto : Function.Surjective F := by
  intro p
  exact ⟨F (F (F p)), fourth p⟩

/-- Every algebraic gate premise is present in this concrete period-four model. -/
def gate : Gate ℂ where
  a := A
  b := B
  period := 4
  period_pos := by decide
  transparent := transparent
  rejoin := rejoin
  onto := onto

/-- Full two-input conservation is checked by complex coordinate arithmetic. -/
theorem norm_conservation (x y : ℂ) :
    Complex.normSq (A x + B y) + Complex.normSq (B x + A y) =
      Complex.normSq x + Complex.normSq y := by
  change Complex.normSq (alpha * x + beta * y) +
    Complex.normSq (beta * x + alpha * y) = Complex.normSq x + Complex.normSq y
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im]
  dsimp only [alpha, beta]
  ring

/-- Simultaneous concrete satisfaction of the complete original contract. -/
theorem complete_nonzero_contract :
    A + B = 1 ∧ A ^ 4 = B ^ 4 ∧ Function.Surjective (twoPort A B) ∧
    Complex.normSq 0 = 0 ∧ (∀ z, 0 ≤ Complex.normSq z) ∧
    (∀ x y, Complex.normSq (A x + B y) + Complex.normSq (B x + A y) =
      Complex.normSq x + Complex.normSq y) ∧ Complex.normSq 1 = 1 :=
  ⟨transparent, rejoin, onto, Complex.normSq_zero, Complex.normSq_nonneg,
    norm_conservation, Complex.normSq_one⟩

/-- The new universal theorem accepts the nonzero concrete model. -/
theorem reconstructed_nonzero_model : Reconstruction gate Complex.normSq :=
  reconstruct gate Complex.normSq Complex.normSq_zero Complex.normSq_nonneg
    norm_conservation

theorem reconstructed_normalized_nonzero :
    Reconstruction gate Complex.normSq ∧ Complex.normSq 1 = 1 :=
  ⟨reconstructed_nonzero_model, Complex.normSq_one⟩

end CanonicalComplex

namespace VacuumControl

open CanonicalComplex

def W (_z : ℂ) : ℝ := 1

theorem nonnegative (z : ℂ) : 0 ≤ W z := by norm_num [W]

theorem conservation (x y : ℂ) :
    W (gate.a x + gate.b y) + W (gate.b x + gate.a y) = W x + W y := rfl

theorem vacuum_failure : W 0 ≠ 0 := by norm_num [W]

/-- Exact defect at the original carrier inputs zero and zero. -/
theorem parallelogram_failure :
    W ((0 : ℂ) + 0) + W ((0 : ℂ) - 0) ≠ 2 * W 0 + 2 * W 0 := by
  norm_num [W]

/-- Every gate law and nonnegativity remain available for this readout. -/
theorem control_contract :
    (∀ z, 0 ≤ W z) ∧
    (∀ x y, W (gate.a x + gate.b y) + W (gate.b x + gate.a y) = W x + W y) ∧
    W 0 ≠ 0 ∧ W ((0 : ℂ) + 0) + W ((0 : ℂ) - 0) ≠ 2 * W 0 + 2 * W 0 :=
  ⟨nonnegative, conservation, vacuum_failure, parallelogram_failure⟩

end VacuumControl

namespace PositivityControl

open CanonicalComplex

def W (z : ℂ) : ℝ := z.re

theorem vacuum : W 0 = 0 := rfl

theorem conservation (x y : ℂ) :
    W (gate.a x + gate.b y) + W (gate.b x + gate.a y) = W x + W y := by
  change (alpha * x + beta * y).re + (beta * x + alpha * y).re = x.re + y.re
  simp only [Complex.add_re, Complex.mul_re]
  dsimp only [alpha, beta]
  ring

theorem nonnegative_failure : ¬ ∀ z, 0 ≤ W z := by
  intro nonnegative
  have h := nonnegative (-1)
  norm_num [W] at h

/-- Exact defect at the original carrier inputs one and one. -/
theorem parallelogram_failure :
    W ((1 : ℂ) + 1) + W ((1 : ℂ) - 1) ≠ 2 * W 1 + 2 * W 1 := by
  norm_num [W]

/-- The first native branch already violates a half response at i. -/
theorem native_half_failure : W (gate.a Complex.I) ≠ W Complex.I / 2 := by
  change (alpha * Complex.I).re ≠ Complex.I.re / 2
  norm_num [alpha, Complex.mul_re]

theorem control_contract :
    W 0 = 0 ∧
    (∀ x y, W (gate.a x + gate.b y) + W (gate.b x + gate.a y) = W x + W y) ∧
    (¬ ∀ z, 0 ≤ W z) ∧
    (W ((1 : ℂ) + 1) + W ((1 : ℂ) - 1) ≠ 2 * W 1 + 2 * W 1) ∧
    W (gate.a Complex.I) ≠ W Complex.I / 2 :=
  ⟨vacuum, conservation, nonnegative_failure, parallelogram_failure, native_half_failure⟩

end PositivityControl

namespace SurjectivityControl

/-- Both branches divide the nonnegative-real preparation by two. -/
def halfEnd : AddMonoid.End ℝ≥0 where
  toFun x := x / 2
  map_zero' := by simp
  map_add' x y := add_div x y 2

def W (x : ℝ≥0) : ℝ := x

theorem halves (x : ℝ≥0) : halfEnd x + halfEnd x = x := by
  change x / 2 + x / 2 = x
  apply NNReal.coe_injective
  simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_two]
  ring

theorem transparent : halfEnd + halfEnd = 1 := by
  apply DFunLike.ext
  intro x
  exact halves x

theorem rejoin : halfEnd ^ 1 = halfEnd ^ 1 := rfl

theorem vacuum : W 0 = 0 := rfl

theorem nonnegative (x : ℝ≥0) : 0 ≤ W x := NNReal.coe_nonneg x

theorem conservation (x y : ℝ≥0) :
    W (halfEnd x + halfEnd y) + W (halfEnd x + halfEnd y) = W x + W y := by
  change ((x / 2 + y / 2 : ℝ≥0) : ℝ) +
    ((x / 2 + y / 2 : ℝ≥0) : ℝ) = (x : ℝ) + (y : ℝ)
  simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_two]
  ring

/-- The diagonal output map misses this exact carrier pair. -/
theorem target_unreachable :
    ¬ ∃ p : ℝ≥0 × ℝ≥0, twoPort halfEnd halfEnd p = (1, 0) := by
  rintro ⟨⟨x, y⟩, h⟩
  have hfirst : halfEnd x + halfEnd y = 1 := congrArg Prod.fst h
  have hsecond : halfEnd x + halfEnd y = 0 := congrArg Prod.snd h
  have hbad : (1 : ℝ≥0) = 0 := hfirst.symm.trans hsecond
  norm_num at hbad

theorem not_surjective : ¬ Function.Surjective (twoPort halfEnd halfEnd) := by
  intro onto
  exact target_unreachable (onto (1, 0))

/-- The supplied original monoid lacks an additive inverse for one. -/
theorem one_has_no_additive_inverse : ¬ ∃ q : ℝ≥0, 1 + q = 0 := by
  rintro ⟨q, h⟩
  have hr := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
  simp only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_zero] at hr
  have hq := NNReal.coe_nonneg q
  linarith

theorem double_gain_failure :
    W ((1 : ℝ≥0) + 1) = 2 ∧ W ((1 : ℝ≥0) + 1) ≠ 4 * W 1 := by
  norm_num [W]

/-- All listed original premises except complete-map surjectivity hold. -/
theorem incomplete_contract :
    (0 : ℕ) < 1 ∧ halfEnd + halfEnd = 1 ∧ halfEnd ^ 1 = halfEnd ^ 1 ∧
    W 0 = 0 ∧ (∀ x, 0 ≤ W x) ∧
    (∀ x y, W (halfEnd x + halfEnd y) + W (halfEnd x + halfEnd y) = W x + W y) ∧
    ¬ Function.Surjective (twoPort halfEnd halfEnd) :=
  ⟨by decide, transparent, rejoin, vacuum, nonnegative, conservation, not_surjective⟩

end SurjectivityControl

end IDT.QMClosure.FiniteRejoinQuadraticReadoutControls
