import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

/-!
# A dephased controlled countercontrol in real matrix theory

The two-Kraus map preserves positivity and trace after every finite real matrix
reference extension. Both distinguished program states induce the same
noninjective dephasing map. The collision uses positive trace-one states.
This rejects inferred recovery from those fixed-program identities. Physical
atomicity, pure-marginal factorization, and complex reconstruction are separate
obligations.
-/

namespace IDT.QMClosure.DephasedControlledCountercontrol

noncomputable section

open Matrix
open scoped Kronecker

abbrev Q := Matrix (Fin 2) (Fin 2) ℝ
abbrev QQ := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ

/-- A normalized state in the supplied real matrix model. -/
def State {ι : Type*} [Fintype ι] (X : Matrix ι ι ℝ) : Prop :=
  X.PosSemidef ∧ X.trace = 1

def P0 : Q := !![1, 0; 0, 0]
def P1 : Q := !![0, 0; 0, 1]
def Z : Q := P0 - P1

def yPlus : Q := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]
def yMinus : Q := !![1 / 2, -(1 / 2); -(1 / 2), 1 / 2]

@[simp] theorem P0_adjoint : P0ᴴ = P0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P0, conjTranspose_apply]
@[simp] theorem P1_adjoint : P1ᴴ = P1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P1, conjTranspose_apply]
@[simp] theorem Z_adjoint : Zᴴ = Z := by
  rw [Z, conjTranspose_sub, P0_adjoint, P1_adjoint]
@[simp] theorem P0_square : P0 * P0 = P0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P0, mul_apply, Fin.sum_univ_two]
@[simp] theorem P1_square : P1 * P1 = P1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P1, mul_apply, Fin.sum_univ_two]
@[simp] theorem P0_P1 : P0 * P1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P0, P1, mul_apply, Fin.sum_univ_two]
@[simp] theorem P1_P0 : P1 * P0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P0, P1, mul_apply, Fin.sum_univ_two]
@[simp] theorem P0_add_P1 : P0 + P1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P0, P1]
@[simp] theorem Z_square : Z * Z = 1 := by
  simp [Z, mul_sub, sub_mul]

def phase (τ : Q) : Q := Z * τ * Z
def dephase (ρ : Q) : Q := P0 * ρ * P0 + P1 * ρ * P1

/-- Two Kraus operators, with the adjoint explicit. -/
def krausMap {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℝ) : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ where
  toFun X := A * X * Aᴴ + B * X * Bᴴ
  map_add' X Y := by
    simp only [mul_add, add_mul]
    abel
  map_smul' t X := by
    simp only [mul_smul_comm, smul_mul_assoc, smul_add, RingHom.id_apply]

@[simp] theorem krausMap_apply {ι : Type*} [Fintype ι]
    (A B X : Matrix ι ι ℝ) : krausMap A B X = A * X * Aᴴ + B * X * Bᴴ := rfl

theorem kraus_positive {ι : Type*} [Fintype ι]
    (A B X : Matrix ι ι ℝ) (hX : X.PosSemidef) :
    (krausMap A B X).PosSemidef :=
  (hX.mul_mul_conjTranspose_same A).add (hX.mul_mul_conjTranspose_same B)

theorem kraus_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B X : Matrix ι ι ℝ) (h : Aᴴ * A + Bᴴ * B = 1) :
    (krausMap A B X).trace = X.trace := by
  rw [krausMap_apply, trace_add, trace_mul_cycle A X Aᴴ, trace_mul_cycle B X Bᴴ,
    ← trace_add, ← add_mul, h, one_mul]

def K0 : QQ := P0 ⊗ₖ (1 : Q)
def K1 : QQ := P1 ⊗ₖ Z
def controlled : QQ →ₗ[ℝ] QQ := krausMap K0 K1

theorem kraus_normalization : K0ᴴ * K0 + K1ᴴ * K1 = 1 := by
  simp only [K0, K1, conjTranspose_kronecker, P0_adjoint, P1_adjoint, Z_adjoint,
    conjTranspose_one, ← mul_kronecker_mul, P0_square, P1_square, Z_square, one_mul]
  rw [← add_kronecker, P0_add_P1, one_kronecker_one]

theorem controlled_positive (X : QQ) (hX : X.PosSemidef) :
    (controlled X).PosSemidef := kraus_positive K0 K1 X hX

theorem controlled_trace (X : QQ) : (controlled X).trace = X.trace :=
  kraus_trace K0 K1 X kraus_normalization

section Reference

variable (r : Type*) [Fintype r] [DecidableEq r]

/-- The actual identity-reference amplification of the two Kraus operators. -/
def withReference :
    Matrix ((Fin 2 × Fin 2) × r) ((Fin 2 × Fin 2) × r) ℝ →ₗ[ℝ]
      Matrix ((Fin 2 × Fin 2) × r) ((Fin 2 × Fin 2) × r) ℝ :=
  krausMap (K0 ⊗ₖ (1 : Matrix r r ℝ)) (K1 ⊗ₖ (1 : Matrix r r ℝ))

theorem reference_normalization :
    (K0 ⊗ₖ (1 : Matrix r r ℝ))ᴴ * (K0 ⊗ₖ (1 : Matrix r r ℝ)) +
    (K1 ⊗ₖ (1 : Matrix r r ℝ))ᴴ * (K1 ⊗ₖ (1 : Matrix r r ℝ)) = 1 := by
  simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, one_mul]
  rw [← add_kronecker, kraus_normalization, one_kronecker_one]

theorem reference_positive
    (X : Matrix ((Fin 2 × Fin 2) × r) ((Fin 2 × Fin 2) × r) ℝ)
    (hX : X.PosSemidef) : (withReference r X).PosSemidef :=
  kraus_positive _ _ X hX

theorem reference_trace
    (X : Matrix ((Fin 2 × Fin 2) × r) ((Fin 2 × Fin 2) × r) ℝ) :
    (withReference r X).trace = X.trace :=
  kraus_trace _ _ X (reference_normalization r)

theorem reference_product (X : QQ) (τ : Matrix r r ℝ) :
    withReference r (X ⊗ₖ τ) = controlled X ⊗ₖ τ := by
  simp only [withReference, controlled, krausMap_apply, conjTranspose_kronecker,
    conjTranspose_one, ← mul_kronecker_mul, one_mul, mul_one, add_kronecker]

theorem reference_state
    (X : Matrix ((Fin 2 × Fin 2) × r) ((Fin 2 × Fin 2) × r) ℝ)
    (hX : State X) : State (withReference r X) :=
  ⟨reference_positive r X hX.1, (reference_trace r X).trans hX.2⟩

end Reference

/-- The two sectors of this map are the identity and the supplied phase. -/
theorem controlled_product (ρ τ : Q) :
    controlled (ρ ⊗ₖ τ) = (P0 * ρ * P0) ⊗ₖ τ + (P1 * ρ * P1) ⊗ₖ phase τ := by
  simp only [controlled, krausMap_apply, K0, K1, conjTranspose_kronecker,
    P0_adjoint, P1_adjoint, Z_adjoint, conjTranspose_one,
    ← mul_kronecker_mul, one_mul, mul_one, phase]

theorem sector_zero (τ : Q) : controlled (P0 ⊗ₖ τ) = P0 ⊗ₖ τ := by
  simp [controlled_product]

theorem sector_one (τ : Q) : controlled (P1 ⊗ₖ τ) = P1 ⊗ₖ phase τ := by
  simp [controlled_product]

@[simp] theorem phase_P0 : phase P0 = P0 := by
  simp [phase, Z, sub_mul, mul_sub]
@[simp] theorem phase_P1 : phase P1 = P1 := by
  simp [phase, Z, sub_mul, mul_sub]
@[simp] theorem phase_yPlus : phase yPlus = yMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [phase, Z, P0, P1, yPlus, yMinus, mul_apply, Fin.sum_univ_two]
@[simp] theorem phase_yMinus : phase yMinus = yPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [phase, Z, P0, P1, yPlus, yMinus, mul_apply, Fin.sum_univ_two]

theorem fixed_program_zero (ρ : Q) :
    controlled (ρ ⊗ₖ P0) = dephase ρ ⊗ₖ P0 := by
  rw [controlled_product, phase_P0, ← add_kronecker]
  rfl

theorem fixed_program_one (ρ : Q) :
    controlled (ρ ⊗ₖ P1) = dephase ρ ⊗ₖ P1 := by
  rw [controlled_product, phase_P1, ← add_kronecker]
  rfl

theorem ensemble_equality : P0 + P1 = yPlus + yMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P0, P1, yPlus, yMinus]

theorem yPlus_ne_yMinus : yPlus ≠ yMinus := by
  intro h
  have he := congrArg (fun X : Q => X 0 1) h
  norm_num [yPlus, yMinus] at he

/-- Exact real Gram factors for the two collision states. -/
def plusGram : Q := !![1, 1; 0, 0]
def minusGram : Q := !![1, -1; 0, 0]

theorem yPlus_gram : yPlus = (1 / 2 : ℝ) • (plusGramᴴ * plusGram) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [yPlus, plusGram, mul_apply, conjTranspose_apply, Fin.sum_univ_two]

theorem yMinus_gram : yMinus = (1 / 2 : ℝ) • (minusGramᴴ * minusGram) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [yMinus, minusGram, mul_apply, conjTranspose_apply, Fin.sum_univ_two]

theorem P0_state : State P0 := by
  constructor
  · simpa only [P0_adjoint, P0_square] using (posSemidef_conjTranspose_mul_self P0)
  · norm_num [P0, trace_fin_two]

theorem P1_state : State P1 := by
  constructor
  · simpa only [P1_adjoint, P1_square] using (posSemidef_conjTranspose_mul_self P1)
  · norm_num [P1, trace_fin_two]

theorem yPlus_state : State yPlus := by
  constructor
  · rw [yPlus_gram]
    exact (posSemidef_conjTranspose_mul_self plusGram).smul (by norm_num)
  · norm_num [yPlus, trace_fin_two]

theorem yMinus_state : State yMinus := by
  constructor
  · rw [yMinus_gram]
    exact (posSemidef_conjTranspose_mul_self minusGram).smul (by norm_num)
  · norm_num [yMinus, trace_fin_two]

theorem dephase_yPlus : dephase yPlus = (1 / 2 : ℝ) • (1 : Q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [dephase, P0, P1, yPlus, mul_apply, Fin.sum_univ_two]

theorem dephase_yMinus : dephase yMinus = (1 / 2 : ℝ) • (1 : Q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [dephase, P0, P1, yMinus, mul_apply, Fin.sum_univ_two]

/-- The phase exists, while averaging over it removes coherence. -/
theorem dephase_as_phase_average (ρ : Q) :
    dephase ρ = (1 / 2 : ℝ) • (ρ + phase ρ) := by
  have hsum : ρ + phase ρ = (2 : ℝ) • dephase ρ := by
    have hid : ρ = (P0 + P1) * ρ * (P0 + P1) := by simp
    conv_lhs => lhs; rw [hid]
    simp only [phase, Z, dephase, mul_add, add_mul, mul_sub, sub_mul]
    module
  rw [hsum, smul_smul]
  norm_num

/-- A checked Gram argument supplies positivity of the product collision states. -/
theorem gram_product_positive (A : Q) :
    (((1 / 2 : ℝ) • (Aᴴ * A)) ⊗ₖ P0).PosSemidef := by
  have he : ((1 / 2 : ℝ) • (Aᴴ * A)) ⊗ₖ P0 =
      (1 / 2 : ℝ) • ((A ⊗ₖ P0)ᴴ * (A ⊗ₖ P0)) := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, P0_adjoint,
      P0_square, smul_kronecker]
  rw [he]
  exact (posSemidef_conjTranspose_mul_self (A ⊗ₖ P0)).smul (by norm_num)

theorem product_yPlus_state : State (yPlus ⊗ₖ P0) := by
  constructor
  · rw [yPlus_gram]
    exact gram_product_positive plusGram
  · rw [trace_kronecker, yPlus_state.2, P0_state.2, one_mul]

theorem product_yMinus_state : State (yMinus ⊗ₖ P0) := by
  constructor
  · rw [yMinus_gram]
    exact gram_product_positive minusGram
  · rw [trace_kronecker, yMinus_state.2, P0_state.2, one_mul]

theorem product_states_distinct : yPlus ⊗ₖ P0 ≠ yMinus ⊗ₖ P0 := by
  intro h
  have he := congrArg (fun X : QQ => X (0, 0) (1, 0)) h
  norm_num [yPlus, yMinus, P0, kronecker_apply] at he

theorem controlled_collision :
    controlled (yPlus ⊗ₖ P0) = controlled (yMinus ⊗ₖ P0) := by
  rw [fixed_program_zero, fixed_program_zero, dephase_yPlus, dephase_yMinus]

theorem dephase_noninjective : ¬ Function.Injective dephase := by
  intro h
  exact yPlus_ne_yMinus (h (dephase_yPlus.trans dephase_yMinus.symm))

theorem controlled_noninjective : ¬ Function.Injective controlled := by
  intro h
  exact product_states_distinct (h controlled_collision)

/-- Recovery fails even when required only on normalized positive inputs. -/
theorem dephase_no_state_recovery :
    ¬ ∃ R : Q → Q, ∀ ρ, State ρ → R (dephase ρ) = ρ := by
  rintro ⟨R, hR⟩
  apply yPlus_ne_yMinus
  rw [← hR yPlus yPlus_state, ← hR yMinus yMinus_state,
    dephase_yPlus, dephase_yMinus]

/-- The full controlled map also has a valid-state collision, so no recovery
function can invert it on all normalized positive inputs. -/
theorem controlled_no_state_recovery :
    ¬ ∃ R : QQ → QQ, ∀ X, State X → R (controlled X) = X := by
  rintro ⟨R, hR⟩
  apply product_states_distinct
  rw [← hR _ product_yPlus_state, ← hR _ product_yMinus_state, controlled_collision]

/-- The coherent companion has the same two Kraus sectors before their sum
is dephased. This is an explicit candidate in the supplied matrix model. -/
def U : QQ := K0 + K1

def coherent (X : QQ) : QQ := U * X * Uᴴ

@[simp] theorem U_adjoint : Uᴴ = U := by
  rw [U, conjTranspose_add]
  simp only [K0, K1, conjTranspose_kronecker, P0_adjoint, P1_adjoint,
    conjTranspose_one, Z_adjoint]

@[simp] theorem U_square : U * U = 1 := by
  simp only [U, add_mul, mul_add, K0, K1, ← mul_kronecker_mul,
    P0_square, P1_square, P0_P1, P1_P0, Z_square, one_mul, mul_one,
    zero_kronecker, zero_add, add_zero]
  rw [← add_kronecker, P0_add_P1, one_kronecker_one]

theorem coherent_positive (X : QQ) (hX : X.PosSemidef) :
    (coherent X).PosSemidef := hX.mul_mul_conjTranspose_same U

theorem coherent_trace (X : QQ) : (coherent X).trace = X.trace := by
  rw [coherent, trace_mul_cycle, U_adjoint, U_square, one_mul]

theorem coherent_involutive : Function.Involutive coherent := by
  intro X
  simp only [coherent, U_adjoint]
  calc
    U * (U * X * U) * U = (U * U) * X * (U * U) := by simp only [mul_assoc]
    _ = X := by simp

theorem coherent_sector_zero (τ : Q) : coherent (P0 ⊗ₖ τ) = P0 ⊗ₖ τ := by
  rw [coherent, U_adjoint]
  simp only [U, add_mul, mul_add, K0, K1,
    ← mul_kronecker_mul, P0_square, P0_P1, P1_P0, one_mul, mul_one,
    zero_kronecker, add_zero]

theorem coherent_sector_one (τ : Q) : coherent (P1 ⊗ₖ τ) = P1 ⊗ₖ phase τ := by
  rw [coherent, U_adjoint]
  simp only [U, add_mul, mul_add, K0, K1,
    ← mul_kronecker_mul, P1_square, P0_P1, P1_P0, one_mul, mul_one,
    zero_kronecker, zero_add, phase]

/-- Partial trace over the two-dimensional target factor. -/
def discardTarget (X : QQ) : Q := fun i j => ∑ k : Fin 2, X (i, k) (j, k)

theorem coherent_discard_product (ρ τ : Q) :
    discardTarget (coherent (ρ ⊗ₖ τ)) = τ 0 0 • ρ + τ 1 1 • phase ρ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [discardTarget, coherent, phase, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      conjTranspose_apply] <;>
    norm_num [U, K0, K1, P0, P1, Z, kronecker_apply] <;> ring

theorem coherent_program_zero (ρ : Q) :
    discardTarget (coherent (ρ ⊗ₖ P0)) = ρ := by
  rw [coherent_discard_product]
  norm_num [P0]

theorem coherent_program_one (ρ : Q) :
    discardTarget (coherent (ρ ⊗ₖ P1)) = phase ρ := by
  rw [coherent_discard_product]
  norm_num [P1]

theorem coherent_program_yPlus (ρ : Q) :
    discardTarget (coherent (ρ ⊗ₖ yPlus)) = dephase ρ := by
  rw [coherent_discard_product]
  change (1 / 2 : ℝ) • ρ + (1 / 2 : ℝ) • phase ρ = dephase ρ
  rw [← smul_add, dephase_as_phase_average]

theorem coherent_program_yMinus (ρ : Q) :
    discardTarget (coherent (ρ ⊗ₖ yMinus)) = dephase ρ := by
  rw [coherent_discard_product]
  change (1 / 2 : ℝ) • ρ + (1 / 2 : ℝ) • phase ρ = dephase ρ
  rw [← smul_add, dephase_as_phase_average]

theorem phase_nontrivial : phase yPlus ≠ yPlus := by
  rw [phase_yPlus]
  exact yPlus_ne_yMinus.symm

end

end IDT.QMClosure.DephasedControlledCountercontrol
