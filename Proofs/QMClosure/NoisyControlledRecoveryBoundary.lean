import Proofs.QMClosure.PositiveMixtureRecoveryObstruction
import Proofs.QMClosure.DephasedControlledCountercontrol

/-!
# Injective noisy controlled maps and positive recovery

For a strictly intermediate real coherence parameter, the supplied real-matrix
channel has an algebraic inverse and preserves positivity and trace under every
finite real reference extension. Every positive linear recovery already fails
on two explicit normalized positive states. Algebraic recovery functions exist.
These statements concern this supplied matrix model and the inference from an
invertible positive map to a positive inverse.
-/

namespace IDT.QMClosure.NoisyControlledRecoveryBoundary

noncomputable section

open Matrix
open scoped Kronecker
open IDT.QMClosure.DephasedControlledCountercontrol
open IDT.QMClosure.PositiveMixtureRecoveryObstruction

/-- The coherent companion as a bundled real linear map. -/
def C : QQ →ₗ[ℝ] QQ := krausMap U 0

@[simp] theorem C_apply (X : QQ) : C X = coherent X := by
  simp only [C, krausMap_apply, coherent, zero_mul, add_zero]

theorem C_involutive : Function.Involutive C := by
  intro X
  simpa only [C_apply] using coherent_involutive X

def L1 : QQ := P1 ⊗ₖ (1 : Q)
def delta : QQ →ₗ[ℝ] QQ := krausMap K0 L1

@[simp] theorem K0_adjoint : K0ᴴ = K0 := by
  rw [K0, conjTranspose_kronecker, P0_adjoint, conjTranspose_one]
@[simp] theorem L1_adjoint : L1ᴴ = L1 := by
  rw [L1, conjTranspose_kronecker, P1_adjoint, conjTranspose_one]

theorem U_K0 : U * K0 = K0 := by
  simp only [U, add_mul, K0, K1, ← mul_kronecker_mul,
    P0_square, P1_P0, one_mul, zero_kronecker, add_zero]

theorem U_L1 : U * L1 = K1 := by
  simp only [U, add_mul, K0, K1, L1, ← mul_kronecker_mul,
    P0_P1, P1_square, mul_one, zero_kronecker, zero_add]

/-- This dephases the control index, retaining both complete diagonal blocks. -/
theorem delta_entry (X : QQ) (i j : Fin 2 × Fin 2) :
    delta X i j = if i.1 = j.1 then X i j else 0 := by
  rcases i with ⟨i, k⟩
  rcases j with ⟨j, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [delta, krausMap_apply, Matrix.add_apply, mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, conjTranspose_apply] <;>
    norm_num [K0, L1, P0, P1, kronecker_apply]

theorem delta_idempotent : ∀ X, delta (delta X) = delta X := by
  intro X
  ext i j
  simp only [delta_entry]
  split_ifs <;> rfl

/-- The dephased channel is coherent conjugation after control dephasing. -/
theorem C_delta (X : QQ) : C (delta X) = controlled X := by
  rw [C_apply, coherent]
  change U * (K0 * X * K0ᴴ + L1 * X * L1ᴴ) * Uᴴ =
    K0 * X * K0ᴴ + K1 * X * K1ᴴ
  calc
    _ = (U * K0) * X * (U * K0)ᴴ + (U * L1) * X * (U * L1)ᴴ := by
      simp only [conjTranspose_mul, mul_add, add_mul, mul_assoc]
    _ = _ := by rw [U_K0, U_L1]

/-- A convex mixture of coherent and dephased controlled implementations. -/
def noisy (η : ℝ) : QQ →ₗ[ℝ] QQ := η • C + (1 - η) • controlled

@[simp] theorem noisy_apply (η : ℝ) (X : QQ) :
    noisy η X = η • coherent X + (1 - η) • controlled X := by
  simp only [noisy, LinearMap.add_apply, LinearMap.smul_apply, C_apply]

theorem noisy_positive (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (X : QQ) (hX : X.PosSemidef) : (noisy η X).PosSemidef := by
  rw [noisy_apply]
  exact ((coherent_positive X hX).smul hη0).add
    ((controlled_positive X hX).smul (sub_nonneg.mpr hη1))

theorem noisy_trace (η : ℝ) (X : QQ) : (noisy η X).trace = X.trace := by
  rw [noisy_apply, trace_add, trace_smul, trace_smul, coherent_trace, controlled_trace]
  simp only [smul_eq_mul]
  ring

theorem noisy_state (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (X : QQ) (hX : State X) : State (noisy η X) :=
  ⟨noisy_positive η hη0 hη1 X hX.1, (noisy_trace η X).trans hX.2⟩

theorem noisy_factor (η : ℝ) (X : QQ) :
    noisy η X = C (scaleComplement delta η X) := by
  change η • C X + (1 - η) • controlled X = C (delta X + η • (X - delta X))
  rw [map_add, map_smul, map_sub, C_delta]
  module

/-- A two-sided algebraic inverse, without a positivity assertion. -/
def algebraicInverse (η : ℝ) : QQ →ₗ[ℝ] QQ :=
  (scaleComplement delta η⁻¹).comp C

theorem inverse_left (η : ℝ) (hη : η ≠ 0) :
    Function.LeftInverse (algebraicInverse η) (noisy η) := by
  intro X
  change scaleComplement delta η⁻¹ (C (noisy η X)) = X
  rw [noisy_factor, C_involutive]
  exact scaleComplement_inverse_left delta delta_idempotent η hη X

theorem inverse_right (η : ℝ) (hη : η ≠ 0) :
    Function.RightInverse (algebraicInverse η) (noisy η) := by
  intro X
  rw [noisy_factor]
  change C (scaleComplement delta η (scaleComplement delta η⁻¹ (C X))) = X
  rw [scaleComplement_inverse_right delta delta_idempotent η hη, C_involutive]

theorem noisy_bijective (η : ℝ) (hη : η ≠ 0) : Function.Bijective (noisy η) :=
  ⟨(inverse_left η hη).injective, (inverse_right η hη).surjective⟩

section Reference

variable (r : Type*) [Fintype r] [DecidableEq r]

def coherentReference :
    Matrix ((Fin 2 × Fin 2) × r) ((Fin 2 × Fin 2) × r) ℝ →ₗ[ℝ]
      Matrix ((Fin 2 × Fin 2) × r) ((Fin 2 × Fin 2) × r) ℝ :=
  krausMap (U ⊗ₖ (1 : Matrix r r ℝ)) 0

theorem coherent_reference_normalization :
    (U ⊗ₖ (1 : Matrix r r ℝ))ᴴ * (U ⊗ₖ (1 : Matrix r r ℝ)) +
      (0 : Matrix ((Fin 2 × Fin 2) × r) ((Fin 2 × Fin 2) × r) ℝ)ᴴ * 0 = 1 := by
  simp only [conjTranspose_kronecker, U_adjoint, conjTranspose_one,
    ← mul_kronecker_mul, U_square, one_mul, one_kronecker_one,
    conjTranspose_zero, zero_mul, add_zero]

theorem coherent_reference_positive
    (X : Matrix ((Fin 2 × Fin 2) × r) ((Fin 2 × Fin 2) × r) ℝ)
    (hX : X.PosSemidef) : (coherentReference r X).PosSemidef :=
  kraus_positive _ _ X hX

theorem coherent_reference_trace
    (X : Matrix ((Fin 2 × Fin 2) × r) ((Fin 2 × Fin 2) × r) ℝ) :
    (coherentReference r X).trace = X.trace :=
  kraus_trace _ _ X (coherent_reference_normalization r)

theorem coherent_reference_product (X : QQ) (τ : Matrix r r ℝ) :
    coherentReference r (X ⊗ₖ τ) = coherent X ⊗ₖ τ := by
  simp only [coherentReference, krausMap_apply, zero_mul, add_zero,
    conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
    one_mul, mul_one, coherent]

def noisyReference (η : ℝ) := η • coherentReference r + (1 - η) • withReference r

theorem noisy_reference_positive (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (X : Matrix ((Fin 2 × Fin 2) × r) ((Fin 2 × Fin 2) × r) ℝ)
    (hX : X.PosSemidef) : (noisyReference r η X).PosSemidef :=
  ((coherent_reference_positive r X hX).smul hη0).add
    ((reference_positive r X hX).smul (sub_nonneg.mpr hη1))

theorem noisy_reference_trace (η : ℝ)
    (X : Matrix ((Fin 2 × Fin 2) × r) ((Fin 2 × Fin 2) × r) ℝ) :
    (noisyReference r η X).trace = X.trace := by
  change (η • coherentReference r X + (1 - η) • withReference r X).trace = X.trace
  rw [trace_add, trace_smul, trace_smul, coherent_reference_trace, reference_trace]
  simp only [smul_eq_mul]
  ring

theorem noisy_reference_product (η : ℝ) (X : QQ) (τ : Matrix r r ℝ) :
    noisyReference r η (X ⊗ₖ τ) = noisy η X ⊗ₖ τ := by
  simp only [noisyReference, LinearMap.add_apply, LinearMap.smul_apply,
    coherent_reference_product, reference_product, noisy_apply,
    add_kronecker, smul_kronecker]

end Reference

/-- The corresponding local control-dephasing projector. -/
def D : Q →ₗ[ℝ] Q := krausMap P0 P1

@[simp] theorem D_apply (ρ : Q) : D ρ = dephase ρ := by
  simp only [D, krausMap_apply, P0_adjoint, P1_adjoint, dephase]

theorem D_entry (ρ : Q) (i j : Fin 2) :
    D ρ i j = if i = j then ρ i j else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [D_apply, dephase, Matrix.add_apply, mul_apply, Fin.sum_univ_two] <;>
    norm_num [P0, P1]

theorem D_idempotent : ∀ ρ, D (D ρ) = D ρ := by
  intro ρ
  ext i j
  simp only [D_entry]
  split_ifs <;> rfl

def localResponse (η : ℝ) : Q →ₗ[ℝ] Q := scaleComplement D η

@[simp] theorem localResponse_apply (η : ℝ) (ρ : Q) :
    localResponse η ρ = dephase ρ + η • (ρ - dephase ρ) := by
  simp only [localResponse, scaleComplement_apply, D_apply]

theorem localResponse_injective (η : ℝ) (hη : η ≠ 0) :
    Function.Injective (localResponse η) :=
  (scaleComplement_inverse_left D D_idempotent η hη).injective

/-- Full coherent outputs at the two fixed target program states. -/
theorem coherent_fixed_zero (ρ : Q) : coherent (ρ ⊗ₖ P0) = ρ ⊗ₖ P0 := by
  ext i j
  rcases i with ⟨i, k⟩
  rcases j with ⟨j, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [coherent, mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      conjTranspose_apply] <;>
    norm_num [U, K0, K1, P0, P1, Z, kronecker_apply]

theorem coherent_fixed_one (ρ : Q) : coherent (ρ ⊗ₖ P1) = phase ρ ⊗ₖ P1 := by
  ext i j
  rcases i with ⟨i, k⟩
  rcases j with ⟨j, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [coherent, phase, kronecker_apply, mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      conjTranspose_apply] <;>
    norm_num [U, K0, K1, P0, P1, Z, kronecker_apply]

theorem noisy_fixed_zero (η : ℝ) (ρ : Q) :
    noisy η (ρ ⊗ₖ P0) = localResponse η ρ ⊗ₖ P0 := by
  rw [noisy_apply, coherent_fixed_zero, fixed_program_zero]
  rw [← smul_kronecker, ← smul_kronecker, ← add_kronecker]
  apply congrArg (fun A : Q => A ⊗ₖ P0)
  rw [localResponse_apply]
  module

theorem noisy_fixed_one (η : ℝ) (ρ : Q) :
    noisy η (ρ ⊗ₖ P1) = localResponse (-η) ρ ⊗ₖ P1 := by
  rw [noisy_apply, coherent_fixed_one, fixed_program_one]
  rw [← smul_kronecker, ← smul_kronecker, ← add_kronecker]
  apply congrArg (fun A : Q => A ⊗ₖ P1)
  rw [localResponse_apply, dephase_as_phase_average]
  module

theorem noisy_sector_zero (η : ℝ) (τ : Q) :
    noisy η (P0 ⊗ₖ τ) = P0 ⊗ₖ τ := by
  rw [noisy_apply, coherent_sector_zero, sector_zero]
  module

theorem noisy_sector_one (η : ℝ) (τ : Q) :
    noisy η (P1 ⊗ₖ τ) = P1 ⊗ₖ phase τ := by
  rw [noisy_apply, coherent_sector_one, sector_one]
  module

/-- Dephased control outputs discard to `D` for every normalized target. -/
theorem controlled_discard_product (ρ τ : Q) (hτ : τ.trace = 1) :
    discardTarget (controlled (ρ ⊗ₖ τ)) = dephase ρ := by
  have ht : τ 0 0 + τ 1 1 = 1 := by simpa only [trace_fin_two] using hτ
  have hmul (t : ℝ) : t * (τ 0 0 + τ 1 1) = t := by rw [ht, mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [discardTarget, controlled_product, phase, dephase, Matrix.add_apply,
      kronecker_apply, mul_apply, Fin.sum_univ_two] <;>
    norm_num [P0, P1, Z] <;>
    nlinarith [hmul (ρ 0 0), hmul (ρ 0 1), hmul (ρ 1 0), hmul (ρ 1 1)]

theorem discardTarget_add (X Y : QQ) :
    discardTarget (X + Y) = discardTarget X + discardTarget Y := by
  ext i j
  simp [discardTarget, Finset.sum_add_distrib]

theorem discardTarget_smul (t : ℝ) (X : QQ) :
    discardTarget (t • X) = t • discardTarget X := by
  ext i j
  simp [discardTarget, mul_add]

theorem noisy_flipped_plus (η : ℝ) (ρ : Q) :
    discardTarget (noisy η (ρ ⊗ₖ yPlus)) = dephase ρ := by
  rw [noisy_apply, discardTarget_add, discardTarget_smul, discardTarget_smul,
    coherent_program_yPlus, controlled_discard_product ρ yPlus yPlus_state.2]
  module

theorem noisy_flipped_minus (η : ℝ) (ρ : Q) :
    discardTarget (noisy η (ρ ⊗ₖ yMinus)) = dephase ρ := by
  rw [noisy_apply, discardTarget_add, discardTarget_smul, discardTarget_smul,
    coherent_program_yMinus, controlled_discard_product ρ yMinus yMinus_state.2]
  module

/-- A nonnegative PSD readout vanishing on `yPlus` and equal to one on `yMinus`. -/
def readout : Q →ₗ[ℝ] ℝ where
  toFun M := (M 0 0 - M 0 1 - M 1 0 + M 1 1) / 2
  map_add' M N := by simp; ring
  map_smul' t M := by simp; ring

theorem readout_nonnegative (M : Q) (hM : M.PosSemidef) : 0 ≤ readout M := by
  have h := hM.dotProduct_mulVec_nonneg ![1, -1]
  norm_num [dotProduct, mulVec, Fin.sum_univ_two] at h
  change 0 ≤ (M 0 0 - M 0 1 - M 1 0 + M 1 1) / 2
  linarith

@[simp] theorem readout_yPlus : readout yPlus = 0 := by norm_num [readout, yPlus]
@[simp] theorem readout_yMinus : readout yMinus = 1 := by norm_num [readout, yMinus]

def jointReadout : QQ →ₗ[ℝ] ℝ where
  toFun M := (M (0, 0) (0, 0) - M (0, 0) (1, 0) -
    M (1, 0) (0, 0) + M (1, 0) (1, 0)) / 2
  map_add' M N := by simp; ring
  map_smul' t M := by simp; ring

theorem jointReadout_nonnegative (M : QQ) (hM : M.PosSemidef) :
    0 ≤ jointReadout M := by
  exact readout_nonnegative (M.submatrix (fun i => (i, 0)) (fun i => (i, 0)))
    (hM.submatrix (fun i => (i, 0)))

@[simp] theorem jointReadout_plus : jointReadout (yPlus ⊗ₖ P0) = 0 := by
  norm_num [jointReadout, yPlus, P0, kronecker_apply]
@[simp] theorem jointReadout_minus : jointReadout (yMinus ⊗ₖ P0) = 1 := by
  norm_num [jointReadout, yMinus, P0, kronecker_apply]

theorem local_mixture_plus (η : ℝ) :
    localResponse η yPlus = ((1 + η) / 2) • yPlus + ((1 - η) / 2) • yMinus := by
  rw [localResponse_apply, dephase_yPlus]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [yPlus, yMinus] <;> ring

theorem local_mixture_minus (η : ℝ) :
    localResponse η yMinus = ((1 - η) / 2) • yPlus + ((1 + η) / 2) • yMinus := by
  rw [localResponse_apply, dephase_yMinus]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [yPlus, yMinus] <;> ring

theorem noisy_mixture_plus (η : ℝ) :
    noisy η (yPlus ⊗ₖ P0) =
      ((1 + η) / 2) • (yPlus ⊗ₖ P0) + ((1 - η) / 2) • (yMinus ⊗ₖ P0) := by
  rw [noisy_fixed_zero, local_mixture_plus, add_kronecker, smul_kronecker, smul_kronecker]

theorem noisy_mixture_minus (η : ℝ) :
    noisy η (yMinus ⊗ₖ P0) =
      ((1 - η) / 2) • (yPlus ⊗ₖ P0) + ((1 + η) / 2) • (yMinus ⊗ₖ P0) := by
  rw [noisy_fixed_zero, local_mixture_minus, add_kronecker, smul_kronecker, smul_kronecker]

theorem local_no_positive_recovery (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ¬ ∃ R : Q →ₗ[ℝ] Q, (∀ X : Q, X.PosSemidef → (R X).PosSemidef) ∧
      R (localResponse η yPlus) = yPlus ∧ R (localResponse η yMinus) = yMinus := by
  exact no_positive_two_state_recovery {M : Q | M.PosSemidef} yPlus yMinus
    yPlus_state.1 yMinus_state.1 readout readout_nonnegative readout_yPlus readout_yMinus
    ((1 + η) / 2) ((1 - η) / 2) (by linarith) (by linarith)
    (localResponse η) (local_mixture_plus η) (local_mixture_minus η)

theorem noisy_no_positive_recovery (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ¬ ∃ R : QQ →ₗ[ℝ] QQ, (∀ X : QQ, X.PosSemidef → (R X).PosSemidef) ∧
      R (noisy η (yPlus ⊗ₖ P0)) = yPlus ⊗ₖ P0 ∧
      R (noisy η (yMinus ⊗ₖ P0)) = yMinus ⊗ₖ P0 := by
  exact no_positive_two_state_recovery {M : QQ | M.PosSemidef}
    (yPlus ⊗ₖ P0) (yMinus ⊗ₖ P0) product_yPlus_state.1 product_yMinus_state.1
    jointReadout jointReadout_nonnegative jointReadout_plus jointReadout_minus
    ((1 + η) / 2) ((1 - η) / 2) (by linarith) (by linarith)
    (noisy η) (noisy_mixture_plus η) (noisy_mixture_minus η)

theorem algebraic_inverse_not_positive (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ¬ ∀ X : QQ, X.PosSemidef → (algebraicInverse η X).PosSemidef := by
  intro hpos
  exact noisy_no_positive_recovery η hη0 hη1
    ⟨algebraicInverse η, hpos, inverse_left η (ne_of_gt hη0) _,
      inverse_left η (ne_of_gt hη0) _⟩

/-- A uniform bound over these two inputs and one specified PSD readout. -/
theorem noisy_two_readout_error_bound (η ε : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (R : QQ →ₗ[ℝ] QQ) (hR : ∀ X : QQ, X.PosSemidef → (R X).PosSemidef)
    (hA : jointReadout (R (noisy η (yPlus ⊗ₖ P0))) ≤ ε)
    (hB : 1 - jointReadout (R (noisy η (yMinus ⊗ₖ P0))) ≤ ε) :
    (1 - η) / 2 ≤ ε := by
  exact positive_two_mixture_error_bound {M : QQ | M.PosSemidef}
    (yPlus ⊗ₖ P0) (yMinus ⊗ₖ P0) product_yPlus_state.1
    jointReadout jointReadout_nonnegative η ε hη0 hη1 (noisy η)
    (noisy_mixture_plus η) (noisy_mixture_minus η) R hR hA hB

/-- Identity recovery attains that bound for both selected readout errors. -/
theorem identity_attains_two_readout_bound (η : ℝ) :
    jointReadout (noisy η (yPlus ⊗ₖ P0)) = (1 - η) / 2 ∧
    1 - jointReadout (noisy η (yMinus ⊗ₖ P0)) = (1 - η) / 2 := by
  constructor
  · rw [noisy_mixture_plus]
    simp only [map_add, map_smul, smul_eq_mul, jointReadout_plus, jointReadout_minus,
      mul_zero, mul_one, zero_add]
  · rw [noisy_mixture_minus]
    simp only [map_add, map_smul, smul_eq_mul, jointReadout_plus, jointReadout_minus,
      mul_zero, mul_one, zero_add]
    ring

/-- One family simultaneously supplies bijectivity, physical-state
preservation, and failure of positive linear recovery of two physical inputs. -/
theorem noisy_recovery_boundary (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    Function.Bijective (noisy η) ∧
    (∀ X : QQ, State X → State (noisy η X)) ∧
    ¬ ∃ R : QQ →ₗ[ℝ] QQ, (∀ X : QQ, X.PosSemidef → (R X).PosSemidef) ∧
      R (noisy η (yPlus ⊗ₖ P0)) = yPlus ⊗ₖ P0 ∧
      R (noisy η (yMinus ⊗ₖ P0)) = yMinus ⊗ₖ P0 :=
  ⟨noisy_bijective η (ne_of_gt hη0), noisy_state η hη0.le hη1.le,
    noisy_no_positive_recovery η hη0 hη1⟩

/-- An explicit nonvacuous instance at half coherence. -/
theorem half_noisy_recovery_boundary :
    Function.Bijective (noisy (1 / 2)) ∧
    (∀ X : QQ, State X → State (noisy (1 / 2) X)) ∧
    ¬ ∃ R : QQ →ₗ[ℝ] QQ, (∀ X : QQ, X.PosSemidef → (R X).PosSemidef) ∧
      R (noisy (1 / 2) (yPlus ⊗ₖ P0)) = yPlus ⊗ₖ P0 ∧
      R (noisy (1 / 2) (yMinus ⊗ₖ P0)) = yMinus ⊗ₖ P0 :=
  noisy_recovery_boundary (1 / 2) (by norm_num) (by norm_num)

end

end IDT.QMClosure.NoisyControlledRecoveryBoundary
