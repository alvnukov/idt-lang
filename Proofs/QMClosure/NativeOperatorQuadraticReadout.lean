import Proofs.QMClosure.FiniteRejoinObservableQuotient

/-!
# Universal quadratic gains of the native generated operators

This conditional algebraic transfer starts from the finite-rejoin reconstruction
and its faithful observable quotient. A positive source is supplied only to
select a numerical normalization and the existing canonical conjugation.
Every native generated operator has one quadratic gain on the entire native
carrier. Reference independence and numerical multiplicativity are conclusions.

The pairing adjoint below is relative to the derived real polarization. The
paired-echo normalization is an equality of native additive endomorphisms.
There is no real scalar action on the carrier in this construction. Physical
accessibility of positive histories is a separate proof obligation.
-/

noncomputable section

namespace IDT.QMClosure.NativeOperatorQuadraticReadout

open QuadraticRecordRefinement
open FiniteRejoinObservableQuotient
open SingleCalibrationScalarFaithfulness

variable {V : Type*} [AddCommMonoid V]
variable {G : FiniteRejoinReversibleQuadraticReadout.Gate V} {W : V → ℝ}

abbrev Carrier (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) :=
  (nativeGate h).Carrier

abbrev Operator (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) :=
  (nativeGate h).generated

local instance (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W) :
    CommRing (Operator h) := (nativeGate h).generatedCommRing

variable (h : FiniteRejoinReversibleQuadraticReadout.Reconstruction G W)

/-- Evaluation uses only native additive endomorphism action. -/
def act (T : Operator h) (x : Carrier h) : Carrier h :=
  (T : AddMonoid.End (Carrier h)) x

@[simp]theorem act_zero (x : Carrier h) : act h 0 x = 0 := rfl
@[simp]theorem act_one (x : Carrier h) : act h 1 x = x := rfl
@[simp]theorem act_add (T S : Operator h) (x : Carrier h) :
    act h (T + S) x = act h T x + act h S x := rfl
@[simp]theorem act_mul (T S : Operator h) (x : Carrier h) :
    act h (T * S) x = act h T (act h S x) := rfl
@[simp]theorem act_neg (T : Operator h) (x : Carrier h) :
    act h (-T) x = -act h T x := rfl
@[simp]theorem act_sub (T S : Operator h) (x : Carrier h) :
    act h (T - S) x = act h T x - act h S x := rfl
@[simp]theorem act_intCast (m : ℤ) (x : Carrier h) :
    act h (m : Operator h) x = m • x := by
  exact AddMonoid.End.intCast_apply m x

theorem act_map_add (T : Operator h) (x y : Carrier h) :
    act h T (x + y) = act h T x + act h T y :=
  map_add (T : AddMonoid.End (Carrier h)) x y

theorem act_commute (T S : Operator h) (x : Carrier h) :
    act h T (act h S x) = act h S (act h T x) := by
  rw [← act_mul, mul_comm T S, act_mul]

/-- Real polarization on the faithful native quotient. -/
def pairing (x y : Carrier h) : ℝ :=
  PositiveQuadraticPolarization.polarization (nativeWeight h) x y

theorem pairing_symmetric (x y : Carrier h) : pairing h x y = pairing h y x :=
  PositiveQuadraticPolarization.symmetric x y

theorem pairing_diagonal (x : Carrier h) : pairing h x x = nativeWeight h x :=
  PositiveQuadraticPolarization.diagonal (nativePositiveQuadratic h) x

theorem pairing_add_left (x y z : Carrier h) :
    pairing h (x + y) z = pairing h x z + pairing h y z :=
  PositiveQuadraticPolarization.add_left (nativePositiveQuadratic h) x y z

theorem pairing_add_right (x y z : Carrier h) :
    pairing h x (y + z) = pairing h x y + pairing h x z :=
  PositiveQuadraticPolarization.add_right (nativePositiveQuadratic h) x y z

theorem pairing_zsmul_left (m : ℤ) (x y : Carrier h) :
    pairing h (m • x) y = (m : ℝ) * pairing h x y :=
  PositiveQuadraticPolarization.zsmul_left (nativePositiveQuadratic h) m x y

theorem pairing_zsmul_right (m : ℤ) (x y : Carrier h) :
    pairing h x (m • y) = (m : ℝ) * pairing h x y :=
  PositiveQuadraticPolarization.zsmul_right (nativePositiveQuadratic h) m x y

theorem pairing_neg_right (x y : Carrier h) :
    pairing h x (-y) = -pairing h x y := by
  simpa using pairing_zsmul_right h (-1) x y

theorem pairing_sub_right (x y z : Carrier h) :
    pairing h x (y - z) = pairing h x y - pairing h x z := by
  rw [sub_eq_add_neg, pairing_add_right, pairing_neg_right, sub_eq_add_neg]

theorem branch_a_weight (x : Carrier h) :
    nativeWeight h ((nativeGate h).A x) = nativeWeight h x / 2 := by
  simpa only [LocalBranchOperatorFaithfulness.Gate.branch] using native_branch_half h true x

theorem branch_b_weight (x : Carrier h) :
    nativeWeight h ((nativeGate h).B x) = nativeWeight h x / 2 := by
  simpa only [LocalBranchOperatorFaithfulness.Gate.branch] using native_branch_half h false x

theorem half_weight (x : Carrier h) :
    nativeWeight h (act h (nativeGate h).generatedH x) = nativeWeight h x / 4 := by
  change nativeWeight h ((nativeGate h).A ((nativeGate h).B x)) = _
  rw [branch_a_weight, branch_b_weight]
  ring

theorem phase_weight (x : Carrier h) :
    nativeWeight h (act h (nativeGate h).generatedU x) = nativeWeight h x := by
  change nativeWeight h
    ((nativeGate h).A ((nativeGate h).A x) + (nativeGate h).A ((nativeGate h).A x)) = _
  rw [(nativePositiveQuadratic h).double, branch_a_weight, branch_a_weight]
  ring

theorem phase_square_apply (x : Carrier h) :
    act h (nativeGate h).generatedU (act h (nativeGate h).generatedU x) = -x := by
  have hu : (nativeGate h).generatedU ^ 2 = -(1 : Operator h) :=
    Subtype.ext (nativeGate h).phase_square
  have he := congrArg (fun T : Operator h => act h T x) hu
  simpa only [pow_two, act_mul, act_neg, act_one] using he

theorem phase_pairing_covariance (x y : Carrier h) :
    pairing h (act h (nativeGate h).generatedU x) (act h (nativeGate h).generatedU y) =
      pairing h x y := by
  unfold pairing PositiveQuadraticPolarization.polarization
  rw [← act_map_add, phase_weight, phase_weight, phase_weight]

theorem phase_pairing_skew (x y : Carrier h) :
    pairing h (act h (nativeGate h).generatedU x) y =
      -pairing h x (act h (nativeGate h).generatedU y) := by
  have he := phase_pairing_covariance h x (act h (nativeGate h).generatedU y)
  rw [phase_square_apply, pairing_neg_right] at he
  linarith

theorem phase_orthogonal (x : Carrier h) :
    pairing h x (act h (nativeGate h).generatedU x) = 0 := by
  have he := phase_pairing_skew h x x
  rw [pairing_symmetric h (act h (nativeGate h).generatedU x) x] at he
  linarith

theorem gaussian_action (z : LocalHistoryReadoutOrderWall.Residual) (x : Carrier h) :
    act h (Arithmetic.gaussian (nativeGate h).generatedU z) x =
      z.1 • x + z.2 • act h (nativeGate h).generatedU x := by
  simp only [Arithmetic.gaussian, act_add, act_mul, act_intCast]

theorem gaussian_weight (z : LocalHistoryReadoutOrderWall.Residual) (x : Carrier h) :
    nativeWeight h (act h (Arithmetic.gaussian (nativeGate h).generatedU z) x) =
      ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) * nativeWeight h x := by
  rw [gaussian_action]
  have he := PositiveQuadraticPolarization.integer_coordinate_law
    (nativePositiveQuadratic h) z.1 z.2 x (act h (nativeGate h).generatedU x)
  change nativeWeight h _ = (z.1 : ℝ) ^ 2 * nativeWeight h x +
    2 * (z.1 : ℝ) * (z.2 : ℝ) * pairing h x (act h (nativeGate h).generatedU x) +
      (z.2 : ℝ) ^ 2 * nativeWeight h (act h (nativeGate h).generatedU x) at he
  rw [phase_orthogonal, phase_weight] at he
  rw [he]
  ring

theorem half_power_weight (k : ℕ) (x : Carrier h) :
    nativeWeight h (act h ((nativeGate h).generatedH ^ k) x) =
      nativeWeight h x / (4 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', act_mul, half_weight, ih, pow_succ]
    ring

/-- A numerical expression in the real codomain only. -/
def presentationGain (k : ℕ) (z : LocalHistoryReadoutOrderWall.Residual) : ℝ :=
  ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) / (4 : ℝ) ^ k

theorem value_weight (k : ℕ) (z : LocalHistoryReadoutOrderWall.Residual) (x : Carrier h) :
    nativeWeight h
      (act h (Arithmetic.value (nativeGate h).generatedU (nativeGate h).generatedH k z) x) =
        presentationGain k z * nativeWeight h x := by
  rw [Arithmetic.value, act_mul, half_power_weight, gaussian_weight]
  unfold presentationGain
  ring

section PositiveReference

variable (p : V) (hp : 0 < W p)

include hp

/-- Exact coverage of all native generated operators by Gaussian-dyadic forms. -/
theorem operator_normal_form (T : Operator h) :
    ∃ k z, T = Arithmetic.value (nativeGate h).generatedU (nativeGate h).generatedH k z := by
  let C := sourceResponse h p hp
  letI := C.operatorResponse.generatedCharacteristicZero
  obtain ⟨k, z, he⟩ := Arithmetic.presentation_exists
    (nativeGate h).generatedU (nativeGate h).generatedH
    C.operatorResponse.arithmetic_parameters.1
    C.operatorResponse.arithmetic_parameters.2.1
    (C.operatorResponse.generatedArithmeticEquiv T)
  exact ⟨k, z, congrArg Subtype.val he⟩

theorem reference_weight :
    nativeWeight h (sourceResponse h p hp).reference = W p :=
  nativeWeight_projection h p

/-- A normalized readout at one positive source. -/
def gain (T : Operator h) : ℝ :=
  nativeWeight h (act h T (sourceResponse h p hp).reference) / W p

theorem gain_value (k : ℕ) (z : LocalHistoryReadoutOrderWall.Residual) :
    gain h p hp
      (Arithmetic.value (nativeGate h).generatedU (nativeGate h).generatedH k z) =
        presentationGain k z := by
  unfold gain
  rw [value_weight, reference_weight]
  exact mul_div_cancel_right₀ _ (ne_of_gt hp)

/-- One derived gain applies to every native carrier input. -/
theorem weight_action (T : Operator h) (x : Carrier h) :
    nativeWeight h (act h T x) = gain h p hp T * nativeWeight h x := by
  obtain ⟨k, z, rfl⟩ := operator_normal_form h p hp T
  rw [value_weight, gain_value]

/-- Every positive native reference recovers the same numerical gain. -/
theorem gain_from_native_reference (T : Operator h) (x : Carrier h)
    (hx : 0 < nativeWeight h x) :
    nativeWeight h (act h T x) / nativeWeight h x = gain h p hp T := by
  rw [weight_action h p hp T]
  exact mul_div_cancel_right₀ _ (ne_of_gt hx)

theorem gain_reference_independent (q : V) (hq : 0 < W q) (T : Operator h) :
    gain h p hp T = gain h q hq T := by
  have he := weight_action h p hp T (sourceResponse h q hq).reference
  rw [reference_weight h q hq] at he
  unfold gain
  rw [he]
  exact (mul_div_cancel_right₀ _ (ne_of_gt hq)).symm

theorem gain_nonnegative (T : Operator h) : 0 ≤ gain h p hp T :=
  div_nonneg ((nativePositiveQuadratic h).nonnegative _) (le_of_lt hp)

@[simp]theorem gain_zero : gain h p hp 0 = 0 := by
  simp [gain, (nativePositiveQuadratic h).zero]

@[simp]theorem gain_one : gain h p hp 1 = 1 := by
  unfold gain
  rw [act_one, reference_weight, div_self (ne_of_gt hp)]

/-- Numerical serial multiplication is derived from universal native action. -/
theorem gain_mul (T S : Operator h) :
    gain h p hp (T * S) = gain h p hp T * gain h p hp S := by
  change nativeWeight h (act h (T * S) (sourceResponse h p hp).reference) / W p = _
  rw [act_mul, weight_action h p hp T]
  unfold gain
  ring

/-- Faithful zero gain concerns operators. Distinct phases can share a gain. -/
theorem gain_eq_zero_iff (T : Operator h) : gain h p hp T = 0 ↔ T = 0 := by
  constructor
  · intro he
    have hz : nativeWeight h (act h T (sourceResponse h p hp).reference) = 0 := by
      have he' := (div_eq_iff (ne_of_gt hp)).mp he
      simpa using he'
    have hv := (nativeWeight_eq_zero_iff h _).mp hz
    apply generatedEvaluation_injective h p hp
    change act h T (sourceResponse h p hp).reference =
      act h 0 (sourceResponse h p hp).reference
    simpa using hv
  · rintro rfl
    exact gain_zero h p hp

theorem conjugation_half :
    canonicalConjugation h p hp (nativeGate h).generatedH = (nativeGate h).generatedH := by
  change canonicalConjugation h p hp
    ((nativeGate h).generatedA * (nativeGate h).generatedB) = _
  rw [map_mul, canonicalConjugation_a, canonicalConjugation_b]
  exact mul_comm _ _

theorem conjugation_phase :
    canonicalConjugation h p hp (nativeGate h).generatedU = -(nativeGate h).generatedU := by
  have hs : (nativeGate h).generatedA * (nativeGate h).generatedA +
      (nativeGate h).generatedB * (nativeGate h).generatedB = 0 :=
    Subtype.ext (nativeGate h).same_coefficients
  change canonicalConjugation h p hp
    ((nativeGate h).generatedA * (nativeGate h).generatedA +
      (nativeGate h).generatedA * (nativeGate h).generatedA) = _
  simp only [map_add, map_mul, canonicalConjugation_a]
  change (nativeGate h).generatedB * (nativeGate h).generatedB +
      (nativeGate h).generatedB * (nativeGate h).generatedB =
    -((nativeGate h).generatedA * (nativeGate h).generatedA +
      (nativeGate h).generatedA * (nativeGate h).generatedA)
  linear_combination 2 * hs

theorem conjugation_value (k : ℕ) (z : LocalHistoryReadoutOrderWall.Residual) :
    canonicalConjugation h p hp
      (Arithmetic.value (nativeGate h).generatedU (nativeGate h).generatedH k z) =
    Arithmetic.value (nativeGate h).generatedU (nativeGate h).generatedH k
      (Arithmetic.conjugatePair z) := by
  change canonicalConjugation h p hp
    ((nativeGate h).generatedH ^ k *
      ((z.1 : Operator h) + (z.2 : Operator h) * (nativeGate h).generatedU)) =
    (nativeGate h).generatedH ^ k *
      ((z.1 : Operator h) + ((-z.2 : ℤ) : Operator h) * (nativeGate h).generatedU)
  rw [map_mul, map_pow, conjugation_half, map_add, map_mul,
    map_intCast, map_intCast, conjugation_phase]
  push_cast
  ring

theorem gain_conjugation (T : Operator h) :
    gain h p hp (canonicalConjugation h p hp T) = gain h p hp T := by
  obtain ⟨k, z, rfl⟩ := operator_normal_form h p hp T
  rw [conjugation_value, gain_value, gain_value]
  simp [presentationGain, Arithmetic.conjugatePair]

/-- Single-echo numerical gain. -/
theorem gain_paired_echo (T : Operator h) :
    gain h p hp (T * canonicalConjugation h p hp T) = gain h p hp T ^ 2 := by
  rw [gain_mul, gain_conjugation, pow_two]

/-- Exact endomorphism echo in a selected normal form. -/
theorem value_paired_echo (k : ℕ) (z : LocalHistoryReadoutOrderWall.Residual) :
    Arithmetic.value (nativeGate h).generatedU (nativeGate h).generatedH k z *
      canonicalConjugation h p hp
        (Arithmetic.value (nativeGate h).generatedU (nativeGate h).generatedH k z) =
      (nativeGate h).generatedH ^ (2 * k) *
        ((z.1 * z.1 + z.2 * z.2 : ℤ) : Operator h) := by
  have hu : (nativeGate h).generatedU ^ 2 = -(1 : Operator h) :=
    Subtype.ext (nativeGate h).phase_square
  rw [conjugation_value]
  change ((nativeGate h).generatedH ^ k *
      ((z.1 : Operator h) + (z.2 : Operator h) * (nativeGate h).generatedU)) *
    ((nativeGate h).generatedH ^ k *
      ((z.1 : Operator h) + ((-z.2 : ℤ) : Operator h) * (nativeGate h).generatedU)) =
    (nativeGate h).generatedH ^ (2 * k) *
      ((z.1 * z.1 + z.2 * z.2 : ℤ) : Operator h)
  simp only [Int.cast_add, Int.cast_mul, Int.cast_neg,
    show 2 * k = k + k by omega, pow_add]
  linear_combination
    -((nativeGate h).generatedH ^ k) ^ 2 * (z.2 : Operator h) ^ 2 * hu

theorem half_double_apply (x : Carrier h) :
    act h (nativeGate h).generatedH x + act h (nativeGate h).generatedH x = x := by
  have hh : (nativeGate h).generatedH + (nativeGate h).generatedH = (1 : Operator h) := by
    rw [← two_mul]
    exact (sourceResponse h p hp).operatorResponse.arithmetic_parameters.2.1
  exact congrArg (fun T : Operator h => act h T x) hh

theorem pairing_half_adjoint (x y : Carrier h) :
    pairing h (act h (nativeGate h).generatedH x) y =
      pairing h x (act h (nativeGate h).generatedH y) := by
  have hx := pairing_add_left h
    (act h (nativeGate h).generatedH x) (act h (nativeGate h).generatedH x) y
  have hy := pairing_add_right h x
    (act h (nativeGate h).generatedH y) (act h (nativeGate h).generatedH y)
  rw [half_double_apply h p hp x] at hx
  rw [half_double_apply h p hp y] at hy
  linarith

theorem pairing_half_power_adjoint (k : ℕ) (x y : Carrier h) :
    pairing h (act h ((nativeGate h).generatedH ^ k) x) y =
      pairing h x (act h ((nativeGate h).generatedH ^ k) y) := by
  induction k generalizing x y with
  | zero => simp
  | succ k ih =>
    calc
      pairing h (act h ((nativeGate h).generatedH ^ (k + 1)) x) y =
        pairing h (act h (nativeGate h).generatedH
          (act h ((nativeGate h).generatedH ^ k) x)) y := by
        rw [pow_succ', act_mul]
      _ = pairing h (act h ((nativeGate h).generatedH ^ k) x)
          (act h (nativeGate h).generatedH y) := pairing_half_adjoint h p hp _ _
      _ = pairing h x (act h ((nativeGate h).generatedH ^ k)
          (act h (nativeGate h).generatedH y)) := ih _ _
      _ = pairing h x (act h ((nativeGate h).generatedH ^ (k + 1)) y) := by
        rw [pow_succ]
        exact (congrArg (pairing h x)
          (act_mul h ((nativeGate h).generatedH ^ k)
            (nativeGate h).generatedH y)).symm

omit hp in
theorem pairing_gaussian_adjoint (z : LocalHistoryReadoutOrderWall.Residual) (x y : Carrier h) :
    pairing h (act h (Arithmetic.gaussian (nativeGate h).generatedU z) x) y =
      pairing h x (act h
        (Arithmetic.gaussian (nativeGate h).generatedU (Arithmetic.conjugatePair z)) y) := by
  simp only [gaussian_action, Arithmetic.conjugatePair, Prod.fst, Prod.snd,
    pairing_add_left, pairing_add_right, pairing_zsmul_left, pairing_zsmul_right,
    Int.cast_neg]
  rw [phase_pairing_skew]
  ring

/-- Canonical conjugation is the adjoint for this derived pairing. -/
theorem pairing_operator_adjoint (T : Operator h) (x y : Carrier h) :
    pairing h (act h T x) y =
      pairing h x (act h (canonicalConjugation h p hp T) y) := by
  obtain ⟨k, z, rfl⟩ := operator_normal_form h p hp T
  rw [conjugation_value]
  simp only [Arithmetic.value, act_mul]
  rw [pairing_half_power_adjoint h p hp, pairing_gaussian_adjoint]
  rw [act_commute]

theorem pairing_operator_covariance (T : Operator h) (x y : Carrier h) :
    pairing h (act h T x) (act h T y) = gain h p hp T * pairing h x y := by
  unfold pairing PositiveQuadraticPolarization.polarization
  rw [← act_map_add, weight_action h p hp T, weight_action h p hp T,
    weight_action h p hp T]
  ring

theorem pairing_echo (T : Operator h) (x y : Carrier h) :
    pairing h x (act h (T * canonicalConjugation h p hp T) y) =
      gain h p hp T * pairing h x y := by
  have he := pairing_operator_adjoint h p hp (canonicalConjugation h p hp T)
    x (act h (canonicalConjugation h p hp T) y)
  rw [canonicalConjugation_involutive h p hp T] at he
  rw [act_mul, ← he, pairing_operator_covariance h p hp, gain_conjugation]

/-- A normalized pair of numeric gains gives an exact paired-echo identity. -/
theorem normalized_paired_echo (T S : Operator h)
    (normalized : gain h p hp T + gain h p hp S = 1) :
    T * canonicalConjugation h p hp T + S * canonicalConjugation h p hp S = 1 := by
  let N : Operator h :=
    T * canonicalConjugation h p hp T + S * canonicalConjugation h p hp S - 1
  have hn (x y : Carrier h) : pairing h x (act h N y) = 0 := by
    dsimp only [N]
    rw [act_sub, act_add, act_one, pairing_sub_right, pairing_add_right,
      pairing_echo h p hp T, pairing_echo h p hp S, ← add_mul, normalized]
    ring
  have hz (y : Carrier h) : act h N y = 0 := by
    apply (nativeWeight_eq_zero_iff h _).mp
    rw [← pairing_diagonal h (act h N y)]
    exact hn (act h N y) y
  have hN : N = 0 := by
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro y
    exact hz y
  exact sub_eq_zero.mp hN

end PositiveReference

end IDT.QMClosure.NativeOperatorQuadraticReadout
