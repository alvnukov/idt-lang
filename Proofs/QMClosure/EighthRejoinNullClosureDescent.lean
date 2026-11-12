import Proofs.QMClosure.EighthRejoinReadoutCountermodels
import Proofs.QMClosure.TransparentFourthInitialHistoryPresentation
import Mathlib.Logic.Function.Basic

/-!
# Local null coalescence forces unique eighth-to-fourth readout descent

The positive certificate uses the derived commutativity of the
literal P8 source. A tailored local zero-coalescence law and multiplication by
the one fixed continuation s suffice for unique function-level P4 factorization.
The stronger normalized multiplicative contract transfers its laws to P4.
The P8 source still has a^4 != b^4. Readout factorization establishes neither
literal source equality nor general null insertion or destructive-quotient
descent. Physical primitive selection and full QM remain open.
-/

namespace IDT.QMClosure.EighthRejoinNullClosureDescent

noncomputable section

open EighthRejoinInitialPresentation

abbrev P8 := Presentation
abbrev P4 := TransparentFourthInitialHistoryPresentation.Presentation

local notation "a₄" => TransparentFourthInitialHistoryPresentation.a
local notation "b₄" => TransparentFourthInitialHistoryPresentation.b

def certificateA : P8 :=
  b ^ 7 + 34 * a ^ 2 * b ^ 5 + 83 * a ^ 3 * b ^ 4 +
    83 * a ^ 4 * b ^ 3 + 34 * a ^ 5 * b ^ 2 + a ^ 7

def certificateB : P8 :=
  9 * a * b ^ 4 + a ^ 2 * b ^ 3 + a ^ 3 * b ^ 2 + 9 * a ^ 4 * b

/-- Every coefficient is natural in this positive polynomial identity. -/
theorem positive_certificate :
    T * certificateA + s * certificateB = (a + b) ^ 9 := by
  dsimp [T, s, certificateA, certificateB]
  ring

theorem certificate_unit : T * certificateA + s * certificateB = 1 := by
  rw [positive_certificate, transparent, one_pow]

/-- The predecessor's positive half-evaluation polynomial is literally a half. -/
def scalarHalf : P8 :=
  a ^ 8 + 4 * a ^ 7 * b + 14 * a ^ 6 * b ^ 2 + 28 * a ^ 5 * b ^ 3 +
    35 * a ^ 4 * b ^ 4 + 28 * a ^ 3 * b ^ 5 +
    14 * a ^ 2 * b ^ 6 + 4 * a * b ^ 7

theorem scalar_half_identity : 2 * scalarHalf = 1 := by
  have hbinom : (a + b) ^ 8 = a ^ 8 + b ^ 8 +
      8 * a ^ 7 * b + 28 * a ^ 6 * b ^ 2 + 56 * a ^ 5 * b ^ 3 +
      70 * a ^ 4 * b ^ 4 + 56 * a ^ 3 * b ^ 5 +
      28 * a ^ 2 * b ^ 6 + 8 * a * b ^ 7 := by ring
  rw [← eighth_rejoin] at hbinom
  calc
    2 * scalarHalf = (a + b) ^ 8 := by rw [hbinom]; dsimp [scalarHalf]; ring
    _ = 1 := by rw [transparent, one_pow]

theorem fixed_continuation_fourth : s * a ^ 4 = s * b ^ 4 := by
  calc
    s * a ^ 4 = a ^ 8 + a ^ 4 * b ^ 4 := by dsimp [s]; ring
    _ = b ^ 8 + a ^ 4 * b ^ 4 := by rw [eighth_rejoin]
    _ = s * b ^ 4 := by dsimp [s]; ring

/-- The canonical map uses fourth rejoin only in its target. -/
def π : P8 →+* P4 :=
  eval a₄ b₄ TransparentFourthInitialHistoryPresentation.transparent (by
    calc
      a₄ ^ 8 = (a₄ ^ 4) ^ 2 := by ring
      _ = (b₄ ^ 4) ^ 2 := by rw [TransparentFourthInitialHistoryPresentation.fourth_rejoin]
      _ = b₄ ^ 8 := by ring)

@[simp] theorem pi_a : π a = a₄ := by simp [π]
@[simp] theorem pi_b : π b = b₄ := by simp [π]

theorem pi_surjective : Function.Surjective π := by
  intro q
  apply TransparentFourthInitialHistoryPresentation.presentation_induction
    (motive := fun q => ∃ p : P8, π p = q)
  · exact ⟨0, map_zero π⟩
  · exact ⟨1, map_one π⟩
  · exact ⟨a, pi_a⟩
  · exact ⟨b, pi_b⟩
  · intro x y hx hy
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    exact ⟨p + q, by rw [map_add, hp, hq]⟩
  · intro x y hx hy
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    exact ⟨p * q, by rw [map_mul, hp, hq]⟩

/-- Multiplication closure uses commutativity and two continuation rewrites. -/
def continuationCon : RingCon P8 where
  r x y := s * x = s * y
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
  add' := by
    intro w x y z h₁ h₂
    change s * w = s * x at h₁
    change s * y = s * z at h₂
    rw [mul_add, mul_add, h₁, h₂]
  mul' := by
    intro w x y z h₁ h₂
    change s * w = s * x at h₁
    change s * y = s * z at h₂
    calc
      s * (w * y) = (s * w) * y := by ring
      _ = (s * x) * y := by rw [h₁]
      _ = x * (s * y) := by ring
      _ = x * (s * z) := by rw [h₂]
      _ = s * (x * z) := by ring

/-- P4 receives its universal map because the continuation congruence has fourth rejoin. -/
def fourthToContinuation : P4 →+* continuationCon.Quotient :=
  TransparentFourthInitialHistoryPresentation.eval
    (continuationCon.mk' a) (continuationCon.mk' b)
    (by rw [← map_add, transparent, map_one])
    (by
      rw [← map_pow, ← map_pow]
      exact continuationCon.eq.mpr fixed_continuation_fourth)

theorem continuation_factor_map :
    fourthToContinuation.comp π = continuationCon.mk' := by
  apply hom_ext <;> simp [fourthToContinuation]

/-- Only this kernel containment is needed. No reverse containment is asserted. -/
theorem pi_fiber_continuation {x y : P8} (hxy : π x = π y) : s * x = s * y := by
  apply continuationCon.eq.mp
  calc
    continuationCon.mk' x = fourthToContinuation (π x) :=
      (DFunLike.congr_fun continuation_factor_map x).symm
    _ = fourthToContinuation (π y) := congrArg fourthToContinuation hxy
    _ = continuationCon.mk' y := DFunLike.congr_fun continuation_factor_map y

/-- The local sufficient package exposes every response premise used by descent. -/
structure LocalCoalescenceContract (R : P8 → ℝ) : Prop where
  unit_ne_zero : R 1 ≠ 0
  dark : R T = 0
  dark_product : R (T * certificateA) = R T * R certificateA
  fixed_continuation : ∀ p, R (s * p) = R s * R p
  coalesce : R (T * certificateA) = 0 → R (s * certificateB) = 0 →
    R (T * certificateA + s * certificateB) = 0

theorem continuation_response_nonzero {R : P8 → ℝ} (hR : LocalCoalescenceContract R) :
    R s ≠ 0 := by
  intro hs
  have hfirst : R (T * certificateA) = 0 := by
    rw [hR.dark_product, hR.dark, zero_mul]
  have hsecond : R (s * certificateB) = 0 := by
    rw [hR.fixed_continuation, hs, zero_mul]
  have hunit := hR.coalesce hfirst hsecond
  rw [certificate_unit] at hunit
  exact hR.unit_ne_zero hunit

theorem response_constant_on_pi_fibers {R : P8 → ℝ}
    (hR : LocalCoalescenceContract R) {x y : P8} (hxy : π x = π y) : R x = R y := by
  have he : R s * R x = R s * R y := by
    rw [← hR.fixed_continuation, ← hR.fixed_continuation, pi_fiber_continuation hxy]
  exact mul_left_cancel₀ (continuation_response_nonzero hR) he

/-- Chosen preimages define a function before its well-definedness theorem is used. -/
def descend (R : P8 → ℝ) : P4 → ℝ :=
  fun q => R (Function.surjInv pi_surjective q)

theorem descend_apply {R : P8 → ℝ} (hR : LocalCoalescenceContract R) (p : P8) :
    descend R (π p) = R p := by
  apply response_constant_on_pi_fibers hR
  exact Function.surjInv_eq pi_surjective (π p)

/-- Full unique function-level factorization through the literal P4 presentation. -/
theorem unique_fourth_factorization {R : P8 → ℝ} (hR : LocalCoalescenceContract R) :
    ∃! R4 : P4 → ℝ, R = R4 ∘ π := by
  refine ⟨descend R, ?_, ?_⟩
  · funext p
    exact (descend_apply hR p).symm
  · intro R4 hfactor
    funext q
    obtain ⟨p, rfl⟩ := pi_surjective q
    exact (congrFun hfactor p).symm.trans (descend_apply hR p).symm

/-- A simple multiplicative context is one consequence of the full factorization. -/
theorem contextual_fourth_response {R : P8 → ℝ} (hR : LocalCoalescenceContract R)
    (p q : P8) : R (p * a ^ 4 * q) = R (p * b ^ 4 * q) := by
  apply response_constant_on_pi_fibers hR
  simp only [map_mul, map_pow, pi_a, pi_b,
    TransparentFourthInitialHistoryPresentation.fourth_rejoin]

/-- The usual global sufficient package is parameterized by its dark element. -/
structure GlobalNullClosedContract {S : Type*} [Semiring S] (darkElement : S)
    (R : S → ℝ) : Prop where
  unit : R 1 = 1
  multiply : ∀ p q, R (p * q) = R p * R q
  dark : R darkElement = 0
  zero_add : ∀ p q, R p = 0 → R q = 0 → R (p + q) = 0

def local_of_global {R : P8 → ℝ} (hR : GlobalNullClosedContract T R) :
    LocalCoalescenceContract R where
  unit_ne_zero := by rw [hR.unit]; norm_num
  dark := hR.dark
  dark_product := hR.multiply T certificateA
  fixed_continuation := hR.multiply s
  coalesce := hR.zero_add (T * certificateA) (s * certificateB)

theorem pi_T : π T = a₄ ^ 2 + b₄ ^ 2 := by simp [T]

theorem descend_global_contract {R : P8 → ℝ} (hR : GlobalNullClosedContract T R) :
    GlobalNullClosedContract (a₄ ^ 2 + b₄ ^ 2) (descend R) := by
  have hlocal := local_of_global hR
  constructor
  · have he := descend_apply hlocal (1 : P8)
    simpa only [map_one, hR.unit] using he
  · intro x y
    obtain ⟨p, rfl⟩ := pi_surjective x
    obtain ⟨q, rfl⟩ := pi_surjective y
    rw [← map_mul, descend_apply hlocal, descend_apply hlocal,
      descend_apply hlocal, hR.multiply]
  · have he := descend_apply hlocal T
    rw [pi_T, hR.dark] at he
    exact he
  · intro x y hx hy
    obtain ⟨p, rfl⟩ := pi_surjective x
    obtain ⟨q, rfl⟩ := pi_surjective y
    have hp : R p = 0 := (descend_apply hlocal p).symm.trans hx
    have hq : R q = 0 := (descend_apply hlocal q).symm.trans hy
    rw [← map_add, descend_apply hlocal]
    exact hR.zero_add p q hp hq

theorem global_unique_fourth_factorization {R : P8 → ℝ}
    (hR : GlobalNullClosedContract T R) :
    ∃! R4 : P4 → ℝ, R = R4 ∘ π ∧
      GlobalNullClosedContract (a₄ ^ 2 + b₄ ^ 2) R4 := by
  refine ⟨descend R, ⟨?_, descend_global_contract hR⟩, ?_⟩
  · funext p
    exact (descend_apply (local_of_global hR) p).symm
  · intro R4 hfactor
    funext q
    obtain ⟨p, rfl⟩ := pi_surjective q
    exact (congrFun hfactor.1 p).symm.trans
      (descend_apply (local_of_global hR) p).symm

/-! Finite exact certificate controls for the predecessor's concrete responses. -/

theorem E2_first : EighthRejoinReadoutCountermodels.E2 (T * certificateA) = 0 := by
  simp [EighthRejoinReadoutCountermodels.E2_T]

theorem E2_second : EighthRejoinReadoutCountermodels.E2 (s * certificateB) = 1 := by
  have he := congrArg EighthRejoinReadoutCountermodels.E2 certificate_unit
  simpa only [map_add, map_mul, map_one,
    EighthRejoinReadoutCountermodels.E2_T, zero_mul, zero_add] using he

theorem E1_first : EighthRejoinReadoutCountermodels.E1 (T * certificateA) = 1 := by
  have he := congrArg EighthRejoinReadoutCountermodels.E1 certificate_unit
  simpa only [map_add, map_mul, map_one,
    EighthRejoinReadoutCountermodels.E1_s, zero_mul, add_zero] using he

theorem E3_first : EighthRejoinReadoutCountermodels.E3 (T * certificateA) = 1 := by
  have he := congrArg EighthRejoinReadoutCountermodels.E3 certificate_unit
  simpa only [map_add, map_mul, map_one,
    EighthRejoinReadoutCountermodels.E3_s, zero_mul, add_zero] using he

theorem E1_second : EighthRejoinReadoutCountermodels.E1 (s * certificateB) = 0 := by
  rw [map_mul, EighthRejoinReadoutCountermodels.E1_s, zero_mul]

theorem E3_second : EighthRejoinReadoutCountermodels.E3 (s * certificateB) = 0 := by
  rw [map_mul, EighthRejoinReadoutCountermodels.E3_s, zero_mul]

theorem certificate_norm_pairs :
    EighthRejoinReadoutCountermodels.X (T * certificateA) = 0 ∧
    EighthRejoinReadoutCountermodels.Y (T * certificateA) = 1 ∧
    EighthRejoinReadoutCountermodels.X (s * certificateB) = 1 ∧
    EighthRejoinReadoutCountermodels.Y (s * certificateB) = 0 := by
  simp only [EighthRejoinReadoutCountermodels.X, EighthRejoinReadoutCountermodels.Y]
  rw [E2_first, E1_first, E3_first, E2_second, E1_second, E3_second]
  norm_num

def CertificateZeroCoalescence (R : P8 → ℝ) : Prop :=
  R (T * certificateA) = 0 → R (s * certificateB) = 0 →
    R (T * certificateA + s * certificateB) = 0

theorem concrete_certificate_values :
    EighthRejoinReadoutCountermodels.W (T * certificateA) = 0 ∧
    EighthRejoinReadoutCountermodels.W (s * certificateB) = 0 ∧
    EighthRejoinReadoutCountermodels.W (T * certificateA + s * certificateB) = 1 ∧
    EighthRejoinReadoutCountermodels.V (T * certificateA) = 0 ∧
    EighthRejoinReadoutCountermodels.V (s * certificateB) = 0 ∧
    EighthRejoinReadoutCountermodels.V (T * certificateA + s * certificateB) = 1 := by
  rcases certificate_norm_pairs with ⟨hx₁, hy₁, hx₂, hy₂⟩
  norm_num [EighthRejoinReadoutCountermodels.W, EighthRejoinReadoutCountermodels.V,
    hx₁, hy₁, hx₂, hy₂, certificate_unit]

theorem concrete_local_coalescence_failures :
    ¬ CertificateZeroCoalescence EighthRejoinReadoutCountermodels.W ∧
    ¬ CertificateZeroCoalescence EighthRejoinReadoutCountermodels.V := by
  rcases concrete_certificate_values with ⟨hw₁, hw₂, hw₃, hv₁, hv₂, hv₃⟩
  constructor
  · intro h
    have he := h hw₁ hw₂
    rw [hw₃] at he
    norm_num at he
  · intro h
    have he := h hv₁ hv₂
    rw [hv₃] at he
    norm_num at he

/-!
The tailored local condition supplies separation of explicit certificate terms.
Its physical justification remains open. The factorized response need not be a
Gaussian norm, and P4 norm selection remains a separate analytic problem. The
existing P4 W_alpha null-ideal family is compatible with this descent target.
Full null-insertion invariance and destructive T=0 quotient descent require
additional arguments and premises.
-/

end

end IDT.QMClosure.EighthRejoinNullClosureDescent
