import Proofs.QMClosure.OperationalQuadraticReconstruction
import Proofs.QMClosure.DyadicResponseExtension
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic

/-!
# Single-column calibration and faithful generated scalar arithmetic

A commutative semiring, transparent swap-root coefficient equations, one real
multiplicative scalar response, and one normalized native column are supplied.
The old additive reconstruction is reused to derive additive inverses. The new
claim is faithful Gaussian-dyadic arithmetic, independent of a global quadratic
response law. Conjugation is constructed only on that generated arithmetic.
No response-conjugation law, positivity, count order, global conservation,
finite dimensionality, domain axiom, characteristic-zero axiom, or QM closure
is an input or a conclusion silently attached to the reconstruction.
-/

namespace IDT.QMClosure.SingleCalibrationScalarFaithfulness

noncomputable section

open LocalHistoryReadoutOrderWall

/-- The scalar hypotheses. The response has no assumed additive law. -/
structure Contract (S : Type*) [CommSemiring S] where
  a : S
  b : S
  transparent : a + b = 1
  same : a * a + b * b = 0
  cross : a * b + b * a = 1
  weight : S → ℝ
  multiplicative : ∀ x y, weight (x * y) = weight x * weight y
  column : weight a + weight b = 1

namespace Contract

variable {S : Type*} [CommSemiring S] (C : Contract S)

/-- Scalar multiplication regarded as an additive endomorphism. -/
def mulEnd (c : S) : S →+ S where
  toFun x := c * x
  map_zero' := mul_zero c
  map_add' := mul_add c

/-- This adapter reuses the existing transparent swap-root theorem. -/
def additiveReconstruction :
    TransparentSwapRoot.Reconstruction (mulEnd C.a) (mulEnd C.b) := by
  apply TransparentSwapRoot.reconstruct
  · intro x
    change C.a * x + C.b * x = x
    rw [← add_mul, C.transparent, one_mul]
  · intro p
    apply Prod.ext
    · change C.a * (C.a * p.1 + C.b * p.2) +
        C.b * (C.b * p.1 + C.a * p.2) = p.2
      calc
        _ = (C.a * C.a + C.b * C.b) * p.1 +
            (C.a * C.b + C.b * C.a) * p.2 := by ring
        _ = p.2 := by rw [C.same, C.cross]; simp
    · change C.b * (C.a * p.1 + C.b * p.2) +
        C.a * (C.b * p.1 + C.a * p.2) = p.1
      calc
        _ = (C.a * C.b + C.b * C.a) * p.1 +
            (C.a * C.a + C.b * C.b) * p.2 := by ring
        _ = p.1 := by rw [C.same, C.cross]; simp

/-- The additive group preserves the supplied additive monoid exactly. -/
abbrev additiveGroup : AddCommGroup S :=
  OperationalQuadraticReconstruction.groupFromAntipodes
    (TransparentSwapRoot.phase (mulEnd C.a)) C.additiveReconstruction.cancellation

/-- The commutative ring structure is derived, including its additive inverse. -/
abbrev scalarRing : CommRing S :=
  { (inferInstance : CommSemiring S), C.additiveGroup with }

def phaseScalar : S := C.a * C.a + C.a * C.a

def halfScalar : S := C.a * C.b

theorem phase_apply (x : S) :
    TransparentSwapRoot.phase (mulEnd C.a) x = C.phaseScalar * x := by
  change C.a * (C.a * x) + C.a * (C.a * x) = (C.a * C.a + C.a * C.a) * x
  ring

theorem phase_square_add_one : C.phaseScalar * C.phaseScalar + 1 = 0 := by
  have h := C.additiveReconstruction.cancellation (1 : S)
  rw [C.phase_apply, C.phase_apply, mul_one] at h
  simpa only [add_comm] using h

theorem double_half : (2 : S) * C.halfScalar = 1 := by
  calc
    _ = C.a * C.b + C.b * C.a := by dsimp [halfScalar]; ring
    _ = 1 := C.cross

theorem coefficient_a : C.a = C.halfScalar * (1 + C.phaseScalar) := by
  have h := C.additiveReconstruction.coefficientA (1 : S)
  change C.a * 1 = C.a * (C.b * (1 + TransparentSwapRoot.phase (mulEnd C.a) 1)) at h
  rw [C.phase_apply, mul_one, mul_one] at h
  simpa only [halfScalar, mul_assoc] using h

theorem fourth_coefficients_equal : C.a ^ 4 = C.b ^ 4 := by
  letI := C.scalarRing
  have hs : C.a * C.a = -(C.b * C.b) := eq_neg_of_add_eq_zero_left C.same
  calc
    C.a ^ 4 = (C.a * C.a) ^ 2 := by ring
    _ = (C.b * C.b) ^ 2 := by rw [hs]; ring
    _ = C.b ^ 4 := by ring

theorem weight_one : C.weight 1 = 1 := by
  have ha : C.weight C.a = C.weight 1 * C.weight C.a := by
    simpa using C.multiplicative 1 C.a
  have hb : C.weight C.b = C.weight 1 * C.weight C.b := by
    simpa using C.multiplicative 1 C.b
  calc
    C.weight 1 = C.weight 1 * (C.weight C.a + C.weight C.b) := by
      rw [C.column, mul_one]
    _ = C.weight C.a + C.weight C.b := by rw [mul_add, ← ha, ← hb]
    _ = 1 := C.column

theorem weight_zero : C.weight 0 = 0 := by
  have ha : C.weight 0 = C.weight C.a * C.weight 0 := by
    simpa using C.multiplicative C.a 0
  have hb : C.weight 0 = C.weight C.b * C.weight 0 := by
    simpa using C.multiplicative C.b 0
  have he : C.weight 0 + C.weight 0 =
      (C.weight C.a + C.weight C.b) * C.weight 0 := by
    rw [add_mul, ← ha, ← hb]
  rw [C.column, one_mul] at he
  linarith

theorem weight_pow (x : S) (k : ℕ) : C.weight (x ^ k) = C.weight x ^ k := by
  induction k with
  | zero => simpa using C.weight_one
  | succ k ih => rw [pow_succ, C.multiplicative, ih, pow_succ]

/-- Real codomain and the one column exclude the opposite-sign fourth root. -/
theorem native_weights : C.weight C.a = 1 / 2 ∧ C.weight C.b = 1 / 2 := by
  have hf := congrArg C.weight C.fourth_coefficients_equal
  rw [C.weight_pow, C.weight_pow] at hf
  have hs : C.weight C.a ^ 2 = C.weight C.b ^ 2 := by
    have hsquares : (C.weight C.a ^ 2) ^ 2 = (C.weight C.b ^ 2) ^ 2 := by
      nlinarith [hf]
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsquares with h | h
    · exact h
    · nlinarith [sq_nonneg (C.weight C.a), sq_nonneg (C.weight C.b)]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with h | h
  · constructor <;> linarith [C.column]
  · linarith [C.column]

theorem weight_half : C.weight C.halfScalar = 1 / 4 := by
  rw [halfScalar, C.multiplicative, C.native_weights.1, C.native_weights.2]
  norm_num

theorem weight_two : C.weight (2 : S) = 4 := by
  have hh := congrArg C.weight C.double_half
  rw [C.multiplicative, C.weight_half, C.weight_one] at hh
  linarith

theorem weight_phase : C.weight C.phaseScalar = 1 := by
  have hu : C.phaseScalar = (2 : S) * (C.a * C.a) := by
    dsimp [phaseScalar]; ring
  rw [hu, C.multiplicative, C.multiplicative, C.weight_two, C.native_weights.1]
  norm_num

end Contract

/-- Characteristic zero follows from a single multiplicative doubling scale.
The proof uses no order or cancellation in the scalar ring. -/
theorem charZero_of_real_doubling {R : Type*} [Ring R]
    (w : R → ℝ) (wmul : ∀ x y, w (x * y) = w x * w y)
    (wone : w 1 = 1) (wtwo : w (2 : R) = 4) : CharZero R := by
  have wpow : ∀ k : ℕ, w ((2 : R) ^ k) = (4 : ℝ) ^ k := by
    intro k
    induction k with
    | zero => simpa using wone
    | succ k ih => rw [pow_succ, wmul, ih, wtwo, pow_succ]
  apply charZero_of_inj_zero
  intro n hn
  by_contra hnzero
  have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
  have reduce : ∀ m : ℕ, ((m % n : ℕ) : R) = (m : R) := by
    intro m
    have he := congrArg (fun q : ℕ => (q : R)) (Nat.mod_add_div m n)
    simpa only [Nat.cast_add, Nat.cast_mul, hn, zero_mul, add_zero] using he
  let f : ℕ → Fin n := fun k => ⟨2 ^ k % n, Nat.mod_lt _ hnpos⟩
  obtain ⟨j, k, hjk, he⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hmod : 2 ^ j % n = 2 ^ k % n := congrArg Fin.val he
  have hcast : (2 : R) ^ j = (2 : R) ^ k := by
    calc
      _ = ((2 ^ j : ℕ) : R) := by norm_cast
      _ = ((2 ^ j % n : ℕ) : R) := (reduce _).symm
      _ = ((2 ^ k % n : ℕ) : R) := congrArg (fun q : ℕ => (q : R)) hmod
      _ = ((2 ^ k : ℕ) : R) := reduce _
      _ = (2 : R) ^ k := by norm_cast
  have hw : (4 : ℝ) ^ j = (4 : ℝ) ^ k := by
    simpa only [wpow] using congrArg w hcast
  exact hjk ((pow_right_strictMono₀ (by norm_num : (1 : ℝ) < 4)).injective hw)

namespace Contract

variable {S : Type*} [CommSemiring S] (C : Contract S)

/-- Its natural cast is definitionally the supplied semiring natural cast. -/
def characteristicZero : letI := C.scalarRing; CharZero S := by
  letI := C.scalarRing
  exact charZero_of_real_doubling C.weight C.multiplicative C.weight_one C.weight_two

/-- Adapter facts for the generic faithful arithmetic API below. -/
theorem arithmetic_parameters : letI := C.scalarRing
    C.phaseScalar ^ 2 = -(1 : S) ∧ (2 : S) * C.halfScalar = 1 ∧
    C.a = C.halfScalar * (1 + C.phaseScalar) ∧
    C.b = C.halfScalar * (1 - C.phaseScalar) := by
  letI := C.scalarRing
  have hu : C.phaseScalar ^ 2 = -(1 : S) := by
    have hh := C.phase_square_add_one
    rw [← pow_two] at hh
    exact eq_neg_of_add_eq_zero_left hh
  refine ⟨hu, C.double_half, C.coefficient_a, ?_⟩
  have hb : C.b = 1 - C.a := by linear_combination C.transparent
  rw [hb, C.coefficient_a]
  linear_combination -C.double_half

end Contract

namespace Arithmetic

variable {R : Type*} [CommRing R] [CharZero R]
variable (u h : R) (hu : u ^ 2 = -(1 : R)) (hh : (2 : R) * h = 1)

def gaussian (z : Residual) : R := (z.1 : R) + (z.2 : R) * u

def conjugatePair (z : Residual) : Residual := (z.1, -z.2)

theorem gaussian_add (z t : Residual) :
    gaussian u (z + t) = gaussian u z + gaussian u t := by
  dsimp [gaussian]; push_cast; ring

theorem gaussian_neg (z : Residual) : gaussian u (-z) = -gaussian u z := by
  dsimp [gaussian]; push_cast; ring

theorem gaussian_serial (hu : u ^ 2 = -(1 : R)) (z t : Residual) :
    gaussian u (serial z t) = gaussian u z * gaussian u t := by
  dsimp [gaussian, serial]
  push_cast
  calc
    _ = (z.1 : R) * t.1 + (z.2 : R) * t.2 * u ^ 2 +
        ((z.1 : R) * t.2 + (z.2 : R) * t.1) * u := by rw [hu]; ring
    _ = _ := by ring

theorem gaussian_conjugate_product (hu : u ^ 2 = -(1 : R)) (z : Residual) :
    gaussian u z * gaussian u (conjugatePair z) =
      ((z.1 ^ 2 + z.2 ^ 2 : ℤ) : R) := by
  dsimp [gaussian, conjugatePair]
  push_cast
  calc
    _ = (z.1 : R) ^ 2 - (z.2 : R) ^ 2 * u ^ 2 := by ring
    _ = _ := by rw [hu]; ring

theorem gaussian_eq_zero_iff (hu : u ^ 2 = -(1 : R)) (z : Residual) : gaussian u z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have hn : ((z.1 ^ 2 + z.2 ^ 2 : ℤ) : R) = 0 := by
      rw [← gaussian_conjugate_product u hu, hz, zero_mul]
    have hi : z.1 ^ 2 + z.2 ^ 2 = 0 := Int.cast_eq_zero.mp hn
    apply Prod.ext <;> change _ = (0 : ℤ)
    · nlinarith [sq_nonneg z.1, sq_nonneg z.2]
    · nlinarith [sq_nonneg z.1, sq_nonneg z.2]
  · rintro rfl
    simp [gaussian]

theorem gaussian_injective (hu : u ^ 2 = -(1 : R)) : Function.Injective (gaussian u : Residual → R) := by
  intro z t hzt
  have hz : gaussian u (z - t) = 0 := by
    dsimp [gaussian] at *
    push_cast
    linear_combination hzt
  have he := (gaussian_eq_zero_iff u hu (z - t)).mp hz
  exact sub_eq_zero.mp he

theorem gaussian_scale (k : ℕ) (z : Residual) :
    gaussian u (DyadicResponseExtension.scale k z) = (2 : R) ^ k * gaussian u z := by
  dsimp [gaussian, DyadicResponseExtension.scale]
  push_cast
  ring

def value (k : ℕ) (z : Residual) : R := h ^ k * gaussian u z

theorem denominator_unit (hh : (2 : R) * h = 1) (k : ℕ) : (2 : R) ^ k * h ^ k = 1 := by
  rw [← mul_pow, hh, one_pow]

theorem clear_denominator (hh : (2 : R) * h = 1) (k l : ℕ) (z : Residual) :
    (2 : R) ^ (k + l) * value u h k z =
      gaussian u (DyadicResponseExtension.scale l z) := by
  rw [gaussian_scale]
  calc
    _ = (2 : R) ^ l * ((2 : R) ^ k * h ^ k) * gaussian u z := by
      dsimp [value]; rw [pow_add]; ring
    _ = _ := by rw [denominator_unit h hh]; ring

/-- Cross denominators have the orientation `2^l z = 2^k t`. -/
theorem value_eq_iff (hu : u ^ 2 = -(1 : R)) (hh : (2 : R) * h = 1) (k l : ℕ) (z t : Residual) :
    value u h k z = value u h l t ↔
      DyadicResponseExtension.scale l z = DyadicResponseExtension.scale k t := by
  constructor
  · intro he
    apply gaussian_injective u hu
    rw [← clear_denominator u h hh k l z, ← clear_denominator u h hh l k t,
      Nat.add_comm l k, he]
  · intro he
    have hc : (2 : R) ^ (k + l) * value u h k z =
        (2 : R) ^ (k + l) * value u h l t := by
      rw [clear_denominator u h hh k l z, Nat.add_comm k l,
        clear_denominator u h hh l k t, he]
    have hc' := congrArg (fun x : R => h ^ (k + l) * x) hc
    have hi : h ^ (k + l) * (2 : R) ^ (k + l) = 1 := by
      rw [mul_comm]; exact denominator_unit h hh _
    simpa only [← mul_assoc, hi, one_mul] using hc'

/-- The exact integer cross-denominator criterion for the triple presentation. -/
theorem triple_eq_iff (hu : u ^ 2 = -(1 : R)) (hh : (2 : R) * h = 1) (k l : ℕ) (m n r s : ℤ) :
    value u h k (m, n) = value u h l (r, s) ↔
      (2 : ℤ) ^ l * m = (2 : ℤ) ^ k * r ∧
      (2 : ℤ) ^ l * n = (2 : ℤ) ^ k * s := by
  rw [value_eq_iff u h hu hh]
  simp only [DyadicResponseExtension.scale, Prod.mk.injEq]

def dyadicEval : DyadicResponseExtension.Dyadic → R :=
  Quotient.lift (fun p : DyadicResponseExtension.Presentation =>
    value u h p.denominator p.numerator)
    (fun p q he => (value_eq_iff u h hu hh _ _ _ _).mpr he)

theorem dyadicEval_fraction (k : ℕ) (z : Residual) :
    dyadicEval u h hu hh (DyadicResponseExtension.fraction z k) = value u h k z := rfl

theorem dyadicEval_injective : Function.Injective (dyadicEval u h hu hh) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro p q he
  apply Quotient.sound
  exact (value_eq_iff u h hu hh _ _ _ _).mp he

theorem value_zero (k : ℕ) : value u h k 0 = 0 := by simp [value, gaussian]

theorem value_one : value u h 0 (1, 0) = 1 := by simp [value, gaussian]

theorem value_neg (k : ℕ) (z : Residual) :
    value u h k (-z) = -value u h k z := by
  simp only [value, gaussian_neg]
  ring

theorem value_add (hh : (2 : R) * h = 1) (k l : ℕ) (z t : Residual) :
    value u h k z + value u h l t =
      value u h (k + l)
        (DyadicResponseExtension.scale l z + DyadicResponseExtension.scale k t) := by
  simp only [value, gaussian_add, gaussian_scale]
  have hk := denominator_unit h hh k
  have hl := denominator_unit h hh l
  calc
    _ = h ^ k * gaussian u z * ((2 : R) ^ l * h ^ l) +
        h ^ l * gaussian u t * ((2 : R) ^ k * h ^ k) := by rw [hk, hl]; ring
    _ = _ := by rw [pow_add]; ring

theorem value_mul (hu : u ^ 2 = -(1 : R)) (k l : ℕ) (z t : Residual) :
    value u h k z * value u h l t = value u h (k + l) (serial z t) := by
  simp only [value, gaussian_serial u hu]
  rw [pow_add]
  ring

/-- This is exactly the generated image, rather than the whole ambient ring. -/
def generatedSubring : Subring R where
  carrier := {x | ∃ k z, x = value u h k z}
  zero_mem' := ⟨0, 0, (value_zero u h 0).symm⟩
  one_mem' := ⟨0, (1, 0), (value_one u h).symm⟩
  add_mem' := by
    rintro x y ⟨k, z, rfl⟩ ⟨l, t, rfl⟩
    exact ⟨k + l, _, value_add u h hh k l z t⟩
  neg_mem' := by
    rintro x ⟨k, z, rfl⟩
    exact ⟨k, -z, (value_neg u h k z).symm⟩
  mul_mem' := by
    rintro x y ⟨k, z, rfl⟩ ⟨l, t, rfl⟩
    exact ⟨k + l, serial z t, value_mul u h hu k l z t⟩

def present (k : ℕ) (z : Residual) : generatedSubring u h hu hh :=
  ⟨value u h k z, k, z, rfl⟩

theorem present_add (k l : ℕ) (z t : Residual) :
    present u h hu hh k z + present u h hu hh l t =
      present u h hu hh (k + l)
        (DyadicResponseExtension.scale l z + DyadicResponseExtension.scale k t) := by
  apply Subtype.ext
  exact value_add u h hh k l z t

theorem present_mul (k l : ℕ) (z t : Residual) :
    present u h hu hh k z * present u h hu hh l t =
      present u h hu hh (k + l) (serial z t) := by
  apply Subtype.ext
  exact value_mul u h hu k l z t

theorem conjugate_pair_scale (k : ℕ) (z : Residual) :
    conjugatePair (DyadicResponseExtension.scale k z) =
      DyadicResponseExtension.scale k (conjugatePair z) := by
  apply Prod.ext <;> simp [conjugatePair, DyadicResponseExtension.scale]

theorem conjugate_pair_add (z t : Residual) :
    conjugatePair (z + t) = conjugatePair z + conjugatePair t := by
  apply Prod.ext <;> simp [conjugatePair] <;> ring

theorem conjugate_pair_serial (z t : Residual) :
    conjugatePair (serial z t) = serial (conjugatePair z) (conjugatePair t) := by
  apply Prod.ext <;> dsimp [conjugatePair, serial] <;> ring

/-- Faithfulness makes this change of presentation independent of witnesses. -/
theorem conjugation_well_defined (hu : u ^ 2 = -(1 : R)) (hh : (2 : R) * h = 1)
    (k l : ℕ) (z t : Residual)
    (he : value u h k z = value u h l t) :
    value u h k (conjugatePair z) = value u h l (conjugatePair t) := by
  apply (value_eq_iff u h hu hh _ _ _ _).mpr
  have hc := congrArg conjugatePair ((value_eq_iff u h hu hh _ _ _ _).mp he)
  simpa only [conjugate_pair_scale] using hc

def conjugate (x : generatedSubring u h hu hh) : generatedSubring u h hu hh :=
  let k := Classical.choose x.property
  let z := Classical.choose (Classical.choose_spec x.property)
  present u h hu hh k (conjugatePair z)

theorem conjugate_present (k : ℕ) (z : Residual) :
    conjugate u h hu hh (present u h hu hh k z) =
      present u h hu hh k (conjugatePair z) := by
  apply Subtype.ext
  dsimp only [conjugate, present]
  apply conjugation_well_defined u h hu hh
  exact (Classical.choose_spec (Classical.choose_spec
    (show ∃ l t, value u h k z = value u h l t from ⟨k, z, rfl⟩))).symm

theorem presentation_exists (x : generatedSubring u h hu hh) :
    ∃ k z, x = present u h hu hh k z := by
  obtain ⟨k, z, he⟩ := x.property
  exact ⟨k, z, Subtype.ext he⟩

/-- A ring endomorphism of the generated image only. No law for w is asserted. -/
def conjugation : generatedSubring u h hu hh →+* generatedSubring u h hu hh where
  toFun := conjugate u h hu hh
  map_zero' := by
    have hz : (0 : generatedSubring u h hu hh) = present u h hu hh 0 0 := by
      apply Subtype.ext; simp [present, value, gaussian]
    rw [hz, conjugate_present]
    rfl
  map_one' := by
    have ho : (1 : generatedSubring u h hu hh) = present u h hu hh 0 (1, 0) := by
      apply Subtype.ext; simp [present, value, gaussian]
    rw [ho, conjugate_present]
    apply Subtype.ext; simp [present, conjugatePair, value, gaussian]
  map_add' := by
    intro x y
    obtain ⟨k, z, rfl⟩ := presentation_exists u h hu hh x
    obtain ⟨l, t, rfl⟩ := presentation_exists u h hu hh y
    rw [present_add, conjugate_present, conjugate_present, conjugate_present,
      present_add, conjugate_pair_add, conjugate_pair_scale, conjugate_pair_scale]
  map_mul' := by
    intro x y
    obtain ⟨k, z, rfl⟩ := presentation_exists u h hu hh x
    obtain ⟨l, t, rfl⟩ := presentation_exists u h hu hh y
    rw [present_mul, conjugate_present, conjugate_present, conjugate_present,
      present_mul, conjugate_pair_serial]

theorem conjugation_involutive : Function.Involutive (conjugation u h hu hh) := by
  intro x
  obtain ⟨k, z, rfl⟩ := presentation_exists u h hu hh x
  change conjugate u h hu hh (conjugate u h hu hh _) = _
  rw [conjugate_present, conjugate_present]
  simp [conjugatePair]

/-- The inverse is the same map. Its domain remains the generated image. -/
def conjugationEquiv : generatedSubring u h hu hh ≃+* generatedSubring u h hu hh :=
  { conjugation u h hu hh with
    invFun := conjugation u h hu hh
    left_inv := conjugation_involutive u h hu hh
    right_inv := conjugation_involutive u h hu hh }

def generatedHalf : generatedSubring u h hu hh := present u h hu hh 1 (1, 0)

def generatedPhase : generatedSubring u h hu hh := present u h hu hh 0 (0, 1)

theorem generatedHalf_value : (generatedHalf u h hu hh : R) = h := by
  simp [generatedHalf, present, value, gaussian]

theorem generatedPhase_value : (generatedPhase u h hu hh : R) = u := by
  simp [generatedPhase, present, value, gaussian]

theorem conjugation_half : conjugation u h hu hh (generatedHalf u h hu hh) =
    generatedHalf u h hu hh := by
  change conjugate u h hu hh (present u h hu hh 1 (1, 0)) = _
  rw [conjugate_present]
  rfl

theorem conjugation_phase : conjugation u h hu hh (generatedPhase u h hu hh) =
    generatedPhase u h hu hh ^ 3 := by
  apply Subtype.ext
  change (conjugate u h hu hh (present u h hu hh 0 (0, 1)) : R) = _
  rw [conjugate_present]
  simp only [present, value, gaussian, conjugatePair, pow_zero, one_mul,
    Int.cast_zero, Int.cast_one, Int.cast_neg, zero_add, neg_mul, one_mul,
    Subring.coe_pow, generatedPhase_value]
  calc
    -u = u * (-(1 : R)) := by ring
    _ = u * u ^ 2 := by rw [hu]
    _ = u ^ 3 := by ring

def generatedA : generatedSubring u h hu hh := present u h hu hh 1 (1, 1)

def generatedB : generatedSubring u h hu hh := present u h hu hh 1 (1, -1)

theorem generatedA_value : (generatedA u h hu hh : R) = h * (1 + u) := by
  simp [generatedA, present, value, gaussian]

theorem generatedB_value : (generatedB u h hu hh : R) = h * (1 - u) := by
  simp [generatedB, present, value, gaussian, sub_eq_add_neg]

theorem conjugation_a : conjugation u h hu hh (generatedA u h hu hh) =
    generatedB u h hu hh := by
  change conjugate u h hu hh (present u h hu hh 1 (1, 1)) = _
  rw [conjugate_present]
  rfl

theorem conjugation_b : conjugation u h hu hh (generatedB u h hu hh) =
    generatedA u h hu hh := by
  change conjugate u h hu hh (present u h hu hh 1 (1, -1)) = _
  rw [conjugate_present]
  apply Subtype.ext
  simp [generatedA, present, value, gaussian, conjugatePair]

end Arithmetic

namespace Contract

variable {S : Type*} [CommSemiring S] (C : Contract S)

/-- The public entry point retains the original semiring hypotheses.
All ring and characteristic-zero inputs to the arithmetic are discharged here. -/
theorem faithful_dyadic_arithmetic : letI := C.scalarRing
    letI := C.characteristicZero
    Function.Injective
      (Arithmetic.dyadicEval C.phaseScalar C.halfScalar
        C.arithmetic_parameters.1 C.double_half) := by
  letI := C.scalarRing
  letI := C.characteristicZero
  exact Arithmetic.dyadicEval_injective C.phaseScalar C.halfScalar
    C.arithmetic_parameters.1 C.double_half

/-- The coefficients reconstructed by the generated image are the supplied ones. -/
theorem generated_coefficients : letI := C.scalarRing
    letI := C.characteristicZero
    let hu := C.arithmetic_parameters.1
    (Arithmetic.generatedA C.phaseScalar C.halfScalar hu C.double_half : S) = C.a ∧
    (Arithmetic.generatedB C.phaseScalar C.halfScalar hu C.double_half : S) = C.b := by
  letI := C.scalarRing
  letI := C.characteristicZero
  constructor
  · rw [Arithmetic.generatedA_value, ← C.arithmetic_parameters.2.2.1]
  · rw [Arithmetic.generatedB_value, ← C.arithmetic_parameters.2.2.2]

end Contract

end

end IDT.QMClosure.SingleCalibrationScalarFaithfulness
