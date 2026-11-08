import Proofs.QMClosure.SingleCalibrationScalarFaithfulness
import Proofs.QMClosure.FiniteScalarReversalBoundary
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Initial scalar presentation for exact destructive two-channel composition

This registered Lean artifact presents the exact two-channel coefficient laws.

The input grammar is the free possibly noncommutative unital semiring on two
letters. The only extra relators are a + b = 1 and a² + b² = 0. In particular,
additive inverses, coefficient commutativity, characteristic zero, a detector
response, and a calibrated scale are not premises of the universal map.

The concrete complex model below is an algebraic consistency/separation model.
It does not supply a detector response or a physical calibration. The exact
physical origin of the destructive composition relator remains open. No claim
of a derivation of semiring grammar, readout, or full QM is made.

Normal-form completeness means existence and the exact integer
cross-denominator equality criterion. No canonical normalizer algorithm is supplied.
-/

namespace IDT.QMClosure.NativeInitialHistoryPresentation

noncomputable section

open LocalHistoryReadoutOrderWall

namespace ExactPair

/-- Exactly the two input coefficient laws, with no response law. -/
structure Laws (S : Type*) [Semiring S] where
  a : S
  b : S
  transparent : a + b = 1
  destructive : a * a + b * b = 0

namespace Laws

variable {S : Type*} [Semiring S] (L : Laws S)

/-- The cross law follows by expansion without additive cancellation. -/
theorem cross : L.a * L.b + L.b * L.a = 1 := by
  calc
    _ = (L.a * L.a + L.b * L.b) + (L.a * L.b + L.b * L.a) := by
      rw [L.destructive, zero_add]
    _ = (L.a + L.b) * (L.a + L.b) := by noncomm_ring
    _ = 1 := by rw [L.transparent, one_mul]

/-- Left multiplication preserves addition in every semiring. -/
def leftMulEnd (c : S) : S →+ S where
  toFun x := c * x
  map_zero' := mul_zero c
  map_add' := mul_add c

/-- Reuse the existing additive theorem without assuming coefficient commutation. -/
def reconstruction :
    TransparentSwapRoot.Reconstruction (leftMulEnd L.a) (leftMulEnd L.b) := by
  apply TransparentSwapRoot.reconstruct
  · intro x
    change L.a * x + L.b * x = x
    rw [← add_mul, L.transparent, one_mul]
  · intro p
    apply Prod.ext
    · change L.a * (L.a * p.1 + L.b * p.2) +
        L.b * (L.b * p.1 + L.a * p.2) = p.2
      calc
        _ = (L.a * L.a + L.b * L.b) * p.1 +
            (L.a * L.b + L.b * L.a) * p.2 := by noncomm_ring
        _ = p.2 := by rw [L.destructive, L.cross]; simp
    · change L.b * (L.a * p.1 + L.b * p.2) +
        L.a * (L.b * p.1 + L.a * p.2) = p.1
      calc
        _ = (L.a * L.b + L.b * L.a) * p.1 +
            (L.a * L.a + L.b * L.b) * p.2 := by noncomm_ring
        _ = p.1 := by rw [L.destructive, L.cross]; simp

/-- The group extends the supplied additive monoid, preserving its operations. -/
abbrev additiveGroup : AddCommGroup S :=
  OperationalQuadraticReconstruction.groupFromAntipodes
    (TransparentSwapRoot.phase (leftMulEnd L.a)) L.reconstruction.cancellation

/-- All multiplication remains the original possibly noncommutative multiplication. -/
abbrev scalarRing : Ring S :=
  { (inferInstance : Semiring S), L.additiveGroup with }

def half : S := L.a * L.b

def phase : S := L.a * L.a + L.a * L.a

theorem coefficients_commute : L.a * L.b = L.b * L.a := by
  have h := L.reconstruction.commute (1 : S)
  change L.a * (L.b * 1) = L.b * (L.a * 1) at h
  simpa only [mul_one] using h

theorem double_half : (2 : S) * L.half = 1 := by
  calc
    _ = L.a * L.b + L.b * L.a := by
      dsimp [half]
      rw [← L.coefficients_commute]
      noncomm_ring
    _ = 1 := L.cross

theorem phase_apply (x : S) :
    TransparentSwapRoot.phase (leftMulEnd L.a) x = L.phase * x := by
  change L.a * (L.a * x) + L.a * (L.a * x) =
    (L.a * L.a + L.a * L.a) * x
  noncomm_ring

theorem phase_square_add_one : L.phase * L.phase + 1 = 0 := by
  have h := L.reconstruction.cancellation (1 : S)
  rw [L.phase_apply, L.phase_apply, mul_one] at h
  simpa only [add_comm] using h

theorem coefficient_a : L.a = L.half * (1 + L.phase) := by
  have h := L.reconstruction.coefficientA (1 : S)
  change L.a * 1 = L.a * (L.b *
    (1 + TransparentSwapRoot.phase (leftMulEnd L.a) 1)) at h
  rw [L.phase_apply, mul_one, mul_one] at h
  simpa only [half, mul_assoc] using h

theorem coefficient_b : letI := L.scalarRing
    L.b = L.half * (1 - L.phase) := by
  letI := L.scalarRing
  have hb : L.b = 1 - L.a := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using L.transparent
  rw [hb, L.coefficient_a]
  have hh : L.half + L.half = 1 := by
    simpa only [two_mul] using L.double_half
  calc
    1 - L.half * (1 + L.phase) =
        (L.half + L.half) - L.half * (1 + L.phase) := by rw [hh]
    _ = L.half * (1 - L.phase) := by noncomm_ring

end Laws

end ExactPair

abbrev Free := FreeAlgebra ℕ Bool

def freeA : Free := FreeAlgebra.ι ℕ false

def freeB : Free := FreeAlgebra.ι ℕ true

/-- Only two additional equations are imposed on the free semiring. -/
inductive Rel : Free → Free → Prop
  | transparent : Rel (freeA + freeB) 1
  | destructive : Rel (freeA ^ 2 + freeB ^ 2) 0

def presentationCon : RingCon Free := ringConGen Rel

abbrev Presentation := presentationCon.Quotient

def a : Presentation := presentationCon.mk' freeA

def b : Presentation := presentationCon.mk' freeB

/-- Quotient equality is exactly derivability in the generated congruence. -/
theorem quotient_eq_iff (x y : Free) :
    presentationCon.mk' x = presentationCon.mk' y ↔ RingConGen.Rel Rel x y :=
  presentationCon.eq

theorem transparent : a + b = 1 := by
  change presentationCon.mk' (freeA + freeB) = presentationCon.mk' 1
  exact presentationCon.eq.mpr (RingConGen.Rel.of _ _ Rel.transparent)

theorem destructive : a * a + b * b = 0 := by
  change presentationCon.mk' (freeA * freeA + freeB * freeB) = presentationCon.mk' 0
  apply presentationCon.eq.mpr
  simpa only [pow_two] using (RingConGen.Rel.of _ _ Rel.destructive)

def laws : ExactPair.Laws Presentation := ⟨a, b, transparent, destructive⟩

/-- The presentation has a derived ring structure, with its original operations. -/
abbrev presentationRing : Ring Presentation := laws.scalarRing

attribute [local instance] presentationRing

section Universal

variable {S : Type*} [Semiring S] (x y : S)
  (htransparent : x + y = 1) (hdestructive : x ^ 2 + y ^ 2 = 0)

def freeEval : Free →+* S :=
  (FreeAlgebra.lift ℕ (fun t => if t then y else x)).toRingHom

@[simp] theorem freeEval_a : freeEval x y freeA = x := by
  simp [freeEval, freeA]

@[simp] theorem freeEval_b : freeEval x y freeB = y := by
  simp [freeEval, freeB]

include htransparent hdestructive in
theorem relation_in_kernel :
    presentationCon ≤ RingCon.ker (freeEval x y) := by
  apply RingCon.ringConGen_le
  intro p q h
  cases h with
  | transparent => simpa only [RingCon.ker_apply, map_add, map_one,
      freeEval_a, freeEval_b] using htransparent
  | destructive => simpa only [RingCon.ker_apply, map_add, map_pow, map_zero,
      freeEval_a, freeEval_b] using hdestructive

/-- The universal map permits every semiring target, including the zero semiring. -/
def eval : Presentation →+* S :=
  presentationCon.lift (freeEval x y)
    (relation_in_kernel x y htransparent hdestructive)

@[simp] theorem eval_a : eval x y htransparent hdestructive a = x := by
  simpa only [eval, a, RingCon.lift_mk'] using freeEval_a x y

@[simp] theorem eval_b : eval x y htransparent hdestructive b = y := by
  simpa only [eval, b, RingCon.lift_mk'] using freeEval_b x y

/-- A map out of the presentation is uniquely determined by its two generators. -/
theorem hom_ext {f g : Presentation →+* S} (ha : f a = g a) (hb : f b = g b) : f = g := by
  apply RingCon.Quotient.hom_ext
  have hfree : (f.comp presentationCon.mk').toNatAlgHom =
      (g.comp presentationCon.mk').toNatAlgHom := by
    apply FreeAlgebra.hom_ext
    funext t
    cases t
    · exact ha
    · exact hb
  exact congrArg AlgHom.toRingHom hfree

theorem eval_unique (f : Presentation →+* S) (ha : f a = x) (hb : f b = y) :
    f = eval x y htransparent hdestructive := by
  apply hom_ext
  · simpa using ha
  · simpa using hb

end Universal

/-- Induction on the original two-generator semiring syntax. -/
theorem presentation_induction (motive : Presentation → Prop)
    (hzero : motive 0) (hone : motive 1) (ha : motive a) (hb : motive b)
    (hadd : ∀ x y, motive x → motive y → motive (x + y))
    (hmul : ∀ x y, motive x → motive y → motive (x * y))
    (p : Presentation) : motive p := by
  obtain ⟨q, rfl⟩ := presentationCon.mk'_surjective p
  apply FreeAlgebra.induction
    (motive := fun q => motive (presentationCon.mk' q))
  · intro n
    have hn : motive (n : Presentation) := by
      induction n with
      | zero => simpa only [Nat.cast_zero] using hzero
      | succ n ih => simpa only [Nat.cast_succ] using hadd (n : Presentation) 1 ih hone
    simpa using hn
  · intro t
    cases t
    · exact ha
    · exact hb
  · intro x y hx hy
    simpa only [map_mul] using hmul _ _ hx hy
  · intro x y hx hy
    simpa only [map_add] using hadd _ _ hx hy

/-- Generated coefficient commutativity imposes nothing on an ambient target. -/
theorem generator_commutes (t : Bool) (p : Presentation) :
    Commute (presentationCon.mk' (FreeAlgebra.ι ℕ t)) p := by
  apply presentation_induction
    (motive := fun p => Commute (presentationCon.mk' (FreeAlgebra.ι ℕ t)) p)
  · change _ * 0 = 0 * _
    simp
  · exact Commute.one_right _
  · cases t
    · exact Commute.refl a
    · exact laws.coefficients_commute.symm
  · cases t
    · exact laws.coefficients_commute
    · exact Commute.refl b
  · intro x y hx hy
    exact hx.add_right hy
  · intro x y hx hy
    exact hx.mul_right hy

theorem multiplication_commutes (p q : Presentation) : p * q = q * p := by
  have hc : Commute p q := by
    apply presentation_induction (motive := fun p => Commute p q)
    · change 0 * q = q * 0
      simp
    · exact Commute.one_left q
    · exact generator_commutes false q
    · exact generator_commutes true q
    · intro x y hx hy
      exact hx.add_left hy
    · intro x y hx hy
      exact hx.mul_left hy
  exact hc

abbrev presentationCommRing : CommRing Presentation :=
  { presentationRing with mul_comm := multiplication_commutes }

attribute [local instance] presentationCommRing

def half : Presentation := laws.half

def phase : Presentation := laws.phase

theorem half_doubles : (2 : Presentation) * half = 1 := laws.double_half

theorem phase_square : phase ^ 2 = -(1 : Presentation) := by
  apply eq_neg_of_add_eq_zero_left
  simpa only [pow_two] using laws.phase_square_add_one

theorem coefficient_a : a = half * (1 + phase) := laws.coefficient_a

theorem coefficient_b : b = half * (1 - phase) := laws.coefficient_b

namespace ComplexModel

def a : ℂ := (1 + Complex.I) / 2

def b : ℂ := (1 - Complex.I) / 2

theorem transparent : a + b = 1 := by dsimp [a, b]; ring

theorem destructive : a ^ 2 + b ^ 2 = 0 := by
  dsimp [a, b]
  have hi := Complex.I_sq
  linear_combination hi / 2

theorem phase_square : Complex.I ^ 2 = -(1 : ℂ) := Complex.I_sq

theorem half_doubles : (2 : ℂ) * (1 / 2) = 1 := by norm_num

end ComplexModel

/-- An explicit algebraic model, unrelated to any calibration or detector response. -/
def complexEval : Presentation →+* ℂ :=
  eval ComplexModel.a ComplexModel.b ComplexModel.transparent ComplexModel.destructive

@[simp] theorem complexEval_a : complexEval a = ComplexModel.a := by simp [complexEval]

@[simp] theorem complexEval_b : complexEval b = ComplexModel.b := by simp [complexEval]

/-- Characteristic zero is derived from the existence of this unital model map. -/
abbrev presentationCharZero : CharZero Presentation where
  cast_injective := by
    intro m n h
    have hc : (m : ℂ) = (n : ℂ) := by
      simpa only [map_natCast] using congrArg complexEval h
    exact_mod_cast hc

attribute [local instance] presentationCharZero

@[simp] theorem complexEval_half : complexEval half = (1 / 2 : ℂ) := by
  change complexEval (a * b) = _
  rw [map_mul, complexEval_a, complexEval_b]
  dsimp [ComplexModel.a, ComplexModel.b]
  have hi := Complex.I_sq
  linear_combination -hi / 4

@[simp] theorem complexEval_phase : complexEval phase = Complex.I := by
  change complexEval (a * a + a * a) = _
  simp only [map_add, map_mul, complexEval_a]
  dsimp [ComplexModel.a]
  have hi := Complex.I_sq
  linear_combination hi / 2

namespace NormalForm

open SingleCalibrationScalarFaithfulness

abbrev Coefficients := LocalHistoryReadoutOrderWall.Residual

abbrev value (k : ℕ) (z : Coefficients) : Presentation := Arithmetic.value phase half k z

def generated : Subring Presentation :=
  Arithmetic.generatedSubring phase half phase_square half_doubles

/-- Semiring generation proves that every presented coefficient has a dyadic Gaussian form. -/
theorem exists_value (p : Presentation) : ∃ k z, p = value k z := by
  have hp : p ∈ generated := by
    apply presentation_induction (motive := fun p => p ∈ generated)
    · exact generated.zero_mem
    · exact generated.one_mem
    · change ∃ k z, a = value k z
      refine ⟨1, (1, 1), ?_⟩
      simpa [value, Arithmetic.value, Arithmetic.gaussian] using coefficient_a
    · change ∃ k z, b = value k z
      refine ⟨1, (1, -1), ?_⟩
      simpa [value, Arithmetic.value, Arithmetic.gaussian, sub_eq_add_neg] using coefficient_b
    · intro x y hx hy
      exact generated.add_mem hx hy
    · intro x y hx hy
      exact generated.mul_mem hx hy
  exact hp

/-- No primitive normalization algorithm is asserted by this equality criterion. -/
theorem cross_denominator (k l : ℕ) (m n r s : ℤ) :
    value k (m, n) = value l (r, s) ↔
      (2 : ℤ) ^ l * m = (2 : ℤ) ^ k * r ∧
      (2 : ℤ) ^ l * n = (2 : ℤ) ^ k * s :=
  Arithmetic.triple_eq_iff phase half phase_square half_doubles k l m n r s

@[simp] theorem complexEval_value (k : ℕ) (z : Coefficients) :
    complexEval (value k z) = Arithmetic.value Complex.I (1 / 2 : ℂ) k z := by
  simp [value, Arithmetic.value, Arithmetic.gaussian]

theorem complexEval_injective : Function.Injective complexEval := by
  intro p q hpq
  obtain ⟨k, z, rfl⟩ := exists_value p
  obtain ⟨l, t, rfl⟩ := exists_value q
  apply (Arithmetic.value_eq_iff phase half phase_square half_doubles k l z t).mpr
  apply (Arithmetic.value_eq_iff Complex.I (1 / 2 : ℂ)
    ComplexModel.phase_square ComplexModel.half_doubles k l z t).mp
  simpa only [complexEval_value] using hpq

/-- The concrete model detects exactly the equations of the least semiring congruence. -/
theorem syntactic_completeness (x y : Free) :
    RingConGen.Rel Rel x y ↔
      complexEval (presentationCon.mk' x) = complexEval (presentationCon.mk' y) := by
  constructor
  · intro h
    exact congrArg complexEval ((quotient_eq_iff x y).mpr h)
  · intro h
    exact (quotient_eq_iff x y).mp (complexEval_injective h)

/-- Any chosen normal-form presentations give an exact cross-denominator derivability test. -/
theorem normal_form_completeness (x y : Free) (k l : ℕ) (z t : Coefficients)
    (hx : presentationCon.mk' x = value k z)
    (hy : presentationCon.mk' y = value l t) :
    RingConGen.Rel Rel x y ↔
      DyadicResponseExtension.scale l z = DyadicResponseExtension.scale k t := by
  rw [← quotient_eq_iff x y, hx, hy]
  exact Arithmetic.value_eq_iff phase half phase_square half_doubles k l z t

/-- The concrete Gaussian-dyadic coefficient ring inside the explicit complex model. -/
abbrev GaussianDyadic := Arithmetic.generatedSubring Complex.I (1 / 2 : ℂ)
  ComplexModel.phase_square ComplexModel.half_doubles

/-- The presentation maps into precisely the normal-form carrier. -/
def toGaussianDyadic : Presentation →+* GaussianDyadic where
  toFun p := ⟨complexEval p, by
    obtain ⟨k, z, rfl⟩ := exists_value p
    exact ⟨k, z, complexEval_value k z⟩⟩
  map_zero' := Subtype.ext (map_zero complexEval)
  map_one' := Subtype.ext (map_one complexEval)
  map_add' p q := Subtype.ext (map_add complexEval p q)
  map_mul' p q := Subtype.ext (map_mul complexEval p q)

theorem toGaussianDyadic_injective : Function.Injective toGaussianDyadic := by
  intro p q hpq
  exact complexEval_injective (congrArg Subtype.val hpq)

theorem toGaussianDyadic_surjective : Function.Surjective toGaussianDyadic := by
  intro z
  obtain ⟨k, t, ht⟩ := z.property
  refine ⟨value k t, ?_⟩
  apply Subtype.ext
  exact (complexEval_value k t).trans ht.symm

/-- The initial presentation is the Gaussian-dyadic ring, without an input characteristic axiom. -/
def equivalence : Presentation ≃+* GaussianDyadic :=
  RingEquiv.ofBijective toGaussianDyadic
    ⟨toGaussianDyadic_injective, toGaussianDyadic_surjective⟩

@[simp] theorem equivalence_value (k : ℕ) (z : Coefficients) :
    equivalence (value k z) = Arithmetic.present Complex.I (1 / 2 : ℂ)
      ComplexModel.phase_square ComplexModel.half_doubles k z := by
  apply Subtype.ext
  exact complexEval_value k z

/-- The identified concrete ring retains the unrestricted target universal property. -/
def universalMap {S : Type*} [Semiring S] (x y : S)
    (htransparent : x + y = 1) (hdestructive : x ^ 2 + y ^ 2 = 0) :
    GaussianDyadic →+* S :=
  (eval x y htransparent hdestructive).comp equivalence.symm.toRingHom

/-- Uniqueness transfers through the initial presentation isomorphism. -/
theorem universalMap_unique {S : Type*} [Semiring S] (x y : S)
    (htransparent : x + y = 1) (hdestructive : x ^ 2 + y ^ 2 = 0)
    (f : GaussianDyadic →+* S)
    (ha : f (equivalence a) = x) (hb : f (equivalence b) = y) :
    f = universalMap x y htransparent hdestructive := by
  have hf : f.comp equivalence.toRingHom = eval x y htransparent hdestructive := by
    apply eval_unique x y htransparent hdestructive
    · exact ha
    · exact hb
  ext z
  have hz := DFunLike.congr_fun hf (equivalence.symm z)
  simpa [universalMap] using hz

end NormalForm

/-- Generator interchange is defined syntactically through the initial property. -/
def reflection : Presentation →+* Presentation :=
  eval b a (by simpa only [add_comm] using transparent)
    (by simpa only [pow_two, add_comm] using destructive)

@[simp] theorem reflection_a : reflection a = b := by simp [reflection]

@[simp] theorem reflection_b : reflection b = a := by simp [reflection]

theorem reflection_involutive : Function.Involutive reflection := by
  have h : reflection.comp reflection = RingHom.id Presentation := by
    apply hom_ext <;> simp
  intro p
  exact DFunLike.congr_fun h p

def reflectionEquiv : Presentation ≃+* Presentation :=
  { reflection with
    invFun := reflection
    left_inv := reflection_involutive
    right_inv := reflection_involutive }

@[simp] theorem reflection_half : reflection half = half := by
  change reflection (a * b) = a * b
  rw [map_mul, reflection_a, reflection_b]
  exact laws.coefficients_commute.symm

@[simp] theorem reflection_phase : reflection phase = -phase := by
  change reflection (a * a + a * a) = -(a * a + a * a)
  simp only [map_add, map_mul, reflection_a]
  linear_combination 2 * destructive

theorem reflection_phase_inverse : reflection phase = phase ^ 3 := by
  rw [reflection_phase]
  calc
    -phase = phase * (-(1 : Presentation)) := by ring
    _ = phase ^ 3 := by rw [← phase_square]; ring

namespace NormalForm

open SingleCalibrationScalarFaithfulness

@[simp] theorem reflection_value (k : ℕ) (z : Coefficients) :
    reflection (value k z) = value k (Arithmetic.conjugatePair z) := by
  simp [value, Arithmetic.value, Arithmetic.gaussian, Arithmetic.conjugatePair]

theorem reflection_is_gaussian_conjugation (p : Presentation) :
    equivalence (reflection p) =
      Arithmetic.conjugation Complex.I (1 / 2 : ℂ)
        ComplexModel.phase_square ComplexModel.half_doubles (equivalence p) := by
  obtain ⟨k, z, rfl⟩ := exists_value p
  rw [reflection_value, equivalence_value, equivalence_value]
  change Arithmetic.present Complex.I (1 / 2 : ℂ)
      ComplexModel.phase_square ComplexModel.half_doubles k (Arithmetic.conjugatePair z) =
    Arithmetic.conjugate Complex.I (1 / 2 : ℂ)
      ComplexModel.phase_square ComplexModel.half_doubles
      (Arithmetic.present Complex.I (1 / 2 : ℂ)
        ComplexModel.phase_square ComplexModel.half_doubles k z)
  exact (Arithmetic.conjugate_present Complex.I (1 / 2 : ℂ)
    ComplexModel.phase_square ComplexModel.half_doubles k z).symm

end NormalForm

namespace Controls

abbrev F5 := FiniteScalarReversalBoundary.Scalar

def finiteEval : Presentation →+* F5 :=
  eval FiniteScalarReversalBoundary.a FiniteScalarReversalBoundary.b
    FiniteScalarReversalBoundary.coefficient_laws.1
    (by simpa only [pow_two] using
      FiniteScalarReversalBoundary.coefficient_laws.2.1)

@[simp] theorem finiteEval_a : finiteEval a = FiniteScalarReversalBoundary.a := by
  simp [finiteEval]

@[simp] theorem finiteEval_b : finiteEval b = FiniteScalarReversalBoundary.b := by
  simp [finiteEval]

theorem five_nonzero : (5 : Presentation) ≠ 0 := by norm_num

theorem finiteEval_five : finiteEval (5 : Presentation) = 0 := by
  change finiteEval (Nat.cast 5) = 0
  rw [map_natCast]
  decide

/-- A supplied quotient can obey both relators and lose initial arithmetic faithfulness. -/
theorem finiteEval_not_injective : ¬ Function.Injective finiteEval := by
  intro h
  apply five_nonzero
  apply h
  rw [finiteEval_five, map_zero]

/-- The syntactic reflection need not descend to an additional supplied quotient. -/
theorem reflection_does_not_descend :
    ¬ ∃ J : F5 →+* F5, ∀ p, J (finiteEval p) = finiteEval (reflection p) := by
  rintro ⟨J, hJ⟩
  apply FiniteScalarReversalBoundary.no_additive_unital_coefficient_swap
  refine ⟨J.toAddMonoidHom, J.map_one, ?_⟩
  simpa only [finiteEval_a, reflection_a, finiteEval_b] using hJ a

end Controls

end

end IDT.QMClosure.NativeInitialHistoryPresentation
