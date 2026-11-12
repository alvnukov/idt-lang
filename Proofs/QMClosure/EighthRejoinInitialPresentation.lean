import Proofs.QMClosure.TransparentPositivePowerRejoin
import Mathlib.Algebra.FreeAlgebra
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.Tactic

/-!
# Literal initial eighth-rejoin presentation

The source is the semiring-congruence quotient of
`FreeAlgebra ℕ Bool` by precisely `a+b=1` and `a^8=b^8`. No source
commutativity, cancellation, fourth rejoin, or faithful evaluation is supplied.
Pair and generated whole-carrier commutativity are derived after construction.
This is an algebraic countermodel carrier, with no physical-origin claim.
-/

namespace IDT.QMClosure.EighthRejoinInitialPresentation

noncomputable section

abbrev Free := FreeAlgebra ℕ Bool

def freeA : Free := FreeAlgebra.ι ℕ false

def freeB : Free := FreeAlgebra.ι ℕ true

inductive Rel : Free → Free → Prop
  | transparent : Rel (freeA + freeB) 1
  | eighthRejoin : Rel (freeA ^ 8) (freeB ^ 8)

def presentationCon : RingCon Free := ringConGen Rel

abbrev Presentation := presentationCon.Quotient

def a : Presentation := presentationCon.mk' freeA

def b : Presentation := presentationCon.mk' freeB

theorem quotient_eq_iff (x y : Free) :
    presentationCon.mk' x = presentationCon.mk' y ↔ RingConGen.Rel Rel x y :=
  presentationCon.eq

theorem transparent : a + b = 1 := by
  change presentationCon.mk' (freeA + freeB) = presentationCon.mk' 1
  exact presentationCon.eq.mpr (RingConGen.Rel.of _ _ Rel.transparent)

theorem eighth_rejoin : a ^ 8 = b ^ 8 := by
  change presentationCon.mk' (freeA ^ 8) = presentationCon.mk' (freeB ^ 8)
  exact presentationCon.eq.mpr (RingConGen.Rel.of _ _ Rel.eighthRejoin)

section Universal

variable {S : Type*} [Semiring S] (x y : S)
  (hsum : x + y = 1) (height : x ^ 8 = y ^ 8)

def freeEval : Free →+* S :=
  (FreeAlgebra.lift ℕ (fun t => if t then y else x)).toRingHom

@[simp] theorem freeEval_a : freeEval x y freeA = x := by
  simp [freeEval, freeA]

@[simp] theorem freeEval_b : freeEval x y freeB = y := by
  simp [freeEval, freeB]

include hsum height in
theorem relation_in_kernel : presentationCon ≤ RingCon.ker (freeEval x y) := by
  apply RingCon.ringConGen_le
  intro p q h
  cases h with
  | transparent =>
      simpa only [RingCon.ker_apply, map_add, map_one, freeEval_a, freeEval_b] using hsum
  | eighthRejoin =>
      simpa only [RingCon.ker_apply, map_pow, freeEval_a, freeEval_b] using height

def eval : Presentation →+* S :=
  presentationCon.lift (freeEval x y) (relation_in_kernel x y hsum height)

@[simp] theorem eval_a : eval x y hsum height a = x := by
  simpa only [eval, a, RingCon.lift_mk'] using freeEval_a x y

@[simp] theorem eval_b : eval x y hsum height b = y := by
  simpa only [eval, b, RingCon.lift_mk'] using freeEval_b x y

theorem hom_ext {f g : Presentation →+* S}
    (ha : f a = g a) (hb : f b = g b) : f = g := by
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
    f = eval x y hsum height := by
  apply hom_ext
  · simpa using ha
  · simpa using hb

end Universal

/-- Structural induction retains the literal positive source syntax. -/
theorem presentation_induction (motive : Presentation → Prop)
    (hzero : motive 0) (hone : motive 1) (ha : motive a) (hb : motive b)
    (hadd : ∀ x y, motive x → motive y → motive (x + y))
    (hmul : ∀ x y, motive x → motive y → motive (x * y))
    (p : Presentation) : motive p := by
  obtain ⟨q, rfl⟩ := presentationCon.mk'_surjective p
  apply FreeAlgebra.induction (motive := fun q => motive (presentationCon.mk' q))
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

theorem coefficients_commute : Commute a b :=
  IDT.TransparentPositivePowerRejoin.commute_of_transparent_finite_rejoin
    8 (by norm_num) transparent eighth_rejoin

theorem generator_commutes (t : Bool) (p : Presentation) :
    Commute (presentationCon.mk' (FreeAlgebra.ι ℕ t)) p := by
  apply presentation_induction
    (motive := fun p => Commute (presentationCon.mk' (FreeAlgebra.ι ℕ t)) p)
  · change _ * 0 = 0 * _
    simp
  · exact Commute.one_right _
  · cases t
    · exact Commute.refl a
    · exact coefficients_commute.symm
  · cases t
    · exact coefficients_commute
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

/-- The instance keeps the original quotient operations. -/
instance presentationCommSemiring : CommSemiring Presentation :=
  { (inferInstance : Semiring Presentation) with mul_comm := multiplication_commutes }

/-- Generator swap, constructed on the literal quotient. -/
def J : Presentation →+* Presentation :=
  eval b a (by simpa only [add_comm] using transparent) eighth_rejoin.symm

@[simp] theorem J_a : J a = b := by simp [J]

@[simp] theorem J_b : J b = a := by simp [J]

theorem J_comp_J : J.comp J = RingHom.id Presentation := by
  apply hom_ext <;> simp

@[simp] theorem J_involutive (p : Presentation) : J (J p) = p :=
  DFunLike.congr_fun J_comp_J p

/-- Natural raw count bag. Left multiplication fixes the preparation convention. -/
def B (n m : ℕ) : Presentation := (n : Presentation) * a + (m : Presentation) * b

def h : Presentation := a * b

def c : Presentation := 2 * h

def T : Presentation := a ^ 2 + b ^ 2

def s : Presentation := a ^ 4 + b ^ 4

def z : Presentation := 2 * a ^ 4 + b ^ 4

/-- The further fourth-rejoin congruence is kept separate from the source. -/
def fourthCon : RingCon Presentation :=
  ringConGen (fun p q => p = a ^ 4 ∧ q = b ^ 4)

abbrev FourthQuotient := fourthCon.Quotient

theorem fourth_sum_identification :
    fourthCon.mk' s = fourthCon.mk' (2 * a ^ 4) := by
  have hab : fourthCon.mk' (a ^ 4) = fourthCon.mk' (b ^ 4) := by
    exact fourthCon.eq.mpr (RingConGen.Rel.of _ _ ⟨rfl, rfl⟩)
  simp only [s, map_add, map_mul, map_ofNat]
  rw [← hab, two_mul]

/-- Descent is factorization as a function through the further quotient. -/
def FourthDescent (R : Presentation → ℝ) : Prop :=
  ∃ f : FourthQuotient → ℝ, ∀ p, R p = f (fourthCon.mk' p)

theorem no_fourth_descent_of_separated_sum (R : Presentation → ℝ)
    (hne : R s ≠ R (2 * a ^ 4)) : ¬ FourthDescent R := by
  rintro ⟨f, hf⟩
  apply hne
  rw [hf s, hf (2 * a ^ 4), fourth_sum_identification]

end

end IDT.QMClosure.EighthRejoinInitialPresentation
