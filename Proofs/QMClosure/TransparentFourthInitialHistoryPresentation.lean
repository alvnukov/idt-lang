import Proofs.QMClosure.FourthRejoinIdempotentCore
import Mathlib.Algebra.FreeAlgebra
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.Data.NNReal.Basic

/-!
# Literal initial semiring for transparency and fourth rejoin

The statements below concern this algebraic presentation and its maps.
The source grammar is FreeAlgebra Nat Bool, with exactly a+b=1 and a^4=b^4.
Its quotient uses semiring congruence generation. The construction supplies
neither additive inverses nor destructive cancellation. Pair commutation and
whole-carrier commutativity are consequences, proved after construction.
The classical shadow is an algebraic model. Its zero detection is weaker than
injectivity. No detector, physical selection, or QM closure is established.
-/

namespace IDT.QMClosure.TransparentFourthInitialHistoryPresentation

noncomputable section

open scoped NNReal

abbrev Free := FreeAlgebra ℕ Bool

def freeA : Free := FreeAlgebra.ι ℕ false

def freeB : Free := FreeAlgebra.ι ℕ true

/-- These are the complete additional input equations. -/
inductive Rel : Free → Free → Prop
  | transparent : Rel (freeA + freeB) 1
  | fourthRejoin : Rel (freeA ^ 4) (freeB ^ 4)

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

theorem fourth_rejoin : a ^ 4 = b ^ 4 := by
  change presentationCon.mk' (freeA ^ 4) = presentationCon.mk' (freeB ^ 4)
  exact presentationCon.eq.mpr (RingConGen.Rel.of _ _ Rel.fourthRejoin)

section Universal

variable {S : Type*} [Semiring S] (x y : S)
  (hsum : x + y = 1) (hfour : x ^ 4 = y ^ 4)

def freeEval : Free →+* S :=
  (FreeAlgebra.lift ℕ (fun t => if t then y else x)).toRingHom

@[simp] theorem freeEval_a : freeEval x y freeA = x := by
  simp [freeEval, freeA]

@[simp] theorem freeEval_b : freeEval x y freeB = y := by
  simp [freeEval, freeB]

include hsum hfour in
theorem relation_in_kernel : presentationCon ≤ RingCon.ker (freeEval x y) := by
  apply RingCon.ringConGen_le
  intro p q h
  cases h with
  | transparent =>
      simpa only [RingCon.ker_apply, map_add, map_one, freeEval_a, freeEval_b] using hsum
  | fourthRejoin =>
      simpa only [RingCon.ker_apply, map_pow, freeEval_a, freeEval_b] using hfour

/-- Every semiring target with the two equations receives this map. -/
def eval : Presentation →+* S :=
  presentationCon.lift (freeEval x y) (relation_in_kernel x y hsum hfour)

@[simp] theorem eval_a : eval x y hsum hfour a = x := by
  simpa only [eval, a, RingCon.lift_mk'] using freeEval_a x y

@[simp] theorem eval_b : eval x y hsum hfour b = y := by
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
    f = eval x y hsum hfour := by
  apply hom_ext
  · simpa using ha
  · simpa using hb

end Universal

/-- Induction uses the positive two-generator semiring grammar. -/
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

def pairContract : FourthRejoinIdempotent.Contract a b :=
  FourthRejoinIdempotent.contract_of_transparent_fourth transparent fourth_rejoin

theorem coefficients_commute : Commute a b := pairContract.commute

/-- The generated carrier commutes because its two selected generators commute. -/
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

/-- This instance retains the quotient's original semiring operations. -/
instance presentationCommSemiring : CommSemiring Presentation :=
  { (inferInstance : Semiring Presentation) with mul_comm := multiplication_commutes }

def T : Presentation := a ^ 2 + b ^ 2

def e : Presentation := (2 : Presentation) * T

theorem e_idempotent : e * e = e :=
  FourthRejoinIdempotent.sector_idempotent pairContract

theorem e_zero_iff_T_zero : e = 0 ↔ T = 0 :=
  FourthRejoinIdempotent.sector_eq_zero_iff pairContract

theorem e_one_iff_a_eq_b : e = 1 ↔ a = b :=
  FourthRejoinIdempotent.sector_eq_one_iff pairContract

theorem inverse_contexts : FourthRejoinIdempotent.InverseContexts a b :=
  FourthRejoinIdempotent.inverse_contexts pairContract

/-- The all-positive classical model is constructed after the initial object. -/
def shadow : Presentation →+* ℝ≥0 :=
  eval (1 / 2) (1 / 2) (by norm_num) rfl

@[simp] theorem shadow_a : shadow a = 1 / 2 := by simp [shadow]

@[simp] theorem shadow_b : shadow b = 1 / 2 := by simp [shadow]

/-- Positive syntax makes this model detect zero, without an injectivity claim. -/
theorem shadow_zero_detection (p : Presentation) : shadow p = 0 → p = 0 := by
  apply presentation_induction (motive := fun p => shadow p = 0 → p = 0)
  · intro _
    rfl
  · intro h
    norm_num at h
  · intro h
    rw [shadow_a] at h
    norm_num at h
  · intro h
    rw [shadow_b] at h
    norm_num at h
  · intro x y hx hy h
    have hh : shadow x = 0 ∧ shadow y = 0 := by
      simpa only [map_add, add_eq_zero] using h
    rw [hx hh.1, hy hh.2, add_zero]
  · intro x y hx hy h
    have hh : shadow x = 0 ∨ shadow y = 0 := by
      simpa only [map_mul, mul_eq_zero] using h
    rcases hh with hx0 | hy0
    · rw [hx hx0, zero_mul]
    · rw [hy hy0, mul_zero]

theorem shadow_zero_iff (p : Presentation) : shadow p = 0 ↔ p = 0 :=
  ⟨shadow_zero_detection p, fun h => by rw [h, map_zero]⟩

theorem shadow_nonnegative (p : Presentation) : 0 ≤ shadow p := zero_le _

theorem shadow_positive (p : Presentation) (hp : p ≠ 0) : 0 < shadow p := by
  apply lt_of_le_of_ne (zero_le _)
  intro h
  exact hp (shadow_zero_detection p h.symm)

theorem shadow_column (p : Presentation) :
    shadow (a * p) + shadow (b * p) = shadow p := by
  rw [map_mul, map_mul, shadow_a, shadow_b]
  ring

theorem shadow_half_a (p : Presentation) : shadow (a * p) = shadow p / 2 := by
  rw [map_mul, shadow_a]
  ring

theorem shadow_half_b (p : Presentation) : shadow (b * p) = shadow p / 2 := by
  rw [map_mul, shadow_b]
  ring

theorem shadow_duplication_gain_two (p : Presentation) :
    shadow ((2 : Presentation) * p) = 2 * shadow p := by
  rw [map_mul, map_ofNat]

theorem shadow_counts (n m : ℕ) :
    shadow ((n : Presentation) * a + (m : Presentation) * b) =
      ((n : ℝ≥0) + (m : ℝ≥0)) / 2 := by
  simp only [map_add, map_mul, map_natCast, shadow_a, shadow_b]
  ring

theorem shadow_mixed (x y : Presentation) :
    shadow (a * x + b * y) = (shadow x + shadow y) / 2 := by
  rw [map_add, map_mul, map_mul, shadow_a, shadow_b]
  ring

theorem mixed_zero_iff (x y : Presentation) :
    a * x + b * y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have hh := congrArg shadow h
    have hhalf : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
    simpa only [map_add, map_mul, map_zero, shadow_a, shadow_b,
      add_eq_zero, mul_eq_zero, hhalf, false_or, shadow_zero_iff] using hh
  · rintro ⟨rfl, rfl⟩
    simp

theorem shadow_mixed_zero_iff (x y : Presentation) :
    shadow (a * x + b * y) = 0 ↔ x = 0 ∧ y = 0 := by
  rw [shadow_zero_iff, mixed_zero_iff]

@[simp] theorem shadow_T : shadow T = 1 / 2 := by
  rw [T, map_add, map_pow, map_pow, shadow_a, shadow_b]
  norm_num

@[simp] theorem shadow_e : shadow e = 1 := by
  rw [e, map_mul, map_ofNat, shadow_T]
  norm_num

theorem T_ne_zero : T ≠ 0 := by
  intro h
  have hh := congrArg shadow h
  rw [shadow_T, map_zero] at hh
  norm_num at hh

theorem e_ne_zero : e ≠ 0 := by
  intro h
  exact T_ne_zero (e_zero_iff_T_zero.mp h)

/-- There is no additive inverse of the unit in this initial carrier. -/
theorem no_additive_inverse_one : ¬ ∃ p : Presentation, 1 + p = 0 := by
  rintro ⟨p, hp⟩
  have h := congrArg shadow hp
  simp only [map_add, map_one, map_zero, add_eq_zero, one_ne_zero, false_and] at h

/-- The classical model realizes linear duplication and equal coefficients. -/
theorem shadow_linear_contrasts :
    shadow ((2 : Presentation) * a) = 1 ∧ shadow (2 : Presentation) = 2 := by
  constructor
  · rw [map_mul, map_ofNat, shadow_a]
    norm_num
  · rw [map_ofNat]

def realShadow : Presentation →+* ℝ := NNReal.toRealHom.comp shadow

@[simp] theorem realShadow_a : realShadow a = 1 / 2 := by
  simp [realShadow]

@[simp] theorem realShadow_b : realShadow b = 1 / 2 := by
  simp [realShadow]

end

end IDT.QMClosure.TransparentFourthInitialHistoryPresentation
