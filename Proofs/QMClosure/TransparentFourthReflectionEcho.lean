import Proofs.QMClosure.TransparentFourthInitialHistoryPresentation

/-!
# Reflection and algebraic echoes in the transparent fourth-rejoin presentation

The canonical NNReal homomorphism detects zero in the initial semiring.
It supplies a proof witness for zero-sum reflection and absence of zero
divisors. Generator interchange defines a unique involutive semiring map.
Its algebraic echoes preserve nonzero inputs and have squared shadow values.

These constructions supply no physical availability or normalization of an
echo, no symmetry of a selected physical readout, and no Born or QM closure.
-/

namespace IDT.QMClosure.TransparentFourthReflectionEcho

noncomputable section

open TransparentFourthInitialHistoryPresentation

/-- An additive zero has two zero summands in the initial presentation. -/
theorem add_eq_zero_iff (p q : Presentation) : p + q = 0 ↔ p = 0 ∧ q = 0 := by
  constructor
  · intro h
    have hs : shadow p = 0 ∧ shadow q = 0 := by
      simpa only [map_add, map_zero, add_eq_zero] using congrArg shadow h
    exact ⟨shadow_zero_detection p hs.1, shadow_zero_detection q hs.2⟩
  · rintro ⟨rfl, rfl⟩
    exact add_zero 0

/-- Multiplicative zero is reflected through the canonical NNReal witness. -/
theorem mul_eq_zero_iff (p q : Presentation) : p * q = 0 ↔ p = 0 ∨ q = 0 := by
  constructor
  · intro h
    have hs : shadow p = 0 ∨ shadow q = 0 := by
      simpa only [map_mul, map_zero, mul_eq_zero] using congrArg shadow h
    rcases hs with hp | hq
    · exact Or.inl (shadow_zero_detection p hp)
    · exact Or.inr (shadow_zero_detection q hq)
  · rintro (rfl | rfl)
    · exact zero_mul q
    · exact mul_zero p

/-- Absence of zero divisors is a conclusion about the original operations. -/
instance presentationNoZeroDivisors : NoZeroDivisors Presentation where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro p q h
    exact (mul_eq_zero_iff p q).mp h

theorem no_additive_inverse_right (p : Presentation) (hp : p ≠ 0) :
    ¬ ∃ q : Presentation, p + q = 0 := by
  rintro ⟨q, h⟩
  exact hp ((add_eq_zero_iff p q).mp h).1

theorem no_additive_inverse_left (p : Presentation) (hp : p ≠ 0) :
    ¬ ∃ q : Presentation, q + p = 0 := by
  rintro ⟨q, h⟩
  exact hp ((add_eq_zero_iff q p).mp h).2

/-- The universal generator swap, defined from the same two relators. -/
def J : Presentation →+* Presentation :=
  eval b a (by simpa only [add_comm] using transparent) fourth_rejoin.symm

@[simp] theorem J_a : J a = b := by simp [J]

@[simp] theorem J_b : J b = a := by simp [J]

theorem J_square : J.comp J = RingHom.id Presentation := by
  apply hom_ext
  · change J (J a) = a
    rw [J_a, J_b]
  · change J (J b) = b
    rw [J_b, J_a]

theorem J_involutive : Function.Involutive J := by
  intro p
  exact DFunLike.congr_fun J_square p

theorem J_bijective : Function.Bijective J := by
  constructor
  · intro p q h
    have hh := congrArg J h
    simpa only [J_involutive p, J_involutive q] using hh
  · intro p
    exact ⟨J p, J_involutive p⟩

/-- This equivalence preserves the initial semiring operations. -/
def JEquiv : Presentation ≃+* Presentation :=
  { J with
    invFun := J
    left_inv := J_involutive
    right_inv := J_involutive }

theorem J_unique (f : Presentation →+* Presentation)
    (ha : f a = b) (hb : f b = a) : f = J := by
  apply hom_ext
  · simpa only [J_a] using ha
  · simpa only [J_b] using hb

/-- This invariance concerns the constructed algebraic shadow. -/
theorem shadow_comp_J : shadow.comp J = shadow := by
  apply hom_ext
  · change shadow (J a) = shadow a
    rw [J_a, shadow_b, shadow_a]
  · change shadow (J b) = shadow b
    rw [J_b, shadow_a, shadow_b]

@[simp] theorem shadow_J (p : Presentation) : shadow (J p) = shadow p :=
  DFunLike.congr_fun shadow_comp_J p

@[simp] theorem J_T : J T = T := by
  simp only [T, map_add, map_pow, J_a, J_b]
  exact add_comm _ _

@[simp] theorem J_e : J e = e := by
  simp only [e, map_mul, map_ofNat, J_T]

/-- The echo is an algebraic product in the original initial carrier. -/
def echo (p : Presentation) : Presentation := p * J p

theorem echo_nonzero (p : Presentation) (hp : p ≠ 0) : echo p ≠ 0 := by
  intro h
  rcases (mul_eq_zero_iff p (J p)).mp h with hp0 | hJ0
  · exact hp hp0
  · have hh := congrArg J hJ0
    rw [J_involutive p, map_zero] at hh
    exact hp hh

@[simp] theorem shadow_echo (p : Presentation) : shadow (echo p) = shadow p ^ 2 := by
  simp only [echo, map_mul, shadow_J, pow_two]

@[simp] theorem echo_a : echo a = a * b := by
  rw [echo, J_a]

@[simp] theorem echo_b : echo b = a * b := by
  rw [echo, J_b]
  exact mul_comm _ _

@[simp] theorem shadow_echo_a : shadow (echo a) = 1 / 4 := by
  rw [echo_a, map_mul, shadow_a, shadow_b]
  norm_num

@[simp] theorem echo_e : echo e = e := by
  rw [echo, J_e]
  exact e_idempotent

theorem echo_e_nonzero : echo e ≠ 0 := by
  rw [echo_e]
  exact e_ne_zero

/-- The generator echo fails the algebraic inverse-of-two normalization. -/
theorem generator_echo_not_inverse_two : (2 : Presentation) * echo a ≠ 1 := by
  intro h
  have hs := congrArg shadow h
  rw [map_mul, map_ofNat, shadow_echo_a, map_one] at hs
  norm_num at hs

end

end IDT.QMClosure.TransparentFourthReflectionEcho
