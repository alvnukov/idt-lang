import Mathlib

/-!
# A fourth rejoin yields a canonical idempotent

The direct entry
points require only transparency a+b=1 and fourth-power equality in an
arbitrary semiring. Positive geometric inverse words derive pair commutation.
The earlier explicit-commutation Contract and its declarations are preserved.
Every coefficient in the derived inverse words is natural. The input supplies
no readout, additive cancellation, additive inverses, ambient commutativity,
or physical availability of these words.

The global idempotent-purity premise is an additional structural restriction.
Applying that premise to measurement algebras or projector families would need
its own justification. This file constructs no ambient product decomposition.
-/

namespace IDT.FourthRejoinIdempotent

section Algebra

variable {S : Type*} [Semiring S] {a b : S}

/-- The supplied pair contract. -/
structure Contract (a b : S) : Prop where
  commute : Commute a b
  sum : a + b = 1
  fourthRejoin : a ^ 4 = b ^ 4

/-- The two-square defect. -/
def defect (a b : S) : S := a ^ 2 + b ^ 2

/-- The canonical idempotent candidate, written with a natural coefficient. -/
def sector (a b : S) : S := (2 : S) * defect a b

/-- A sorting rule that retains an arbitrary right-hand context. -/
lemma commute_context (hcomm : Commute a b) (x : S) :
    b * (a * x) = a * (b * x) := by
  calc
    b * (a * x) = (b * a) * x := (mul_assoc _ _ _).symm
    _ = (a * b) * x := by rw [hcomm.symm.eq]
    _ = a * (b * x) := mul_assoc _ _ _

/-- The initial fourth-power identity is valid without cancellation. -/
theorem square_context_eq (hcomm : Commute a b) (hfour : a ^ 4 = b ^ 4) :
    a ^ 2 * defect a b = b ^ 2 * defect a b := by
  have hsort := commute_context hcomm
  calc
    a ^ 2 * defect a b = a ^ 4 + a ^ 2 * b ^ 2 := by
      dsimp [defect]; noncomm_ring
    _ = b ^ 4 + a ^ 2 * b ^ 2 := by rw [hfour]
    _ = b ^ 2 * defect a b := by
      dsimp [defect]; noncomm_ring [hcomm.symm.eq, hsort]

/-- Transparency lowers the square identity to one extra pair factor. -/
theorem linear_context_eq (h : Contract a b) :
    a * defect a b = b * defect a b := by
  have hsort := commute_context h.commute
  have hsquare := square_context_eq h.commute h.fourthRejoin
  calc
    a * defect a b = a * defect a b * (a + b) := by rw [h.sum]; simp
    _ = a ^ 2 * defect a b + (a * b) * defect a b := by
      dsimp [defect]; noncomm_ring [h.commute.symm.eq, hsort]
    _ = b ^ 2 * defect a b + (a * b) * defect a b := by rw [hsquare]
    _ = b * defect a b * (a + b) := by
      dsimp [defect]; noncomm_ring [h.commute.symm.eq, hsort]
    _ = b * defect a b := by rw [h.sum]; simp

/-- Both duplication identities follow by splitting through a+b=1. -/
theorem duplication_identities (h : Contract a b) :
    defect a b = (2 : S) * (a * defect a b) ∧
      defect a b = (2 : S) * (b * defect a b) := by
  have hlinear := linear_context_eq h
  have hsplit : defect a b = a * defect a b + b * defect a b := by
    calc
      defect a b = (a + b) * defect a b := by rw [h.sum]; simp
      _ = a * defect a b + b * defect a b := add_mul _ _ _
  constructor
  · calc
      defect a b = a * defect a b + b * defect a b := hsplit
      _ = (2 : S) * (a * defect a b) := by rw [← hlinear]; noncomm_ring
  · calc
      defect a b = a * defect a b + b * defect a b := hsplit
      _ = (2 : S) * (b * defect a b) := by rw [hlinear]; noncomm_ring

/-- Iteration uses the same equality inside a multiplication context. -/
theorem four_square_context (h : Contract a b) :
    defect a b = (4 : S) * (a ^ 2 * defect a b) := by
  have ha := (duplication_identities h).1
  calc
    defect a b = (2 : S) * (a * defect a b) := ha
    _ = (2 : S) * (a * ((2 : S) * (a * defect a b))) :=
      congrArg (fun x : S => (2 : S) * (a * x)) ha
    _ = (4 : S) * (a ^ 2 * defect a b) := by noncomm_ring

/-- The defect satisfies a quadratic identity with coefficient two. -/
theorem two_defect_sq (h : Contract a b) :
    (2 : S) * (defect a b) ^ 2 = defect a b := by
  have hsquare := square_context_eq h.commute h.fourthRejoin
  calc
    (2 : S) * (defect a b) ^ 2 =
        (2 : S) * (a ^ 2 * defect a b) +
          (2 : S) * (b ^ 2 * defect a b) := by
      have hexpand : (defect a b) ^ 2 = (a ^ 2 + b ^ 2) * defect a b := by
        rw [pow_two]
        rfl
      rw [hexpand]
      noncomm_ring
    _ = (4 : S) * (a ^ 2 * defect a b) := by rw [← hsquare]; noncomm_ring
    _ = defect a b := (four_square_context h).symm

/-- The candidate is idempotent in the original semiring. -/
theorem sector_idempotent (h : Contract a b) :
    sector a b * sector a b = sector a b := by
  calc
    sector a b * sector a b = (2 : S) * ((2 : S) * (defect a b) ^ 2) := by
      dsimp [sector]; noncomm_ring
    _ = sector a b := by rw [two_defect_sq h]; rfl

/-- Multiplication by the canonical idempotent fixes the defect. -/
theorem sector_mul_defect (h : Contract a b) :
    sector a b * defect a b = defect a b := by
  calc
    sector a b * defect a b = (2 : S) * (defect a b) ^ 2 := by
      dsimp [sector]; noncomm_ring
    _ = defect a b := two_defect_sq h

/-- The pair has the same value in the idempotent-supported context. -/
theorem pair_mul_sector (h : Contract a b) :
    a * sector a b = defect a b ∧ b * sector a b = defect a b ∧
      sector a b * a = defect a b ∧ sector a b * b = defect a b := by
  obtain ⟨ha, hb⟩ := duplication_identities h
  have hsort := commute_context h.commute
  have hae : a * sector a b = defect a b := by
    calc
      a * sector a b = (2 : S) * (a * defect a b) := by
        dsimp [sector]; noncomm_ring
      _ = defect a b := ha.symm
  have hbe : b * sector a b = defect a b := by
    calc
      b * sector a b = (2 : S) * (b * defect a b) := by
        dsimp [sector]; noncomm_ring
      _ = defect a b := hb.symm
  refine ⟨hae, hbe, ?_, ?_⟩
  · calc
      sector a b * a = a * sector a b := by
        dsimp [sector, defect]; noncomm_ring [h.commute.symm.eq, hsort]
      _ = defect a b := hae
  · calc
      sector a b * b = b * sector a b := by
        dsimp [sector, defect]; noncomm_ring [h.commute.symm.eq, hsort]
      _ = defect a b := hbe

/-- Zero sector is equivalent to a destructive defect. -/
theorem sector_eq_zero_iff (h : Contract a b) :
    sector a b = 0 ↔ defect a b = 0 := by
  constructor
  · intro he
    have hfix := sector_mul_defect h
    rw [he, zero_mul] at hfix
    exact hfix.symm
  · intro hT
    simp [sector, hT]

/-- Unit sector is equivalent to equal pair coefficients. -/
theorem sector_eq_one_iff (h : Contract a b) :
    sector a b = 1 ↔ a = b := by
  constructor
  · intro he
    obtain ⟨hae, hbe, _, _⟩ := pair_mul_sector h
    calc
      a = a * sector a b := by rw [he]; simp
      _ = defect a b := hae
      _ = b * sector a b := hbe.symm
      _ = b := by rw [he]; simp
  · intro hab
    have hT : defect a b = a := by
      calc
        defect a b = a * (a + b) := by
          dsimp [defect]; rw [← hab]; noncomm_ring
        _ = a := by rw [h.sum]; simp
    calc
      sector a b = (2 : S) * a := by rw [sector, hT]
      _ = a + b := by rw [← hab]; noncomm_ring
      _ = 1 := h.sum

/-- The three algebraic alternatives require no readout. -/
theorem sector_trilemma (h : Contract a b) :
    defect a b = 0 ∨ a = b ∨
      (sector a b * sector a b = sector a b ∧
        sector a b ≠ 0 ∧ sector a b ≠ 1) := by
  by_cases hT : defect a b = 0
  · exact Or.inl hT
  · by_cases hab : a = b
    · exact Or.inr (Or.inl hab)
    · exact Or.inr (Or.inr ⟨sector_idempotent h,
        fun he => hT ((sector_eq_zero_iff h).mp he),
        fun he => hab ((sector_eq_one_iff h).mp he)⟩)

/-- Unequal coefficients and a surviving defect force a nontrivial idempotent. -/
theorem nontrivial_sector (h : Contract a b) (hab : a ≠ b)
    (hT : defect a b ≠ 0) :
    sector a b * sector a b = sector a b ∧
      sector a b ≠ 0 ∧ sector a b ≠ 1 := by
  exact ⟨sector_idempotent h,
    fun he => hT ((sector_eq_zero_iff h).mp he),
    fun he => hab ((sector_eq_one_iff h).mp he)⟩

/-- An explicit additional global coefficient restriction. -/
def CoefficientIdempotentPurity (S : Type*) [Semiring S] : Prop :=
  ∀ x : S, x * x = x → x = 0 ∨ x = 1

/-- Global coefficient-idempotent purity excludes the mixed alternative. -/
theorem destructive_of_coefficient_purity (h : Contract a b)
    (hpure : CoefficientIdempotentPurity S) (hab : a ≠ b) :
    defect a b = 0 := by
  rcases hpure (sector a b) (sector_idempotent h) with he | he
  · exact (sector_eq_zero_iff h).mp he
  · exact False.elim (hab ((sector_eq_one_iff h).mp he))

/-- Transparency has a positive-coefficient square expansion. -/
theorem transparency_square (hcomm : Commute a b) (hsum : a + b = 1) :
    defect a b + (2 : S) * (a * b) = 1 := by
  have hsort := commute_context hcomm
  calc
    defect a b + (2 : S) * (a * b) = (a + b) ^ 2 := by
      dsimp [defect]; noncomm_ring [hcomm.symm.eq, hsort]
    _ = 1 := by rw [hsum]; simp

/-- All witnesses are finite positive-coefficient words in the supplied pair. -/
structure InverseContexts (a b : S) : Prop where
  aRight : a * ((2 : S) * b + sector a b) = 1
  aLeft : ((2 : S) * b + sector a b) * a = 1
  bRight : b * ((2 : S) * a + sector a b) = 1
  bLeft : ((2 : S) * a + sector a b) * b = 1
  crossRight : (a * b) * ((2 : S) + (2 : S) * sector a b) = 1
  crossLeft : ((2 : S) + (2 : S) * sector a b) * (a * b) = 1
  twoRight : (2 : S) * (a * b + (defect a b) ^ 2) = 1
  twoLeft : (a * b + (defect a b) ^ 2) * (2 : S) = 1

/-- The pair coefficients have explicit two-sided inverse contexts. -/
theorem pair_inverse_contexts (h : Contract a b) :
    (a * ((2 : S) * b + sector a b) = 1 ∧
      ((2 : S) * b + sector a b) * a = 1) ∧
    (b * ((2 : S) * a + sector a b) = 1 ∧
      ((2 : S) * a + sector a b) * b = 1) := by
  obtain ⟨hae, hbe, hea, heb⟩ := pair_mul_sector h
  have ht := transparency_square h.commute h.sum
  have hsort := commute_context h.commute
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · calc
      a * ((2 : S) * b + sector a b) = (2 : S) * (a * b) + a * sector a b := by
        noncomm_ring
      _ = 1 := by rw [hae, add_comm]; exact ht
  · calc
      ((2 : S) * b + sector a b) * a = (2 : S) * (a * b) + sector a b * a := by
        noncomm_ring [h.commute.symm.eq, hsort]
      _ = 1 := by rw [hea, add_comm]; exact ht
  · calc
      b * ((2 : S) * a + sector a b) = (2 : S) * (a * b) + b * sector a b := by
        noncomm_ring [h.commute.symm.eq, hsort]
      _ = 1 := by rw [hbe, add_comm]; exact ht
  · calc
      ((2 : S) * a + sector a b) * b = (2 : S) * (a * b) + sector a b * b := by
        noncomm_ring
      _ = 1 := by rw [heb, add_comm]; exact ht

/-- Multiplying the two inverse words produces the corrected cross inverse. -/
theorem inverse_word_product (h : Contract a b) :
    ((2 : S) * b + sector a b) * ((2 : S) * a + sector a b) =
      (2 : S) + (2 : S) * sector a b := by
  obtain ⟨_, hbe, hea, _⟩ := pair_mul_sector h
  have ht := transparency_square h.commute h.sum
  calc
    ((2 : S) * b + sector a b) * ((2 : S) * a + sector a b) =
        (4 : S) * (b * a) + (2 : S) * (b * sector a b) +
          (2 : S) * (sector a b * a) + sector a b * sector a b := by
      noncomm_ring
    _ = (4 : S) * (a * b) + (4 : S) * defect a b + sector a b := by
      rw [h.commute.symm.eq, hbe, hea, sector_idempotent h]
      noncomm_ring
    _ = (2 : S) * (defect a b + (2 : S) * (a * b)) +
        (2 : S) * sector a b := by
      dsimp [sector]; noncomm_ring
    _ = (2 : S) + (2 : S) * sector a b := by rw [ht]; simp

/-- The cross return is 2+2e, including the mixed idempotent case. -/
theorem cross_inverse_contexts (h : Contract a b) :
    (a * b) * ((2 : S) + (2 : S) * sector a b) = 1 ∧
      ((2 : S) + (2 : S) * sector a b) * (a * b) = 1 := by
  obtain ⟨⟨haR, haL⟩, ⟨hbR, hbL⟩⟩ := pair_inverse_contexts h
  have hwords := inverse_word_product h
  have hsort := commute_context h.commute
  constructor
  · calc
      (a * b) * ((2 : S) + (2 : S) * sector a b) =
          (a * b) * (((2 : S) * b + sector a b) *
            ((2 : S) * a + sector a b)) := by rw [hwords]
      _ = (a * ((2 : S) * b + sector a b)) *
          (b * ((2 : S) * a + sector a b)) := by
        dsimp [sector, defect]; noncomm_ring [h.commute.symm.eq, hsort]
      _ = 1 := by rw [haR, hbR]; simp
  · calc
      ((2 : S) + (2 : S) * sector a b) * (a * b) =
          (((2 : S) * b + sector a b) *
            ((2 : S) * a + sector a b)) * (a * b) := by rw [hwords]
      _ = (((2 : S) * b + sector a b) * a) *
          (((2 : S) * a + sector a b) * b) := by
        dsimp [sector, defect]; noncomm_ring [h.commute.symm.eq, hsort]
      _ = 1 := by rw [haL, hbL]; simp

/-- Natural two has the generated inverse ab+T squared. -/
theorem two_inverse_contexts (h : Contract a b) :
    (2 : S) * (a * b + (defect a b) ^ 2) = 1 ∧
      (a * b + (defect a b) ^ 2) * (2 : S) = 1 := by
  have ht := transparency_square h.commute h.sum
  have hright : (2 : S) * (a * b + (defect a b) ^ 2) = 1 := by
    calc
      (2 : S) * (a * b + (defect a b) ^ 2) =
          (2 : S) * (a * b) + (2 : S) * (defect a b) ^ 2 := mul_add _ _ _
      _ = (2 : S) * (a * b) + defect a b := by rw [two_defect_sq h]
      _ = 1 := by rw [add_comm]; exact ht
  refine ⟨hright, ?_⟩
  calc
    (a * b + (defect a b) ^ 2) * (2 : S) =
        (2 : S) * (a * b + (defect a b) ^ 2) :=
      (Nat.cast_comm 2 (a * b + (defect a b) ^ 2)).symm
    _ = 1 := hright

/-- The full universal finite algebraic inverse-context certificate. -/
theorem inverse_contexts (h : Contract a b) : InverseContexts a b := by
  obtain ⟨⟨haR, haL⟩, ⟨hbR, hbL⟩⟩ := pair_inverse_contexts h
  obtain ⟨hcR, hcL⟩ := cross_inverse_contexts h
  obtain ⟨htR, htL⟩ := two_inverse_contexts h
  exact ⟨haR, haL, hbR, hbL, hcR, hcL, htR, htL⟩

/-- Destructive specialization recovers the scalar cross return two. -/
theorem destructive_inverse_words (hT : defect a b = 0) :
    (2 : S) * b + sector a b = (2 : S) * b ∧
      (2 : S) * a + sector a b = (2 : S) * a ∧
      (2 : S) + (2 : S) * sector a b = (2 : S) := by
  simp [sector, hT]

/-- Unit-sector specialization gives the classical scalar cross return four. -/
theorem classical_cross_word (he : sector a b = 1) :
    (2 : S) + (2 : S) * sector a b = (4 : S) := by
  rw [he]
  norm_num


/-- A positive geometric word for the inverse of a. -/
def geometricInverse (a b : S) : S := 1 + b + b ^ 2 + b ^ 3 + a ^ 3

/-- Successive left multiplication expands the transparent unit positively. -/
theorem left_geometric_telescope (hsum : a + b = 1) :
    1 = a + b * a + b ^ 2 * a + b ^ 3 * a + b ^ 4 := by
  calc
    1 = a + b := hsum.symm
    _ = a + b * (a + b) := by simp [hsum]
    _ = a + b * a + b ^ 2 := by noncomm_ring
    _ = a + b * a + b ^ 2 * (a + b) := by rw [hsum]; simp
    _ = a + b * a + b ^ 2 * a + b ^ 3 := by noncomm_ring
    _ = a + b * a + b ^ 2 * a + b ^ 3 * (a + b) := by rw [hsum]; simp
    _ = a + b * a + b ^ 2 * a + b ^ 3 * a + b ^ 4 := by noncomm_ring

/-- Successive right multiplication gives the reverse telescope. -/
theorem right_geometric_telescope (hsum : a + b = 1) :
    1 = a + a * b + a * b ^ 2 + a * b ^ 3 + b ^ 4 := by
  calc
    1 = a + b := hsum.symm
    _ = a + (a + b) * b := by simp [hsum]
    _ = a + a * b + b ^ 2 := by noncomm_ring
    _ = a + a * b + (a + b) * b ^ 2 := by rw [hsum]; simp
    _ = a + a * b + a * b ^ 2 + b ^ 3 := by noncomm_ring
    _ = a + a * b + a * b ^ 2 + (a + b) * b ^ 3 := by rw [hsum]; simp
    _ = a + a * b + a * b ^ 2 + a * b ^ 3 + b ^ 4 := by noncomm_ring

/-- Geometric inverses precede every use of pair commutation. -/
theorem geometric_inverse_a (hsum : a + b = 1) (hfour : a ^ 4 = b ^ 4) :
    geometricInverse a b * a = 1 ∧ a * geometricInverse a b = 1 := by
  constructor
  · calc
      geometricInverse a b * a = a + b * a + b ^ 2 * a + b ^ 3 * a + a ^ 4 := by
        dsimp [geometricInverse]; noncomm_ring
      _ = a + b * a + b ^ 2 * a + b ^ 3 * a + b ^ 4 := by rw [hfour]
      _ = 1 := (left_geometric_telescope hsum).symm
  · calc
      a * geometricInverse a b = a + a * b + a * b ^ 2 + a * b ^ 3 + a ^ 4 := by
        dsimp [geometricInverse]; noncomm_ring
      _ = a + a * b + a * b ^ 2 + a * b ^ 3 + b ^ 4 := by rw [hfour]
      _ = 1 := (right_geometric_telescope hsum).symm

/-- The symmetric positive geometric word is a two-sided inverse of b. -/
theorem geometric_inverse_b (hsum : a + b = 1) (hfour : a ^ 4 = b ^ 4) :
    geometricInverse b a * b = 1 ∧ b * geometricInverse b a = 1 := by
  have hsum' : b + a = 1 := by rw [add_comm]; exact hsum
  exact geometric_inverse_a hsum' hfour.symm

/-- The two local relators derive pair commutation inside any semiring. -/
theorem commute_of_transparent_fourth
    (hsum : a + b = 1) (hfour : a ^ 4 = b ^ 4) : Commute a b := by
  let u := geometricInverse a b
  let v := geometricInverse b a
  obtain ⟨hua, hau⟩ := geometric_inverse_a hsum hfour
  obtain ⟨hvb, hbv⟩ := geometric_inverse_b hsum hfour
  change u * a = 1 at hua
  change a * u = 1 at hau
  change v * b = 1 at hvb
  change b * v = 1 at hbv
  have huv : u * v = v * u := by
    calc
      u * v = u * (a + b) * v := by rw [hsum]; simp
      _ = (u * a) * v + u * (b * v) := by noncomm_ring
      _ = v + u := by rw [hua, hbv]; simp
      _ = v * (a * u) + (v * b) * u := by rw [hau, hvb]; simp
      _ = v * (a + b) * u := by noncomm_ring
      _ = v * u := by rw [hsum]; simp
  have hleft : (a * b) * (u * v) * (b * a) = a * b := by
    calc
      (a * b) * (u * v) * (b * a) = (a * b) * (u * ((v * b) * a)) := by
        noncomm_ring
      _ = a * b := by rw [hvb]; simp only [one_mul, hua, mul_one]
  have hright : (a * b) * (v * u) * (b * a) = b * a := by
    calc
      (a * b) * (v * u) * (b * a) = ((a * (b * v)) * u) * (b * a) := by
        noncomm_ring
      _ = b * a := by rw [hbv]; simp only [mul_one, hau, one_mul]
  change a * b = b * a
  calc
    a * b = (a * b) * (u * v) * (b * a) := hleft.symm
    _ = (a * b) * (v * u) * (b * a) := by rw [huv]
    _ = b * a := hright

/-- Construct the preserved commuting-pair interface from only two relators. -/
theorem contract_of_transparent_fourth
    (hsum : a + b = 1) (hfour : a ^ 4 = b ^ 4) : Contract a b :=
  ⟨commute_of_transparent_fourth hsum hfour, hsum, hfour⟩

/-- Direct two-relator entry point for the canonical idempotent. -/
theorem sector_idempotent_of_transparent_fourth
    (hsum : a + b = 1) (hfour : a ^ 4 = b ^ 4) :
    sector a b * sector a b = sector a b :=
  sector_idempotent (contract_of_transparent_fourth hsum hfour)

/-- Direct two-relator entry point for the three algebraic alternatives. -/
theorem sector_trilemma_of_transparent_fourth
    (hsum : a + b = 1) (hfour : a ^ 4 = b ^ 4) :
    defect a b = 0 ∨ a = b ∨
      (sector a b * sector a b = sector a b ∧
        sector a b ≠ 0 ∧ sector a b ≠ 1) :=
  sector_trilemma (contract_of_transparent_fourth hsum hfour)

/-- Direct two-relator entry point for all finite algebraic inverse contexts. -/
theorem inverse_contexts_of_transparent_fourth
    (hsum : a + b = 1) (hfour : a ^ 4 = b ^ 4) : InverseContexts a b :=
  inverse_contexts (contract_of_transparent_fourth hsum hfour)

/-- The purity corollary also has a direct two-relator interface. -/
theorem destructive_of_purity_transparent_fourth
    (hsum : a + b = 1) (hfour : a ^ 4 = b ^ 4)
    (hpure : CoefficientIdempotentPurity S) (hab : a ≠ b) : defect a b = 0 :=
  destructive_of_coefficient_purity (contract_of_transparent_fourth hsum hfour) hpure hab

end Algebra

end IDT.FourthRejoinIdempotent
