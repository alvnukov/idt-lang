import Proofs.QMClosure.TransparentFourthNullPassivity
import Proofs.QMClosure.TransparentFourthDestructiveQuotient

/-!
# Set-function descent through the destructive quotient

Lean kernel-checked set-function descent under the stated premises.
This downstream module uses the existing generated e=0 quotient.
The core null-insertion proof imports only the initial presentation.
The descended readout is an arbitrary set-function.
-/

namespace IDT.QMClosure.TransparentFourthNullPassivityQuotient

noncomputable section

open TransparentFourthInitialHistoryPresentation
open TransparentFourthNullPassivity

/-- The Bourne relation of the principal e-supported semiring ideal. -/
def bourne : RingCon P where
  r x y := ∃ p q : P, x + e * p = y + e * q
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact ⟨0, 0, rfl⟩
    · rintro x y ⟨p, q, h⟩
      exact ⟨q, p, h.symm⟩
    · rintro x y z ⟨p, q, hxy⟩ ⟨r, s, hyz⟩
      refine ⟨p + r, s + q, ?_⟩
      calc
        x + e * (p + r) = (x + e * p) + e * r := by ring
        _ = (y + e * q) + e * r := by rw [hxy]
        _ = (y + e * r) + e * q := by ring
        _ = (z + e * s) + e * q := by rw [hyz]
        _ = z + e * (s + q) := by ring
  add' := by
    rintro x y z w ⟨p, q, hxy⟩ ⟨r, s, hzw⟩
    refine ⟨p + r, q + s, ?_⟩
    calc
      (x + z) + e * (p + r) = (x + e * p) + (z + e * r) := by ring
      _ = (y + e * q) + (w + e * s) := by rw [hxy, hzw]
      _ = (y + w) + e * (q + s) := by ring
  mul' := by
    rintro x y z w ⟨p, q, hxy⟩ ⟨r, s, hzw⟩
    refine ⟨x * r + p * z + e * p * r, y * s + q * w + e * q * s, ?_⟩
    calc
      x * z + e * (x * r + p * z + e * p * r) =
          (x + e * p) * (z + e * r) := by ring
      _ = (y + e * q) * (w + e * s) := by rw [hxy, hzw]
      _ = y * w + e * (y * s + q * w + e * q * s) := by ring

lemma destructiveCon_le_bourne : TransparentFourthDestructiveQuotient.destructiveCon ≤ bourne := by
  apply RingCon.ringConGen_le
  intro x y h
  cases h with
  | killSector => exact ⟨0, 1, by simp⟩

lemma bourne_le_destructiveCon : bourne ≤ TransparentFourthDestructiveQuotient.destructiveCon := by
  rintro x y ⟨p, q, h⟩
  apply TransparentFourthDestructiveQuotient.destructiveCon.eq.mp
  have hh := congrArg TransparentFourthDestructiveQuotient.q h
  simpa only [map_add, map_mul, TransparentFourthDestructiveQuotient.q_e, zero_mul, add_zero] using hh

/-- The generated e=0 relation has exactly the Bourne witnesses. -/
theorem destructiveCon_eq_bourne : TransparentFourthDestructiveQuotient.destructiveCon = bourne :=
  le_antisymm destructiveCon_le_bourne bourne_le_destructiveCon

lemma respects_destructiveCon_of_nullInsertion (W : P → ℝ) (hnull : NullInsertion W)
    {x y : P} (hxy : TransparentFourthDestructiveQuotient.destructiveCon x y) : W x = W y := by
  obtain ⟨p, q, h⟩ := destructiveCon_le_bourne hxy
  calc
    W x = W (x + e * p) := (hnull x p).symm
    _ = W (y + e * q) := congrArg W h
    _ = W y := hnull y q

/-- A section is used only to construct the descended arbitrary set-function. -/
def quotientReadout (W : P → ℝ) : TransparentFourthDestructiveQuotient.Quotient → ℝ :=
  fun z => W (Classical.choose (TransparentFourthDestructiveQuotient.destructiveCon.mk'_surjective z))

lemma quotientReadout_q (W : P → ℝ) (hnull : NullInsertion W) (p : P) :
    quotientReadout W (TransparentFourthDestructiveQuotient.q p) = W p := by
  unfold quotientReadout
  apply respects_destructiveCon_of_nullInsertion W hnull
  apply TransparentFourthDestructiveQuotient.destructiveCon.eq.mp
  exact Classical.choose_spec (TransparentFourthDestructiveQuotient.destructiveCon.mk'_surjective (TransparentFourthDestructiveQuotient.q p))

def FactorsThrough (W : P → ℝ) : Prop :=
  ∃ f : TransparentFourthDestructiveQuotient.Quotient → ℝ, ∀ p, f (TransparentFourthDestructiveQuotient.q p) = W p

/-- Existence and uniqueness apply to set-functions without additive laws. -/
theorem unique_factorization_of_nullInsertion (W : P → ℝ) (hnull : NullInsertion W) :
    ∃! f : TransparentFourthDestructiveQuotient.Quotient → ℝ, ∀ p, f (TransparentFourthDestructiveQuotient.q p) = W p := by
  refine ⟨quotientReadout W, quotientReadout_q W hnull, ?_⟩
  intro f hf
  funext z
  obtain ⟨p, rfl⟩ := TransparentFourthDestructiveQuotient.destructiveCon.mk'_surjective z
  exact (hf p).trans (quotientReadout_q W hnull p).symm

lemma nullInsertion_of_factorization (W : P → ℝ) (hfactor : FactorsThrough W) :
    NullInsertion W := by
  obtain ⟨f, hf⟩ := hfactor
  intro x p
  calc
    W (x + e * p) = f (TransparentFourthDestructiveQuotient.q (x + e * p)) := (hf _).symm
    _ = f (TransparentFourthDestructiveQuotient.q x) := by rw [map_add, map_mul, TransparentFourthDestructiveQuotient.q_e, zero_mul, add_zero]
    _ = W x := hf x

lemma factorization_iff_nullInsertion (W : P → ℝ) : FactorsThrough W ↔ NullInsertion W := by
  refine ⟨nullInsertion_of_factorization W, ?_⟩
  intro hnull
  exact ⟨quotientReadout W, quotientReadout_q W hnull⟩

lemma invariance_of_nullInsertion (W : P → ℝ) (hnull : NullInsertion W) :
    ∀ p, W (c * p) = W p := by
  intro p
  have hsplit : c * p + e * (T * p) = p := by
    calc
      c * p + e * (T * p) = (c + T) * p := by rw [← mul_assoc, e_mul_T]; ring
      _ = p := by rw [c_add_T, one_mul]
  have h := hnull (c * p) (T * p)
  rw [hsplit] at h
  exact h.symm

lemma calibration_of_nullInsertion (W : P → ℝ) (hnull : NullInsertion W) : W T = W 0 := by
  simpa only [zero_add, e_mul_T] using hnull 0 T

/-- An exact local equivalence with explicit invariance, calibration, and one
of the global one-sided fixed-T inequalities. -/
theorem factorization_iff_calibrated_fixedT_nonincrease (W : P → ℝ) :
    FactorsThrough W ↔
      (∀ p, W (c * p) = W p) ∧ W T = W 0 ∧ FixedTNonincrease W := by
  constructor
  · intro hfactor
    have hn := nullInsertion_of_factorization W hfactor
    exact ⟨invariance_of_nullInsertion W hn, calibration_of_nullInsertion W hn,
      fun x => le_of_eq (fixedT_equality_of_nullInsertion W hn x)⟩
  · rintro ⟨ht, hc, hp⟩
    exact (factorization_iff_nullInsertion W).mpr
      (nullInsertion_of_calibrated_fixedT_nonincrease W ht hc hp)

theorem factorization_iff_calibrated_fixedT_nondecrease (W : P → ℝ) :
    FactorsThrough W ↔
      (∀ p, W (c * p) = W p) ∧ W T = W 0 ∧ FixedTNondecrease W := by
  constructor
  · intro hfactor
    have hn := nullInsertion_of_factorization W hfactor
    exact ⟨invariance_of_nullInsertion W hn, calibration_of_nullInsertion W hn,
      fun x => le_of_eq (fixedT_equality_of_nullInsertion W hn x).symm⟩
  · rintro ⟨ht, hc, hp⟩
    exact (factorization_iff_nullInsertion W).mpr
      (nullInsertion_of_calibrated_fixedT_nondecrease W ht hc hp)

theorem unique_factorization_of_calibrated_fixedT_nonincrease (W : P → ℝ)
    (htrans : ∀ p, W (c * p) = W p) (hcal : W T = W 0)
    (hpass : FixedTNonincrease W) :
    ∃! f : TransparentFourthDestructiveQuotient.Quotient → ℝ, ∀ p, f (TransparentFourthDestructiveQuotient.q p) = W p :=
  unique_factorization_of_nullInsertion W
    (nullInsertion_of_calibrated_fixedT_nonincrease W htrans hcal hpass)

end

end IDT.QMClosure.TransparentFourthNullPassivityQuotient
