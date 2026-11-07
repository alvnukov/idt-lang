import Proofs.QMClosure.NativeAllocatedStableObservation
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Ring.Int.Parity

/-!
# A separating Boolean arithmetic observation without reference settling

The real coordinate of every generated Gaussian dyadic has a unique rational
value. The supplied Boolean observation records the parity of its exact
2-adic valuation, with valuation zero at the rational zero. Contextual response
equivalence separates literal generated values, although no generated reference
settles this observation. For each reference, the actually allocated input
obtained by adding one has opposite observations at arbitrarily late adjacent
native reference steps.

This is an exact arithmetic readout on the supplied scalar carrier and native
gate, rather than a physical detector construction. Repeated known-reference
occurrences remain separately allocated and charged; no uniform resource bound
or unknown-token cloning is supplied. The existing single-basis law can be
transported with its whole probability field unchanged. No probability
provenance, physical availability, multi-source probability extension,
actualization, or QM closure is asserted. No topology premise is used.
-/

namespace IDT.QMClosure.NativeAllocatedValuationObservation

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open OperationalContextQuotient ResponseContextQuotient
open NativeAllocatedObservationBoundary NativeAllocatedSourceArithmetic
open NativeAllocatedStableObservation NativeAllocatedSignatureLaw
open NativeAttenuationCircuit (a)

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem exists_rational_real (x : G) : ∃ q : ℚ, (q : ℝ) = x.val.re := by
  have hx : Reachable x.val := (generated_iff_reachable x.val).mp x.property
  obtain ⟨k, g, hg⟩ := (reachable_iff_gaussian_dyadic x.val).mp hx
  refine ⟨(g.re : ℚ) / (2 : ℚ)^k, ?_⟩
  have hp : (((2 : ℚ)^k : ℚ) : ℂ) = (2 : ℂ)^k := by norm_cast
  rw [hg, ← hp, Complex.div_ratCast_re]
  rw [← GaussianInt.intCast_re]
  push_cast
  rfl

/-- The unique rational value of the literal real coordinate, independent of
the chosen allocated program or dyadic presentation. -/
def realCoord (x : G) : ℚ := Classical.choose (exists_rational_real x)

theorem realCoord_cast (x : G) : (realCoord x : ℝ) = x.val.re :=
  Classical.choose_spec (exists_rational_real x)

theorem realCoord_eq_of_cast (x : G) (q : ℚ) (hq : (q : ℝ) = x.val.re) :
    realCoord x = q := by
  apply Rat.cast_injective (α := ℝ)
  exact (realCoord_cast x).trans hq.symm

@[simp] theorem realCoord_zeroG : realCoord zeroG = 0 := by
  apply realCoord_eq_of_cast
  simp

@[simp] theorem realCoord_unitG : realCoord unitG = 1 := by
  apply realCoord_eq_of_cast
  simp

/-- The exact binary arithmetic observation; zero has valuation zero. -/
def valuationSignature (x : G) : Bool := decide (Odd (padicValRat 2 (realCoord x)))

@[simp] theorem valuationSignature_zeroG : valuationSignature zeroG = false := by
  simp [valuationSignature]

private def chosenProgram (x : G) : ScalarProgram := Classical.choose x.property

private theorem value_chosenProgram (x : G) : value (chosenProgram x) = x.val :=
  Classical.choose_spec x.property

/-- An actual allocated program adding the known unit source to its input recipe. -/
def plusUnit (z : G) : G := ofProgram (NativeAllocatedSourceArithmetic.add (chosenProgram z) one)

theorem val_plusUnit (z : G) : (plusUnit z).val = z.val + 1 := by
  simp only [plusUnit, val_ofProgram, value_add, value_chosenProgram, value_one]

private def tiny (n : ℕ) : ℚ := ((2 : ℚ)^n)⁻¹

private theorem valuation_tiny (n : ℕ) : padicValRat 2 (tiny n) = -(n : ℤ) :=
  padicValRat.self_pow_inv n

/-- The smaller valuation dominates addition to any fixed rational coordinate. -/
private theorem valuation_add_tiny (q : ℚ) (n : ℕ)
    (hsmall : -(n : ℤ) < padicValRat 2 q) :
    padicValRat 2 (q + tiny n) = -(n : ℤ) := by
  by_cases hq : q = 0
  · simpa only [hq, zero_add] using valuation_tiny n
  have ht : tiny n ≠ 0 := inv_ne_zero (pow_ne_zero n (by norm_num : (2 : ℚ) ≠ 0))
  have hsum : q + tiny n ≠ 0 := by
    intro he
    have heq : q = -tiny n := (eq_neg_iff_add_eq_zero).mpr he
    have hv : padicValRat 2 q = -(n : ℤ) := by
      rw [heq, padicValRat.neg, valuation_tiny]
    omega
  rw [add_comm]
  exact (padicValRat.add_eq_of_lt (by rwa [add_comm]) ht hq
    (by simpa only [valuation_tiny] using hsmall)).trans (valuation_tiny n)

private theorem a_pow_eight : a^8 = (((2 : ℚ)^4)⁻¹ : ℂ) := by
  apply Complex.ext <;>
    norm_num [a, pow_succ, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

private theorem a_pow_eight_mul (k : ℕ) : a^(8 * k) = (tiny (4 * k) : ℂ) := by
  rw [pow_mul, a_pow_eight]
  simp only [tiny, Rat.cast_inv, Rat.cast_pow]
  push_cast
  rw [inv_pow, ← pow_mul]

private theorem re_a_pow_eight_mul (k : ℕ) :
    (a^(8 * k)).re = (tiny (4 * k) : ℝ) := by
  rw [a_pow_eight_mul, Complex.ratCast_re]

private theorem re_a_pow_eight_mul_add_one (k : ℕ) :
    (a^(8 * k + 1)).re = (tiny (4 * k + 1) : ℝ) := by
  rw [pow_succ, a_pow_eight_mul, Complex.mul_re]
  simp only [Complex.ratCast_re, Complex.ratCast_im]
  have ht : tiny (4 * k + 1) = tiny (4 * k) / 2 := by
    simp only [tiny, pow_succ, mul_inv_rev, div_eq_mul_inv]
    ring
  rw [ht, Rat.cast_div]
  norm_num [a, Complex.div_re, Complex.div_im]
  ring

theorem realCoord_reference_eighth (z : G) (k : ℕ) :
    realCoord ((referenceStep z)^[8 * k] (plusUnit z)) = realCoord z + tiny (4 * k) := by
  apply realCoord_eq_of_cast
  rw [referenceStep_iterate_coe, val_plusUnit]
  have hd : z.val + 1 - z.val = 1 := by ring
  rw [hd, mul_one, Complex.add_re, re_a_pow_eight_mul]
  push_cast
  rw [realCoord_cast]

theorem realCoord_reference_eighth_next (z : G) (k : ℕ) :
    realCoord ((referenceStep z)^[8 * k + 1] (plusUnit z)) =
      realCoord z + tiny (4 * k + 1) := by
  apply realCoord_eq_of_cast
  rw [referenceStep_iterate_coe, val_plusUnit]
  have hd : z.val + 1 - z.val = 1 := by ring
  rw [hd, mul_one, Complex.add_re, re_a_pow_eight_mul_add_one]
  push_cast
  rw [realCoord_cast]

private theorem not_odd_neg_four_mul (k : ℕ) : ¬ Odd (-(4 * k : ℕ) : ℤ) := by
  rw [Int.odd_iff]
  omega

private theorem odd_neg_four_mul_add_one (k : ℕ) : Odd (-((4 * k + 1 : ℕ) : ℤ)) := by
  rw [Int.odd_iff]
  omega

private theorem signature_eighth_false (z : G) (k : ℕ)
    (hk : -((4 * k : ℕ) : ℤ) < padicValRat 2 (realCoord z)) :
    valuationSignature ((referenceStep z)^[8 * k] (plusUnit z)) = false := by
  simp only [valuationSignature, realCoord_reference_eighth,
    valuation_add_tiny (realCoord z) (4 * k) hk,
    not_odd_neg_four_mul, decide_false]

private theorem signature_eighth_next_true (z : G) (k : ℕ)
    (hk : -((4 * k + 1 : ℕ) : ℤ) < padicValRat 2 (realCoord z)) :
    valuationSignature ((referenceStep z)^[8 * k + 1] (plusUnit z)) = true := by
  simp only [valuationSignature, realCoord_reference_eighth_next,
    valuation_add_tiny (realCoord z) (4 * k + 1) hk,
    odd_neg_four_mul_add_one, decide_true]

/-- At every generated reference, an allocated input has arbitrarily late
adjacent opposite Boolean responses. No finite-carrier premise is supplied. -/
theorem late_adjacent_opposite_signatures (z : G) (N : ℕ) :
    ∃ k : ℕ, N ≤ 8 * k ∧
      valuationSignature ((referenceStep z)^[8 * k] (plusUnit z)) = false ∧
      valuationSignature ((referenceStep z)^[8 * k + 1] (plusUnit z)) = true := by
  obtain ⟨M, hM⟩ := exists_nat_gt (-padicValRat 2 (realCoord z))
  let k := N + M + 1
  refine ⟨k, by dsimp [k]; omega, signature_eighth_false z k ?_,
    signature_eighth_next_true z k ?_⟩ <;> dsimp [k] <;> omega

/-- For each reference the chosen allocated input has no eventual constant
Boolean tail, even with a freely chosen eventual value. -/
theorem plusUnit_no_eventual_constant (z : G) :
    ¬ (∃ c : Bool, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      valuationSignature ((referenceStep z)^[n] (plusUnit z)) = c) := by
  rintro ⟨c, N, hN⟩
  obtain ⟨k, hk, heven, hodd⟩ := late_adjacent_opposite_signatures z N
  have hsame := (hN (8 * k) hk).trans (hN (8 * k + 1) (by omega)).symm
  rw [heven, hodd] at hsame
  contradiction

theorem valuationSignature_no_reference_settles : ¬ ReferenceSettles valuationSignature := by
  rintro ⟨z, hz⟩
  obtain ⟨N, hN⟩ := hz (plusUnit z)
  obtain ⟨k, hk, heven, hodd⟩ := late_adjacent_opposite_signatures z N
  have hsame := (hN (8 * k) hk).trans (hN (8 * k + 1) (by omega)).symm
  rw [heven, hodd] at hsame
  contradiction

private theorem responseEq_return_multiple (σ : G → Bool) (L : ℕ)
    (hret : ∀ z x : G, ResponseEq operationG σ x ((referenceStep z)^[L] x))
    (z x : G) (m : ℕ) :
    ResponseEq operationG σ x ((referenceStep z)^[L * m] x) := by
  induction m with
  | zero => intro C; rfl
  | succ m ih =>
    rw [Nat.mul_succ, Nat.add_comm, Function.iterate_add_apply]
    intro C
    exact (ih C).trans (hret z ((referenceStep z)^[L * m] x) C)

private def twoG : G := ofProgram (naturalProgram 2)

private theorem realCoord_twoG : realCoord twoG = 2 := by
  apply realCoord_eq_of_cast
  have hv : twoG.val = 2 := value_naturalProgram 2
  rw [hv]
  norm_num

private theorem twoG_eq_plusUnit_unitG : twoG = plusUnit unitG := by
  apply Subtype.ext
  change value (naturalProgram 2) = (plusUnit unitG).val
  rw [value_naturalProgram, val_plusUnit, val_unitG]
  norm_num

private theorem signature_twoG : valuationSignature twoG = true := by
  have hv : padicValRat 2 (2 : ℚ) = 1 := by
    convert padicValRat.self (by decide : 1 < 2) using 1
  rw [valuationSignature, realCoord_twoG, hv]
  decide

/-- A common positive contextual return contradicts the real-coordinate
valuation parity at the generated value two and generated unit reference. -/
theorem valuationSignature_separates : Separates valuationSignature := by
  intro x y h
  by_contra hxy
  obtain ⟨L, hL, hret⟩ :=
    common_contextual_return_of_distinct_responseEq valuationSignature hxy h
  have hreturn := responseEq_return_multiple valuationSignature L hret unitG twoG 8
  have hs := signature_eq hreturn
  rw [signature_twoG, Nat.mul_comm L 8, twoG_eq_plusUnit_unitG] at hs
  have hsmall : -((4 * L : ℕ) : ℤ) < padicValRat 2 (realCoord unitG) := by
    simp only [realCoord_unitG, padicValRat.one]
    omega
  rw [signature_eighth_false unitG L hsmall] at hs
  contradiction

theorem valuationSignature_nonconstant : ∃ x y : G, valuationSignature x ≠ valuationSignature y := by
  refine ⟨zeroG, twoG, ?_⟩
  rw [valuationSignature_zeroG, signature_twoG]
  decide

theorem valuationSignature_no_settling_reference (z : G) :
    ¬ (∀ x : G, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      valuationSignature ((referenceStep z)^[n] x) = valuationSignature z) := by
  intro h
  exact valuationSignature_no_reference_settles ⟨z, h⟩

/-- The original single-basis law exists despite the failure of settling. -/
theorem valuationSignature_law_without_settling :
    Nonempty (ResponseNativeProbabilitySelection.Law (signatureData valuationSignature) unitG) ∧
      ¬ ReferenceSettles valuationSignature :=
  ⟨(law_nonempty_iff_separates valuationSignature).mpr valuationSignature_separates,
    valuationSignature_no_reference_settles⟩

/-- Transport any supplied scalar probability field without changing it. -/
def lawOfScalar (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law (signatureData valuationSignature) unitG :=
  NativeAllocatedSignatureLaw.lawOfScalar valuationSignature valuationSignature_separates L

theorem lawOfScalar_probability (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob G Bool (signatureData valuationSignature) unitG
        (lawOfScalar L) = @NativeVacuumProbabilityFamily.Law.prob L := rfl

end
end IDT.QMClosure.NativeAllocatedValuationObservation
