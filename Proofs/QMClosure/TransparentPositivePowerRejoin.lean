import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Positive-power rejoining in a transparent semiring pair

The generic theorem chain comprises positive telescopes, inverse words,
inverse-product expansions, and pair commutation.

Finite geometric words give two-sided inverses when a+b=1 and a positive
power of a equals a positive power of b. Their product expansions then give
pair commutation. All coefficients and exponents in the inverse words are
natural, and the ambient algebra is an arbitrary semiring.
-/

open scoped BigOperators

namespace IDT.TransparentPositivePowerRejoin

section Algebra

variable {S : Type*} [Semiring S] {a b : S}

/-- A finite complement telescope with the transparent coefficient on the left. -/
theorem left_geometric_telescope (hsum : a + b = 1) (k : ℕ) :
    a * (∑ j ∈ Finset.range k, b ^ j) + b ^ k = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      calc
        a * ((∑ j ∈ Finset.range k, b ^ j) + b ^ k) + b ^ (k + 1) =
            a * (∑ j ∈ Finset.range k, b ^ j) + (a + b) * b ^ k := by
          rw [pow_succ']
          noncomm_ring
        _ = a * (∑ j ∈ Finset.range k, b ^ j) + b ^ k := by rw [hsum, one_mul]
        _ = 1 := ih

/-- The reverse telescope retains the transparent coefficient on the right. -/
theorem right_geometric_telescope (hsum : a + b = 1) (k : ℕ) :
    (∑ j ∈ Finset.range k, b ^ j) * a + b ^ k = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      calc
        ((∑ j ∈ Finset.range k, b ^ j) + b ^ k) * a + b ^ (k + 1) =
            (∑ j ∈ Finset.range k, b ^ j) * a + b ^ k * (a + b) := by
          rw [pow_succ]
          noncomm_ring
        _ = (∑ j ∈ Finset.range k, b ^ j) * a + b ^ k := by rw [hsum, mul_one]
        _ = 1 := ih

/-- The explicit inverse word for a under a^(m+1)=b^(n+1). -/
def inverseWordA (a b : S) (m n : ℕ) : S :=
  (∑ j ∈ Finset.range (n + 1), b ^ j) + a ^ m

/-- The symmetric explicit inverse word for b. -/
def inverseWordB (a b : S) (m n : ℕ) : S :=
  (∑ j ∈ Finset.range (m + 1), a ^ j) + b ^ n

/-- Both inverse identities for the first coefficient precede pair commutation. -/
theorem geometric_inverse_a (m n : ℕ)
    (hsum : a + b = 1) (hjoin : a ^ (m + 1) = b ^ (n + 1)) :
    inverseWordA a b m n * a = 1 ∧ a * inverseWordA a b m n = 1 := by
  constructor
  · calc
      inverseWordA a b m n * a =
          (∑ j ∈ Finset.range (n + 1), b ^ j) * a + a ^ (m + 1) := by
        dsimp [inverseWordA]
        rw [add_mul, pow_succ]
      _ = (∑ j ∈ Finset.range (n + 1), b ^ j) * a + b ^ (n + 1) := by rw [hjoin]
      _ = 1 := right_geometric_telescope hsum (n + 1)
  · calc
      a * inverseWordA a b m n =
          a * (∑ j ∈ Finset.range (n + 1), b ^ j) + a ^ (m + 1) := by
        dsimp [inverseWordA]
        rw [mul_add, pow_succ']
      _ = a * (∑ j ∈ Finset.range (n + 1), b ^ j) + b ^ (n + 1) := by rw [hjoin]
      _ = 1 := left_geometric_telescope hsum (n + 1)

/-- The second coefficient has the symmetric two-sided inverse word. -/
theorem geometric_inverse_b (m n : ℕ)
    (hsum : a + b = 1) (hjoin : a ^ (m + 1) = b ^ (n + 1)) :
    inverseWordB a b m n * b = 1 ∧ b * inverseWordB a b m n = 1 := by
  have hsum' : b + a = 1 := by rw [add_comm]; exact hsum
  exact geometric_inverse_a n m hsum' hjoin.symm

/-- Both products of inverse words have the same positive expansion. -/
theorem inverse_product_expansions (m n : ℕ)
    (hsum : a + b = 1) (hjoin : a ^ (m + 1) = b ^ (n + 1)) :
    inverseWordA a b m n * inverseWordB a b m n =
        inverseWordB a b m n + inverseWordA a b m n ∧
      inverseWordB a b m n * inverseWordA a b m n =
        inverseWordB a b m n + inverseWordA a b m n := by
  let u := inverseWordA a b m n
  let v := inverseWordB a b m n
  obtain ⟨hua, hau⟩ := geometric_inverse_a m n hsum hjoin
  obtain ⟨hvb, hbv⟩ := geometric_inverse_b m n hsum hjoin
  change u * a = 1 at hua
  change a * u = 1 at hau
  change v * b = 1 at hvb
  change b * v = 1 at hbv
  change u * v = v + u ∧ v * u = v + u
  constructor
  · calc
      u * v = u * (a + b) * v := by rw [hsum]; simp
      _ = (u * a) * v + u * (b * v) := by noncomm_ring
      _ = v + u := by rw [hua, hbv]; simp
  · calc
      v * u = v * (a + b) * u := by rw [hsum]; simp
      _ = v * (a * u) + (v * b) * u := by noncomm_ring
      _ = v + u := by rw [hau, hvb]; simp

/-- The explicit inverse words commute. -/
theorem inverse_words_commute (m n : ℕ)
    (hsum : a + b = 1) (hjoin : a ^ (m + 1) = b ^ (n + 1)) :
    Commute (inverseWordA a b m n) (inverseWordB a b m n) := by
  obtain ⟨huv, hvu⟩ := inverse_product_expansions m n hsum hjoin
  change inverseWordA a b m n * inverseWordB a b m n =
    inverseWordB a b m n * inverseWordA a b m n
  exact huv.trans hvu.symm

/-- Transparency and positive-power rejoining imply pair commutation. -/
theorem commute_of_transparent_positive_power (m n : ℕ)
    (hsum : a + b = 1) (hjoin : a ^ (m + 1) = b ^ (n + 1)) : Commute a b := by
  let u := inverseWordA a b m n
  let v := inverseWordB a b m n
  obtain ⟨hua, hau⟩ := geometric_inverse_a m n hsum hjoin
  obtain ⟨hvb, hbv⟩ := geometric_inverse_b m n hsum hjoin
  change u * a = 1 at hua
  change a * u = 1 at hau
  change v * b = 1 at hvb
  change b * v = 1 at hbv
  have huv : u * v = v * u := (inverse_words_commute m n hsum hjoin).eq
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

/-- Equal positive finite rejoin is a specialization of the unequal-power theorem. -/
theorem commute_of_transparent_finite_rejoin (n : ℕ) (hn : 0 < n)
    (hsum : a + b = 1) (hjoin : a ^ n = b ^ n) : Commute a b := by
  cases n with
  | zero => omega
  | succ k => exact commute_of_transparent_positive_power k k hsum hjoin

end Algebra

end IDT.TransparentPositivePowerRejoin
