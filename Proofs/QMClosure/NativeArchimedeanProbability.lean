import Proofs.QMClosure.NativeProbabilityUniqueness
import Mathlib.Data.Real.Embedding

/-!
# Conditional native probability uniqueness over an additive ordered carrier

The probability-family contract uses addition, order, and a chosen normalization
element `1`; it does not multiply or divide probabilities. A normalized monotone
additive map transports the same six fields to the frozen real-valued `Law`.
An injective such map then transfers its conditional uniqueness theorem back.

For an Archimedean linearly ordered additive commutative group with positive
chosen `1`, mathlib supplies this map into the reals. Every actual
Gaussian-dyadic native output consequently satisfies an intrinsic additive
denominator identity. No field, rational scalar action, topology, or completeness
of the probability carrier is assumed.

These results are conditional on a supplied `LawOver`; they do not assert that
every carrier admits one. They weaken only the native probability carrier.
Earlier real-valued raw weights and Hilbert completion remain separate issues.
Archimedeanness is a sufficient transport hypothesis, not a global minimality
claim. This module neither derives the six fields from IDT's primitive base nor
establishes physical actualization or full QM closure.
-/

namespace IDT.QMClosure.NativeArchimedeanProbability

noncomputable section
open NativeVacuumProbabilityFamily
open scoped BigOperators

/-- The six fields of the real-valued `Law`, with only its probability carrier
changed. The chosen `1` is a normalization element, not a multiplicative unit. -/
structure LawOver (A : Type*) [AddCommMonoid A] [PartialOrder A] [One A] where
  prob : {ι : Type} → [Fintype ι] → [DecidableEq ι] → ι → Native ι → ι → A
  nonnegative : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) i,
    0 ≤ prob s c i
  normalized : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι),
    ∑ i, prob s c i = 1
  prepared_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c d : Native ι), c.eval (source s) = d.eval (source s) → prob s c = prob s d
  output_perm : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (e : Equiv.Perm ι) i,
    prob s (.seq c (.permute e)) i = prob s c (e i)
  spectator_pair : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (i j k : ι) (hij : i ≠ j),
    k ≠ i → k ≠ j → prob s (.seq c (.pair i j hij)) k = prob s c k
  vacuum : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (s : ι) (c : Native ι) i,
    prob (.inl s) (padCircuit κ c) (.inl i) = prob s c i

section Transport

variable {A : Type*} [AddCommMonoid A] [PartialOrder A] [One A]

/-- Transport along a normalized order-preserving additive map. Injectivity is
not required to obtain the real-valued law. -/
def LawOver.toReal (L : LawOver A) (f : A →+o ℝ) (h_one : f 1 = 1) : Law where
  prob s c i := f (L.prob s c i)
  nonnegative s c i := by
    have h : f 0 ≤ f (L.prob s c i) := f.monotone' (L.nonnegative s c i)
    simpa only [map_zero] using h
  normalized s c := by
    rw [← map_sum, L.normalized, h_one]
  prepared_eq s c d h := by
    funext i
    exact congrArg f (congrFun (L.prepared_eq s c d h) i)
  output_perm s c e i := congrArg f (L.output_perm s c e i)
  spectator_pair s c i j k hij hki hkj :=
    congrArg f (L.spectator_pair s c i j k hij hki hkj)
  vacuum s c i := congrArg f (L.vacuum s c i)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The established real-valued selection theorem applies to every transported
law without strengthening its six fields. -/
theorem mapped_native_probability_eq_normSq (L : LawOver A) (f : A →+o ℝ)
    (h_one : f 1 = 1) (s : ι) (c : Native ι) (i : ι) :
    f (L.prob s c i) = Complex.normSq (c.eval (source s) i) :=
  NativeProbabilityUniqueness.native_probability_eq_normSq (L.toReal f h_one) s c i

/-- Injectivity is needed only when transferring uniqueness back to the
original probability carrier. -/
theorem native_probabilities_equal_of_injective (L M : LawOver A) (f : A →+o ℝ)
    (h_one : f 1 = 1) (h_injective : Function.Injective f)
    (s : ι) (c : Native ι) (i : ι) : L.prob s c i = M.prob s c i := by
  apply h_injective
  exact (mapped_native_probability_eq_normSq L f h_one s c i).trans
    (mapped_native_probability_eq_normSq M f h_one s c i).symm

end Transport

section Archimedean

variable {A : Type*} [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A]
  [One A] [ZeroLEOneClass A] [NeZero (1 : A)] [Archimedean A]

/-- The chosen unit is positive, and the standard Archimedean embedding
preserves it. No multiplication structure on `A` is involved. -/
def LawOver.archimedeanToReal (L : LawOver A) : Law :=
  L.toReal (Archimedean.embedReal A) Archimedean.embedReal_one

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem embedded_native_probability_eq_normSq (L : LawOver A)
    (s : ι) (c : Native ι) (i : ι) :
    Archimedean.embedReal A (L.prob s c i) = Complex.normSq (c.eval (source s) i) :=
  mapped_native_probability_eq_normSq L (Archimedean.embedReal A)
    Archimedean.embedReal_one s c i

/-- Conditional pointwise uniqueness; no inhabitant of `LawOver A` is claimed
for an arbitrary carrier satisfying the typeclass assumptions. -/
theorem native_probabilities_equal (L M : LawOver A)
    (s : ι) (c : Native ι) (i : ι) : L.prob s c i = M.prob s c i :=
  native_probabilities_equal_of_injective L M (Archimedean.embedReal A)
    Archimedean.embedReal_one (Archimedean.embedReal_injective A) s c i

/-- For any Gaussian-dyadic witness of an actual native output, selection has
an intrinsic additive form even when the carrier has no division operation. -/
theorem native_probability_denominator_identity (L : LawOver A)
    (s : ι) (c : Native ι) (i : ι) (g : GaussianInt) (k : ℕ)
    (h_output : c.eval (source s) i = (g : ℂ) / (2 : ℂ)^k) :
    (4^k : ℕ) • L.prob s c i = (g.re^2 + g.im^2 : ℤ) • (1 : A) := by
  apply Archimedean.embedReal_injective A
  simp only [map_nsmul, map_zsmul, Archimedean.embedReal_one, nsmul_eq_mul,
    zsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat, Int.cast_add, Int.cast_pow]
  rw [embedded_native_probability_eq_normSq L, h_output,
    NativeProbabilityUniqueness.normSq_gaussian_dyadic]
  field_simp

end Archimedean
end

end IDT.QMClosure.NativeArchimedeanProbability
