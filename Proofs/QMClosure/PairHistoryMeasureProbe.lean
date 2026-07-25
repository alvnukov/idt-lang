import Mathlib

namespace IDT.QMClosure

/-!
# Pair-history measure probe

This file tests a deliberately small candidate below the current IDT primitive
packages: event weights may contain only singleton and pair-history terms.

The proved result is intentionally narrow. Pairwise event weights force the
third-order Sorkin interference term to vanish, while a quadratic weight on
signed history amplitudes still permits ordinary two-path interference,
nonnegative weights, and multiplicative composition.

Nothing here derives the pair functional from a local rewrite rule, selects
complex phases, proves strong positivity, or reconstructs quantum mechanics.
-/

structure PairHistoryTripleData where
  singletonA : ℤ
  singletonB : ℤ
  singletonC : ℤ
  pairAB : ℤ
  pairAC : ℤ
  pairBC : ℤ
deriving DecidableEq, Repr

def pairHistorySorkinI3 (data : PairHistoryTripleData) : ℤ :=
  (data.singletonA + data.singletonB + data.singletonC +
      data.pairAB + data.pairAC + data.pairBC) -
    (data.singletonA + data.singletonB + data.pairAB) -
    (data.singletonA + data.singletonC + data.pairAC) -
    (data.singletonB + data.singletonC + data.pairBC) +
    data.singletonA + data.singletonB + data.singletonC

theorem pair_history_measure_has_zero_sorkin_i3
    (data : PairHistoryTripleData) :
    pairHistorySorkinI3 data = 0 := by
  simp only [pairHistorySorkinI3]
  ring

def pairHistoryQuadraticWeight (amplitude : ℤ) : ℤ :=
  amplitude ^ 2

def pairHistoryQuadraticSorkinI3 (a b c : ℤ) : ℤ :=
  pairHistoryQuadraticWeight (a + b + c) -
    pairHistoryQuadraticWeight (a + b) -
    pairHistoryQuadraticWeight (a + c) -
    pairHistoryQuadraticWeight (b + c) +
    pairHistoryQuadraticWeight a +
    pairHistoryQuadraticWeight b +
    pairHistoryQuadraticWeight c

theorem quadratic_pair_history_measure_has_zero_sorkin_i3
    (a b c : ℤ) :
    pairHistoryQuadraticSorkinI3 a b c = 0 := by
  simp only [pairHistoryQuadraticSorkinI3, pairHistoryQuadraticWeight]
  ring

theorem quadratic_pair_history_weight_is_nonnegative
    (amplitude : ℤ) :
    0 ≤ pairHistoryQuadraticWeight amplitude := by
  exact sq_nonneg amplitude

theorem quadratic_pair_history_product_factorizes
    (left right : ℤ) :
    pairHistoryQuadraticWeight (left * right) =
      pairHistoryQuadraticWeight left * pairHistoryQuadraticWeight right := by
  simp only [pairHistoryQuadraticWeight]
  ring

theorem quadratic_pair_history_allows_constructive_interference :
    pairHistoryQuadraticWeight (1 + 1) = 4 ∧
      pairHistoryQuadraticWeight 1 + pairHistoryQuadraticWeight 1 = 2 := by
  norm_num [pairHistoryQuadraticWeight]

theorem quadratic_pair_history_allows_destructive_interference :
    pairHistoryQuadraticWeight (1 + (-1)) = 0 ∧
      pairHistoryQuadraticWeight 1 = 1 ∧
      pairHistoryQuadraticWeight (-1) = 1 := by
  norm_num [pairHistoryQuadraticWeight]

/--
The exact finite signature checked above. It is deliberately weaker than a
quantum reconstruction: it asks only for nonnegative weight, zero third-order
interference, multiplicative product weight, and one nonadditive two-path
witness.
-/
structure PairHistoryFiniteGateWitness (Amplitude : Type) where
  add : Amplitude → Amplitude → Amplitude
  mul : Amplitude → Amplitude → Amplitude
  weight : Amplitude → ℤ
  weightNonnegative : ∀ amplitude, 0 ≤ weight amplitude
  sorkinI3Zero : ∀ a b c,
    weight (add (add a b) c) - weight (add a b) -
      weight (add a c) - weight (add b c) +
      weight a + weight b + weight c = 0
  productFactorizes : ∀ left right,
    weight (mul left right) = weight left * weight right
  hasTwoPathInterference : ∃ a b,
    weight (add a b) ≠ weight a + weight b

def signedScalarPairHistoryGate : PairHistoryFiniteGateWitness ℤ where
  add := (· + ·)
  mul := (· * ·)
  weight := pairHistoryQuadraticWeight
  weightNonnegative := quadratic_pair_history_weight_is_nonnegative
  sorkinI3Zero := by
    intro a b c
    simp only [pairHistoryQuadraticWeight]
    ring
  productFactorizes := quadratic_pair_history_product_factorizes
  hasTwoPathInterference := by
    refine ⟨1, 1, ?_⟩
    norm_num [pairHistoryQuadraticWeight]

structure GaussianHistoryAmplitude where
  re : ℤ
  im : ℤ
deriving DecidableEq, Repr

def gaussianHistoryAdd
    (left right : GaussianHistoryAmplitude) : GaussianHistoryAmplitude :=
  ⟨left.re + right.re, left.im + right.im⟩

def gaussianHistoryMul
    (left right : GaussianHistoryAmplitude) : GaussianHistoryAmplitude :=
  ⟨left.re * right.re - left.im * right.im,
   left.re * right.im + left.im * right.re⟩

def gaussianHistoryWeight (amplitude : GaussianHistoryAmplitude) : ℤ :=
  amplitude.re ^ 2 + amplitude.im ^ 2

def gaussianPairHistoryGate :
    PairHistoryFiniteGateWitness GaussianHistoryAmplitude where
  add := gaussianHistoryAdd
  mul := gaussianHistoryMul
  weight := gaussianHistoryWeight
  weightNonnegative := by
    intro amplitude
    simp only [gaussianHistoryWeight]
    positivity
  sorkinI3Zero := by
    intro a b c
    rcases a with ⟨aRe, aIm⟩
    rcases b with ⟨bRe, bIm⟩
    rcases c with ⟨cRe, cIm⟩
    simp only [gaussianHistoryAdd, gaussianHistoryWeight]
    ring
  productFactorizes := by
    intro left right
    rcases left with ⟨leftRe, leftIm⟩
    rcases right with ⟨rightRe, rightIm⟩
    simp only [gaussianHistoryMul, gaussianHistoryWeight]
    ring
  hasTwoPathInterference := by
    refine ⟨⟨1, 0⟩, ⟨1, 0⟩, ?_⟩
    norm_num [gaussianHistoryAdd, gaussianHistoryWeight]

def gaussianUnitSamples : List GaussianHistoryAmplitude :=
  [⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]

theorem gaussian_gate_has_four_distinct_unit_weight_samples :
    gaussianUnitSamples.Nodup ∧
      gaussianUnitSamples.map gaussianHistoryWeight = [1, 1, 1, 1] := by
  decide

theorem signed_scalar_unit_weight_is_only_a_sign
    (amplitude : ℤ)
    (unitWeight : pairHistoryQuadraticWeight amplitude = 1) :
    amplitude = 1 ∨ amplitude = -1 := by
  simp only [pairHistoryQuadraticWeight] at unitWeight
  have factorization : (amplitude - 1) * (amplitude + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp factorization with positive | negative
  · left
    omega
  · right
    omega

inductive PairHistoryMeasureFinding where
  | pairwiseWeightForcesZeroI3
  | signedQuadraticWeightAllowsTwoPathInterference
  | quadraticWeightIsNonnegative
  | independentAmplitudeProductFactorizes
  | currentGatesUnderdetermineAmplitudeCarrier
deriving DecidableEq, Repr

def pairHistoryMeasureFindings : List PairHistoryMeasureFinding :=
  [ .pairwiseWeightForcesZeroI3,
    .signedQuadraticWeightAllowsTwoPathInterference,
    .quadraticWeightIsNonnegative,
    .independentAmplitudeProductFactorizes,
    .currentGatesUnderdetermineAmplitudeCarrier ]

theorem pair_history_measure_probe_records_five_findings :
    pairHistoryMeasureFindings.length = 5 := by
  rfl

inductive PairHistoryMeasureOpenObligation where
  | derivePairFunctionalFromLocalRewrite
  | deriveStrongPositivity
  | selectComplexPhaseOrEquivalentHolonomy
  | proveContinuumAndCompositeClosure
  | excludeNonQuantumPairMeasureModels
deriving DecidableEq, Repr

def pairHistoryMeasureOpenObligations :
    List PairHistoryMeasureOpenObligation :=
  [ .derivePairFunctionalFromLocalRewrite,
    .deriveStrongPositivity,
    .selectComplexPhaseOrEquivalentHolonomy,
    .proveContinuumAndCompositeClosure,
    .excludeNonQuantumPairMeasureModels ]

theorem pair_history_measure_probe_keeps_five_open_obligations :
    pairHistoryMeasureOpenObligations.length = 5 := by
  rfl

def pairHistoryMeasureProbeStatus : String :=
  "pair_history_gates_underdetermine_amplitude_carrier"

def pairHistoryMeasureProbeClaimBoundary : String :=
  "Two inequivalent finite amplitude carriers pass the current gates. The probe does not derive the pair functional, select complex quantum theory, or prove the Born rule, full QM, the Standard Model, or gravity."

end IDT.QMClosure
