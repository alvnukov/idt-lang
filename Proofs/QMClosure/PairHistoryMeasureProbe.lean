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

inductive PairHistoryMeasureFinding where
  | pairwiseWeightForcesZeroI3
  | signedQuadraticWeightAllowsTwoPathInterference
  | quadraticWeightIsNonnegative
  | independentAmplitudeProductFactorizes
deriving DecidableEq, Repr

def pairHistoryMeasureFindings : List PairHistoryMeasureFinding :=
  [ .pairwiseWeightForcesZeroI3,
    .signedQuadraticWeightAllowsTwoPathInterference,
    .quadraticWeightIsNonnegative,
    .independentAmplitudeProductFactorizes ]

theorem pair_history_measure_probe_records_four_findings :
    pairHistoryMeasureFindings.length = 4 := by
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
  "finite_pair_history_mechanism_only"

def pairHistoryMeasureProbeClaimBoundary : String :=
  "Does not derive the pair functional, Hilbert space, the Born rule, full QM, the Standard Model, or gravity."

end IDT.QMClosure
