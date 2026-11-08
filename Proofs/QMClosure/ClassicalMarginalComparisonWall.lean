import Proofs.QMClosure.RawClassicalProcessEnvelope
import Proofs.QMClosure.BoundedComparisonReferenceWall
import Proofs.QMClosure.RawProcessComparisonBridge
import Proofs.QMClosure.NativeAttenuationCircuit

/-!
# Classical joint and marginal comparison boundaries

Classical joint-TV processing and independent-reference laws do not supply
nonexpansion of the sum of raw pair-port comparisons. The actual supplied
complex mixer preserves joint TV while increasing the sum of marginal Dirac
TV comparisons. Squaring those comparisons retains this counterexample.

Separately, squared TV fails ordinary flag-weighted mixture additivity on an
explicit labeled classical carrier. This excludes that particular comparison
law, without excluding every quadratic comparison. The supplied complex mixer
is a mathematical witness, with no primitive-origin, physical-readout, Born,
Bell, non-hidden-joint, or full-QM conclusion. Resource grading supplies no
additional comparison law here.
-/

namespace IDT.QMClosure.ClassicalMarginalComparisonWall

noncomputable section

open RationalFiniteDistribution RawProcessComparisonBridge

variable {V : Type*}

@[simp] theorem tv_self (μ : FinDist V) : tv μ μ = 0 := by
  simp [tv]

/-- Real TV between pure classical embeddings of raw points. -/
def diracComparison (x y : V) : ℝ := tv (dirac x) (dirac y)

@[simp] theorem diracComparison_self (x : V) : diracComparison x x = 0 := by
  simp [diracComparison]

theorem diracComparison_of_ne (x y : V) (h : x ≠ y) :
    diracComparison x y = 1 :=
  BoundedComparisonReferenceWall.real_tv_dirac_of_ne x y h

def squaredDiracComparison (x y : V) : ℝ := (diracComparison x y) ^ 2

def inputPair : ℂ × ℂ := (1, 0)
def zeroPair : ℂ × ℂ := (0, 0)

theorem mixer_inputPair :
    NativeMixerEventConeExclusion.mixer inputPair =
      (NativeAttenuationCircuit.a, NativeAttenuationCircuit.b) := by
  apply Prod.ext <;>
    simp [inputPair, NativeAttenuationCircuit.mixer_fst,
      NativeAttenuationCircuit.mixer_snd]

theorem mixer_zeroPair :
    NativeMixerEventConeExclusion.mixer zeroPair = zeroPair := by
  simpa [zeroPair] using NativeMixerEventConeExclusion.mixer_transparent (0 : ℂ)

theorem mixer_coefficients_nonzero :
    NativeAttenuationCircuit.a ≠ 0 ∧ NativeAttenuationCircuit.b ≠ 0 := by
  constructor <;> intro h <;>
    have hre := congrArg Complex.re h <;>
    norm_num [NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
      Complex.div_re, Complex.div_im] at hre

theorem marginal_tv_before : pairComparison diracComparison inputPair zeroPair = 1 := by
  simp [pairComparison, inputPair, zeroPair,
    diracComparison_of_ne (1 : ℂ) 0 one_ne_zero]

theorem marginal_tv_after :
    pairComparison diracComparison
      (NativeMixerEventConeExclusion.mixer inputPair)
      (NativeMixerEventConeExclusion.mixer zeroPair) = 2 := by
  rw [mixer_inputPair, mixer_zeroPair]
  norm_num [pairComparison, zeroPair,
    diracComparison_of_ne _ _ mixer_coefficients_nonzero.1,
    diracComparison_of_ne _ _ mixer_coefficients_nonzero.2]

theorem marginal_tv_not_nonexpanding :
    ¬ PairComparisonNonexpanding diracComparison
      NativeMixerEventConeExclusion.mixer := by
  intro h
  have hh := h inputPair zeroPair
  rw [marginal_tv_after, marginal_tv_before] at hh
  norm_num at hh

theorem squared_marginal_tv_before :
    pairComparison squaredDiracComparison inputPair zeroPair = 1 := by
  simp [pairComparison, squaredDiracComparison, inputPair, zeroPair,
    diracComparison_of_ne (1 : ℂ) 0 one_ne_zero]

theorem squared_marginal_tv_after :
    pairComparison squaredDiracComparison
      (NativeMixerEventConeExclusion.mixer inputPair)
      (NativeMixerEventConeExclusion.mixer zeroPair) = 2 := by
  rw [mixer_inputPair, mixer_zeroPair]
  norm_num [pairComparison, squaredDiracComparison, zeroPair,
    diracComparison_of_ne _ _ mixer_coefficients_nonzero.1,
    diracComparison_of_ne _ _ mixer_coefficients_nonzero.2]

theorem squared_marginal_tv_not_nonexpanding :
    ¬ PairComparisonNonexpanding squaredDiracComparison
      NativeMixerEventConeExclusion.mixer := by
  intro h
  have hh := h inputPair zeroPair
  rw [squared_marginal_tv_after, squared_marginal_tv_before] at hh
  norm_num at hh

/-- The whole-pair carrier has its own TV, preserved for all distributions. -/
theorem joint_tv_preserved (μ ν : FinDist (ℂ × ℂ)) :
    tv (map NativeMixerEventConeExclusion.mixer μ)
      (map NativeMixerEventConeExclusion.mixer ν) = tv μ ν :=
  RawClassicalProcessEnvelope.gate_pushforward_tv _
    NativeMixerEventConeExclusion.mixer_square μ ν

theorem joint_tv_before : tv (dirac inputPair) (dirac zeroPair) = 1 := by
  have hne : inputPair ≠ zeroPair := by
    intro h
    have hh := congrArg Prod.fst h
    norm_num [inputPair, zeroPair] at hh
  exact_mod_cast BoundedComparisonReferenceWall.real_tv_dirac_of_ne _ _ hne

theorem joint_tv_after :
    tv (map NativeMixerEventConeExclusion.mixer (dirac inputPair))
      (map NativeMixerEventConeExclusion.mixer (dirac zeroPair)) = 1 := by
  rw [joint_tv_preserved, joint_tv_before]

/-- A common classical component cancels exactly in the finite L1 difference. -/
theorem tv_shared_mixture (t : ℚ) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (μ ν ρ : FinDist V) :
    tv (mixture t ht ht' μ ρ) (mixture t ht ht' ν ρ) = t * tv μ ν := by
  have hdifference :
      (mixture t ht ht' μ ρ).coeff - (mixture t ht ht' ν ρ).coeff =
        t • (μ.coeff - ν.coeff) := by
    simp only [mixture, smul_sub]
    abel
  unfold tv
  rw [hdifference, l1_smul, abs_of_nonneg ht]
  ring

theorem squared_tv_shared_mixture (t : ℚ) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (μ ν ρ : FinDist V) :
    tv (mixture t ht ht' μ ρ) (mixture t ht ht' ν ρ) ^ 2 =
      t ^ 2 * tv μ ν ^ 2 := by
  rw [tv_shared_mixture, mul_pow]

abbrev FlagCarrier := Bool ⊕ Unit

def flaggedLeft : FinDist FlagCarrier :=
  mixture (1 / 2) (by norm_num) (by norm_num)
    (map Sum.inl (dirac false)) (map Sum.inr (dirac ()))

def flaggedRight : FinDist FlagCarrier :=
  mixture (1 / 2) (by norm_num) (by norm_num)
    (map Sum.inl (dirac true)) (map Sum.inr (dirac ()))

theorem flagged_component_tv :
    tv (map (Sum.inl : Bool → FlagCarrier) (dirac false))
      (map Sum.inl (dirac true)) = 1 := by
  simp only [map_dirac]
  exact_mod_cast BoundedComparisonReferenceWall.real_tv_dirac_of_ne
    (Sum.inl false : FlagCarrier) (Sum.inl true) (by simp)

theorem flagged_tv : tv flaggedLeft flaggedRight = 1 / 2 := by
  unfold flaggedLeft flaggedRight
  rw [tv_shared_mixture, flagged_component_tv]
  ring

theorem flagged_squared_tv : tv flaggedLeft flaggedRight ^ 2 = 1 / 4 := by
  rw [flagged_tv]
  norm_num

/-- Ordinary flag weights multiply component squared comparisons linearly. -/
def flagWeightedSquaredComparison : ℚ :=
  (1 / 2) * tv (map (Sum.inl : Bool → FlagCarrier) (dirac false))
      (map Sum.inl (dirac true)) ^ 2 +
    (1 - 1 / 2) * tv (map (Sum.inr : Unit → FlagCarrier) (dirac ()))
      (map Sum.inr (dirac ())) ^ 2

theorem flag_weighted_squared_comparison : flagWeightedSquaredComparison = 1 / 2 := by
  unfold flagWeightedSquaredComparison
  rw [flagged_component_tv, tv_self]
  norm_num

theorem squared_tv_fails_ordinary_flagged_additivity :
    tv flaggedLeft flaggedRight ^ 2 < flagWeightedSquaredComparison := by
  rw [flagged_squared_tv, flag_weighted_squared_comparison]
  norm_num

end
end IDT.QMClosure.ClassicalMarginalComparisonWall
