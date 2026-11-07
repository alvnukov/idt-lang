import Proofs.QMClosure.NativeThreeWireSpectralCoefficient
import Proofs.QMClosure.FiniteStochasticTwistedReadout
import Proofs.QMClosure.NativeFiniteMemoryReadoutWall
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# A uniform finite stochastic preparation model cannot track the native readout

The contract is one finite uniform COMPOSITIONAL hidden PREPARATION model:
the same row-stochastic kernel P and fixed vectors mu and r apply across word
depth n. This n is not the repeated-trial counter in the deterministic detector
theorem. Allowing arbitrary fixed complex vectors includes real probability
initial distributions and real event readouts as a special case. For this fixed
model class, a uniform error bound across ALL preparation depths must be at
least 2/9; no optimality or eventual-bound assertion is made.

The native complex backend remains supplied. The raw Law corollary retains all
six Law axioms and both contextual diagonal-fixed hypotheses. No model with
n-dependent kernels, distributions or readouts, finite-prefix fit, external
drive, continuous or unbounded memory is excluded. No physical justification
of this uniform hidden-preparation contract, Born actualization, detector or
probability provenance, or QM closure is established.
-/

namespace IDT.QMClosure.NativeFiniteStochasticReadoutWall

open Filter Finset
open scoped Topology
open NativeThreeWireProbabilityDenominator NativeThreeWireSpectralCoefficient

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- A fixed complex linear readout of the repeated preparation kernel. -/
noncomputable def prediction (P : Matrix S S ℝ) (μ r : S → ℂ) (n : ℕ) : ℂ :=
  ∑ i, μ i * ((FiniteStochasticPeripheral.complexify P) ^ n).mulVec r i

private theorem lambda_norm_eq_one : ‖lambda‖ = 1 := by
  have hs : ‖lambda‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact lambda_normSq
  nlinarith [norm_nonneg lambda]

/-- Every model has the opposite of the native nonzero twisted coefficient. -/
theorem twisted_error_tendsto {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) (μ r : S → ℂ) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N,
      (lambda⁻¹) ^ n * (prediction P μ r n - (selectedWeight n : ℂ)))
      atTop (𝓝 (-(2 : ℂ) / 9)) := by
  have hmodel := FiniteStochasticTwistedReadout.tendsto_twistedCesaroMean_zero
    hP lambda_normSq lambda_pow_ne_one μ r
  have hsub := hmodel.sub selectedWeight_twistedCesaro_limit
  simpa only [FiniteStochasticTwistedReadout.twistedCesaroMean, prediction,
    mul_sub, sum_sub_distrib, zero_sub, neg_div] using hsub

/-- The native nonzero twisted coefficient prevents vanishing model error. -/
theorem no_vanishing_error {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) (μ r : S → ℂ) :
    ¬ Tendsto (fun n => prediction P μ r n - (selectedWeight n : ℂ))
      atTop (𝓝 0) := by
  intro herror
  have htwist : Tendsto
      (fun n => (lambda⁻¹) ^ n * (prediction P μ r n - (selectedWeight n : ℂ)))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n => ‖prediction P μ r n - (selectedWeight n : ℂ)‖)
    · intro n
      simp [norm_pow, norm_inv, lambda_norm_eq_one]
    · simpa using herror.norm
  have hmean := htwist.cesaro_smul
  change Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • ∑ n ∈ range N,
    (lambda⁻¹) ^ n * (prediction P μ r n - (selectedWeight n : ℂ)))
    atTop (𝓝 0) at hmean
  have havg : Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N,
      (lambda⁻¹) ^ n * (prediction P μ r n - (selectedWeight n : ℂ)))
      atTop (𝓝 0) := by
    simpa only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
      using hmean
  have hfalse := tendsto_nhds_unique havg (twisted_error_tendsto hP μ r)
  norm_num at hfalse

/-- A uniform bound over every preparation depth is at least 2/9. -/
theorem uniform_error_lower_bound {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) (μ r : S → ℂ) (epsilon : ℝ)
    (hbound : ∀ n : ℕ, ‖prediction P μ r n - (selectedWeight n : ℂ)‖ ≤ epsilon) :
    (2 : ℝ) / 9 ≤ epsilon := by
  have hmean (N : ℕ) (hN : 0 < N) :
      ‖(N : ℂ)⁻¹ * ∑ n ∈ range N,
        (lambda⁻¹) ^ n * (prediction P μ r n - (selectedWeight n : ℂ))‖ ≤ epsilon := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    calc
      _ = (N : ℝ)⁻¹ * ‖∑ n ∈ range N,
          (lambda⁻¹) ^ n * (prediction P μ r n - (selectedWeight n : ℂ))‖ := by
        simp [norm_inv]
      _ ≤ (N : ℝ)⁻¹ * ∑ n ∈ range N,
          ‖(lambda⁻¹) ^ n * (prediction P μ r n - (selectedWeight n : ℂ))‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (N : ℝ)⁻¹ * ∑ _n ∈ range N, epsilon := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_le_sum
        intro n _hn
        simpa only [norm_mul, norm_pow, norm_inv, lambda_norm_eq_one,
          inv_one, one_pow, one_mul] using hbound n
      _ = epsilon := by
        simp [sum_const, card_range, nsmul_eq_mul, hNpos.ne']
  have hle := le_of_tendsto (twisted_error_tendsto hP μ r).norm
    (by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
      exact hmean N hN)
  norm_num [norm_div] at hle ⊢
  exact hle

/-- Exact representation at every preparation depth is also impossible. -/
theorem no_exact_representation {P : Matrix S S ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ S) (μ r : S → ℂ) :
    ¬ (∀ n : ℕ, prediction P μ r n = (selectedWeight n : ℂ)) := by
  intro h
  apply no_vanishing_error hP μ r
  have hz : (fun n => prediction P μ r n - (selectedWeight n : ℂ)) =
      (fun _ : ℕ => (0 : ℂ)) := by
    funext n
    rw [h n, sub_self]
  rw [hz]
  exact tendsto_const_nhds

/-- The supplied original Law gives the same obstruction with both fixedness premises. -/
theorem rawLaw_no_vanishing_error {V Ω : Type*}
    (d : ResponseContextQuotient.Data V Ω) (v : V)
    (hz : ResponseSourceLocalProbability.DiagonalFixed d d.chosenZero)
    (hv : ResponseSourceLocalProbability.DiagonalFixed d v)
    (L : ResponseNativeProbabilitySelection.Law d v)
    {P : Matrix S S ℝ} (hP : P ∈ Matrix.rowStochastic ℝ S) (μ r : S → ℂ) :
    ¬ Tendsto (fun n => prediction P μ r n -
      (L.prob (0 : Fin 3) (repeatedWord n) 0 : ℂ)) atTop (𝓝 0) := by
  simpa only [NativeFiniteMemoryReadoutWall.rawLaw_repeatedWord_probability d v hz hv L]
    using no_vanishing_error hP μ r

end IDT.QMClosure.NativeFiniteStochasticReadoutWall
