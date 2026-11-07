import Proofs.QMClosure.NativeAllocatedSourceArithmetic
import Proofs.QMClosure.AllocatedGeneratedContexts
import Mathlib.Data.Real.Archimedean
import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Gaussian-dyadic density for exact finite scalar preparations

Ordinary complex arithmetic, norm, and topology are
supplied here. Integer floor approximations on a common power-of-two grid prove
that Gaussian-dyadic scalars are dense in this topology. The checked exact
dyadic preparation compiler then supplies a finite allocated program for each
requested approximation. Approximation does not assert exact reachability of
an arbitrary complex scalar.

This establishes no derivation of topology, probability law, physical gate or
source availability, efficiency, uniform resource ceiling, tensor structure,
source independence, outcome actualization, or QM closure. Allocation and
retained-output semantics are those of the existing exact scalar compiler;
joint availability in a common scalar frame remains supplied separately.
-/

namespace IDT.QMClosure.NativeGaussianDyadicDensity

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open NativeAllocatedSourceArithmetic
open NativeMixerEventConeExclusion (mixer)

/-- The finite Gaussian numerator obtained by flooring both scaled coordinates. -/
def floorGaussian (k : ℕ) (z : ℂ) : GaussianInt :=
  ⟨⌊(2 : ℝ)^k * z.re⌋, ⌊(2 : ℝ)^k * z.im⌋⟩

theorem gaussian_div_pow_re (g : GaussianInt) (k : ℕ) :
    ((g : ℂ) / (2 : ℂ)^k).re = (g.re : ℝ) / (2 : ℝ)^k := by
  have hden : (2 : ℂ)^k = (((2 : ℝ)^k : ℝ) : ℂ) := by norm_cast
  rw [hden, Complex.div_ofReal_re, ← GaussianInt.intCast_re]

theorem gaussian_div_pow_im (g : GaussianInt) (k : ℕ) :
    ((g : ℂ) / (2 : ℂ)^k).im = (g.im : ℝ) / (2 : ℝ)^k := by
  have hden : (2 : ℂ)^k = (((2 : ℝ)^k : ℝ) : ℂ) := by norm_cast
  rw [hden, Complex.div_ofReal_im, ← GaussianInt.intCast_im]

/-- The scaled floor gives a one-sided coordinate error smaller than one grid step. -/
theorem floor_coordinate_error (k : ℕ) (x : ℝ) :
    0 ≤ x - ((⌊(2 : ℝ)^k * x⌋ : ℤ) : ℝ) / (2 : ℝ)^k ∧
    x - ((⌊(2 : ℝ)^k * x⌋ : ℤ) : ℝ) / (2 : ℝ)^k < 1 / (2 : ℝ)^k := by
  have hp : 0 < (2 : ℝ)^k := pow_pos (by norm_num) k
  have hlo := Int.floor_le ((2 : ℝ)^k * x)
  have hhi := Int.lt_floor_add_one ((2 : ℝ)^k * x)
  have heq : x - ((⌊(2 : ℝ)^k * x⌋ : ℤ) : ℝ) / (2 : ℝ)^k =
      ((2 : ℝ)^k * x - ((⌊(2 : ℝ)^k * x⌋ : ℤ) : ℝ)) / (2 : ℝ)^k := by
    field_simp [ne_of_gt hp]
  rw [heq]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlo) hp.le
  · exact div_lt_div_of_pos_right (by linarith) hp

/-- A quantitative bound for the concrete common-denominator numerator. -/
theorem floorGaussian_error (k : ℕ) (z : ℂ) :
    ‖z - (floorGaussian k z : ℂ) / (2 : ℂ)^k‖ < 2 / (2 : ℝ)^k := by
  have hr := floor_coordinate_error k z.re
  have hi := floor_coordinate_error k z.im
  have hr0 : 0 ≤ (z - (floorGaussian k z : ℂ) / (2 : ℂ)^k).re := by
    rw [Complex.sub_re, gaussian_div_pow_re]
    exact hr.1
  have hi0 : 0 ≤ (z - (floorGaussian k z : ℂ) / (2 : ℂ)^k).im := by
    rw [Complex.sub_im, gaussian_div_pow_im]
    exact hi.1
  have hr1 : (z - (floorGaussian k z : ℂ) / (2 : ℂ)^k).re < 1 / (2 : ℝ)^k := by
    rw [Complex.sub_re, gaussian_div_pow_re]
    exact hr.2
  have hi1 : (z - (floorGaussian k z : ℂ) / (2 : ℂ)^k).im < 1 / (2 : ℝ)^k := by
    rw [Complex.sub_im, gaussian_div_pow_im]
    exact hi.2
  apply (Complex.norm_le_abs_re_add_abs_im _).trans_lt
  rw [abs_of_nonneg hr0, abs_of_nonneg hi0]
  calc
    _ < 1 / (2 : ℝ)^k + 1 / (2 : ℝ)^k := add_lt_add hr1 hi1
    _ = 2 / (2 : ℝ)^k := by ring

/-- Explicit Gaussian numerators and a shared dyadic denominator approximate every scalar. -/
theorem exists_gaussian_dyadic_approx (z : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∃ g : GaussianInt, ‖z - (g : ℂ) / (2 : ℂ)^k‖ < ε := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (1 / 2 : ℝ)^k < ε / 2 :=
    exists_pow_lt_of_lt_one (by linarith) (by norm_num)
  have hk' : 1 / (2 : ℝ)^k < ε / 2 := by
    simpa only [div_pow, one_pow] using hk
  have hbound : 2 / (2 : ℝ)^k < ε := by
    calc
      2 / (2 : ℝ)^k = 2 * (1 / (2 : ℝ)^k) := by ring
      _ < ε := by linarith
  exact ⟨k, floorGaussian k z, (floorGaussian_error k z).trans hbound⟩

theorem gaussian_dyadic_dense : Dense {z : ℂ | GaussianDyadic z} := by
  intro z
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨k, g, hg⟩ := exists_gaussian_dyadic_approx z ε hε
  refine ⟨(g : ℂ) / (2 : ℂ)^k, ⟨k, g, rfl⟩, ?_⟩
  simpa only [dist_eq_norm] using hg

/-- This carrier is definitionally the existing point-observation module's G. -/
theorem generated_coe_denseRange :
    DenseRange (fun x : AllocatedGeneratedContexts.G mixer (0 : ℂ)
      (fun _ : Unit => (1 : ℂ)) => x.val) := by
  apply Metric.denseRange_iff.mpr
  intro z ε hε
  obtain ⟨k, g, hg⟩ := exists_gaussian_dyadic_approx z ε hε
  refine ⟨AllocatedGeneratedContexts.value mixer 0 (fun _ : Unit => (1 : ℂ))
    (dyadicProgram g k), ?_⟩
  change dist z (value (dyadicProgram g k)) < ε
  rw [value_dyadicProgram, dist_eq_norm]
  exact hg

/-- Each approximation has one exact finite allocated-program witness. -/
theorem exists_program_approx (z : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ScalarProgram, ‖value p - z‖ < ε := by
  obtain ⟨k, g, hg⟩ := exists_gaussian_dyadic_approx z ε hε
  refine ⟨dyadicProgram g k, ?_⟩
  rw [value_dyadicProgram, norm_sub_rev]
  exact hg

inductive BoundaryRole where
  | ordinaryComplexTopologyExplicitlySupplied
  | floorProofWithSharedPowerOfTwoDenominator
  | actualGaussianDyadicDensityNotArbitraryRationalSubstitution
  | exactFiniteAllocatedProgramForEachApproximation
  | approximationDoesNotAssertExactReachability
  | noProbabilityLawOrTopologyDerivation
  | noEfficiencyOrUniformResourceCeiling
  | retainedOutputsAndSuppliedCommonFrame
  | noPhysicalSourceOrGateAvailability
  | noTensorIndependenceActualizationOrQMClosure
  deriving DecidableEq, Repr

def boundaryRoles : List BoundaryRole := [
  .ordinaryComplexTopologyExplicitlySupplied,
  .floorProofWithSharedPowerOfTwoDenominator,
  .actualGaussianDyadicDensityNotArbitraryRationalSubstitution,
  .exactFiniteAllocatedProgramForEachApproximation,
  .approximationDoesNotAssertExactReachability,
  .noProbabilityLawOrTopologyDerivation,
  .noEfficiencyOrUniformResourceCeiling,
  .retainedOutputsAndSuppliedCommonFrame,
  .noPhysicalSourceOrGateAvailability,
  .noTensorIndependenceActualizationOrQMClosure]

end
end IDT.QMClosure.NativeGaussianDyadicDensity
