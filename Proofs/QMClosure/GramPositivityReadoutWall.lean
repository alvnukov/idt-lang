import Mathlib

namespace IDT.QMClosure.GramPositivityReadoutWall

/-!
# Finite Gram positivity without coherent-addition preservation

Complex numbers are a supplied countermodel carrier, not a reconstruction from
IDT primitives. The nonlinear power map is multiplicative and dagger compatible.
Every finite kernel quadratic form factors as the squared norm of an explicitly
weighted power sum. Nevertheless its quartic self-response has equal-unit I3=36.

This is finite Gram-kernel positivity, not full linear reflection positivity:
the usual linear-functional assumption is deliberately absent. Evaluation also
respects equalities of underlying closed scalars (the limited cut statement);
no law interchanging evaluation with coherent sums follows from this.
No physical model, operational accessibility, Born rule, or QM closure is proved.
-/

open scoped BigOperators

noncomputable section

def powerEvaluation (k : ℕ) (z : ℂ) : ℂ := z ^ k

theorem power_evaluation_mul (k : ℕ) (u v : ℂ) :
    powerEvaluation k (u * v) = powerEvaluation k u * powerEvaluation k v := by
  simp [powerEvaluation, mul_pow]

theorem power_evaluation_one (k : ℕ) : powerEvaluation k 1 = 1 := by
  simp [powerEvaluation]

theorem power_evaluation_zero (k : ℕ) (hk : 0 < k) :
    powerEvaluation k 0 = 0 := by
  simp [powerEvaluation, Nat.ne_of_gt hk]

theorem power_evaluation_dagger (k : ℕ) (z : ℂ) :
    powerEvaluation k (star z) = star (powerEvaluation k z) := by
  simp [powerEvaluation]

def gramKernel (k : ℕ) (u v : ℂ) : ℂ := star (u ^ k) * v ^ k

theorem gram_kernel_as_evaluated_scalar (k : ℕ) (u v : ℂ) :
    gramKernel k u v = powerEvaluation k (star u * v) := by
  simp [gramKernel, powerEvaluation, mul_pow, star_pow]

theorem gram_kernel_dagger (k : ℕ) (u v : ℂ) :
    star (gramKernel k u v) = gramKernel k v u := by
  simp [gramKernel, star_mul]

/-- An actual finite double-sum identity for arbitrary complex coefficients. -/
theorem finite_gram_quadratic_form {ι : Type} (s : Finset ι)
    (k : ℕ) (u a : ι → ℂ) :
    (∑ i ∈ s, ∑ j ∈ s, star (a i) * gramKernel k (u i) (u j) * a j) =
      star (∑ i ∈ s, a i * u i ^ k) * (∑ j ∈ s, a j * u j ^ k) := by
  rw [star_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [gramKernel, star_mul]
  ring

theorem star_mul_self_real (z : ℂ) : (star z * z).re = Complex.normSq z := by
  simp [Complex.mul_re, Complex.normSq_apply]

theorem finite_gram_real_normSq {ι : Type} (s : Finset ι)
    (k : ℕ) (u a : ι → ℂ) :
    (∑ i ∈ s, ∑ j ∈ s, star (a i) * gramKernel k (u i) (u j) * a j).re =
      Complex.normSq (∑ i ∈ s, a i * u i ^ k) := by
  rw [finite_gram_quadratic_form, star_mul_self_real]

theorem finite_gram_positive {ι : Type} (s : Finset ι)
    (k : ℕ) (u a : ι → ℂ) :
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (a i) * gramKernel k (u i) (u j) * a j).re := by
  rw [finite_gram_real_normSq]
  exact Complex.normSq_nonneg _

def selfResponse (k : ℕ) (z : ℂ) : ℝ := (gramKernel k z z).re

theorem self_response_power (k : ℕ) (z : ℂ) :
    selfResponse k z = Complex.normSq z ^ k := by
  unfold selfResponse gramKernel
  rw [star_mul_self_real]
  exact map_pow Complex.normSq z k

theorem quadratic_self_response (z : ℂ) : selfResponse 1 z = Complex.normSq z := by
  simp [self_response_power]

theorem quartic_self_response (z : ℂ) :
    selfResponse 2 z = Complex.normSq z ^ 2 :=
  self_response_power 2 z

theorem quartic_evaluation_not_additive :
    powerEvaluation 2 ((1 : ℂ) + 1) = 4 ∧
    powerEvaluation 2 (1 : ℂ) + powerEvaluation 2 1 = 2 ∧
    powerEvaluation 2 ((1 : ℂ) + 1) ≠
      powerEvaluation 2 (1 : ℂ) + powerEvaluation 2 1 := by
  norm_num [powerEvaluation]

def equalUnitI3 (response : ℂ → ℝ) : ℝ :=
  response (1 + 1 + 1) - response (1 + 1) - response (1 + 1) -
    response (1 + 1) + response 1 + response 1 + response 1 - response 0

theorem quadratic_equal_unit_i3 : equalUnitI3 (selfResponse 1) = 0 := by
  norm_num [equalUnitI3, self_response_power]

theorem quartic_equal_unit_i3 : equalUnitI3 (selfResponse 2) = 36 := by
  norm_num [equalUnitI3, self_response_power]

/-- Cut only for supplied underlying scalar equality; no sum-interchange law. -/
theorem equal_closed_scalar_evaluation (k : ℕ) {u v : ℂ} (h : u = v) :
    powerEvaluation k u = powerEvaluation k v :=
  congrArg (powerEvaluation k) h

/-- Data-only scope ledger: these are additional obligations, not derived laws. -/
inductive OpenObligation where
  | deriveCarrierFromPrimitiveBase
  | deriveCoherentSumEvaluationLaw
  | derivePhysicalScalarReadoutCoupling
  | justifyLinearFunctionalAssumption
  | deriveOperationalAccessibility
  deriving DecidableEq, Repr

def openObligations : List OpenObligation :=
  [.deriveCarrierFromPrimitiveBase, .deriveCoherentSumEvaluationLaw,
    .derivePhysicalScalarReadoutCoupling, .justifyLinearFunctionalAssumption,
    .deriveOperationalAccessibility]

end

end IDT.QMClosure.GramPositivityReadoutWall
