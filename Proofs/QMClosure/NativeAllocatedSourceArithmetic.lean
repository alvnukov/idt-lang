import Proofs.QMClosure.AllocatedPreparation
import Proofs.QMClosure.NativeGaussianDyadicClosure
import Mathlib.Tactic

/-!
# Scalar arithmetic with explicitly allocated source occurrences

Every repeated subprogram allocates its entire input array again. All outputs are retained. The supplied arrays share one chosen
scalar frame; their physical availability is not established. No tensor
factorization, source independence, probability-law extension to joint arrays,
actualization, optimal resource budget, or QM closure is asserted.

The construction works for the concrete complex scalar mixer. It does not
silently transfer these arithmetic macros to arbitrary raw operations.
-/

namespace IDT.QMClosure.NativeAllocatedSourceArithmetic

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open AllocatedPreparation OperationalContextQuotient
open NativeVacuumProbabilityFamily MixerGeneratedProcessWall
open NativeAttenuationCircuit (a b)

abbrev ScalarProgram := Program Unit

def value (p : ScalarProgram) : ℂ :=
  AllocatedPreparation.eval NativeMixerEventConeExclusion.mixer 0 (fun _ => 1) p

def zero : ScalarProgram := zeroProgram
def one : ScalarProgram := sourceProgram ()
def mix (p q : ScalarProgram) : ScalarProgram := pair .first p q

@[simp] theorem value_zero : value zero = 0 := rfl
@[simp] theorem value_one : value one = 1 := rfl
@[simp] theorem budget_zero : budget zero = 0 := budget_zeroProgram
@[simp] theorem budget_one : budget one = 1 := budget_sourceProgram ()

theorem value_mix (p q : ScalarProgram) :
    value (mix p q) = a * value p + b * value q := by
  unfold value mix
  rw [eval_pair]
  exact NativeAttenuationCircuit.mixer_fst _ _

@[simp] theorem budget_mix (p q : ScalarProgram) :
    budget (mix p q) = budget p + budget q := budget_pair .first p q

/-- A finite Pascal tree. Each occurrence of `p` has a disjoint input array. -/
def pascal : ℕ → ℕ → ScalarProgram → ScalarProgram
  | 0, 0, p => p
  | 0, _ + 1, _ => zero
  | n + 1, 0, p => mix zero (pascal n 0 p)
  | n + 1, k + 1, p => mix (pascal n k p) (pascal n (k + 1) p)

/-- Four depth-four leaves have three left branches and one right branch. -/
def phasePlus (p : ScalarProgram) : ScalarProgram := pascal 4 3 p

/-- Four depth-four leaves have one left branch and three right branches. -/
def phaseMinus (p : ScalarProgram) : ScalarProgram := pascal 4 1 p

theorem value_phasePlus (p : ScalarProgram) :
    value (phasePlus p) = Complex.I * value p := by
  simp only [phasePlus, pascal, value_mix, value_zero]
  apply Complex.ext <;>
    norm_num [a, b, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;>
    ring

theorem value_phaseMinus (p : ScalarProgram) :
    value (phaseMinus p) = -Complex.I * value p := by
  simp only [phaseMinus, pascal, value_mix, value_zero]
  apply Complex.ext <;>
    norm_num [a, b, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;>
    ring

@[simp] theorem budget_phasePlus (p : ScalarProgram) :
    budget (phasePlus p) = 4 * budget p := by
  simp only [phasePlus, pascal, budget_mix, budget_zero]
  omega

@[simp] theorem budget_phaseMinus (p : ScalarProgram) :
    budget (phaseMinus p) = 4 * budget p := by
  simp only [phaseMinus, pascal, budget_mix, budget_zero]
  omega

def half (p : ScalarProgram) : ScalarProgram := mix (mix zero p) zero
def negate (p : ScalarProgram) : ScalarProgram := mix (phasePlus p) (phaseMinus p)
def add (p q : ScalarProgram) : ScalarProgram :=
  mix (mix (phaseMinus p) p) (mix q (phasePlus q))

theorem value_half (p : ScalarProgram) : value (half p) = value p / 2 := by
  simp only [half, value_mix, value_zero]
  apply Complex.ext <;>
    norm_num [a, b, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;>
    ring

theorem value_negate (p : ScalarProgram) : value (negate p) = -value p := by
  simp only [negate, value_mix, value_phasePlus, value_phaseMinus]
  apply Complex.ext <;>
    norm_num [a, b, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;>
    ring

theorem value_add (p q : ScalarProgram) : value (add p q) = value p + value q := by
  simp only [add, value_mix, value_phasePlus, value_phaseMinus]
  apply Complex.ext <;>
    norm_num [a, b, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;>
    ring

@[simp] theorem budget_half (p : ScalarProgram) : budget (half p) = budget p := by
  simp [half]

@[simp] theorem budget_negate (p : ScalarProgram) :
    budget (negate p) = 8 * budget p := by
  simp only [negate, budget_mix, budget_phasePlus, budget_phaseMinus]
  omega

@[simp] theorem budget_add (p q : ScalarProgram) :
    budget (add p q) = 5 * budget p + 5 * budget q := by
  simp only [add, budget_mix, budget_phasePlus, budget_phaseMinus]
  omega

def naturalProgram : ℕ → ScalarProgram
  | 0 => zero
  | n + 1 => add (naturalProgram n) one

def naturalCost : ℕ → ℕ
  | 0 => 0
  | n + 1 => 5 * naturalCost n + 5

theorem value_naturalProgram (n : ℕ) : value (naturalProgram n) = (n : ℂ) := by
  induction n with
  | zero => simpa only [naturalProgram, Nat.cast_zero] using value_zero
  | succ n ih => simp [naturalProgram, value_add, ih, Nat.cast_add, Nat.cast_one]

theorem budget_naturalProgram (n : ℕ) : budget (naturalProgram n) = naturalCost n := by
  induction n with
  | zero => exact budget_zero
  | succ n ih => simp [naturalProgram, naturalCost, ih]

def integerProgram : ℤ → ScalarProgram
  | .ofNat n => naturalProgram n
  | .negSucc n => negate (naturalProgram (n + 1))

def integerCost : ℤ → ℕ
  | .ofNat n => naturalCost n
  | .negSucc n => 8 * naturalCost (n + 1)

theorem value_integerProgram (n : ℤ) : value (integerProgram n) = (n : ℂ) := by
  cases n with
  | ofNat n => simpa [integerProgram] using value_naturalProgram n
  | negSucc n =>
    simp only [integerProgram, value_negate, value_naturalProgram, Int.cast_negSucc]

theorem budget_integerProgram (n : ℤ) : budget (integerProgram n) = integerCost n := by
  cases n <;> simp [integerProgram, integerCost, budget_naturalProgram]

def gaussianProgram (g : GaussianInt) : ScalarProgram :=
  add (integerProgram g.re) (phasePlus (integerProgram g.im))

def gaussianCost (g : GaussianInt) : ℕ :=
  5 * integerCost g.re + 20 * integerCost g.im

theorem value_gaussianProgram (g : GaussianInt) : value (gaussianProgram g) = (g : ℂ) := by
  rw [gaussianProgram, value_add, value_phasePlus, value_integerProgram,
    value_integerProgram, GaussianInt.toComplex_def]
  ring

theorem budget_gaussianProgram (g : GaussianInt) :
    budget (gaussianProgram g) = gaussianCost g := by
  simp only [gaussianProgram, budget_add, budget_phasePlus, budget_integerProgram,
    gaussianCost]
  omega

def halfPower : ℕ → ScalarProgram → ScalarProgram
  | 0, p => p
  | k + 1, p => half (halfPower k p)

theorem value_halfPower (k : ℕ) (p : ScalarProgram) :
    value (halfPower k p) = value p / (2 : ℂ)^k := by
  induction k with
  | zero => simp [halfPower]
  | succ k ih =>
    rw [halfPower, value_half, ih, pow_succ, div_div]

@[simp] theorem budget_halfPower (k : ℕ) (p : ScalarProgram) :
    budget (halfPower k p) = budget p := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [halfPower, budget_half] using ih

def dyadicProgram (g : GaussianInt) (k : ℕ) : ScalarProgram :=
  halfPower k (gaussianProgram g)

theorem value_dyadicProgram (g : GaussianInt) (k : ℕ) :
    value (dyadicProgram g k) = (g : ℂ) / (2 : ℂ)^k := by
  rw [dyadicProgram, value_halfPower, value_gaussianProgram]

theorem budget_dyadicProgram (g : GaussianInt) (k : ℕ) :
    budget (dyadicProgram g k) = gaussianCost g := by
  rw [dyadicProgram, budget_halfPower, budget_gaussianProgram]

/-- Scalar raw/native agreement for the concrete mixer, not arbitrary raw data. -/
theorem evalRaw_eq_native {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Native ι) (x : ι → ℂ) :
    WeightFreeRawProbability.evalRaw NativeMixerEventConeExclusion.mixer c x =
      c.eval x := by
  induction c generalizing x with
  | identity => rfl
  | pair => rfl
  | permute => rfl
  | seq c d hc hd =>
    change WeightFreeRawProbability.evalRaw NativeMixerEventConeExclusion.mixer d
      (WeightFreeRawProbability.evalRaw NativeMixerEventConeExclusion.mixer c x) =
      d.eval (c.eval x)
    rw [hc, hd]

def GaussianDyadic (z : ℂ) : Prop :=
  ∃ k : ℕ, ∃ g : GaussianInt, z = (g : ℂ) / (2 : ℂ)^k

def Reachable (z : ℂ) : Prop := ∃ p : ScalarProgram, value p = z

/-- Arbitrary 0/1 input arrays satisfy the existing arithmetic residue relation. -/
theorem input_has_residue (p : ScalarProgram) (w : p.Wires) :
    ∃ r : ZMod 5, NativeDyadicSixWireObstruction.Related
      (inputState (0 : ℂ) (fun _ : Unit => (1 : ℂ)) p w) r := by
  cases hw : p.input w with
  | none =>
    refine ⟨0, ?_⟩
    simpa [inputState, hw] using NativeGaussianDyadicClosure.related_zero
  | some u =>
    refine ⟨1, ?_⟩
    simpa [inputState, hw] using NativeGaussianDyadicClosure.related_one

theorem value_gaussian_dyadic (p : ScalarProgram) : GaussianDyadic (value p) := by
  obtain ⟨r, k, g, hg, _⟩ := NativeGaussianDyadicClosure.circuit_has_residue p.circuit
    (inputState (0 : ℂ) (fun _ : Unit => (1 : ℂ)) p) (input_has_residue p) p.cursor
  refine ⟨k, g, ?_⟩
  unfold value AllocatedPreparation.eval
  rw [evalRaw_eq_native]
  exact hg

/-- Exact scalar reachability over all finite budgets, under the supplied common frame. -/
theorem reachable_iff_gaussian_dyadic (z : ℂ) : Reachable z ↔ GaussianDyadic z := by
  constructor
  · rintro ⟨p, rfl⟩
    exact value_gaussian_dyadic p
  · rintro ⟨k, g, rfl⟩
    exact ⟨dyadicProgram g k, value_dyadicProgram g k⟩

/-- A rational scalar outside the exact Gaussian-dyadic output domain. -/
theorem third_not_gaussian_dyadic : ¬ GaussianDyadic (1 / 3 : ℂ) := by
  rintro ⟨k, g, hg⟩
  have hp : (2 : ℂ)^k ≠ 0 := pow_ne_zero k (by norm_num)
  have hc := (eq_div_iff hp).mp hg
  have he : (3 : ℂ) * (g : ℂ) = (2 : ℂ)^k := by
    rw [← hc]
    ring
  have hpow : (((2 : ℤ)^k : ℤ) : ℂ) = (2 : ℂ)^k := by norm_cast
  rw [← hpow] at he
  have hre := congrArg Complex.re he
  have hi : (3 : ℤ) * g.re = (2 : ℤ)^k := by
    change (3 : ℝ) * (g : ℂ).re - 0 * (g : ℂ).im = (((2 : ℤ)^k : ℤ) : ℝ) at hre
    rw [zero_mul, sub_zero, ← GaussianInt.intCast_re] at hre
    exact_mod_cast hre
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hz : (2 : ZMod 3)^k = 0 := by
    have hcast := congrArg (fun n : ℤ => (n : ZMod 3)) hi.symm
    push_cast at hcast
    change (2 : ZMod 3)^k = (3 : ZMod 3) * (g.re : ZMod 3) at hcast
    rw [show (3 : ZMod 3) = 0 by decide, zero_mul] at hcast
    exact hcast
  exact (pow_ne_zero k (by decide : (2 : ZMod 3) ≠ 0)) hz

theorem third_not_reachable : ¬ Reachable (1 / 3 : ℂ) := by
  rw [reachable_iff_gaussian_dyadic]
  exact third_not_gaussian_dyadic

/-- A concrete selected value 2, charged as ten source occurrences. -/
def targetTwo : ScalarProgram := add one one

theorem targetTwo_value : value targetTwo = 2 := by
  norm_num [targetTwo, value_add]

theorem targetTwo_budget : budget targetTwo = 10 := by
  norm_num [targetTwo]

inductive BoundaryRole where
  | concreteScalarMixerOnly
  | everyRepeatedPreparationAllocatedAndCharged
  | allProgramOutputsRetained
  | commonFrameAndJointInputArraySupplied
  | noPhysicalAvailabilityOrNormalizationControl
  | noTensorFactorizationOrSourceIndependence
  | noExtensionOfSingleSourceProbabilityLaw
  | noOutcomeActualizationOrQMClosure
  | constructiveBudgetsNotClaimedOptimal
  deriving DecidableEq, Repr

def boundaryRoles : List BoundaryRole := [
  .concreteScalarMixerOnly,
  .everyRepeatedPreparationAllocatedAndCharged,
  .allProgramOutputsRetained,
  .commonFrameAndJointInputArraySupplied,
  .noPhysicalAvailabilityOrNormalizationControl,
  .noTensorFactorizationOrSourceIndependence,
  .noExtensionOfSingleSourceProbabilityLaw,
  .noOutcomeActualizationOrQMClosure,
  .constructiveBudgetsNotClaimedOptimal]

end
end IDT.QMClosure.NativeAllocatedSourceArithmetic
