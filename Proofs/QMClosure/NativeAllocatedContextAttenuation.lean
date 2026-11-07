import Proofs.QMClosure.NativeAllocatedObservationBoundary
import Proofs.QMClosure.NativeAttenuationCircuit
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Set.Finite.Basic

/-!
# Scalar attenuation along fixed one-hole contexts

These are literal complex scalar values in the existing allocated generated
carrier, using its supplied complex metric backend. Each context has one hole
and fixed known generated references. Its depth counts only that selected hole
path, not the total depth of a circuit in which retained companions re-enter.
The allocated recipes retain all companion wires; scalar attenuation asserts
neither global information erasure nor irreversibility.

The sequence theorems use the same input-independent contexts and references
for all compared inputs. Depth tends to infinity, rather than merely being
unbounded. Convergence at one input is a premise, not an existence conclusion.
The general affine sequence is supplied mathematical data and need not be a
sequence of reachable native contexts. Finite image means literal scalar image,
never finite decoded labels. Feedback, input-dependent stopping or decoding,
nonlinear labels, probabilities, richer observables, physical detectors,
probability provenance, actualization, and QM conclusions are outside the claim.
-/

namespace IDT.QMClosure.NativeAllocatedContextAttenuation

noncomputable section

open OperationalContextQuotient NativeAllocatedObservationBoundary
open NativeAllocatedSourceArithmetic
open NativeAttenuationCircuit (a b mixer_fst mixer_snd)
open Filter Topology

/-- Number of mixer nodes on the unique selected hole path. -/
def depth : Context G → ℕ
  | .hole => 0
  | .left _ C _ => depth C + 1
  | .right _ _ C => depth C + 1

private def firstCoefficient : Output → ℂ
  | .first => a
  | .second => b

private def secondCoefficient : Output → ℂ
  | .first => b
  | .second => a

/-- The coefficient of the unique variable input. -/
def slope : Context G → ℂ
  | .hole => 1
  | .left s C _ => firstCoefficient s * slope C
  | .right s _ C => secondCoefficient s * slope C

/-- The offset supplied by the fixed references of this context. -/
def offset : Context G → ℂ
  | .hole => 0
  | .left s C r => firstCoefficient s * offset C + secondCoefficient s * r.val
  | .right s r C => firstCoefficient s * r.val + secondCoefficient s * offset C

theorem eval_affine (C : Context G) (x : G) :
    (C.eval operationG x).val = slope C * x.val + offset C := by
  induction C with
  | hole => simp [Context.eval, slope, offset]
  | left s C r ih =>
    cases s <;>
      simp only [Context.eval, select, slope, offset, firstCoefficient, secondCoefficient]
    · change (NativeMixerEventConeExclusion.mixer ((C.eval operationG x).val, r.val)).1 = _
      rw [mixer_fst, ih]
      ring
    · change (NativeMixerEventConeExclusion.mixer ((C.eval operationG x).val, r.val)).2 = _
      rw [mixer_snd, ih]
      ring
  | right s r C ih =>
    cases s <;>
      simp only [Context.eval, select, slope, offset, firstCoefficient, secondCoefficient]
    · change (NativeMixerEventConeExclusion.mixer (r.val, (C.eval operationG x).val)).1 = _
      rw [mixer_fst, ih]
      ring
    · change (NativeMixerEventConeExclusion.mixer (r.val, (C.eval operationG x).val)).2 = _
      rw [mixer_snd, ih]
      ring

private theorem normSq_a : Complex.normSq a = (1 / 2 : ℝ) := by
  norm_num [a, Complex.normSq_apply, Complex.div_re, Complex.div_im]

private theorem normSq_b : Complex.normSq b = (1 / 2 : ℝ) := by
  norm_num [b, Complex.normSq_apply, Complex.div_re, Complex.div_im]

theorem slope_normSq (C : Context G) :
    Complex.normSq (slope C) = (1 / 2 : ℝ) ^ depth C := by
  induction C with
  | hole => simp [slope, depth]
  | left s C r ih =>
    cases s <;> simp [slope, depth, firstCoefficient, Complex.normSq_mul,
      normSq_a, normSq_b, ih, pow_succ, mul_comm]
  | right s r C ih =>
    cases s <;> simp [slope, depth, secondCoefficient, Complex.normSq_mul,
      normSq_a, normSq_b, ih, pow_succ, mul_comm]

theorem eval_sub (C : Context G) (x y : G) :
    (C.eval operationG x).val - (C.eval operationG y).val =
      slope C * (x.val - y.val) := by
  rw [eval_affine, eval_affine]
  ring

/-- Exact squared norm attenuation, with no probability interpretation. -/
theorem eval_sub_normSq (C : Context G) (x y : G) :
    Complex.normSq ((C.eval operationG x).val - (C.eval operationG y).val) =
      (1 / 2 : ℝ) ^ depth C * Complex.normSq (x.val - y.val) := by
  rw [eval_sub, Complex.normSq_mul, slope_normSq]

theorem slope_ne_zero (C : Context G) : slope C ≠ 0 := by
  have hn : Complex.normSq (slope C) ≠ 0 := by
    rw [slope_normSq]
    exact pow_ne_zero _ (by norm_num)
  intro h
  exact hn (by rw [h]; simp)

theorem eval_injective (C : Context G) : Function.Injective (C.eval operationG) := by
  intro x y h
  apply Subtype.ext
  have hz : slope C * (x.val - y.val) = 0 := by
    rw [← eval_sub, h, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (slope_ne_zero C))

/-- One shared context sequence forgets scalar differences along its selected
path when that path depth tends to infinity. No limit existence is asserted. -/
theorem eval_sub_tendsto_zero (C : ℕ → Context G)
    (hdepth : Tendsto (fun n => depth (C n)) atTop atTop) (x y : G) :
    Tendsto (fun n => (C n |>.eval operationG x).val -
      (C n |>.eval operationG y).val) atTop (𝓝 0) := by
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).comp hdepth
  have hs : Tendsto (fun n => Complex.normSq
      ((C n |>.eval operationG x).val - (C n |>.eval operationG y).val))
      atTop (𝓝 0) := by
    simpa only [eval_sub_normSq, zero_mul] using hp.mul_const (Complex.normSq (x.val-y.val))
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [dist_eq_norm, sub_zero, Complex.norm_def, Real.sqrt_zero] using hs.sqrt

/-- A scalar limit at one input is the same scalar limit at every input. -/
theorem eval_tendsto_of_one (C : ℕ → Context G)
    (hdepth : Tendsto (fun n => depth (C n)) atTop atTop)
    (x y : G) (L : ℂ)
    (hx : Tendsto (fun n => (C n |>.eval operationG x).val) atTop (𝓝 L)) :
    Tendsto (fun n => (C n |>.eval operationG y).val) atTop (𝓝 L) := by
  have h := (eval_sub_tendsto_zero C hdepth y x).add hx
  simpa only [sub_add_cancel, zero_add] using h

/-- Supplied complex affine data, with no native reachability assertion. -/
def scalarAffine (c d : ℂ) (x : G) : ℂ := c * x.val + d

theorem affine_tendsto_of_zero_unit (c d : ℕ → ℂ) (l0 l1 : ℂ)
    (h0 : Tendsto (fun n => scalarAffine (c n) (d n) zeroG) atTop (𝓝 l0))
    (h1 : Tendsto (fun n => scalarAffine (c n) (d n) unitG) atTop (𝓝 l1))
    (x : G) :
    Tendsto (fun n => scalarAffine (c n) (d n) x) atTop
      (𝓝 ((l1 - l0) * x.val + l0)) := by
  have hd : Tendsto d atTop (𝓝 l0) := by
    simpa only [scalarAffine, val_zeroG, mul_zero, zero_add] using h0
  have hc : Tendsto c atTop (𝓝 (l1 - l0)) := by
    simpa only [scalarAffine, val_unitG, val_zeroG, mul_one, mul_zero,
      zero_add, add_sub_cancel_right] using h1.sub h0
  exact (hc.mul_const x.val).add hd

private def naturalEmbedding (n : ℕ) : G := ofProgram (naturalProgram n)

private theorem naturalEmbedding_injective : Function.Injective naturalEmbedding := by
  intro m n h
  have hv := congrArg Subtype.val h
  change value (naturalProgram m) = value (naturalProgram n) at hv
  rw [value_naturalProgram, value_naturalProgram] at hv
  exact_mod_cast hv

local instance : Infinite G := Infinite.of_injective naturalEmbedding naturalEmbedding_injective

/-- Finite image refers to exact complex scalar values, not decoded labels. -/
theorem affine_finite_range_iff (c d : ℂ) :
    (Set.range (scalarAffine c d)).Finite ↔ c = 0 := by
  constructor
  · intro hf
    by_contra hc
    have hi : Function.Injective (scalarAffine c d) := by
      intro x y h
      apply Subtype.ext
      exact mul_left_cancel₀ hc (add_right_cancel h)
    exact (Set.infinite_range_of_injective hi).not_finite hf
  · rintro rfl
    change (Set.range (fun x : G => (0 : ℂ) * x.val + d)).Finite
    simpa only [zero_mul, zero_add] using
      (Set.finite_range_const (c := d) (α := G))

theorem affine_limit_finite_range_iff (l0 l1 : ℂ) :
    (Set.range (fun x : G => (l1 - l0) * x.val + l0)).Finite ↔ l1 = l0 := by
  exact (affine_finite_range_iff (l1 - l0) l0).trans sub_eq_zero

end
end IDT.QMClosure.NativeAllocatedContextAttenuation
