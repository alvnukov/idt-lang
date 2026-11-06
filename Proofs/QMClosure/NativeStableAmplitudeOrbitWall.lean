import Proofs.QMClosure.NativeDyadicSixWireObstruction
import Mathlib.Tactic

/-!
# Equal selected amplitudes do not imply stable spectator connectivity

Two explicit five-gate native three-wire preparations have the same amplitude
at output zero. Their other two amplitudes have different arithmetic content:
reduction modulo `2+i`, implemented by `i ↦ 3` in `ZMod 5`, annihilates both
spectators of the first preparation but not the first spectator of the second.

Actual native gates on the spectator wires preserve the all-zero residue
property. Adding any finite number of zero vacuum spectators does not remove
the obstruction. This rejects one proposed orbit-connectivity proof of scalar
amplitude sufficiency. It does not assert that any probability law distinguishes
these preparations, and it does not prove or refute Born or full QM closure.
-/

namespace IDT.QMClosure.NativeStableAmplitudeOrbitWall

noncomputable section

open scoped BigOperators
open MixerGeneratedProcessWall
open NativeMixerEventConeExclusion
open NativeDyadicSixWireObstruction
  (Related rho related_add related_mul related_a related_b)

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-! ## A functional residue relation on Gaussian dyadic scalars -/

/-- Only Gaussian dyadic presentations are compared. No residue map on all
complex numbers is introduced. -/
theorem related_functional {z : ℂ} {r s : ZMod 5}
    (hr : Related z r) (hs : Related z s) : r = s := by
  obtain ⟨k, g, hzg, hgr⟩ := hr
  obtain ⟨l, h, hzh, hhs⟩ := hs
  have hc : (g : ℂ) * (2 : ℂ) ^ l = (h : ℂ) * (2 : ℂ) ^ k :=
    (div_eq_div_iff (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (by norm_num))).mp (hzg.symm.trans hzh)
  have hg : g * (2 : GaussianInt) ^ l = h * (2 : GaussianInt) ^ k := by
    apply GaussianInt.toComplex_injective
    simpa only [map_mul, map_pow, map_ofNat] using hc
  have hmod : rho g * (2 : ZMod 5) ^ l = rho h * (2 : ZMod 5) ^ k := by
    simpa only [map_mul, map_pow, map_ofNat] using congrArg rho hg
  have hk : (2 : ZMod 5) ^ k ≠ 0 := pow_ne_zero _ (by decide)
  have hl : (2 : ZMod 5) ^ l ≠ 0 := pow_ne_zero _ (by decide)
  apply mul_right_cancel₀ (mul_ne_zero hk hl)
  calc
    r * ((2 : ZMod 5) ^ k * (2 : ZMod 5) ^ l) =
        rho g * (2 : ZMod 5) ^ l := by rw [hgr]; ring
    _ = rho h * (2 : ZMod 5) ^ k := hmod
    _ = s * ((2 : ZMod 5) ^ k * (2 : ZMod 5) ^ l) := by rw [hhs]; ring

theorem related_zero : Related (0 : ℂ) (0 : ZMod 5) := by
  exact ⟨0, 0, by simp, by simp⟩

theorem mixer_preserves_zero {z w : ℂ}
    (hz : Related z 0) (hw : Related w 0) :
    Related (mixer (z, w)).1 0 ∧ Related (mixer (z, w)).2 0 := by
  rw [NativeAttenuationCircuit.mixer_fst, NativeAttenuationCircuit.mixer_snd]
  constructor
  · simpa using related_add (related_mul related_a hz) (related_mul related_b hw)
  · simpa using related_add (related_mul related_b hz) (related_mul related_a hw)

def AllZeroResidue {ι : Type*} (x : ι → ℂ) : Prop := ∀ j, Related (x j) 0

/-- Every constructor is the actual native circuit constructor. -/
theorem circuit_preserves_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Circuit (ι := ι) mixer) (x : ι → ℂ) (hx : AllZeroResidue x) :
    AllZeroResidue (c.eval x) := by
  induction c generalizing x with
  | identity => exact hx
  | pair i j hij =>
      intro k
      have hm := mixer_preserves_zero (hx i) (hx j)
      by_cases hki : k = i
      · simpa [Circuit.eval, pairGate, pairReplace, hki] using hm.1
      · by_cases hkj : k = j
        · simpa [Circuit.eval, pairGate, pairReplace, hki, hkj, Ne.symm hij] using hm.2
        · simpa [Circuit.eval, pairGate, pairReplace, hki, hkj] using hx k
  | permute e => exact fun k => hx (e k)
  | seq c d hc hd => exact hd (c.eval x) (hc x hx)

/-! ## Two exact native preparations with the same selected amplitude -/

def source : Fin 3 → ℂ := Pi.single 0 1

def u : Fin 3 → ℂ :=
  ![-(1 : ℂ) / 4, (7 + Complex.I) / 8, (3 - Complex.I) / 8]

def v : Fin 3 → ℂ :=
  ![-(1 : ℂ) / 4, (7 - Complex.I) / 8, (3 + Complex.I) / 8]

/-- Chronological word `(01,02,12,02,12)`. -/
def prepareU : NativeCircuit :=
  .seq (.seq (.seq (.seq gate01 gate02) gate12) gate02) gate12

/-- Chronological word `(02,12,02,01,12)`. -/
def prepareV : NativeCircuit :=
  .seq (.seq (.seq (.seq gate02 gate12) gate02) gate01) gate12

theorem prepareU_eval : prepareU.eval source = u := by
  funext j
  fin_cases j <;> apply Complex.ext <;>
    norm_num [prepareU, source, u, gate01, gate02, gate12, Circuit.eval,
      pairGate, pairReplace, Pi.single_apply, mixer, Raw,
      CompositeProductControls.RawSign.N, CompositeProductControls.RawSign.n_re,
      CompositeProductControls.RawSign.n_im, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Fin.ext_iff, Matrix.cons_val_two]

theorem prepareV_eval : prepareV.eval source = v := by
  funext j
  fin_cases j <;> apply Complex.ext <;>
    norm_num [prepareV, source, v, gate01, gate02, gate12, Circuit.eval,
      pairGate, pairReplace, Pi.single_apply, mixer, Raw,
      CompositeProductControls.RawSign.N, CompositeProductControls.RawSign.n_re,
      CompositeProductControls.RawSign.n_im, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Fin.ext_iff, Matrix.cons_val_two]

theorem equal_selected_amplitude : u 0 = v 0 := rfl

theorem prepared_selected_amplitude_equal :
    prepareU.eval source 0 = prepareV.eval source 0 := by
  rw [prepareU_eval, prepareV_eval]
  exact equal_selected_amplitude

theorem u_sum : coherentSum u = 1 := by
  norm_num [coherentSum, u, Fin.sum_univ_succ]; ring

theorem v_sum : coherentSum v = 1 := by
  norm_num [coherentSum, v, Fin.sum_univ_succ]; ring

theorem u_norm : totalReadout Complex.normSq u = 1 := by
  norm_num [totalReadout, u, Fin.sum_univ_succ, Complex.normSq_apply,
    Complex.div_re, Complex.div_im]

theorem v_norm : totalReadout Complex.normSq v = 1 := by
  norm_num [totalReadout, v, Fin.sum_univ_succ, Complex.normSq_apply,
    Complex.div_re, Complex.div_im]

/-! ## The obstruction survives every finite zero-vacuum extension -/

/-- The two unselected outputs, followed by `n` fresh zero spectators. -/
def paddedSpectators (n : ℕ) (x : Fin 3 → ℂ) : Fin 2 ⊕ Fin n → ℂ
  | .inl j => ![x 1, x 2] j
  | .inr _ => 0

theorem u_spectators_zero_residue (n : ℕ) :
    AllZeroResidue (paddedSpectators n u) := by
  intro j
  cases j with
  | inl j =>
      fin_cases j
      · refine ⟨3, ⟨7, 1⟩, ?_, ?_⟩
        · norm_num [paddedSpectators, u, GaussianInt.toComplex_def']
        · decide
      · refine ⟨3, ⟨3, -1⟩, ?_, ?_⟩
        · change (3 - Complex.I) / 8 = ((⟨3, -1⟩ : GaussianInt) : ℂ) / (2 : ℂ) ^ 3
          norm_num [GaussianInt.toComplex_def', sub_eq_add_neg]
        · decide
  | inr j => simpa [paddedSpectators] using related_zero

theorem v_first_spectator_related_three : Related (v 1) 3 := by
  refine ⟨3, ⟨7, -1⟩, ?_, ?_⟩
  · norm_num [v, GaussianInt.toComplex_def', sub_eq_add_neg]
  · decide

theorem v_spectators_not_zero_residue (n : ℕ) :
    ¬ AllZeroResidue (paddedSpectators n v) := by
  intro h
  have hz : Related (v 1) 0 := by
    simpa [paddedSpectators] using h (Sum.inl (0 : Fin 2))
  have he : (0 : ZMod 5) = 3 :=
    related_functional hz v_first_spectator_related_three
  exact (by decide : (0 : ZMod 5) ≠ 3) he

/-- No actual spectator circuit connects the preparations, even after any
finite number of zero vacuum wires have been added. -/
theorem no_stable_spectator_connection (n : ℕ)
    (c : Circuit (ι := Fin 2 ⊕ Fin n) mixer) :
    c.eval (paddedSpectators n u) ≠ paddedSpectators n v := by
  intro he
  have hz := circuit_preserves_zero c (paddedSpectators n u)
    (u_spectators_zero_residue n)
  rw [he] at hz
  exact v_spectators_not_zero_residue n hz

/-- Native inverses show that the reverse connection is also impossible. -/
theorem no_reverse_stable_spectator_connection (n : ℕ)
    (c : Circuit (ι := Fin 2 ⊕ Fin n) mixer) :
    c.eval (paddedSpectators n v) ≠ paddedSpectators n u := by
  intro he
  have hback :
      (NativeDyadicSixWireObstruction.inverseCircuit c).eval
        (paddedSpectators n u) = paddedSpectators n v := by
    rw [← he, NativeDyadicSixWireObstruction.inverseCircuit_eval]
  exact no_stable_spectator_connection n
    (NativeDyadicSixWireObstruction.inverseCircuit c) hback

/-- Actual preparations, exact selected-amplitude equality, legal sum/norm,
and the universal finite-padding orbit wall. No probability conclusion occurs. -/
theorem stable_amplitude_orbit_wall :
    prepareU.eval source = u ∧ prepareV.eval source = v ∧ u 0 = v 0 ∧
    coherentSum u = 1 ∧ coherentSum v = 1 ∧
    totalReadout Complex.normSq u = 1 ∧ totalReadout Complex.normSq v = 1 ∧
    ∀ n : ℕ, ∀ c : Circuit (ι := Fin 2 ⊕ Fin n) mixer,
      c.eval (paddedSpectators n u) ≠ paddedSpectators n v :=
  ⟨prepareU_eval, prepareV_eval, equal_selected_amplitude,
    u_sum, v_sum, u_norm, v_norm, no_stable_spectator_connection⟩

end

end IDT.QMClosure.NativeStableAmplitudeOrbitWall
