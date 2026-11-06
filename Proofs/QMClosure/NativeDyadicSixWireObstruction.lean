import Proofs.QMClosure.NativeAttenuationCircuit
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Data.ZMod.Basic

/-!
# A six-coordinate arithmetic obstruction for actual native circuits

The displayed dyadic Gaussian vector has coherent sum one and quadratic norm
one. Nevertheless no word in the actual normalized mixer, permutations,
identity, and composition sends it to a standard basis vector. Reduction
modulo five sends every input coordinate to one, an invariant of these gates.

This disproves unrestricted vector synthesis from sum and norm alone. It does
not decide synthesis of dyadic unitary matrices fixing ones. No general-width
minimality, physical availability, probability rule, or QM closure is asserted
here.
-/

namespace IDT.QMClosure.NativeDyadicSixWireObstruction

noncomputable section
open scoped BigOperators
open MixerGeneratedProcessWall

abbrev G := GaussianInt
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
abbrev NativeCircuit := Circuit (ι := Fin 6) NativeMixerEventConeExclusion.mixer

/-- The Gaussian residue map sending `i` to `3` modulo five. -/
def rho : G →+* ZMod 5 := Zsqrtd.lift ⟨3, by decide⟩

theorem rho_apply (u : G) : rho u = (u.re : ZMod 5) + u.im * 3 := rfl

/-- A dyadic Gaussian scalar and its certified modulo-five residue.
This is a relation on actual complex scalars, not a new circuit syntax. -/
def Related (z : ℂ) (r : ZMod 5) : Prop :=
  ∃ k : ℕ, ∃ u : G, z = (u : ℂ) / (2 : ℂ) ^ k ∧
    rho u = r * (2 : ZMod 5) ^ k

private theorem cast_two_pow (k : ℕ) : ((2 ^ k : G) : ℂ) = (2 : ℂ) ^ k := by
  have htwo : GaussianInt.toComplex (2 : G) = (2 : ℂ) := by
    norm_num [GaussianInt.toComplex_def]
  change GaussianInt.toComplex (2 ^ k) = _
  rw [map_pow, htwo]

theorem related_add {z w : ℂ} {r s : ZMod 5}
    (hz : Related z r) (hw : Related w s) : Related (z + w) (r + s) := by
  obtain ⟨k, u, hu, hr⟩ := hz
  obtain ⟨l, v, hv, hs⟩ := hw
  refine ⟨k + l, u * 2 ^ l + v * 2 ^ k, ?_, ?_⟩
  · rw [GaussianInt.toComplex_add, GaussianInt.toComplex_mul,
      GaussianInt.toComplex_mul, cast_two_pow, cast_two_pow, hu, hv, pow_add]
    field_simp
  · simp only [map_add, map_mul, map_pow, map_ofNat, hr, hs, pow_add]
    ring

theorem related_mul {z w : ℂ} {r s : ZMod 5}
    (hz : Related z r) (hw : Related w s) : Related (z * w) (r * s) := by
  obtain ⟨k, u, hu, hr⟩ := hz
  obtain ⟨l, v, hv, hs⟩ := hw
  refine ⟨k + l, u * v, ?_, ?_⟩
  · rw [GaussianInt.toComplex_mul, hu, hv, pow_add]
    field_simp
  · simp only [map_mul, hr, hs, pow_add]
    ring

theorem zero_not_related_one : ¬ Related 0 1 := by
  rintro ⟨k, u, hu, hr⟩
  have hc : (u : ℂ) = 0 := by
    have h := (eq_div_iff (pow_ne_zero k (by norm_num : (2 : ℂ) ≠ 0))).mp hu
    simpa using h.symm
  have hg : u = 0 := GaussianInt.toComplex_eq_zero.mp hc
  subst u
  have hp : (2 : ZMod 5) ^ k ≠ 0 := pow_ne_zero k (by decide)
  exact hp (by simpa using hr.symm)

theorem related_a : Related NativeAttenuationCircuit.a 2 := by
  refine ⟨1, ⟨1, 1⟩, ?_, ?_⟩
  · norm_num [NativeAttenuationCircuit.a, GaussianInt.toComplex_def']
  · decide

theorem related_b : Related NativeAttenuationCircuit.b 4 := by
  refine ⟨1, ⟨1, -1⟩, ?_, ?_⟩
  · norm_num [NativeAttenuationCircuit.b, GaussianInt.toComplex_def', sub_eq_add_neg]
  · decide

theorem mixer_preserves_one {z w : ℂ} (hz : Related z 1) (hw : Related w 1) :
    Related (NativeMixerEventConeExclusion.mixer (z, w)).1 1 ∧
    Related (NativeMixerEventConeExclusion.mixer (z, w)).2 1 := by
  rw [NativeAttenuationCircuit.mixer_fst, NativeAttenuationCircuit.mixer_snd]
  constructor
  · have h := related_add (related_mul related_a hz) (related_mul related_b hw)
    have he : (2 : ZMod 5) * 1 + 4 * 1 = 1 := by decide
    exact he ▸ h
  · have h := related_add (related_mul related_b hz) (related_mul related_a hw)
    have he : (4 : ZMod 5) * 1 + 2 * 1 = 1 := by decide
    exact he ▸ h

def AllOneResidue {ι : Type*} (v : ι → ℂ) : Prop := ∀ j, Related (v j) 1

theorem circuit_preserves_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Circuit (ι := ι) NativeMixerEventConeExclusion.mixer)
    (v : ι → ℂ) (hv : AllOneResidue v) : AllOneResidue (c.eval v) := by
  induction c generalizing v with
  | identity => exact hv
  | pair i j hij =>
      intro k
      have hm := mixer_preserves_one (hv i) (hv j)
      by_cases hki : k = i
      · simpa [Circuit.eval, pairGate, pairReplace, hki] using hm.1
      · by_cases hkj : k = j
        · simpa [Circuit.eval, pairGate, pairReplace, hki, hkj, Ne.symm hij] using hm.2
        · simpa [Circuit.eval, pairGate, pairReplace, hki, hkj] using hv k
  | permute e => exact fun k => hv (e k)
  | seq c d hc hd => exact hd (c.eval v) (hc v hv)

/-- Four copies of `(1+i)/4`, followed by two copies of `-i/2`. -/
def counterexample (j : Fin 6) : ℂ :=
  if j.val < 4 then (1 + Complex.I) / 4 else -Complex.I / 2

theorem counterexample_sum : coherentSum counterexample = 1 := by
  norm_num [coherentSum, counterexample, Fin.sum_univ_succ]
  ring

theorem counterexample_norm : totalReadout Complex.normSq counterexample = 1 := by
  norm_num [totalReadout, counterexample, Fin.sum_univ_succ,
    Complex.normSq_apply, Complex.div_re, Complex.div_im]

theorem counterexample_all_one : AllOneResidue counterexample := by
  intro j
  by_cases hj : j.val < 4
  · refine ⟨2, ⟨1, 1⟩, ?_, ?_⟩
    · norm_num [counterexample, hj, GaussianInt.toComplex_def']
    · decide
  · refine ⟨1, ⟨0, -1⟩, ?_, ?_⟩
    · norm_num [counterexample, hj, GaussianInt.toComplex_def']
    · decide

theorem basis_not_all_one (s : Fin 6) : ¬ AllOneResidue (single s (1 : ℂ)) := by
  intro h
  by_cases hs : s = 0
  · have hslot := h 1
    have hzero : Related 0 1 := by simpa [single, hs] using hslot
    exact zero_not_related_one hzero
  · have hslot := h 0
    have hzero : Related 0 1 := by simpa [single, Ne.symm hs] using hslot
    exact zero_not_related_one hzero

/-- Actual native syntax, not an abstract invariant-certified substitute. -/
theorem no_native_reduction (c : NativeCircuit) (s : Fin 6) :
    c.eval counterexample ≠ single s (1 : ℂ) := by
  intro h
  have hr := circuit_preserves_one c counterexample counterexample_all_one
  rw [h] at hr
  exact basis_not_all_one s hr

private theorem pair_fourth {ι : Type*} [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) (v : ι → ℂ) :
    let p := pairGate NativeMixerEventConeExclusion.mixer i j
    p (p (p (p v))) = v := by
  dsimp only
  have hm : NativeMixerEventConeExclusion.mixer
      (NativeMixerEventConeExclusion.mixer
        (NativeMixerEventConeExclusion.mixer
          (NativeMixerEventConeExclusion.mixer (v i, v j)))) = (v i, v j) := by
    rw [NativeMixerEventConeExclusion.mixer_square,
      NativeMixerEventConeExclusion.mixer_square]
    rfl
  funext k
  by_cases hki : k = i
  · subst k
    simpa [pairGate, pairReplace, hij, Ne.symm hij] using congrArg Prod.fst hm
  · by_cases hkj : k = j
    · subst k
      simpa [pairGate, pairReplace, hij, Ne.symm hij] using congrArg Prod.snd hm
    · simp [pairGate, pairReplace, hki, hkj]

/-- Inverses remain finite words in the same native generators. -/
def inverseCircuit {ι : Type*} :
    Circuit (ι := ι) NativeMixerEventConeExclusion.mixer →
      Circuit (ι := ι) NativeMixerEventConeExclusion.mixer
  | .identity => .identity
  | .pair i j h => .seq (.seq (.pair i j h) (.pair i j h)) (.pair i j h)
  | .permute e => .permute e.symm
  | .seq c d => .seq (inverseCircuit d) (inverseCircuit c)

theorem inverseCircuit_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Circuit (ι := ι) NativeMixerEventConeExclusion.mixer) (v : ι → ℂ) :
    (inverseCircuit c).eval (c.eval v) = v := by
  induction c generalizing v with
  | identity => rfl
  | pair i j hij =>
      simpa [inverseCircuit, Circuit.eval] using pair_fourth i j hij v
  | permute e =>
      funext k
      simp [inverseCircuit, Circuit.eval]
  | seq c d hc hd =>
      change (inverseCircuit c).eval ((inverseCircuit d).eval (d.eval (c.eval v))) = v
      rw [hd, hc]

theorem no_native_preparation (c : NativeCircuit) (s : Fin 6) :
    c.eval (single s (1 : ℂ)) ≠ counterexample := by
  intro h
  apply no_native_reduction (inverseCircuit c) s
  rw [← h, inverseCircuit_eval]

/-- The exact legal-vector countermodel, with both circuit directions checked. -/
theorem six_wire_vector_obstruction :
    coherentSum counterexample = 1 ∧
    totalReadout Complex.normSq counterexample = 1 ∧
    (∀ c : NativeCircuit, ∀ s : Fin 6, c.eval counterexample ≠ single s (1 : ℂ)) ∧
    (∀ c : NativeCircuit, ∀ s : Fin 6, c.eval (single s (1 : ℂ)) ≠ counterexample) :=
  ⟨counterexample_sum, counterexample_norm, no_native_reduction, no_native_preparation⟩

end
end IDT.QMClosure.NativeDyadicSixWireObstruction
