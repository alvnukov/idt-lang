import Proofs.QMClosure.NativeVacuumProbabilityFamily
import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Tactic

/-!
# A non-Archimedean codomain boundary for native probability selection

The explicit hyperreal readout is nonnegative on every standard complex scalar
and obeys the finite native structural probability contract. An actual native
fresh-vacuum split nevertheless has a nonzero infinitesimal halving defect.
This is not an inhabitant of the existing real-valued `Law`, and it supplies no
physical probability interpretation. No finite real cutoff is asserted here.
-/

namespace IDT.QMClosure.NativeHyperrealProbabilityWall

noncomputable section
open MixerGeneratedProcessWall NativeMixerEventConeExclusion
open NativeVacuumProbabilityFamily
open scoped BigOperators
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def response (z : ℂ) : Hyperreal :=
  (1-Hyperreal.epsilon)*(Complex.normSq z : Hyperreal) +
    Hyperreal.epsilon*(z.re : Hyperreal)

@[simp] theorem response_zero : response 0 = 0 := by simp [response]
@[simp] theorem response_one : response 1 = 1 := by simp [response]

theorem response_positive (z : ℂ) (hz : z ≠ 0) : 0 < response z := by
  have hn : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  have hn' : 0 < (Complex.normSq z : Hyperreal) := by exact_mod_cast hn
  by_cases hc : 0 ≤ z.re-Complex.normSq z
  · have hc' : 0 ≤ (z.re : Hyperreal)-(Complex.normSq z : Hyperreal) := by
      exact_mod_cast hc
    have hp := mul_nonneg (le_of_lt Hyperreal.epsilon_pos) hc'
    unfold response
    nlinarith
  · have hd : 0 < Complex.normSq z-z.re := by linarith
    have hd' : 0 < (Complex.normSq z : Hyperreal)-(z.re : Hyperreal) := by
      exact_mod_cast hd
    have he := Hyperreal.epsilon_lt_of_pos (div_pos hn hd)
    have he' : Hyperreal.epsilon < (Complex.normSq z : Hyperreal) /
        ((Complex.normSq z : Hyperreal)-(z.re : Hyperreal)) := by
      simpa only [Hyperreal.coe_div, Hyperreal.coe_sub] using he
    have hp := (lt_div_iff₀ hd').mp he'
    unfold response
    nlinarith

theorem response_nonnegative (z : ℂ) : 0 ≤ response z := by
  by_cases hz : z = 0
  · subst z; simp
  · exact le_of_lt (response_positive z hz)

def probability {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (i : ι) : Hyperreal := response (c.eval (source s) i)

theorem coe_sum {ι : Type} [Fintype ι] (f : ι → ℝ) :
    ((∑ i, f i : ℝ) : Hyperreal) = ∑ i, (f i : Hyperreal) :=
  map_sum Hyperreal.coeRingHom _ _

theorem probability_nonnegative {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (i : ι) : 0 ≤ probability s c i :=
  response_nonnegative _

theorem probability_normalized {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) : ∑ i, probability s c i = 1 := by
  have hn : (∑ i, Complex.normSq (c.eval (source s) i)) = 1 := by
    simpa [totalReadout, source, single] using
      c.preserves_readout Complex.normSq mixer_conserves (source s)
  have hs : coherentSum (c.eval (source s)) = 1 := by
    simpa [source, single] using
      c.preserves_sum mixer_transparent mixer_square (source s)
  have hr : (∑ i, (c.eval (source s) i).re) = 1 := by
    simpa [coherentSum] using congrArg Complex.re hs
  have hn' : (∑ i, (Complex.normSq (c.eval (source s) i) : Hyperreal)) = 1 := by
    rw [← coe_sum, hn]; simp
  have hr' : (∑ i, ((c.eval (source s) i).re : Hyperreal)) = 1 := by
    rw [← coe_sum, hr]; simp
  simp only [probability, response, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hn', hr']
  ring

theorem probability_prepared_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c d : Native ι) (h : c.eval (source s) = d.eval (source s)) :
    probability s c = probability s d := by
  funext i
  simp only [probability, h]

theorem probability_output_perm {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (e : Equiv.Perm ι) (i : ι) :
    probability s (.seq c (.permute e)) i = probability s c (e i) := rfl

theorem probability_spectator_pair {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (i j k : ι) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) :
    probability s (.seq c (.pair i j hij)) k = probability s c k := by
  simp [probability, Circuit.eval, pairGate, pairReplace, hki, hkj]

theorem probability_vacuum {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (s : ι) (c : Native ι) (i : ι) :
    probability (.inl s) (padCircuit κ c) (.inl i) = probability s c i := by
  simp only [probability, pad_prepared]
  rfl

/-- The analogue of the six fields, with a different codomain and no real-Law claim. -/
structure HyperrealContract : Prop where
  nonnegative : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) i,
    0 ≤ probability s c i
  normalized : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι),
    ∑ i, probability s c i = 1
  prepared_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c d : Native ι),
    c.eval (source s) = d.eval (source s) → probability s c = probability s d
  output_perm : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (e : Equiv.Perm ι) i,
    probability s (.seq c (.permute e)) i = probability s c (e i)
  spectator_pair : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (i j k : ι) (hij : i ≠ j),
    k ≠ i → k ≠ j → probability s (.seq c (.pair i j hij)) k = probability s c k
  vacuum : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (s : ι) (c : Native ι) i,
    probability (.inl s) (padCircuit κ c) (.inl i) = probability s c i

theorem hyperreal_contract : HyperrealContract where
  nonnegative := probability_nonnegative
  normalized := probability_normalized
  prepared_eq := probability_prepared_eq
  output_perm := probability_output_perm
  spectator_pair := probability_spectator_pair
  vacuum := probability_vacuum

theorem probability_basis_calibration {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (j : ι) (hc : c.eval (source s) = source j) (i : ι) :
    probability s c i = if i = j then 1 else 0 := by
  unfold probability
  rw [hc]
  by_cases hi : i = j <;> simp [source, single, hi]

def witness : Native (Fin 3) :=
  .seq (.pair 0 1 (by decide)) (.pair 0 2 (by decide))

theorem witness_amplitude : witness.eval (source (0 : Fin 3)) 0 = Complex.I/2 := by
  apply Complex.ext <;>
    norm_num [witness, source, single, Circuit.eval, pairGate, pairReplace,
      Fin.ext_iff, NativeAttenuationCircuit.mixer_fst, NativeAttenuationCircuit.mixer_snd,
      NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem witness_split_amplitude :
    (split witness 0).eval (source (Sum.inl (0 : Fin 3))) (.inl 0) =
      (-1+Complex.I)/4 := by
  rw [split_retained_amplitude, witness_amplitude]
  apply Complex.ext <;>
    norm_num [NativeAttenuationCircuit.a, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im]

theorem retained_halving_defect :
    probability (Sum.inl (0 : Fin 3)) (split witness 0) (.inl 0) -
      probability (0 : Fin 3) witness 0 / 2 = -Hyperreal.epsilon/4 := by
  simp only [probability, witness_split_amplitude, witness_amplitude]
  norm_num [response, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  ring

/-- The infinitesimal defect is nonzero in the hyperreal codomain. -/
theorem native_split_not_half :
    probability (Sum.inl (0 : Fin 3)) (split witness 0) (.inl 0) ≠
      probability (0 : Fin 3) witness 0 / 2 := by
  intro h
  have hd := retained_halving_defect
  rw [h, sub_self] at hd
  exact (div_ne_zero (neg_ne_zero.mpr Hyperreal.epsilon_ne_zero)
    (by norm_num : (4 : Hyperreal) ≠ 0)) hd.symm

end
end IDT.QMClosure.NativeHyperrealProbabilityWall
