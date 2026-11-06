import Proofs.QMClosure.NativeWireEffectSpan
import Proofs.QMClosure.NativeAttenuationReadout

/-!
# Finite native attenuation with retained ancillary wires

These are literal words in the supplied normalized-mixer circuit grammar.
Every ancillary port begins at zero and remains in the output. Selected-port
squared norms are algebraic readouts, with no probability, physical availability,
reset, discard, postselection, or full-QM conclusion.
-/

namespace IDT.QMClosure.NativeAttenuationCircuit

noncomputable section
open scoped BigOperators
open MixerGeneratedProcessWall

def a : ℂ := (1 + Complex.I) / 2
def b : ℂ := (1 - Complex.I) / 2

theorem mixer_fst (z w : ℂ) :
    (NativeMixerEventConeExclusion.mixer (z, w)).1 = a * z + b * w := by
  apply Complex.ext <;>
    norm_num [NativeMixerEventConeExclusion.mixer, NativeMixerEventConeExclusion.Raw,
      CompositeProductControls.RawSign.N, CompositeProductControls.RawSign.n_re,
      CompositeProductControls.RawSign.n_im, a, b, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im] <;> ring

theorem mixer_snd (z w : ℂ) :
    (NativeMixerEventConeExclusion.mixer (z, w)).2 = b * z + a * w := by
  apply Complex.ext <;>
    norm_num [NativeMixerEventConeExclusion.mixer, NativeMixerEventConeExclusion.Raw,
      CompositeProductControls.RawSign.N, CompositeProductControls.RawSign.n_re,
      CompositeProductControls.RawSign.n_im, a, b, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im] <;> ring

abbrev Wire (n k : ℕ) := Fin n ⊕ Fin k
abbrev NativeCircuit (n k : ℕ) :=
  Circuit (ι := Wire n k) NativeMixerEventConeExclusion.mixer

def input {n k : ℕ} (x : Fin n → ℂ) : Wire n k → ℂ :=
  Sum.elim x (fun _ => 0)

def gateIA {n k : ℕ} (i : Fin n) (l : Fin k) : NativeCircuit n k :=
  .pair (.inl i) (.inr l) (by simp)

def gateIJ {n k : ℕ} (q : NativeWireEffectSpan.UpperPair n) : NativeCircuit n k :=
  .pair (.inl q.val.1) (.inl q.val.2) (by simpa using ne_of_lt q.property)

/-- Guarded recursion is defined for every length; the action theorem uses r≤k. -/
def attenuationPrefix {n k : ℕ} (i : Fin n) : ℕ → NativeCircuit n k
  | 0 => .identity
  | r + 1 => .seq (attenuationPrefix i r)
      (if h : r < k then gateIA i ⟨r, h⟩ else .identity)

/-- Complete state: no environment coordinate is removed or silently cleared. -/
def state {n k : ℕ} (x : Fin n → ℂ) (i : Fin n) (r : ℕ) : Wire n k → ℂ
  | .inl j => if j = i then a ^ r * x i else x j
  | .inr l => if l.val < r then b * a ^ l.val * x i else 0

theorem state_zero {n k : ℕ} (x : Fin n → ℂ) (i : Fin n) :
    state (k := k) x i 0 = input x := by
  funext w
  cases w with
  | inl j => by_cases h : j = i <;> simp [state, input, h]
  | inr l => simp [state, input]

theorem state_step {n k : ℕ} (x : Fin n → ℂ) (i : Fin n) (r : ℕ)
    (h : r < k) :
    (gateIA i ⟨r, h⟩).eval (state x i r) = state x i (r + 1) := by
  funext w
  cases w with
  | inl j =>
      by_cases hj : j = i
      · subst j
        simp [gateIA, Circuit.eval, pairGate, pairReplace, state, mixer_fst,
          pow_succ, mul_comm, mul_left_comm]
      · simp [gateIA, Circuit.eval, pairGate, pairReplace, state, hj]
  | inr l =>
      by_cases hl : l = ⟨r, h⟩
      · subst l
        simp [gateIA, Circuit.eval, pairGate, pairReplace, state, mixer_snd, mul_assoc]
      · have hne : l.val ≠ r := fun hv => hl (Fin.ext hv)
        have hiff : l.val < r + 1 ↔ l.val < r := by omega
        simp [gateIA, Circuit.eval, pairGate, pairReplace, state, hl, hiff]

theorem prefix_eval {n k : ℕ} (x : Fin n → ℂ) (i : Fin n) (r : ℕ)
    (h : r ≤ k) : (attenuationPrefix (k := k) i r).eval (input x) = state x i r := by
  induction r with
  | zero => simpa [attenuationPrefix, Circuit.eval] using (state_zero (k := k) x i).symm
  | succ r ih =>
      have hr : r < k := by omega
      simpa [attenuationPrefix, hr, Circuit.eval, ih (by omega)] using state_step x i r hr

theorem prefix_retained {n k : ℕ} (x : Fin n → ℂ) (i : Fin n) :
    (attenuationPrefix (k := k) i k).eval (input x) (.inl i) = a ^ k * x i := by
  rw [prefix_eval x i k (by omega)]
  simp [state]

theorem prefix_other_data {n k : ℕ} (x : Fin n → ℂ) (i j : Fin n)
    (hij : j ≠ i) :
    (attenuationPrefix (k := k) i k).eval (input x) (.inl j) = x j := by
  rw [prefix_eval x i k (by omega)]
  simp [state, hij]

theorem prefix_leak {n k : ℕ} (x : Fin n → ℂ) (i : Fin n) (l : Fin k) :
    (attenuationPrefix (k := k) i k).eval (input x) (.inr l) = b * a ^ l.val * x i := by
  rw [prefix_eval x i k (by omega)]
  simp [state, l.isLt]

theorem prefix_unused {n k : ℕ} (x : Fin n → ℂ) (i : Fin n)
    (r : ℕ) (hr : r ≤ k) (l : Fin k) (hl : r ≤ l.val) :
    (attenuationPrefix (k := k) i r).eval (input x) (.inr l) = 0 := by
  rw [prefix_eval x i r hr]
  simp [state, Nat.not_lt.mpr hl]

def selectedCircuit {n : ℕ} (q : NativeWireEffectSpan.UpperPair n)
    (k : ℕ) : NativeCircuit n k := .seq (attenuationPrefix q.val.1 k) (gateIJ q)

theorem selected_action {n : ℕ} (q : NativeWireEffectSpan.UpperPair n)
    (k : ℕ) (x : Fin n → ℂ) :
    (selectedCircuit q k).eval (input x) (.inl q.val.2) =
      b * a ^ k * x q.val.1 + a * x q.val.2 := by
  have hij : q.val.2 ≠ q.val.1 := (ne_of_lt q.property).symm
  simp [selectedCircuit, gateIJ, Circuit.eval, pairGate, pairReplace, hij,
    mixer_snd, prefix_retained, prefix_other_data x _ _ hij, mul_assoc]

theorem all_port_resolution {n k : ℕ} (c : NativeCircuit n k) (x : Fin n → ℂ) :
    ∑ w, Complex.normSq (c.eval (input x) w) = ∑ i, Complex.normSq (x i) := by
  have h := c.preserves_readout Complex.normSq
    NativeMixerEventConeExclusion.mixer_conserves (input x)
  simpa [totalReadout, input, Fintype.sum_sum_type] using h

theorem a_square : a ^ 2 = Complex.I / 2 := by
  apply Complex.ext <;>
    norm_num [a, pow_two, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im]

theorem a_fourth : a ^ 4 = -(1 / 4 : ℂ) := by
  calc
    a ^ 4 = (a ^ 2) ^ 2 := by ring
    _ = -(1 / 4 : ℂ) := by rw [a_square, div_pow]; norm_num [Complex.I_sq]

theorem a_eighth : a ^ 8 = (1 / 16 : ℂ) := by
  calc
    a ^ 8 = (a ^ 4) ^ 2 := by ring
    _ = (1 / 16 : ℂ) := by rw [a_fourth]; norm_num

theorem a_sixth : a ^ 6 = -Complex.I / 8 := by
  calc
    a ^ 6 = a ^ 4 * a ^ 2 := by ring
    _ = -Complex.I / 8 := by rw [a_fourth, a_square]; ring

theorem a_pow_eight_mul (m : ℕ) :
    a ^ (8 * m) = (NativeAttenuationReadout.t m : ℂ) := by
  rw [pow_mul, a_eighth]
  norm_num [NativeAttenuationReadout.t]

private theorem quadratic_sub {n : ℕ} (v w : NativeWireEffectSpan.V n)
    (x : Fin n → ℂ) :
    NativeWireEffectSpan.quadratic (v - w) x =
      NativeWireEffectSpan.quadratic v x - NativeWireEffectSpan.quadratic w x := by
  simp [NativeWireEffectSpan.quadratic, sub_mul, Finset.sum_sub_distrib]

open NativeWireEffectSpan NativeAttenuationReadout

/-- All four identities are universal in the complex input, at exact finite lengths. -/
theorem selected_E0 {n : ℕ} (q : UpperPair n) (m : ℕ) (x : Fin n → ℂ) :
    quadratic (E0 q m) x =
      Complex.normSq ((selectedCircuit q (8 * m)).eval (input x) (.inl q.val.2)) := by
  rw [selected_action, a_pow_eight_mul, E0, quadratic_add, quadratic_add,
    quadratic_smul, quadratic_smul, quadratic_smul, quadratic_P, quadratic_P,
    Y, quadratic_single]
  norm_num [atom, a, b, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]
  ring

theorem selected_E2 {n : ℕ} (q : UpperPair n) (m : ℕ) (x : Fin n → ℂ) :
    quadratic (E2 q m) x =
      Complex.normSq ((selectedCircuit q (8 * m + 2)).eval (input x) (.inl q.val.2)) := by
  rw [selected_action, pow_add, a_pow_eight_mul, a_square, E2,
    quadratic_add, quadratic_add, quadratic_smul, quadratic_smul, quadratic_smul,
    quadratic_P, quadratic_P, X, quadratic_single]
  norm_num [atom, a, b, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]
  ring

theorem selected_E4 {n : ℕ} (q : UpperPair n) (m : ℕ) (x : Fin n → ℂ) :
    quadratic (E4 q m) x =
      Complex.normSq ((selectedCircuit q (8 * m + 4)).eval (input x) (.inl q.val.2)) := by
  rw [selected_action, pow_add, a_pow_eight_mul, a_fourth, E4,
    quadratic_sub, quadratic_add, quadratic_smul, quadratic_smul, quadratic_smul,
    quadratic_P, quadratic_P, Y, quadratic_single]
  norm_num [atom, a, b, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]
  ring

theorem selected_E6 {n : ℕ} (q : UpperPair n) (m : ℕ) (x : Fin n → ℂ) :
    quadratic (E6 q m) x =
      Complex.normSq ((selectedCircuit q (8 * m + 6)).eval (input x) (.inl q.val.2)) := by
  rw [selected_action, pow_add, a_pow_eight_mul, a_sixth, E6,
    quadratic_sub, quadratic_add, quadratic_smul, quadratic_smul, quadratic_smul,
    quadratic_P, quadratic_P, X, quadratic_single]
  norm_num [atom, a, b, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]
  ring

end
end IDT.QMClosure.NativeAttenuationCircuit
