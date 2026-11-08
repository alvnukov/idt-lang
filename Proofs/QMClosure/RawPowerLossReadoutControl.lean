import Proofs.QMClosure.NativeVacuumProbabilityFamily
import Proofs.QMClosure.NativeContextualProbabilityControl
import Proofs.QMClosure.RawSparseQuarticControl
import Mathlib.Algebra.BigOperators.Option

/-!
# Power-response readout with a global no-port-record outcome

This mathematical control supplies complex arrays and the existing native mixer.
The conserved quadratic resource sets one exposure for the complete array.
For every positive integer exponent, the port responses and a global residual
form a normalized nonnegative distribution on `Option ι`. The `none` outcome
is one exhaustive no-port-record event. It is not an additional circuit wire.

For exponents greater than one, an actual native vacuum split changes the
residual. Conditioning on a port record also changes the selected spectator's
probability on the existing three-wire basis orbit. These facts separate
unconditional spectator locality from its click-conditioned version.

The resource, complex domain, and response family are supplied mathematical
data. No primitive derivation, physical availability, continuity at vacuum,
actualization, Bell statement, rational FDQ envelope, or full-QM result follows.
-/

namespace IDT.QMClosure.RawPowerLossReadoutControl

noncomputable section
open scoped BigOperators
open MixerGeneratedProcessWall

variable {ι κ : Type} [Fintype ι]

def weight (k : ℕ) (z : ℂ) : ℝ := Complex.normSq z ^ k

def energy (x : ι → ℂ) : ℝ := ∑ i, Complex.normSq (x i)

def exposure (k : ℕ) (x : ι → ℂ) : ℝ := energy x ^ k

def port (k : ℕ) (x : ι → ℂ) (i : ι) : ℝ := weight k (x i) / exposure k x

def residual (k : ℕ) (x : ι → ℂ) : ℝ := 1 - ∑ i, port k x i

def probability (k : ℕ) (x : ι → ℂ) : Option ι → ℝ
  | none => residual k x
  | some i => port k x i

theorem energy_nonneg (x : ι → ℂ) : 0 ≤ energy x :=
  Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

theorem coordinate_energy_le (x : ι → ℂ) (i : ι) :
    Complex.normSq (x i) ≤ energy x :=
  Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Complex.normSq_nonneg (x j))
    (Finset.mem_univ i)

theorem weight_nonneg (k : ℕ) (z : ℂ) : 0 ≤ weight k z :=
  pow_nonneg (Complex.normSq_nonneg _) _

theorem port_nonneg (k : ℕ) (x : ι → ℂ) (i : ι) : 0 ≤ port k x i :=
  div_nonneg (weight_nonneg _ _) (pow_nonneg (energy_nonneg _) _)

theorem port_ratio (k : ℕ) (x : ι → ℂ) (i : ι) :
    port k x i = (Complex.normSq (x i) / energy x) ^ k := by
  simp only [port, weight, exposure, div_pow]

private theorem power_le_self {t : ℝ} (ht : 0 ≤ t) (hu : t ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) : t ^ k ≤ t := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 1 + (n + 1) = (1 + n) + 1 by omega, pow_succ]
      calc
        t ^ (1 + n) * t ≤ t * t := mul_le_mul_of_nonneg_right (ih (by omega)) ht
        _ ≤ 1 * t := mul_le_mul_of_nonneg_right hu ht
        _ = t := one_mul t

theorem zero_energy_coordinate (x : ι → ℂ) (he : energy x = 0) (i : ι) :
    Complex.normSq (x i) = 0 :=
  le_antisymm (by simpa [he] using coordinate_energy_le x i) (Complex.normSq_nonneg _)

theorem zero_energy_port (k : ℕ) (hk : 1 ≤ k) (x : ι → ℂ)
    (he : energy x = 0) (i : ι) : port k x i = 0 := by
  simp [port, weight, exposure, he, zero_energy_coordinate x he i, Nat.ne_of_gt hk]

theorem port_sum_le_one (k : ℕ) (hk : 1 ≤ k) (x : ι → ℂ) :
    ∑ i, port k x i ≤ 1 := by
  by_cases he : energy x = 0
  · simp [zero_energy_port k hk x he]
  · have hpos : 0 < energy x := lt_of_le_of_ne (energy_nonneg x) (Ne.symm he)
    calc
      ∑ i, port k x i ≤ ∑ i, Complex.normSq (x i) / energy x := by
        apply Finset.sum_le_sum
        intro i _
        rw [port_ratio]
        exact power_le_self (div_nonneg (Complex.normSq_nonneg _) (energy_nonneg x))
          ((div_le_one hpos).2 (coordinate_energy_le x i)) k hk
      _ = 1 := by rw [← Finset.sum_div]; exact div_self he

theorem residual_nonneg (k : ℕ) (hk : 1 ≤ k) (x : ι → ℂ) :
    0 ≤ residual k x := sub_nonneg.mpr (port_sum_le_one k hk x)

theorem probability_nonneg (k : ℕ) (hk : 1 ≤ k) (x : ι → ℂ) (o : Option ι) :
    0 ≤ probability k x o := by
  cases o with
  | none => exact residual_nonneg k hk x
  | some i => exact port_nonneg k x i

theorem probability_sum (k : ℕ) (x : ι → ℂ) :
    probability k x none + ∑ i, probability k x (some i) = 1 := by
  simp only [probability, residual]
  ring

theorem probability_sum_all_outcomes (k : ℕ) (x : ι → ℂ) :
    ∑ o : Option ι, probability k x o = 1 := by
  simpa only [Fintype.sum_option] using probability_sum k x

theorem probability_le_one (k : ℕ) (hk : 1 ≤ k) (x : ι → ℂ) (o : Option ι) :
    probability k x o ≤ 1 := by
  classical
  have h := Finset.single_le_sum
    (fun a (_ : a ∈ Finset.univ) => probability_nonneg k hk x a) (Finset.mem_univ o)
  simpa only [probability_sum_all_outcomes] using h

theorem zero_energy_residual (k : ℕ) (hk : 1 ≤ k) (x : ι → ℂ)
    (he : energy x = 0) : residual k x = 1 := by
  simp [residual, zero_energy_port k hk x he]

theorem common_local_response (k : ℕ) (x : ι → ℂ) (i : ι) :
    port k x i = weight k (x i) / energy x ^ k := rfl

theorem prepared_array_consistency (k : ℕ) (x y : ι → ℂ) (hxy : x = y) :
    probability k x = probability k y := congrArg (probability k) hxy

theorem energy_permutation (x : ι → ℂ) (e : Equiv.Perm ι) :
    energy (fun i => x (e i)) = energy x := by
  exact Equiv.sum_comp e (fun i => Complex.normSq (x i))

theorem port_permutation (k : ℕ) (x : ι → ℂ) (e : Equiv.Perm ι) (i : ι) :
    port k (fun j => x (e j)) i = port k x (e i) := by
  simp only [port, exposure, energy_permutation]

theorem residual_permutation (k : ℕ) (x : ι → ℂ) (e : Equiv.Perm ι) :
    residual k (fun i => x (e i)) = residual k x := by
  unfold residual
  simp only [port_permutation]
  rw [Equiv.sum_comp e]

theorem probability_permutation (k : ℕ) (x : ι → ℂ) (e : Equiv.Perm ι)
    (o : Option ι) :
    probability k (fun i => x (e i)) o = probability k x (o.map e) := by
  cases o with
  | none => exact residual_permutation k x e
  | some i => exact port_permutation k x e i

variable [Fintype κ]

theorem energy_padding (x : ι → ℂ) :
    energy (NativeVacuumProbabilityFamily.padState (κ := κ) x) = energy x := by
  simp [energy, NativeVacuumProbabilityFamily.padState, Fintype.sum_sum_type]

theorem port_padding_old (k : ℕ) (x : ι → ℂ) (i : ι) :
    port k (NativeVacuumProbabilityFamily.padState (κ := κ) x) (.inl i) = port k x i := by
  unfold port exposure
  rw [energy_padding]
  rfl

theorem port_padding_new (k : ℕ) (hk : 1 ≤ k) (x : ι → ℂ) (j : κ) :
    port k (NativeVacuumProbabilityFamily.padState x) (.inr j) = 0 := by
  simp [port, weight, NativeVacuumProbabilityFamily.padState, Nat.ne_of_gt hk]

theorem residual_padding (k : ℕ) (hk : 1 ≤ k) (x : ι → ℂ) :
    residual k (NativeVacuumProbabilityFamily.padState (κ := κ) x) = residual k x := by
  simp only [residual, Fintype.sum_sum_type, port_padding_old, port_padding_new k hk,
    Finset.sum_const_zero, add_zero]

variable [DecidableEq ι]

abbrev Native (ι : Type) := NativeVacuumProbabilityFamily.Native ι

theorem native_energy (c : Native ι) (x : ι → ℂ) : energy (c.eval x) = energy x :=
  c.preserves_readout Complex.normSq NativeMixerEventConeExclusion.mixer_conserves x

theorem native_exposure (k : ℕ) (c : Native ι) (x : ι → ℂ) :
    exposure k (c.eval x) = exposure k x := by rw [exposure, exposure, native_energy]

omit [Fintype ι] in
theorem native_spectator_coordinate (x : ι → ℂ) (i j r : ι) (hij : i ≠ j)
    (hri : r ≠ i) (hrj : r ≠ j) : (.pair i j hij : Native ι).eval x r = x r := by
  simp [Circuit.eval, pairGate, pairReplace, hri, hrj]

theorem native_spectator_port (k : ℕ) (x : ι → ℂ) (i j r : ι) (hij : i ≠ j)
    (hri : r ≠ i) (hrj : r ≠ j) :
    port k ((.pair i j hij : Native ι).eval x) r = port k x r := by
  simp only [port, native_exposure, native_spectator_coordinate x i j r hij hri hrj]

def circuitProbability (k : ℕ) (s : ι) (c : Native ι) : Option ι → ℝ :=
  probability k (c.eval (NativeVacuumProbabilityFamily.source s))

theorem circuit_prepared_consistency (k : ℕ) (s : ι) (c d : Native ι)
    (h : c.eval (NativeVacuumProbabilityFamily.source s) =
      d.eval (NativeVacuumProbabilityFamily.source s)) :
    circuitProbability k s c = circuitProbability k s d := congrArg (probability k) h

theorem circuit_output_permutation (k : ℕ) (s : ι) (c : Native ι)
    (e : Equiv.Perm ι) (o : Option ι) :
    circuitProbability k s (.seq c (.permute e)) o =
      circuitProbability k s c (o.map e) := probability_permutation k _ e o

theorem circuit_spectator (k : ℕ) (s : ι) (c : Native ι)
    (i j r : ι) (hij : i ≠ j) (hri : r ≠ i) (hrj : r ≠ j) :
    circuitProbability k s (.seq c (.pair i j hij)) (some r) =
      circuitProbability k s c (some r) :=
  native_spectator_port k _ i j r hij hri hrj

theorem circuit_vacuum_old [DecidableEq κ] (k : ℕ) (s i : ι) (c : Native ι) :
    circuitProbability k (.inl s) (NativeVacuumProbabilityFamily.padCircuit κ c)
      (some (.inl i)) = circuitProbability k s c (some i) := by
  unfold circuitProbability
  rw [NativeVacuumProbabilityFamily.pad_prepared]
  exact port_padding_old k _ i

theorem circuit_vacuum_new [DecidableEq κ] (k : ℕ) (hk : 1 ≤ k)
    (s : ι) (c : Native ι) (j : κ) :
    circuitProbability k (.inl s) (NativeVacuumProbabilityFamily.padCircuit κ c)
      (some (.inr j)) = 0 := by
  unfold circuitProbability
  rw [NativeVacuumProbabilityFamily.pad_prepared]
  exact port_padding_new k hk _ j

theorem circuit_vacuum_residual [DecidableEq κ] (k : ℕ) (hk : 1 ≤ k)
    (s : ι) (c : Native ι) :
    circuitProbability k (.inl s) (NativeVacuumProbabilityFamily.padCircuit κ c) none =
      circuitProbability k s c none := by
  unfold circuitProbability
  rw [NativeVacuumProbabilityFamily.pad_prepared]
  exact residual_padding k hk _

theorem basis_port (k : ℕ) (hk : 1 ≤ k) (s i : ι) (z : ℂ) (hz : z ≠ 0) :
    port k (single s z) i = if i = s then 1 else 0 := by
  have hn : Complex.normSq z ≠ 0 := fun h => hz (Complex.normSq_eq_zero.mp h)
  have he : energy (single s z) = Complex.normSq z := by
    simp [energy, single, apply_ite]
  by_cases hi : i = s
  · subst i
    simp [port, weight, exposure, he, single, pow_ne_zero _ hn]
  · simp [port, weight, exposure, single, hi, Nat.ne_of_gt hk]

theorem basis_residual (k : ℕ) (hk : 1 ≤ k) (s : ι) (z : ℂ) (hz : z ≠ 0) :
    residual k (single s z) = 0 := by
  simp [residual, basis_port k hk s _ z hz]

theorem basis_calibration (k : ℕ) (hk : 1 ≤ k) (s : ι) (z : ℂ) (hz : z ≠ 0)
    (o : Option ι) : probability k (single s z) o = if o = some s then 1 else 0 := by
  cases o with
  | none => simp only [probability, basis_residual k hk s z hz]; simp
  | some i => simpa only [probability, Option.some.injEq] using basis_port k hk s i z hz

/-- The deficit is exactly the change of the global residual at fixed exposure. -/
theorem residual_defect (B S Lin Lout Win Wout : ℝ) (hB : 0 < B)
    (hin : Win / B + S + Lin = 1) (hout : Wout / B + S + Lout = 1) :
    Wout - Win = B * (Lin - Lout) := by
  have hd : Wout / B - Win / B = Lin - Lout := by linarith
  have hm := congrArg (fun z : ℝ => z * B) hd
  field_simp [ne_of_gt hB] at hm
  nlinarith

theorem conservation_iff_residual_invariant (B S Lin Lout Win Wout : ℝ) (hB : 0 < B)
    (hin : Win / B + S + Lin = 1) (hout : Wout / B + S + Lout = 1) :
    Wout = Win ↔ Lin = Lout := by
  have hd := residual_defect B S Lin Lout Win Wout hB hin hout
  constructor
  · intro he
    rw [he, sub_self] at hd
    have hz : Lin - Lout = 0 := (mul_eq_zero.mp hd.symm).resolve_left (ne_of_gt hB)
    linarith
  · intro he
    rw [he, sub_self, mul_zero] at hd
    linarith

/-- Conditional on any port record. It is a different statistic from `port`. -/
def clickConditional (k : ℕ) (x : ι → ℂ) (i : ι) : ℝ :=
  port k x i / (∑ j, port k x j)

omit [DecidableEq ι] in
theorem clickConditional_weights (k : ℕ) (x : ι → ℂ)
    (he : energy x ≠ 0) (i : ι) :
    clickConditional k x i = weight k (x i) / (∑ j, weight k (x j)) := by
  simp only [clickConditional, port, ← Finset.sum_div]
  exact div_div_div_cancel_right₀ (pow_ne_zero k he) _ _

private theorem half_power_pos (k : ℕ) : 0 < (1 / 2 : ℝ) ^ k :=
  pow_pos (by norm_num) _

private theorem half_power_lt_half (k : ℕ) (hk : 1 < k) :
    (1 / 2 : ℝ) ^ k < 1 / 2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ k by omega)
  have hn := power_le_self (t := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    (1 + n) (by omega)
  have hp : (1 / 2 : ℝ) ^ (2 + n) ≤ 1 / 4 := by
    rw [show 2 + n = (1 + n) + 1 by omega, pow_succ]
    nlinarith
  linarith

abbrev before : Native (Fin 3) := NativeContextualProbabilityControl.witnessBefore
abbrev after : Native (Fin 3) := NativeContextualProbabilityControl.witnessAfter
abbrev basis : Fin 3 → ℂ := NativeContextualProbabilityControl.source 0

theorem before_is_native_split : before = NativeMixerEventConeExclusion.gate01 := rfl

theorem after_is_native_spectator_pair :
    after = .seq before NativeMixerEventConeExclusion.gate12 := rfl

theorem native_witness_spectator_amplitude : after.eval basis 0 = before.eval basis 0 :=
  NativeContextualProbabilityControl.selected_amplitude_equal basis

theorem native_witness_energy_before : energy (before.eval basis) = 1 :=
  NativeContextualProbabilityControl.circuit_output_normalized 0 before

theorem native_witness_energy_after : energy (after.eval basis) = 1 :=
  NativeContextualProbabilityControl.circuit_output_normalized 0 after

theorem native_witness_weights_before (k : ℕ) (hk : 1 ≤ k) :
    (fun i => weight k (before.eval basis i)) =
      ![(1 / 2 : ℝ) ^ k, (1 / 2 : ℝ) ^ k, 0] := by
  funext i
  have h := congrFun NativeContextualProbabilityControl.witness_before_weights i
  change Complex.normSq (before.eval basis i) = _ at h
  simp only [weight, h]
  fin_cases i <;> simp [Nat.ne_of_gt hk]

theorem native_witness_weights_after (k : ℕ) :
    (fun i => weight k (after.eval basis i)) =
      ![(1 / 2 : ℝ) ^ k, (1 / 4 : ℝ) ^ k, (1 / 4 : ℝ) ^ k] := by
  funext i
  have h := congrFun NativeContextualProbabilityControl.witness_after_weights i
  change Complex.normSq (after.eval basis i) = _ at h
  simp only [weight, h]
  fin_cases i <;> rfl

theorem native_split_total_weight_before (k : ℕ) (hk : 1 ≤ k) :
    ∑ i, weight k (basis i) = 1 := by
  norm_num [basis, NativeContextualProbabilityControl.source, single, weight,
    Fin.sum_univ_succ, Nat.ne_of_gt hk]

theorem native_split_total_weight_after (k : ℕ) (hk : 1 ≤ k) :
    ∑ i, weight k (before.eval basis i) = 2 * (1 / 2 : ℝ) ^ k := by
  rw [native_witness_weights_before k hk]
  simp [Fin.sum_univ_succ]
  ring

theorem native_split_residual_before (k : ℕ) (hk : 1 ≤ k) : residual k basis = 0 :=
  basis_residual k hk 0 1 (by norm_num)

theorem native_split_residual_after (k : ℕ) (hk : 1 ≤ k) :
    residual k (before.eval basis) = 1 - 2 * (1 / 2 : ℝ) ^ k := by
  simp only [residual, port, exposure, native_witness_energy_before, one_pow, div_one]
  rw [native_split_total_weight_after k hk]

theorem native_split_residual_zero_iff (k : ℕ) (hk : 1 ≤ k) :
    residual k (before.eval basis) = 0 ↔ k = 1 := by
  rw [native_split_residual_after k hk]
  constructor
  · intro h
    by_contra hn
    have hp := half_power_lt_half k (by omega)
    linarith
  · rintro rfl
    norm_num

theorem native_split_residual_invariant_iff (k : ℕ) (hk : 1 ≤ k) :
    residual k (before.eval basis) = residual k basis ↔ k = 1 := by
  rw [native_split_residual_before k hk]
  exact native_split_residual_zero_iff k hk

theorem native_split_pair_weight_after (k : ℕ) :
    weight k (NativeMixerEventConeExclusion.mixer (1, 0)).1 +
      weight k (NativeMixerEventConeExclusion.mixer (1, 0)).2 =
      2 * (1 / 2 : ℝ) ^ k := by
  have ha : Complex.normSq (NativeMixerEventConeExclusion.mixer (1, 0)).1 = 1 / 2 := by
    rw [NativeAttenuationCircuit.mixer_fst]
    norm_num [NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
      Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have hb : Complex.normSq (NativeMixerEventConeExclusion.mixer (1, 0)).2 = 1 / 2 := by
    rw [NativeAttenuationCircuit.mixer_snd]
    norm_num [NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
      Complex.normSq_apply, Complex.div_re, Complex.div_im]
  simp only [weight, ha, hb]
  ring

theorem native_split_pair_weight_before (k : ℕ) (hk : 1 ≤ k) :
    weight k 1 + weight k 0 = 1 := by
  norm_num [weight, Nat.ne_of_gt hk]

/-- Every superquadratic power fails pair conservation on this literal split. -/
theorem native_pair_not_conserved (k : ℕ) (hk : 1 < k) :
    ¬ ∀ z w : ℂ,
      weight k (NativeMixerEventConeExclusion.mixer (z, w)).1 +
        weight k (NativeMixerEventConeExclusion.mixer (z, w)).2 =
        weight k z + weight k w := by
  intro h
  have hs := h 1 0
  rw [native_split_pair_weight_after, native_split_pair_weight_before k (by omega)] at hs
  have hp := half_power_lt_half k hk
  linarith

theorem native_spectator_port_before (k : ℕ) :
    port k (before.eval basis) 0 = (1 / 2 : ℝ) ^ k := by
  have h := congrFun NativeContextualProbabilityControl.witness_before_weights 0
  change Complex.normSq (before.eval basis 0) = (1 / 2 : ℝ) at h
  simp [port, exposure, weight, native_witness_energy_before, h]

theorem native_spectator_port_after (k : ℕ) :
    port k (after.eval basis) 0 = (1 / 2 : ℝ) ^ k := by
  have h := congrFun NativeContextualProbabilityControl.witness_after_weights 0
  change Complex.normSq (after.eval basis 0) = (1 / 2 : ℝ) at h
  simp [port, exposure, weight, native_witness_energy_after, h]

theorem native_spectator_unconditional_invariant (k : ℕ) :
    port k (before.eval basis) 0 = port k (after.eval basis) 0 := by
  rw [native_spectator_port_before, native_spectator_port_after]

theorem native_click_conditional_before (k : ℕ) (hk : 1 ≤ k) :
    clickConditional k (before.eval basis) 0 = 1 / 2 := by
  rw [clickConditional_weights k _ (by rw [native_witness_energy_before]; norm_num)]
  change (fun i => weight k (before.eval basis i)) 0 /
    (∑ j, (fun i => weight k (before.eval basis i)) j) = _
  rw [native_witness_weights_before k hk]
  norm_num [Fin.sum_univ_succ]
  have hp : (1 / 2 : ℝ) ^ k ≠ 0 := ne_of_gt (half_power_pos k)
  field_simp
  ring

theorem native_click_conditional_after (k : ℕ) (hk : 1 ≤ k) :
    clickConditional k (after.eval basis) 0 = (2 : ℝ) ^ k / ((2 : ℝ) ^ k + 2) := by
  rw [clickConditional_weights k _ (by rw [native_witness_energy_after]; norm_num)]
  change (fun i => weight k (after.eval basis i)) 0 /
    (∑ j, (fun i => weight k (after.eval basis i)) j) = _
  rw [native_witness_weights_after k]
  norm_num [Fin.sum_univ_succ]
  have hfour : (1 / 4 : ℝ) ^ k = ((1 / 2 : ℝ) ^ k) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
  rw [hfour]
  have hp : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [div_pow, one_pow]
  have hd : (2 : ℝ) ^ k + 2 ≠ 0 := by positivity
  field_simp
  ring

theorem native_click_conditioning_changes_spectator (k : ℕ) (hk : 1 < k) :
    clickConditional k (before.eval basis) 0 ≠ clickConditional k (after.eval basis) 0 := by
  rw [native_click_conditional_before k (by omega),
    native_click_conditional_after k (by omega)]
  have hh := half_power_lt_half k hk
  have hp : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) _
  have hpow : 2 < (2 : ℝ) ^ k := by
    rw [div_pow, one_pow] at hh
    have hm := (div_lt_iff₀ hp).mp hh
    nlinarith
  intro he
  have hm := (eq_div_iff (show (2 : ℝ) ^ k + 2 ≠ 0 by positivity)).mp he
  nlinarith

theorem quartic_click_conditional_matches_existing :
    clickConditional 2 (before.eval basis) 0 =
        NativeContextualProbabilityControl.circuitProbability 0 before 0 ∧
      clickConditional 2 (after.eval basis) 0 =
        NativeContextualProbabilityControl.circuitProbability 0 after 0 := by
  rw [native_click_conditional_before 2 (by omega),
    native_click_conditional_after 2 (by omega),
    NativeContextualProbabilityControl.witness_before_probability,
    NativeContextualProbabilityControl.witness_after_probability]
  norm_num

theorem quartic_response_matches_existing (z : ℂ) :
    weight 2 z = RawSparseQuarticControl.contract.weight z := rfl

end
end IDT.QMClosure.RawPowerLossReadoutControl
