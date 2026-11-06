import Proofs.QMClosure.NativeMixerEventConeExclusion

/-!
# Contextual probabilities with unchanged native circuit dynamics

This conditional mathematical control retains the existing native mixer and
literal circuit grammar. It assigns normalized squared structural weights to
complete output vectors. Calibration, output relabeling, inert vacuum extension,
complete-process equivalence, and syntactic fair-mixture accounting all hold.
Nevertheless two literal circuits have the same selected-output amplitude for
every complex input and different assigned probabilities at a fixed source.

The fair-mixture law concerns protocol syntax only: no coordinate-domain
midpoint law or descent to individual-event profiles follows. This is neither a
physical probability proposal nor a Bell/no-signalling or Born/full-QM result.
-/

namespace IDT.QMClosure.NativeContextualProbabilityControl

noncomputable section
open scoped BigOperators
open MixerGeneratedProcessWall

variable {ι κ : Type*} [Fintype ι]

def weight (x : ι → ℂ) (i : ι) : ℝ := Complex.normSq (x i)

def denominator (x : ι → ℂ) : ℝ := ∑ i, (weight x i) ^ 2

def probability (x : ι → ℂ) (i : ι) : ℝ := (weight x i) ^ 2 / denominator x

theorem denominator_nonneg (x : ι → ℂ) : 0 ≤ denominator x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem denominator_pos (x : ι → ℂ) (normalized : ∑ i, weight x i = 1) :
    0 < denominator x := by
  by_contra hn
  have hz : denominator x = 0 :=
    le_antisymm (le_of_not_gt hn) (denominator_nonneg x)
  have heach := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ Finset.univ) => sq_nonneg (weight x i))).mp hz
  have hw : ∀ i, weight x i = 0 := by
    intro i
    have hi := heach i (Finset.mem_univ i)
    nlinarith [sq_nonneg (weight x i)]
  have hs : ∑ i, weight x i = 0 := by simp [hw]
  linarith

theorem probability_nonneg (x : ι → ℂ) (i : ι) : 0 ≤ probability x i :=
  div_nonneg (sq_nonneg _) (denominator_nonneg x)

theorem probability_le_one (x : ι → ℂ) (normalized : ∑ i, weight x i = 1)
    (i : ι) : probability x i ≤ 1 := by
  apply (div_le_one (denominator_pos x normalized)).2
  exact Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg (weight x j))
    (Finset.mem_univ i)

theorem probability_sum (x : ι → ℂ) (normalized : ∑ i, weight x i = 1) :
    ∑ i, probability x i = 1 := by
  simp only [probability, ← Finset.sum_div]
  exact div_self (ne_of_gt (denominator_pos x normalized))

theorem basis_calibration [DecidableEq ι] (i k : ι) :
    probability (single i (1 : ℂ)) k = if k = i then 1 else 0 := by
  classical
  simp [probability, denominator, weight, single, apply_ite]

theorem denominator_permutation (x : ι → ℂ) (e : ι ≃ ι) :
    denominator (fun i => x (e i)) = denominator x :=
  e.sum_comp (fun i => (weight x i) ^ 2)

theorem probability_permutation (x : ι → ℂ) (e : ι ≃ ι) (i : ι) :
    probability (fun j => x (e j)) i = probability x (e i) := by
  simp only [probability, denominator_permutation, weight]

def vacuumExtension (x : ι → ℂ) : ι ⊕ κ → ℂ := Sum.elim x (fun _ => 0)

variable [Fintype κ]

theorem denominator_vacuum_extension (x : ι → ℂ) :
    denominator (vacuumExtension (κ := κ) x) = denominator x := by
  simp [denominator, weight, vacuumExtension, Fintype.sum_sum_type]

theorem probability_vacuum_data (x : ι → ℂ) (i : ι) :
    probability (vacuumExtension (κ := κ) x) (.inl i) = probability x i := by
  unfold probability
  rw [denominator_vacuum_extension]
  rfl

theorem probability_vacuum_ancilla (x : ι → ℂ) (k : κ) :
    probability (vacuumExtension x) (.inr k) = 0 := by
  simp [probability, weight, vacuumExtension]

variable [DecidableEq ι]

abbrev NativeCircuit (ι : Type*) [DecidableEq ι] :=
  Circuit (ι := ι) NativeMixerEventConeExclusion.mixer

def source (i : ι) : ι → ℂ := single i 1

def circuitProbability (i : ι) (c : NativeCircuit ι) (k : ι) : ℝ :=
  probability (c.eval (source i)) k

theorem circuit_output_normalized (i : ι) (c : NativeCircuit ι) :
    ∑ k, weight (c.eval (source i)) k = 1 := by
  have h := c.preserves_readout Complex.normSq
    NativeMixerEventConeExclusion.mixer_conserves (source i)
  simpa [weight, totalReadout, source, single] using h

theorem circuit_probability_bounds (i : ι) (c : NativeCircuit ι) (k : ι) :
    0 ≤ circuitProbability i c k ∧ circuitProbability i c k ≤ 1 :=
  ⟨probability_nonneg _ _, probability_le_one _ (circuit_output_normalized i c) _⟩

theorem circuit_probability_sum (i : ι) (c : NativeCircuit ι) :
    ∑ k, circuitProbability i c k = 1 :=
  probability_sum _ (circuit_output_normalized i c)

theorem identity_calibration (i k : ι) :
    circuitProbability i .identity k = if k = i then 1 else 0 :=
  basis_calibration i k

theorem complete_process_equivalence (i : ι) (c d : NativeCircuit ι)
    (same_process : c.eval = d.eval) : circuitProbability i c = circuitProbability i d := by
  funext k
  unfold circuitProbability
  rw [same_process]

/-- The binary constructor is explicit external fair randomization of protocols. -/
inductive FairProtocol (ι : Type*) [DecidableEq ι] where
  | leaf (c : NativeCircuit ι) : FairProtocol ι
  | mix (left right : FairProtocol ι) : FairProtocol ι

def protocolProbability (i : ι) : FairProtocol ι → (ι → ℝ)
  | .leaf c => circuitProbability i c
  | .mix p q => fun k => (protocolProbability i p k + protocolProbability i q k) / 2

theorem syntactic_midpoint (i : ι) (p q : FairProtocol ι) (k : ι) :
    protocolProbability i (.mix p q) k =
      (protocolProbability i p k + protocolProbability i q k) / 2 := rfl

theorem protocol_probability_bounds (i : ι) (p : FairProtocol ι) (k : ι) :
    0 ≤ protocolProbability i p k ∧ protocolProbability i p k ≤ 1 := by
  induction p with
  | leaf c => exact circuit_probability_bounds i c k
  | mix p q hp hq => simp only [protocolProbability]; constructor <;> linarith

theorem protocol_probability_sum (i : ι) (p : FairProtocol ι) :
    ∑ k, protocolProbability i p k = 1 := by
  induction p with
  | leaf c => exact circuit_probability_sum i c
  | mix p q hp hq =>
      simp only [protocolProbability, ← Finset.sum_div, Finset.sum_add_distrib, hp, hq]
      norm_num

def witnessBefore : NativeCircuit (Fin 3) := NativeMixerEventConeExclusion.gate01
def witnessAfter : NativeCircuit (Fin 3) :=
  .seq NativeMixerEventConeExclusion.gate01 NativeMixerEventConeExclusion.gate12

/-- The spectator operation leaves the entire selected amplitude map unchanged. -/
theorem selected_amplitude_equal (x : Fin 3 → ℂ) :
    witnessAfter.eval x 0 = witnessBefore.eval x 0 := by
  simp [witnessAfter, witnessBefore, NativeMixerEventConeExclusion.gate12,
    Circuit.eval, pairGate, pairReplace]

def selectedProfile (c : NativeCircuit (Fin 3)) : (Fin 3 → ℂ) → ℝ :=
  fun x => Complex.normSq (c.eval x 0)

theorem selected_profile_equal : selectedProfile witnessAfter = selectedProfile witnessBefore := by
  funext x
  exact congrArg Complex.normSq (selected_amplitude_equal x)

theorem witness_before_action :
    witnessBefore.eval (source 0) = ![(1 + Complex.I) / 2, (1 - Complex.I) / 2, 0] := by
  funext k
  fin_cases k <;> apply Complex.ext <;>
    norm_num [witnessBefore, source, single,
      NativeMixerEventConeExclusion.gate01, Circuit.eval, pairGate, pairReplace,
      NativeMixerEventConeExclusion.mixer, NativeMixerEventConeExclusion.Raw,
      CompositeProductControls.RawSign.N, CompositeProductControls.RawSign.n,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem witness_after_action :
    witnessAfter.eval (source 0) = ![(1 + Complex.I) / 2, 1 / 2, -Complex.I / 2] := by
  change NativeMixerEventConeExclusion.gate12.eval (witnessBefore.eval (source 0)) = _
  rw [witness_before_action]
  funext k
  fin_cases k
  · rfl
  · change CompositeProductControls.RawSign.n ((1 - Complex.I) / 2) 0 = (1 / 2 : ℂ)
    apply Complex.ext <;>
      norm_num [CompositeProductControls.RawSign.n,
        Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  · change CompositeProductControls.RawSign.n 0 ((1 - Complex.I) / 2) = -Complex.I / 2
    apply Complex.ext <;>
      norm_num [CompositeProductControls.RawSign.n,
        Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem witness_before_weights :
    weight (witnessBefore.eval (source 0)) = ![1 / 2, 1 / 2, 0] := by
  rw [witness_before_action]
  funext k
  fin_cases k <;>
    norm_num [weight, Complex.normSq_apply, Complex.div_re, Complex.div_im]

theorem witness_after_weights :
    weight (witnessAfter.eval (source 0)) = ![1 / 2, 1 / 4, 1 / 4] := by
  rw [witness_after_action]
  funext k
  fin_cases k <;>
    norm_num [weight, Complex.normSq_apply, Complex.div_re, Complex.div_im]

theorem witness_before_probability : circuitProbability 0 witnessBefore 0 = 1 / 2 := by
  norm_num [circuitProbability, probability, denominator, witness_before_weights,
    Fin.sum_univ_succ]

theorem witness_after_probability : circuitProbability 0 witnessAfter 0 = 2 / 3 := by
  norm_num [circuitProbability, probability, denominator, witness_after_weights,
    Fin.sum_univ_succ]

theorem spectator_operation_changes_probability :
    circuitProbability 0 witnessBefore 0 ≠ circuitProbability 0 witnessAfter 0 := by
  rw [witness_before_probability, witness_after_probability]
  norm_num

/-- Even the complete all-input selected weight profile cannot determine this readout. -/
theorem no_selected_profile_readout :
    ¬ ∃ f : ((Fin 3 → ℂ) → ℝ) → ℝ,
      ∀ c : NativeCircuit (Fin 3), f (selectedProfile c) = circuitProbability 0 c 0 := by
  rintro ⟨f, hf⟩
  have hb := hf witnessBefore
  have ha := hf witnessAfter
  rw [selected_profile_equal, witness_after_probability] at ha
  rw [witness_before_probability] at hb
  linarith

end
end IDT.QMClosure.NativeContextualProbabilityControl
