import Proofs.QMClosure.SingleEchoReadout
import Proofs.QMClosure.NormalizedEchoReadoutControls

namespace IDT.QMClosure.SingleEchoReadoutControls

open SingleEchoReadout NormalizedEchoReadout NormalizedEchoReadoutControls
open scoped Topology

noncomputable section

/-- A concrete nonzero equal-branch input for the quadratic weight. -/
def balancedAmplitude : ℂ := (1 + Complex.I) / 2

theorem balanced_amplitude_normSq :
    Complex.normSq balancedAmplitude = 1 / 2 := by
  norm_num [balancedAmplitude, Complex.normSq_div, Complex.normSq_apply]

theorem balanced_amplitude_ne_zero : balancedAmplitude ≠ 0 := by
  intro hz
  have h := balanced_amplitude_normSq
  rw [hz, map_zero] at h
  norm_num at h

/-- The accepted nondegenerate witness premise is inhabited by norm square. -/
theorem normSq_nondegenerate_echo : NondegenerateEcho Complex.normSq := by
  refine ⟨balancedAmplitude, balancedAmplitude, balanced_amplitude_ne_zero,
    balanced_amplitude_ne_zero, ?_, ?_⟩
  · rw [balanced_amplitude_normSq]
    norm_num
  · rw [echo_eq_real, balanced_amplitude_normSq]
    norm_num

theorem normSq_retained_laws :
    ContinuousAt Complex.normSq 1 ∧
      (∀ z t : ℂ, Complex.normSq (z * t) = Complex.normSq z * Complex.normSq t) :=
  ⟨Complex.continuous_normSq.continuousAt, Complex.normSq_mul⟩

/-- A deterministic pair satisfies normalization and echo for the quartic
weight while the quadratic conclusion fails. -/
theorem quartic_deterministic_control :
    ContinuousAt quarticWeight 1 ∧
      (∀ z t, quarticWeight (z * t) = quarticWeight z * quarticWeight t) ∧
      quarticWeight 1 + quarticWeight 0 = 1 ∧
      quarticWeight ((1 : ℂ) * star 1 + 0 * star 0) = 1 ∧
      quarticWeight 2 ≠ Complex.normSq 2 := by
  refine ⟨quartic_laws.continuous.continuousAt, quartic_laws.multiplicative,
    ?_, ?_, ?_⟩ <;> norm_num [quarticWeight, Complex.normSq_apply]

/-- The quartic weight attains half response on a nonzero branch, but its
balanced echo has response four. Normalization alone does not select degree two. -/
theorem quartic_balanced_echo_four :
    ∃ c : ℂ, c ≠ 0 ∧ quarticWeight c = 1 / 2 ∧
      quarticWeight c + quarticWeight c = 1 ∧
      quarticWeight (c * star c + c * star c) = 4 := by
  obtain ⟨r, _, hr⟩ := quartic_positive_real_level (by norm_num : (0 : ℝ) < 1 / 2)
  have hrne : (r : ℂ) ≠ 0 := by
    intro hz
    rw [hz, quartic_laws.zero] at hr
    norm_num at hr
  refine ⟨(r : ℂ), hrne, hr, ?_, ?_⟩
  · rw [hr]
    norm_num
  · rw [echo_eq_real]
    rw [quarticWeight, Complex.normSq_ofReal]
    calc
      ((Complex.normSq (r : ℂ) + Complex.normSq (r : ℂ)) *
          (Complex.normSq (r : ℂ) + Complex.normSq (r : ℂ))) ^ 2 =
          16 * ((Complex.normSq (r : ℂ)) ^ 2) ^ 2 := by ring
      _ = 4 := by change 16 * (quarticWeight (r : ℂ)) ^ 2 = 4; rw [hr]; norm_num

/-- The support control is locally constant at the multiplicative unit. -/
theorem support_continuousAt_one : ContinuousAt supportWeight 1 := by
  have hne : ∀ᶠ z : ℂ in 𝓝 1, z ≠ 0 := eventually_ne_nhds (by norm_num)
  have heq : supportWeight =ᶠ[𝓝 (1 : ℂ)] fun _ => (1 : ℝ) := by
    filter_upwards [hne] with z hz
    simp [supportWeight, hz]
  exact heq.continuousAt

/-- Every normalized support pair is deterministic, so this control has no
nondegenerate normalized echo witness despite satisfying every full echo. -/
theorem support_no_nondegenerate_echo : ¬ NondegenerateEcho supportWeight := by
  rintro ⟨a, b, ha, hb, hab, _⟩
  simp [supportWeight, ha, hb] at hab

theorem support_control :
    ContinuousAt supportWeight 1 ∧
      (∀ z t, supportWeight (z * t) = supportWeight z * supportWeight t) ∧
      NormalizedEcho supportWeight ∧
      ¬ NondegenerateEcho supportWeight :=
  ⟨support_continuousAt_one, support_multiplicative, support_normalized_echo,
    support_no_nondegenerate_echo⟩

end

end IDT.QMClosure.SingleEchoReadoutControls
