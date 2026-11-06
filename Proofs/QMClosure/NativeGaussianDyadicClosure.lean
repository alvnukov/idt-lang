import Proofs.QMClosure.NativeVacuumProbabilityFamily
import Proofs.QMClosure.NativeDyadicSixWireObstruction

/-!
# Gaussian dyadic closure of actual finite native circuits

Every native basis-prepared coordinate has a Gaussian-integer numerator and a
power-of-two denominator. The existing modulo-five relation is used only to
reuse its exact scalar arithmetic closure; the final conclusion forgets the
residue. No probability law or preparation-completeness assumption is used.
-/

namespace IDT.QMClosure.NativeGaussianDyadicClosure

noncomputable section
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open NativeDyadicSixWireObstruction

theorem related_zero : Related (0 : ℂ) (0 : ZMod 5) := by
  exact ⟨0, 0, by simp, by simp⟩

theorem related_one : Related (1 : ℂ) (1 : ZMod 5) := by
  exact ⟨0, 1, by simp, by simp⟩

theorem related_mixer {z w : ℂ} {r s : ZMod 5}
    (hz : Related z r) (hw : Related w s) :
    Related (NativeMixerEventConeExclusion.mixer (z,w)).1 (2*r+4*s) ∧
    Related (NativeMixerEventConeExclusion.mixer (z,w)).2 (4*r+2*s) := by
  constructor
  · rw [NativeAttenuationCircuit.mixer_fst]
    exact related_add (related_mul related_a hz) (related_mul related_b hw)
  · rw [NativeAttenuationCircuit.mixer_snd]
    exact related_add (related_mul related_b hz) (related_mul related_a hw)

/-- The scalar arithmetic certificate propagates through every native constructor. -/
theorem circuit_has_residue {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Native ι) (v : ι → ℂ) (hv : ∀ i, ∃ r : ZMod 5, Related (v i) r) :
    ∀ i, ∃ r : ZMod 5, Related (c.eval v i) r := by
  induction c generalizing v with
  | identity => exact hv
  | pair i j hij =>
    obtain ⟨r, hr⟩ := hv i
    obtain ⟨s, hs⟩ := hv j
    have hm := related_mixer hr hs
    intro k
    by_cases hki : k = i
    · subst k
      refine ⟨2*r+4*s, ?_⟩
      simpa [Circuit.eval, pairGate, pairReplace] using hm.1
    by_cases hkj : k = j
    · subst k
      refine ⟨4*r+2*s, ?_⟩
      simpa [Circuit.eval, pairGate, pairReplace, Ne.symm hij] using hm.2
    · simpa [Circuit.eval, pairGate, pairReplace, hki, hkj] using hv k
  | permute e => exact fun k => hv (e k)
  | seq c d hc hd => exact hd (c.eval v) (hc v hv)

theorem source_has_residue {ι : Type} [DecidableEq ι] (s : ι) :
    ∀ i, ∃ r : ZMod 5, Related (source s i) r := by
  intro i
  by_cases hi : i = s
  · refine ⟨1, ?_⟩
    simpa [source, single, hi] using related_one
  · refine ⟨0, ?_⟩
    simpa [source, single, hi] using related_zero

/-- A denominator representation for every output of every actual native circuit. -/
theorem native_output_gaussian_dyadic {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (i : ι) :
    ∃ k : ℕ, ∃ g : GaussianInt, c.eval (source s) i = (g : ℂ) / (2 : ℂ)^k := by
  obtain ⟨r, k, g, hg, _⟩ := circuit_has_residue c (source s) (source_has_residue s) i
  exact ⟨k, g, hg⟩

end
end IDT.QMClosure.NativeGaussianDyadicClosure
