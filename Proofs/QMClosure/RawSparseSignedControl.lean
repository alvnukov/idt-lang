import Proofs.QMClosure.RawSparseMarginalReconstruction
import Proofs.QMClosure.NativeAttenuationCircuit

/-!
# A signed readout separates the sparse kernel from weight descent

The supplied native complex mixer and the real-part readout satisfy the raw
square-swap, transparency, vacuum-zero, and exact conservation contract. They
also satisfy the universal sparse marginal law. Their final kernel is zero on
every pair, yet the readout is nonconstant, takes negative values, and fails
vacuum halving. Thus kernel equivalence alone cannot imply weight descent
without the positive-readout premise. This is an exact mathematical control,
with no physical availability, probability, actualization, or QM claim.
-/

namespace IDT.QMClosure.RawSparseSignedControl

noncomputable section

open RawSparseMarginalReconstruction

def contract : Contract ℂ where
  chosenZero := 0
  operation := NativeMixerEventConeExclusion.mixer
  weight z := z.re
  vacuum := rfl
  square := NativeMixerEventConeExclusion.mixer_square
  transparent := NativeMixerEventConeExclusion.mixer_transparent
  conserved x y := by
    rw [NativeAttenuationCircuit.mixer_fst, NativeAttenuationCircuit.mixer_snd]
    norm_num [NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
      Complex.add_re, Complex.mul_re, Complex.div_re, Complex.div_im]
    ring

theorem first_channel_medial (x y z w : ℂ) :
    m contract (m contract x y) (m contract z w) =
      m contract (m contract x z) (m contract y w) := by
  change (NativeMixerEventConeExclusion.mixer
    ((NativeMixerEventConeExclusion.mixer (x, y)).1,
      (NativeMixerEventConeExclusion.mixer (z, w)).1)).1 =
    (NativeMixerEventConeExclusion.mixer
      ((NativeMixerEventConeExclusion.mixer (x, z)).1,
        (NativeMixerEventConeExclusion.mixer (y, w)).1)).1
  simp only [NativeAttenuationCircuit.mixer_fst]
  ring

theorem observed_medial : ObservedMedial contract := by
  intro x y z w
  rw [first_channel_medial]
  intro context
  rfl

/-- This direction of the sparse theorem requires no nonnegative readout. -/
theorem sparse_law : SparseMarginalLaw contract :=
  sparse_of_observed_medial contract observed_medial

/-- Real-part additivity makes the final interaction kernel identically zero. -/
theorem kernel_zero (x z : ℂ) : K contract x z = 0 := by
  change (NativeMixerEventConeExclusion.mixer (x, z)).1.re -
    (NativeMixerEventConeExclusion.mixer (x, 0)).1.re -
      (NativeMixerEventConeExclusion.mixer (0, z)).1.re = 0
  rw [NativeAttenuationCircuit.mixer_fst, NativeAttenuationCircuit.mixer_fst,
    NativeAttenuationCircuit.mixer_fst]
  simp only [mul_zero, add_zero, zero_add, Complex.add_re]
  ring

theorem kernelEq_all (x y : ℂ) : KernelEq contract x y := by
  intro z
  rw [kernel_zero, kernel_zero]

theorem imaginary_vacuum_weight : contract.weight (A contract Complex.I) = -1 / 2 := by
  change (NativeMixerEventConeExclusion.mixer (Complex.I, 0)).1.re = -1 / 2
  rw [NativeAttenuationCircuit.mixer_fst]
  norm_num [NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
    Complex.add_re, Complex.mul_re, Complex.div_re, Complex.div_im]

theorem vacuum_half_failure :
    contract.weight (A contract Complex.I) ≠ contract.weight Complex.I / 2 := by
  rw [imaginary_vacuum_weight]
  norm_num [contract]

theorem negative_weight : contract.weight (-1 : ℂ) = -1 := by
  norm_num [contract]

theorem not_nonnegative : ¬ ∀ x : ℂ, 0 ≤ contract.weight x := by
  intro h
  have hn := h (-1)
  rw [negative_weight] at hn
  norm_num at hn

/-- The universal kernel relation identifies zero and one, but their weights differ. -/
theorem kernel_equiv_weight_distinction :
    KernelEq contract (0 : ℂ) 1 ∧ contract.weight 0 ≠ contract.weight 1 := by
  exact ⟨kernelEq_all 0 1, by norm_num [contract]⟩

theorem kernel_equiv_does_not_force_weight_descent :
    ¬ ∀ x y : ℂ, KernelEq contract x y → contract.weight x = contract.weight y := by
  intro h
  exact kernel_equiv_weight_distinction.2
    (h 0 1 kernel_equiv_weight_distinction.1)

end
end IDT.QMClosure.RawSparseSignedControl
