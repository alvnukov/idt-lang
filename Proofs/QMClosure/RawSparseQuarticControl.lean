import Proofs.QMClosure.RawSparseConservationSelection
import Proofs.QMClosure.NativeAttenuationCircuit

/-!
# Quartic readout separates mediality from sparse conservation

The supplied complex mixer with the quartic readout `normSq z ^ 2` satisfies
square-swap, transparency, vacuum-zero, global nonnegativity, and literal
first-channel mediality. Its vacuum outputs at one each have weight one
quarter. Pair conservation fails, and the actual sparse equation at `(0,1,1)`
has left side one and right side one half. Thus observed mediality and
nonnegativity alone do not imply the actual sparse law.

Complex coordinates and the mixer are supplied for this mathematical
countermodel. No physical availability, probability, actualization, or QM
closure is asserted.
-/

namespace IDT.QMClosure.RawSparseQuarticControl

noncomputable section

open RawSparseConservationSelection

def contract : Contract ℂ where
  chosenZero := 0
  operation := NativeMixerEventConeExclusion.mixer
  weight z := Complex.normSq z ^ 2
  vacuum := by norm_num
  square := NativeMixerEventConeExclusion.mixer_square
  transparent := NativeMixerEventConeExclusion.mixer_transparent

theorem nonnegative (z : ℂ) : 0 ≤ contract.weight z :=
  sq_nonneg (Complex.normSq z)

theorem m_eq (x y : ℂ) :
    m contract x y = NativeAttenuationCircuit.a * x + NativeAttenuationCircuit.b * y :=
  NativeAttenuationCircuit.mixer_fst x y

theorem first_channel_medial (x y z w : ℂ) :
    m contract (m contract x y) (m contract z w) =
      m contract (m contract x z) (m contract y w) := by
  simp only [m_eq]
  ring

theorem observed_medial : ObservedMedial contract := by
  intro x y z w
  rw [first_channel_medial]
  intro context
  rfl

theorem vacuum_first_weight : contract.weight (A contract (1 : ℂ)) = 1 / 4 := by
  change Complex.normSq (m contract 1 0) ^ 2 = 1 / 4
  rw [m_eq]
  norm_num [NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
    Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.div_re, Complex.div_im]

theorem vacuum_second_weight : contract.weight (B contract (1 : ℂ)) = 1 / 4 := by
  change Complex.normSq (m contract 0 1) ^ 2 = 1 / 4
  rw [m_eq]
  norm_num [NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
    Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.div_re, Complex.div_im]

theorem pair_output_at_10 :
    contract.weight (contract.operation (1, 0)).1 +
      contract.weight (contract.operation (1, 0)).2 = 1 / 2 := by
  rw [second_eq_reverse contract]
  change contract.weight (A contract 1) + contract.weight (B contract 1) = 1 / 2
  rw [vacuum_first_weight, vacuum_second_weight]
  norm_num

theorem pair_input_at_10 : contract.weight 1 + contract.weight 0 = 1 := by
  norm_num [contract]

theorem not_pair_conserved : ¬ PairConserved contract := by
  intro h
  have hp := h 1 0
  rw [pair_output_at_10, pair_input_at_10] at hp
  norm_num at hp

theorem sparse_lhs_at_011 :
    contract.weight (m contract (m contract 0 1) (A contract 1)) +
      contract.weight (m contract (m contract 1 0) (B contract 1)) = 1 := by
  change Complex.normSq (m contract (m contract 0 1) (m contract 1 0)) ^ 2 +
    Complex.normSq (m contract (m contract 1 0) (m contract 0 1)) ^ 2 = 1
  simp only [m_eq]
  norm_num [NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
    Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.div_re, Complex.div_im]

theorem sparse_rhs_at_011 :
    contract.weight (m contract 0 1) + contract.weight (A contract 1) = 1 / 2 := by
  change contract.weight (B contract 1) + contract.weight (A contract 1) = 1 / 2
  rw [vacuum_second_weight, vacuum_first_weight]
  norm_num

theorem not_sparse_law : ¬ SparseMarginalLaw contract := by
  intro h
  have hs := h 0 1 1
  rw [sparse_lhs_at_011, sparse_rhs_at_011] at hs
  norm_num at hs

/-- This countermodel keeps both mediality and a globally nonnegative readout. -/
theorem observed_medial_nonnegative_not_sparse :
    ObservedMedial contract ∧ (∀ z : ℂ, 0 ≤ contract.weight z) ∧
      ¬ SparseMarginalLaw contract :=
  ⟨observed_medial, nonnegative, not_sparse_law⟩

theorem observed_medial_nonnegative_does_not_imply_sparse :
    ¬ ∀ D : Contract ℂ, ObservedMedial D → (∀ z : ℂ, 0 ≤ D.weight z) →
      SparseMarginalLaw D := by
  intro h
  exact not_sparse_law (h contract observed_medial nonnegative)

end
end IDT.QMClosure.RawSparseQuarticControl
