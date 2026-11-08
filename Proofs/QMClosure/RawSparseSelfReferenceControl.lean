import Proofs.QMClosure.RawSparseSelfReferenceSelector
import Proofs.QMClosure.RawSparsePhaseTwistControl

/-!
# Exact phase-twist control for the self-reference selector

The existing continuous homogeneous phase-twist operation inhabits the supplied
native-profile class. Its four self-defects detect a positive output error at
an exact rational complex witness. These are controls inside the supplied
encoding and assert no physical availability or primitive derivation.
-/

namespace IDT.QMClosure.RawSparseSelfReferenceControl

noncomputable section

open NativeAttenuationCircuit


/-- The existing phase-twist operation satisfies every supplied class field. -/
def contract : RawSparseSelfReferenceSelector.Contract where
  operation := RawSparsePhaseTwistControl.gate
  square := RawSparsePhaseTwistControl.gate_square
  vacuum_right x := RawSparsePhaseTwistControl.gate_of_h_zero _ (RawSparsePhaseTwistControl.h_vacuum_right x)
  vacuum_left x := RawSparsePhaseTwistControl.gate_of_h_zero _ (RawSparsePhaseTwistControl.h_vacuum_left x)
  profile_fst := RawSparsePhaseTwistControl.port_weight_fst
  profile_snd := RawSparsePhaseTwistControl.port_weight_snd

def witness : ℂ × ℂ := (1, 1 + Complex.I)

theorem witness_gate :
    RawSparsePhaseTwistControl.gate witness =
      ((111 + 67 * Complex.I) / 82, (31 + 49 * Complex.I) / 82) := by
  unfold witness RawSparsePhaseTwistControl.gate
  rw [RawSparsePhaseTwistControl.witness_phase]
  apply Prod.ext <;> apply Complex.ext <;>
    norm_num [mixer_fst, mixer_snd, a, b, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.normSq_apply]

private theorem gate_swap (p : ℂ × ℂ) :
    RawSparsePhaseTwistControl.gate p.swap = (RawSparsePhaseTwistControl.gate p).swap :=
  RawSparseSelfReferenceSelector.operation_swap contract p

private theorem selfDefect_formula (p : ℂ × ℂ) :
    RawSparseSelfReferenceSelector.selfDefect contract p =
      Complex.normSq (a * (RawSparsePhaseTwistControl.gate p).1 + b * (a * (a * p.1))) +
        Complex.normSq (a * (RawSparsePhaseTwistControl.gate p).2 + b * (b * (a * p.1))) -
        Complex.normSq (a * p.1 + b * (a * p.1)) - Complex.normSq (a * p.2) := by
  simp only [RawSparseSelfReferenceSelector.selfDefect, RawSparseSelfReferenceSelector.A_native, RawSparseSelfReferenceSelector.defect_native_formula,
    Prod.mk.eta, contract]

theorem selfDefect_witness : RawSparseSelfReferenceSelector.selfDefect contract witness = -5 / 41 := by
  rw [selfDefect_formula, witness_gate]
  norm_num [witness, a, b, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]

theorem selfDefect_swap_witness :
    RawSparseSelfReferenceSelector.selfDefect contract witness.swap = -10 / 41 := by
  rw [selfDefect_formula, gate_swap, witness_gate]
  norm_num [witness, a, b, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]

theorem selfDefect_gate_witness :
    RawSparseSelfReferenceSelector.selfDefect contract (RawSparsePhaseTwistControl.gate witness) = 10 / 41 := by
  rw [selfDefect_formula, RawSparsePhaseTwistControl.gate_square, witness_gate]
  norm_num [witness, a, b, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]

theorem selfDefect_swap_gate_witness :
    RawSparseSelfReferenceSelector.selfDefect contract (RawSparsePhaseTwistControl.gate witness).swap = 2 / 41 := by
  rw [selfDefect_formula, gate_swap, RawSparsePhaseTwistControl.gate_square, witness_gate]
  norm_num [witness, a, b, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]

theorem outputError_witness : RawSparseSelfReferenceSelector.outputError contract witness = 6 / 41 := by
  change Complex.normSq ((RawSparsePhaseTwistControl.gate witness).1 - (RawSparseSelfReferenceSelector.N witness).1) +
    Complex.normSq ((RawSparsePhaseTwistControl.gate witness).2 - (RawSparseSelfReferenceSelector.N witness).2) = _
  rw [witness_gate]
  norm_num [witness, mixer_fst, mixer_snd, a, b, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem four_defect_sum :
    RawSparseSelfReferenceSelector.selfDefect contract witness + RawSparseSelfReferenceSelector.selfDefect contract witness.swap +
      RawSparseSelfReferenceSelector.selfDefect contract (RawSparsePhaseTwistControl.gate witness) +
      RawSparseSelfReferenceSelector.selfDefect contract (RawSparsePhaseTwistControl.gate witness).swap = -3 / 41 := by
  rw [selfDefect_witness, selfDefect_swap_witness, selfDefect_gate_witness,
    selfDefect_swap_gate_witness]
  norm_num

/-- The generic identity is instantiated independently of the four evaluations. -/
theorem four_defect_identity_at_witness :
    RawSparseSelfReferenceSelector.selfDefect contract witness + RawSparseSelfReferenceSelector.selfDefect contract witness.swap +
      RawSparseSelfReferenceSelector.selfDefect contract (RawSparsePhaseTwistControl.gate witness) +
      RawSparseSelfReferenceSelector.selfDefect contract (RawSparsePhaseTwistControl.gate witness).swap =
        -RawSparseSelfReferenceSelector.outputError contract witness / 2 :=
  RawSparseSelfReferenceSelector.four_defect_identity contract witness

theorem violates_self_nondecrease :
    ¬ ∀ p, 0 ≤ RawSparseSelfReferenceSelector.selfDefect contract p := by
  intro h
  have hw := h witness
  rw [selfDefect_witness] at hw
  norm_num at hw

theorem violates_self_equality : ¬ RawSparseSelfReferenceSelector.SelfLaw contract := by
  intro h
  have hw := h witness
  rw [selfDefect_witness] at hw
  norm_num at hw

theorem positive_output_error : 0 < RawSparseSelfReferenceSelector.outputError contract witness := by
  rw [outputError_witness]
  norm_num

end

end IDT.QMClosure.RawSparseSelfReferenceControl
