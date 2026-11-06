import Proofs.QMClosure.NativeCoherentBranchDilation

/-!
# Same-source scalar amplitude sufficiency from coherent native branches

Two levels of actual vacuum duplication produce equal-scale middle branches.
Running different native circuits in those branches places their selected
amplitudes in one prepared state. When those amplitudes agree, output-swap
invariance equates the branch probabilities. The derived quarter accounting
then equates the original probabilities.

This proves a same-wire-type, same-marked-source theorem under `Law`. No law
relating arbitrary source relabelings or different wire types is assumed.
No spectator-orbit transitivity or coarse-effect descent is used or asserted.
-/

namespace IDT.QMClosure.NativeScalarAmplitudeSufficiency

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open MixerGeneratedProcessWall NativeVacuumProbabilityFamily NativeCoherentBranchDilation

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def comparison (c d : Native ι) : Native ((ι ⊕ ι) ⊕ (ι ⊕ ι)) :=
  dilation (dilation .identity c) (dilation d .identity)

theorem comparison_middle_amplitudes (s : ι) (c d : Native ι) (i j : ι)
    (h : c.eval (source s) i = d.eval (source s) j) :
    (comparison c d).eval (source (.inl (.inl s))) (.inl (.inr i)) =
      (comparison c d).eval (source (.inl (.inl s))) (.inr (.inl j)) := by
  simp only [comparison, dilation_amplitude_left, dilation_amplitude_right]
  rw [h]
  ring

/-- Exact scalar equality suffices for any two actual events with the same
original marked source and wire type. All comparisons are inside literal sums. -/
theorem same_source_amplitude_sufficiency (L : Law) (s : ι)
    (c d : Native ι) (i j : ι)
    (h : c.eval (source s) i = d.eval (source s) j) :
    L.prob s c i = L.prob s d j := by
  have hp := equal_coordinate_probabilities L (.inl (.inl s)) (comparison c d)
    (.inl (.inr i)) (.inr (.inl j)) (comparison_middle_amplitudes s c d i j h)
  simp only [comparison, dilation_probability_left, dilation_probability_right] at hp
  linarith

end

end IDT.QMClosure.NativeScalarAmplitudeSufficiency
