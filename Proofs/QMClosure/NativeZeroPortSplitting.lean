import Proofs.QMClosure.NativeBinaryRefinement

/-!
# Halving at an internal zero-amplitude partner

The new-port halving theorem transfers to any existing zero-amplitude partner
using one literal vacuum embedding and one output swap. Every comparison uses
the same marked source and the existing probability-family contract. No wire
relabel law, probability continuity, scalar-probability primitive, or physical
availability conclusion is added.
-/

namespace IDT.QMClosure.NativeZeroPortSplitting

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open MixerGeneratedProcessWall NativeMixerEventConeExclusion
open NativeVacuumProbabilityFamily NativeBinaryRefinement

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def partnerSwap (j : ι) : Equiv.Perm (ι ⊕ PUnit) :=
  Equiv.swap (.inl j) (.inr PUnit.unit)

omit [Fintype ι] in
theorem partnerSwap_retained (i j : ι) (hij : i ≠ j) :
    partnerSwap j (.inl i) = .inl i := by
  simp [partnerSwap, Equiv.swap_apply_def, hij]

/-- The same prepared vector, including the retained fresh output wire. -/
theorem internal_zero_partner_prepared (s : ι) (c : Native ι) (i j : ι)
    (hij : i ≠ j) (hz : c.eval (source s) j = 0) :
    (padCircuit PUnit (.seq c (.pair i j hij))).eval (source (.inl s)) =
      (Circuit.seq (split c i) (.permute (partnerSwap j))).eval (source (.inl s)) := by
  ext w
  cases w with
  | inl k =>
      by_cases hki : k = i
      · subst k
        simp [padCircuit, split, partnerSwap, Circuit.eval, pad_prepared,
          pairGate, pairReplace, padState, Equiv.swap_apply_def, hij, hz,
          NativeAttenuationCircuit.mixer_fst]
      · by_cases hkj : k = j
        · subst k
          simp [padCircuit, split, partnerSwap, Circuit.eval, pad_prepared,
            pairGate, pairReplace, padState, Equiv.swap_apply_def, hij.symm, hz,
            NativeAttenuationCircuit.mixer_snd]
        · simp [padCircuit, split, partnerSwap, Circuit.eval, pad_prepared,
            pairGate, pairReplace, padState, Equiv.swap_apply_def, hki, hkj]
  | inr u =>
      cases u
      simp [padCircuit, split, partnerSwap, Circuit.eval, pad_prepared,
        pairGate, pairReplace, padState, Equiv.swap_apply_def, hij.symm, hz]

/-- Both actual pair outputs receive half the original selected probability. -/
theorem internal_zero_partner_halves (L : Law) (s : ι) (c : Native ι) (i j : ι)
    (hij : i ≠ j) (hz : c.eval (source s) j = 0) :
    L.prob s (.seq c (.pair i j hij)) i = L.prob s c i / 2 ∧
      L.prob s (.seq c (.pair i j hij)) j = L.prob s c i / 2 := by
  have he := internal_zero_partner_prepared s c i j hij hz
  let d0 : Native (ι ⊕ PUnit) := padCircuit PUnit (.seq c (.pair i j hij))
  let d1 : Native (ι ⊕ PUnit) := .seq (split c i) (.permute (partnerSwap j))
  have hstate : L.prob (Sum.inl s : ι ⊕ PUnit) d0 =
      L.prob (Sum.inl s : ι ⊕ PUnit) d1 :=
    L.prepared_eq (Sum.inl s : ι ⊕ PUnit) d0 d1 he
  have hp := congrFun hstate (Sum.inl i : ι ⊕ PUnit)
  change L.prob (.inl s) (padCircuit PUnit (.seq c (.pair i j hij))) (.inl i) =
    L.prob (.inl s) (.seq (split c i) (.permute (partnerSwap j))) (.inl i) at hp
  rw [L.vacuum, L.output_perm, partnerSwap_retained i j hij,
    native_vacuum_split_halves] at hp
  refine ⟨hp, ?_⟩
  have hsum := pair_probability_sum L s c i j hij
  rw [hp, zero_amplitude_probability_zero L s c j hz] at hsum
  linarith

end

end IDT.QMClosure.NativeZeroPortSplitting
