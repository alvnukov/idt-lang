import Mathlib
import Proofs.QMClosure.ExclusivityAdditivityProof

namespace IDT.QMClosure

/-!
# Operational Equivalence Probability Proof

Machine-checked proof for the `operational_equivalence_probability` closure obligation.
-/

variable {H : Type} [Fintype H] [DecidableEq H]
variable (W : H → ℂ)
variable (Γ : H → H → ℂ)

theorem operational_equivalence_probability
    (A A' : Finset H)
    (σ : A ≃ A')
    (h_W : ∀ h : A, W (h : H) = W ((σ h : A') : H))
    (h_Γ : ∀ h h' : A, Γ (h : H) (h' : H) = Γ ((σ h : A') : H) ((σ h' : A') : H)) :
    actualizationMeasure W Γ A = actualizationMeasure W Γ A' := by
  unfold actualizationMeasure
  refine Finset.sum_bij'
    (fun a ha => ((σ ⟨a, ha⟩ : A') : H))
    (fun b hb => ((σ.symm ⟨b, hb⟩ : A) : H))
    (fun a ha => (σ ⟨a, ha⟩).property)
    (fun b hb => (σ.symm ⟨b, hb⟩).property)
    (fun a ha => by simp [Subtype.coe_eta, Equiv.symm_apply_apply])
    (fun b hb => by simp [Subtype.coe_eta, Equiv.apply_symm_apply])
    ?_
  intro a ha
  -- Inner sum
  refine Finset.sum_bij'
    (fun a' ha' => ((σ ⟨a', ha'⟩ : A') : H))
    (fun b hb => ((σ.symm ⟨b, hb⟩ : A) : H))
    (fun a' ha' => (σ ⟨a', ha'⟩).property)
    (fun b hb => (σ.symm ⟨b, hb⟩).property)
    (fun a' ha' => by simp [Subtype.coe_eta, Equiv.symm_apply_apply])
    (fun b hb => by simp [Subtype.coe_eta, Equiv.apply_symm_apply])
    ?_
  intro a' ha'
  simp only [Subtype.coe_eta]
  rw [h_W ⟨a, ha⟩, h_W ⟨a', ha'⟩, h_Γ ⟨a, ha⟩ ⟨a', ha'⟩]

end IDT.QMClosure
