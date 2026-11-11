import Proofs.QMClosure.PositiveColumnConservationCore
import Proofs.QMClosure.NativeGeneratorMixtureReadout

/-!
Conditional native transfer from exact single-column conservation and positive
serial descendants. The universal conclusion retains real scalar order,
arbitrary serial depth and the native equal-fourth-history grammar.
The conditional statements in this module are checked by Lean.
-/

noncomputable section

namespace IDT.QMClosure.PositiveColumnConservation

open NativeInitialHistoryPresentation NativeGeneratorMixtureReadout

attribute [local instance] presentationCommRing

/-- The principal native result needs positivity and conservation only on the
forward serial preparation set containing the preparation under consideration. -/
theorem local_branch_balance
    (W : Presentation → ℝ) (S : Set Presentation)
    (ha : ∀ q ∈ S, a * q ∈ S) (hb : ∀ q ∈ S, b * q ∈ S)
    (hpos : ∀ q ∈ S, 0 ≤ W q)
    (hcons : ∀ q ∈ S, W (a * q) + W (b * q) = W q)
    {p : Presentation} (hp : p ∈ S) :
    W (a * p) = W p / 2 ∧ W (b * p) = W p / 2 :=
  PositiveColumnConservationCore.local_branch_balance
    a b W S ha hb hcons generator_fourth_history hpos hp

/-- Unit calibration adds exactly the unit field of the existing transfer API. -/
theorem nativeTransfer_of_nonnegative_column_conservation
    (W : Presentation → ℝ) (hpos : ∀ p, 0 ≤ W p)
    (hunit : W 1 = 1)
    (hcons : ∀ p, W (a * p) + W (b * p) = W p) : NativeTransfer W := by
  have hbalance (p : Presentation) := local_branch_balance W Set.univ
    (fun _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _)
    (fun q _ => hpos q) (fun q _ => hcons q) (Set.mem_univ p)
  exact ⟨hunit, fun p => (hbalance p).1, fun p => (hbalance p).2⟩

/-- The converse keeps positivity explicitly on both sides of the equivalence.
Native transfer on its own has no positivity field. -/
theorem nonnegative_column_conservation_iff_nativeTransfer
    (W : Presentation → ℝ) :
    ((∀ p, 0 ≤ W p) ∧ W 1 = 1 ∧
      (∀ p, W (a * p) + W (b * p) = W p)) ↔
    ((∀ p, 0 ≤ W p) ∧ NativeTransfer W) := by
  constructor
  · rintro ⟨hpos, hu, hc⟩
    exact ⟨hpos, nativeTransfer_of_nonnegative_column_conservation W hpos hu hc⟩
  · rintro ⟨hpos, L⟩
    refine ⟨hpos, L.unit, ?_⟩
    intro p
    rw [L.left_a, L.left_b]
    ring

/-- Conservation at zero derives the zero reading independently of positivity
and unit calibration. -/
theorem readout_zero_of_column_conservation
    (W : Presentation → ℝ)
    (hcons : ∀ p, W (a * p) + W (b * p) = W p) : W 0 = 0 := by
  have h := hcons 0
  simp only [mul_zero] at h
  linarith

end IDT.QMClosure.PositiveColumnConservation
