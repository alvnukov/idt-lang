import Proofs.QMClosure.PositiveColumnConservation
import Proofs.QMClosure.NativeCrossIncrementReadoutSelection

/-!
Checked conditional composition. Positivity, unit calibration and universal
column conservation supply native transfer. A supplied global or eventual
uniform mixed-increment sign then selects the complex norm-square readout.
The native grammar and sign premise retain their independent physical scope.
-/

noncomputable section

namespace IDT.QMClosure.ConservativeCrossIncrementReadout

open NativeInitialHistoryPresentation
open NativeCrossIncrementReadoutSelection CountCrossIncrementRigidity

attribute [local instance] presentationCommRing

theorem readout_eq_norm_of_uniform_mixed_sign
    {W : Presentation → ℝ}
    (hpos : ∀ p, 0 ≤ W p) (hunit : W 1 = 1)
    (hcolumn : ∀ p, W (a * p) + W (b * p) = W p)
    (hs : (∀ n m, 0 ≤ mixed (countGrid W) n m) ∨
      (∀ n m, mixed (countGrid W) n m ≤ 0)) (p : Presentation) :
    W p = Complex.normSq (complexEval p) := by
  exact NativeCrossIncrementReadoutSelection.readout_eq_norm_of_uniform_mixed_sign
    (PositiveColumnConservation.nativeTransfer_of_nonnegative_column_conservation
      W hpos hunit hcolumn) hs p

theorem readout_eq_norm_of_eventual_mixed_sign
    {W : Presentation → ℝ}
    (hpos : ∀ p, 0 ≤ W p) (hunit : W 1 = 1)
    (hcolumn : ∀ p, W (a * p) + W (b * p) = W p)
    (hs : EventuallyNonnegative (mixed (countGrid W)) ∨
      EventuallyNonpositive (mixed (countGrid W))) (p : Presentation) :
    W p = Complex.normSq (complexEval p) := by
  exact NativeCrossIncrementReadoutSelection.readout_eq_norm_of_eventual_mixed_sign
    (PositiveColumnConservation.nativeTransfer_of_nonnegative_column_conservation
      W hpos hunit hcolumn) hs p

end IDT.QMClosure.ConservativeCrossIncrementReadout
