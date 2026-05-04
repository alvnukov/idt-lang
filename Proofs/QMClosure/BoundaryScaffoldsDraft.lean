namespace IDT.QMClosure

/-!
Mechanical draft artifact for phase/action scale boundary discipline.

The point of this scaffold is negative: a calibrated anchor is not a
first-principles derivation merely because it is present and usable.
-/

structure ScaleBoundary where
  calibratedAnchor : Bool
  firstPrinciplesDerivation : Bool
deriving Repr

def calibratedOnlyBoundary : ScaleBoundary :=
  {
    calibratedAnchor := true,
    firstPrinciplesDerivation := false
  }

theorem calibrated_anchor_is_not_first_principles_derivation :
    calibratedOnlyBoundary.calibratedAnchor = true
      /\ calibratedOnlyBoundary.firstPrinciplesDerivation = false := by
  constructor <;> rfl

theorem no_first_principles_derivation_in_calibrated_only_boundary :
    calibratedOnlyBoundary.firstPrinciplesDerivation = false := by
  rfl

end IDT.QMClosure
