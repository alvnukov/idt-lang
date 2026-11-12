import Proofs.QMClosure.InitialStationaryTriplerCountCalibration
import Proofs.QMClosure.InitialCountHomogeneousReadoutSelection

/-!
The fixed serial tripler gain law remains a supplied mathematical premise.
Its gain nine and the selected numerical response follow from the contract.
-/
namespace IDT.QMClosure.InitialStationaryTriplerSelection

noncomputable section

open TransparentFourthInitialHistoryPresentation
open TransparentFourthInitialNormalForm
open TransparentFourthReflectionEcho
open InitialEchoCoordinates

/-- The accepted base and single fixed-tripler package. -/
abbrev Contract (W : P → ℝ) : Prop :=
  InitialStationaryTriplerCountCalibration.Contract W

variable {W : P → ℝ}

/-- Count calibration supplies the entire natural-gain input to selection. -/
theorem selected (H : Contract W) (p : P) : W p = N p :=
  InitialCountHomogeneousReadoutSelection.selected H.toBaseContract
    (InitialStationaryTriplerCountCalibration.natural_gain H) p

/-- Coordinate norm-square inhabits the supplied fixed-tripler contract. -/
theorem norm_model : Contract N where
  toBaseContract := InitialColumnOrderReadoutCore.norm_model
  tripler := by
    intro p
    have hcoordinate : complexEvaluation (3 : P) = (3 : ℂ) :=
      map_natCast complexEvaluation 3
    have hthree : N (3 : P) = 9 := by
      norm_num [N, InitialCountGeometry.normSq, hcoordinate, Complex.normSq_apply]
    calc
      N ((3 : P) * p) = 9 * N p := by
        have hmul : N ((3 : P) * p) = N (3 : P) * N p :=
          InitialCountGeometry.normSq_mul _ _
        rw [hmul, hthree]
      _ = N (3 : P) * N p := by rw [hthree]

/-- Exactly one numerical response satisfies the supplied contract. -/
theorem exists_unique_response : ∃! W : P → ℝ, Contract W := by
  refine ⟨N, norm_model, ?_⟩
  intro W H
  exact funext (selected H)

/-- Numerical multiplicativity is a consequence of the selected response. -/
theorem multiplicative (H : Contract W) (p r : P) : W (p * r) = W p * W r := by
  rw [selected H, selected H, selected H]
  exact InitialCountGeometry.normSq_mul p r

/-- The numerical square law follows from derived multiplicativity. -/
theorem square_response (H : Contract W) (p : P) : W (p ^ 2) = W p ^ 2 := by
  simpa only [pow_two] using multiplicative H p p

/-- The paired-echo numerical identity follows from mathematical coordinates. -/
theorem paired_echo (H : Contract W) (p : P) : W (p * J p) = W p ^ 2 := by
  change W (echo p) = W p ^ 2
  rw [selected H, selected H, N_echo]

/-- Coordinate-null insertion preserves the selected numerical response. -/
theorem null_insertion (H : Contract W) (p z : P) (hz : E z = 0) :
    W (p + z) = W p := by
  simp only [selected H, N, InitialCountGeometry.normSq, map_add, hz, add_zero]

end
end IDT.QMClosure.InitialStationaryTriplerSelection
