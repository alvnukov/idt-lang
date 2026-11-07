import Proofs.QMClosure.FiniteStochasticCompact
import Proofs.QMClosure.NativeFixedStateFiniteWindow

/-!
# Robust finite windows for bounded stochastic probability models

Fix a finite state type. The exact cardinality-dependent separating window
has a positive uniform error gap over all row-stochastic kernels, probability
initial distributions and `[0,1]` readouts. Separately, every threshold strictly
below `2/9` is exceeded on some finite window uniform over that compact family.

The first gap is only existential and is not identified with `2/9`. The second
window has no effective length bound here. These results concern the stated
fixed finite preparation model contract, not unrestricted classical physics,
finite-data statistics, detector actualization, or completion of QM.
-/

namespace IDT.QMClosure.NativeFixedStateRobustWindow

open FiniteStochasticCompact NativeThreeWireProbabilityDenominator

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The exact `card S + 4` window has a positive, unspecified uniform gap. -/
theorem exists_positive_gap_before_card_add_four :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ parameterFamily S,
      ∃ n : ℕ, n < Fintype.card S + 4 ∧
        δ ≤ ‖modelPrediction S x n - (selectedWeight n : ℂ)‖ := by
  apply exists_positive_window_gap (Fintype.card S + 4) (by omega)
    (fun n => (selectedWeight n : ℂ))
  intro x hx
  simpa only [modelPrediction, NativeFiniteStochasticReadoutWall.prediction] using
    NativeFixedStateFiniteWindow.exists_mismatch_before_card_add_four hx.1
      (fun i => (x.2.1 i : ℂ)) (fun i => (x.2.2 i : ℂ))

/-- Each threshold below `2/9` admits some finite uniform separating window. -/
theorem exists_finite_window_above_threshold (ε : ℝ) (hε : ε < (2 : ℝ) / 9) :
    ∃ N : ℕ, ∀ x ∈ parameterFamily S,
      ∃ n : ℕ, n < N ∧
        ε < ‖modelPrediction S x n - (selectedWeight n : ℂ)‖ := by
  apply exists_finite_threshold_window (fun n => (selectedWeight n : ℂ)) ε
  intro x hx
  by_contra hsep
  push Not at hsep
  have hbound : ∀ n : ℕ,
      ‖NativeFiniteStochasticReadoutWall.prediction x.1
        (fun i => (x.2.1 i : ℂ)) (fun i => (x.2.2 i : ℂ)) n -
        (selectedWeight n : ℂ)‖ ≤ ε := by
    simpa only [modelPrediction, NativeFiniteStochasticReadoutWall.prediction] using hsep
  exact (not_le_of_gt hε)
    (NativeFiniteStochasticReadoutWall.uniform_error_lower_bound hx.1
      (fun i => (x.2.1 i : ℂ)) (fun i => (x.2.2 i : ℂ)) ε hbound)

end IDT.QMClosure.NativeFixedStateRobustWindow
