import Proofs.QMClosure.OriginalOccurrenceNormSelection
import Proofs.QMClosure.NativeRegularReadoutCountercontrol

/-!
# Finite occurrence-kernel separation for regular native readouts

The existing positive-parameter continuous/faithful native countercontrol
cannot have a finite-order, fixed original-a/b occurrence kernel compatible
with every finite bag. This is a consequence of the universal selector and the
existing checked failure of norm square. It requires no coefficient asymptotics
or differentiability claim. Ambient continuity remains the existing extension
property, with no topology installed on the abstract initial carrier.
-/

namespace IDT.QMClosure.RegularReadoutOccurrenceKernelSeparation

open NativeInitialHistoryPresentation
open NativeGeneratorMixtureReadout
open OriginalOccurrenceKernel
open OriginalOccurrenceNormSelection
open NativeRegularReadoutCountercontrol

theorem counterWeight_no_finite_original_kernel (c : ℝ) (hc : 0 < c) :
    ¬∃ K : ℕ, ∃ κ : Kernel, CompatibleOriginalKernel (counterWeight c) K κ := by
  rintro ⟨K, κ, H⟩
  apply counterWeight_not_norm c hc
  intro p
  exact readout_eq_complex_norm_of_original_kernel (counterWeight_native c) H p

end IDT.QMClosure.RegularReadoutOccurrenceKernelSeparation
