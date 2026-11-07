import Proofs.QMClosure.CompositeProductKernel
import Proofs.QMClosure.CompositionExchangeScope

namespace IDT.QMClosure.PairExchangeCombinations

open QuadraticRecordRefinement PositiveQuadraticPolarization QuadraticHermitianKernel

noncomputable section

/-!
Conditional raw pair combinations on a supplied additive carrier. The original
map p retains the universal product-readout law; the new plus/minus maps need
not retain that law. No tensor type, halves, scalar normalization, global
exchange operator, direct sum, or exhaustion is supplied. Pair images need not
be subgroups, and semidefinite null intersections can be nonzero.

Physical availability of products, sums and coherent repeated inputs, exchange
signs and species, spin-statistics, pair-creation probabilities and applicability
to matter remain open. These formulas are not a particle-statistics derivation.
The closed-span Hilbert exchange extension is outside this artifact's scope.
-/

variable {A C : Type*} [AddCommGroup A] [AddCommGroup C]

def plusPair (p : A → A → C) (x y : A) : C := p x y + p y x

def minusPair (p : A → A → C) (x y : A) : C := p x y - p y x

omit [AddCommGroup A] in
theorem plus_exchange (p : A → A → C) (x y : A) :
    plusPair p y x = plusPair p x y := add_comm _ _

omit [AddCommGroup A] in
theorem minus_exchange (p : A → A → C) (x y : A) :
    minusPair p y x = -minusPair p x y := by simp only [minusPair, neg_sub]

omit [AddCommGroup A] in
theorem minus_diagonal (p : A → A → C) (x : A) : minusPair p x x = 0 :=
  sub_self _

omit [AddCommGroup A] in
theorem plus_add_minus (p : A → A → C) (x y : A) :
    plusPair p x y + minusPair p x y = (2 : ℕ) • p x y := by
  simp only [plusPair, minusPair, two_nsmul]
  abel

section AdditivePhase

variable {QA : A → ℝ} {QC : C → ℝ}
    (jA : QuadraticPhase QA) (jC : QuadraticPhase QC) (p : A → A → C)
    (addA : ∀ x x' y, p (x + x') y = p x y + p x' y)
    (addB : ∀ x y y', p x (y + y') = p x y + p x y')
    (phaseA : ∀ x y, p (jA.J x) y = jC.J (p x y))
    (phaseB : ∀ x y, p x (jA.J y) = jC.J (p x y))

include addA addB in
theorem plus_add_left (x x' y : A) :
    plusPair p (x + x') y = plusPair p x y + plusPair p x' y := by
  simp only [plusPair, addA, addB]
  abel

include addA addB in
theorem plus_add_right (x y y' : A) :
    plusPair p x (y + y') = plusPair p x y + plusPair p x y' := by
  simp only [plusPair, addA, addB]
  abel

include addA addB in
theorem minus_add_left (x x' y : A) :
    minusPair p (x + x') y = minusPair p x y + minusPair p x' y := by
  simp only [minusPair, addA, addB]
  abel

include addA addB in
theorem minus_add_right (x y y' : A) :
    minusPair p x (y + y') = minusPair p x y + minusPair p x y' := by
  simp only [minusPair, addA, addB]
  abel

include phaseA phaseB in
theorem plus_phase_left (x y : A) :
    plusPair p (jA.J x) y = jC.J (plusPair p x y) := by
  simp only [plusPair, phaseA, phaseB, map_add]

include phaseA phaseB in
theorem plus_phase_right (x y : A) :
    plusPair p x (jA.J y) = jC.J (plusPair p x y) := by
  simp only [plusPair, phaseA, phaseB, map_add]

include phaseA phaseB in
theorem minus_phase_left (x y : A) :
    minusPair p (jA.J x) y = jC.J (minusPair p x y) := by
  simp only [minusPair, phaseA, phaseB, map_sub]

include phaseA phaseB in
theorem minus_phase_right (x y : A) :
    minusPair p x (jA.J y) = jC.J (minusPair p x y) := by
  simp only [minusPair, phaseA, phaseB, map_sub]

end AdditivePhase

section KernelSubtraction

variable {V : Type*} [AddCommGroup V] {Q : V → ℝ}
    (h : PositiveQuadratic Q) (j : QuadraticPhase Q)

include h in
theorem kernel_sub_left (u v z : V) :
    kernel j (u - v) z = kernel j u z - kernel j v z := by
  have he := QuadraticHermitianKernel.add_left h j (u - v) v z
  rw [sub_add_cancel] at he
  exact eq_sub_of_add_eq he.symm

include h in
theorem kernel_sub_right (u v z : V) :
    kernel j u (v - z) = kernel j u v - kernel j u z := by
  have he := QuadraticHermitianKernel.add_right h j u (v - z) z
  rw [sub_add_cancel] at he
  exact eq_sub_of_add_eq he.symm

end KernelSubtraction

section ProductBridge

variable {QA : A → ℝ} {QC : C → ℝ}
    (hA : PositiveQuadratic QA) (hC : PositiveQuadratic QC)
    (jA : QuadraticPhase QA) (jC : QuadraticPhase QC) (p : A → A → C)
    (addA : ∀ x x' y, p (x + x') y = p x y + p x' y)
    (addB : ∀ x y y', p x (y + y') = p x y + p x y')
    (phaseA : ∀ x y, p (jA.J x) y = jC.J (p x y))
    (phaseB : ∀ x y, p x (jA.J y) = jC.J (p x y))
    (factor : ∀ x y, QC (p x y) = QA x * QA y)

include hA hC jA jC p addA addB phaseA phaseB factor

theorem plus_kernel (x y x' y' : A) :
    kernel jC (plusPair p x y) (plusPair p x' y') =
      2 * (kernel jA x x' * kernel jA y y' + kernel jA x y' * kernel jA y x') := by
  simp only [plusPair, QuadraticHermitianKernel.add_left hC,
    QuadraticHermitianKernel.add_right hC,
    CompositeProductKernel.product_kernel hA hC jA jA jC p addA addB phaseA phaseB factor]
  ring

theorem minus_kernel (x y x' y' : A) :
    kernel jC (minusPair p x y) (minusPair p x' y') =
      2 * (kernel jA x x' * kernel jA y y' - kernel jA x y' * kernel jA y x') := by
  simp only [minusPair, kernel_sub_left hC, kernel_sub_right hC,
    CompositeProductKernel.product_kernel hA hC jA jA jC p addA addB phaseA phaseB factor]
  ring

theorem mixed_kernel (x y x' y' : A) :
    kernel jC (plusPair p x y) (minusPair p x' y') = 0 := by
  simp only [plusPair, minusPair, QuadraticHermitianKernel.add_left hC,
    kernel_sub_right hC,
    CompositeProductKernel.product_kernel hA hC jA jA jC p addA addB phaseA phaseB factor]
  ring

theorem cross_polarization (x y : A) :
    polarization QC (p x y) (p y x) = Complex.normSq (kernel jA x y) := by
  calc
    polarization QC (p x y) (p y x) = (kernel jC (p x y) (p y x)).re :=
      (kernel_re jC _ _).symm
    _ = Complex.normSq (kernel jA x y) := by
      rw [CompositeProductKernel.product_kernel hA hC jA jA jC p
        addA addB phaseA phaseB factor x y y x,
        ← QuadraticHermitianKernel.hermitian hA jA y x]
      simp [Complex.mul_re, Complex.normSq_apply]

theorem plus_readout (x y : A) : QC (plusPair p x y) =
    2 * QA x * QA y + 2 * Complex.normSq (kernel jA x y) := by
  rw [plusPair, sum_expansion (Q := QC), factor, factor,
    cross_polarization hA hC jA jC p addA addB phaseA phaseB factor]
  ring

theorem minus_readout (x y : A) : QC (minusPair p x y) =
    2 * QA x * QA y - 2 * Complex.normSq (kernel jA x y) := by
  have he := hC.parallelogram (p x y) (p y x)
  change QC (plusPair p x y) + QC (minusPair p x y) =
    2 * QC (p x y) + 2 * QC (p y x) at he
  rw [plus_readout hA hC jA jC p addA addB phaseA phaseB factor, factor, factor] at he
  nlinarith

theorem plus_diagonal_readout (x : A) : QC (plusPair p x x) = 4 * (QA x)^2 := by
  rw [plus_readout hA hC jA jC p addA addB phaseA phaseB factor,
    QuadraticHermitianKernel.diagonal hA, Complex.normSq_ofReal]
  ring

theorem sum_readouts (x y : A) :
    QC (plusPair p x y) + QC (minusPair p x y) = 4 * QA x * QA y := by
  rw [plus_readout hA hC jA jC p addA addB phaseA phaseB factor,
    minus_readout hA hC jA jC p addA addB phaseA phaseB factor]
  ring

/-- This proves conditional nontriviality at an orthogonal positive pair,
not nontriviality for every supplied source or composition map. -/
theorem minus_positive_of_orthogonal (x y : A) (positive_x : 0 < QA x)
    (positive_y : 0 < QA y) (orthogonal : kernel jA x y = 0) :
    0 < QC (minusPair p x y) := by
  rw [minus_readout hA hC jA jC p addA addB phaseA phaseB factor,
    orthogonal, Complex.normSq_zero, mul_zero, sub_zero]
  exact mul_pos (mul_pos (by norm_num) positive_x) positive_y

end ProductBridge

omit [AddCommGroup A] in
theorem plus_nonnegative {QC : C → ℝ} (hC : PositiveQuadratic QC)
    (p : A → A → C) (x y : A) : 0 ≤ QC (plusPair p x y) := hC.nonnegative _

omit [AddCommGroup A] in
theorem minus_nonnegative {QC : C → ℝ} (hC : PositiveQuadratic QC)
    (p : A → A → C) (x y : A) : 0 ≤ QC (minusPair p x y) := hC.nonnegative _

/-- A fixed nontrivial scalar control can have identically zero minus pairs. -/
theorem scalar_control_minus_zero (x y : ℂ) :
    minusPair CompositionExchangeScope.ComplexMultiplicationControl.product x y = 0 := by
  simp only [minusPair, CompositionExchangeScope.ComplexMultiplicationControl.product]
  rw [mul_comm y x, sub_self]

end

end IDT.QMClosure.PairExchangeCombinations
