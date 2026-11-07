import Proofs.QMClosure.CompositeProductKernel
import Proofs.QMClosure.CompositeProductControls

namespace IDT.QMClosure.CompositionExchangeScope

open QuadraticRecordRefinement QuadraticHermitianKernel

noncomputable section

/-!
Scope tests for the universal product-readout bridge. These are conditional
mathematical statements about supplied composition maps. They do not provide a
particle grammar, identify mode permutations with tensor-factor or particle
exchange, or assess physical indistinguishability, Bose condensation, matter
regimes, or spin-statistics. A readout-null difference is used only for the
supplied quadratic readout and its reconstructed kernel; interpreting it as
physical observational equivalence requires a separate bridge.
The exchange obstruction uses universal factorization with the full additive
and phase hypotheses. It does not exclude symmetric or exterior compositions
that factorize only on an explicitly restricted class, such as orthogonal
inputs, or nonlinear normalized products.
-/

section DiagonalObstruction

variable {X C : Type*} (Q : X → ℝ) (W : C → ℝ) (chosenZero : C)
    (zero_readout : W chosenZero = 0) (p : X → X → C)
    (factor : ∀ x y, W (p x y) = Q x * Q y)

include zero_readout factor

/-- No additive, phase, or complex structure is needed for this obstruction. -/
theorem source_zero_of_diagonal_zero (x : X) (diagonal_zero : p x x = chosenZero) :
    Q x = 0 := by
  have hs : Q x * Q x = 0 := by
    rw [← factor x x, diagonal_zero, zero_readout]
  rcases mul_eq_zero.mp hs with h | h <;> exact h

theorem all_source_zero_of_diagonal_zero
    (diagonal_zero : ∀ x, p x x = chosenZero) : ∀ x, Q x = 0 := by
  intro x
  exact source_zero_of_diagonal_zero Q W chosenZero zero_readout p factor x
    (diagonal_zero x)

theorem positive_source_excludes_diagonal_zero (x : X) (positive : 0 < Q x) :
    p x x ≠ chosenZero := by
  intro hz
  have h := source_zero_of_diagonal_zero Q W chosenZero zero_readout p factor x hz
  linarith

theorem positive_source_excludes_universal_diagonal_zero
    (positive : ∃ x, 0 < Q x) : ¬ ∀ x, p x x = chosenZero := by
  intro hz
  obtain ⟨x, hx⟩ := positive
  exact positive_source_excludes_diagonal_zero Q W chosenZero zero_readout p factor
    x hx (hz x)

end DiagonalObstruction

section ExchangeObstruction

variable {A C : Type*} [AddCommGroup A] [AddCommGroup C]
    {QA : A → ℝ} {QC : C → ℝ}
    (hA : PositiveQuadratic QA) (hC : PositiveQuadratic QC)
    (jA : QuadraticPhase QA) (jC : QuadraticPhase QC)
    (p : A → A → C)
    (addA : ∀ x x' y, p (x + x') y = p x y + p x' y)
    (addB : ∀ x y y', p x (y + y') = p x y + p x y')
    (phaseA : ∀ x y, p (jA.J x) y = jC.J (p x y))
    (phaseB : ∀ x y, p x (jA.J y) = jC.J (p x y))
    (factor : ∀ x y, QC (p x y) = QA x * QA y)

include hA hC jC addA addB phaseA phaseB factor

/-- Readout-null exchange difference forces saturation of the source kernel
bound at this pair, under every hypothesis of the supplied product bridge. -/
theorem normSq_kernel_eq_of_null_exchange_difference (x y : A)
    (exchange_null : QC (p x y - p y x) = 0) :
    Complex.normSq (kernel jA x y) = QA x * QA y := by
  have he : p y x + (p x y - p y x) = p x y := by abel
  have hk := CompositeProductKernel.null_translate_right hC jC
    (p x y) (p y x) (p x y - p y x) exchange_null
  rw [he] at hk
  have hp : ((QA x * QA y : ℝ) : ℂ) = kernel jA x y * kernel jA y x := by
    calc
      ((QA x * QA y : ℝ) : ℂ) = kernel jC (p x y) (p x y) := by
        rw [QuadraticHermitianKernel.diagonal hC, factor]
      _ = kernel jC (p x y) (p y x) := hk
      _ = kernel jA x y * kernel jA y x :=
        CompositeProductKernel.product_kernel hA hC jA jA jC p
          addA addB phaseA phaseB factor x y y x
  have hr : (kernel jA x y * kernel jA y x).re =
      Complex.normSq (kernel jA x y) := by
    rw [← QuadraticHermitianKernel.hermitian hA jA y x]
    simp [Complex.mul_re, Complex.normSq_apply]
  have hp_re := congrArg Complex.re hp
  simpa only [Complex.ofReal_re, hr] using hp_re.symm

/-- Literal exchange equality is a special case of readout-null difference. -/
theorem normSq_kernel_eq_of_exchange_eq (x y : A) (exchange_eq : p x y = p y x) :
    Complex.normSq (kernel jA x y) = QA x * QA y := by
  apply normSq_kernel_eq_of_null_exchange_difference hA hC jA jC p
    addA addB phaseA phaseB factor x y
  rw [exchange_eq, sub_self, hC.zero]

/-- A positive-weight orthogonal pair excludes even readout-null exchange
identification for a composition satisfying this universal factor bridge. -/
theorem positive_orthogonal_excludes_null_exchange_difference (x y : A)
    (positive_x : 0 < QA x) (positive_y : 0 < QA y)
    (orthogonal : kernel jA x y = 0) : QC (p x y - p y x) ≠ 0 := by
  intro hn
  have he := normSq_kernel_eq_of_null_exchange_difference hA hC jA jC p
    addA addB phaseA phaseB factor x y hn
  rw [orthogonal, Complex.normSq_zero] at he
  exact (ne_of_gt (mul_pos positive_x positive_y)) he.symm

theorem positive_orthogonal_excludes_exchange_eq (x y : A)
    (positive_x : 0 < QA x) (positive_y : 0 < QA y)
    (orthogonal : kernel jA x y = 0) : p x y ≠ p y x := by
  intro he
  apply positive_orthogonal_excludes_null_exchange_difference hA hC jA jC p
    addA addB phaseA phaseB factor x y positive_x positive_y orthogonal
  rw [he, sub_self, hC.zero]

end ExchangeObstruction

namespace ComplexMultiplicationControl

/- A fixed mathematical consistency control. It establishes that symmetric
factorizing composition can exist; no dimension classification is claimed. -/

def product (z w : ℂ) : ℂ := z * w

abbrev standardPhase := CompositeProductControls.ConjugateSlot.standardPhase

theorem norm_positiveQuadratic : PositiveQuadratic (Complex.normSq : ℂ → ℝ) :=
  CompositeProductControls.ConjugateSlot.norm_positiveQuadratic

theorem additive_left (x x' y : ℂ) :
    product (x + x') y = product x y + product x' y := by
  exact add_mul x x' y

theorem additive_right (x y y' : ℂ) :
    product x (y + y') = product x y + product x y' := by
  exact mul_add x y y'

theorem phase_left (x y : ℂ) :
    product (standardPhase.J x) y = standardPhase.J (product x y) := by
  change (Complex.I * x) * y = Complex.I * (x * y)
  ring

theorem phase_right (x y : ℂ) :
    product x (standardPhase.J y) = standardPhase.J (product x y) := by
  change x * (Complex.I * y) = Complex.I * (x * y)
  ring

theorem factor (x y : ℂ) :
    Complex.normSq (product x y) = Complex.normSq x * Complex.normSq y :=
  Complex.normSq_mul x y

theorem symmetric (x y : ℂ) : product x y = product y x := mul_comm x y

theorem positive_reference : 0 < Complex.normSq (1 : ℂ) := by norm_num

/-- All premises used in the symmetric scope test hold simultaneously in a
nonzero fixed control. Thus the obstruction does not reject every symmetric
factorizing composition. -/
theorem nontrivial_symmetric_factorizing_control :
    PositiveQuadratic (Complex.normSq : ℂ → ℝ) ∧
    (∀ x x' y, product (x + x') y = product x y + product x' y) ∧
    (∀ x y y', product x (y + y') = product x y + product x y') ∧
    (∀ x y, product (standardPhase.J x) y = standardPhase.J (product x y)) ∧
    (∀ x y, product x (standardPhase.J y) = standardPhase.J (product x y)) ∧
    (∀ x y, Complex.normSq (product x y) = Complex.normSq x * Complex.normSq y) ∧
    (∀ x y, product x y = product y x) ∧
    0 < Complex.normSq (1 : ℂ) := by
  exact ⟨norm_positiveQuadratic, additive_left, additive_right, phase_left,
    phase_right, factor, symmetric, positive_reference⟩

end ComplexMultiplicationControl

end

end IDT.QMClosure.CompositionExchangeScope
