import Proofs.QMClosure.NativeAttenuationCircuit

/-!
# Self-reference selection in a supplied native output-profile class

The complex scalar geometry, vacuum action, and both native output profiles are
supplied hypotheses. The four-defect identity selects the supplied native mixer
from this class. It asserts no origin of that geometry or physical readout.
-/

namespace IDT.QMClosure.RawSparseSelfReferenceSelector

noncomputable section

open NativeAttenuationCircuit

abbrev N := NativeMixerEventConeExclusion.mixer

/-- Arbitrary operations with the recorded native profiles and vacuum action. -/
structure Contract where
  operation : (ℂ × ℂ) → (ℂ × ℂ)
  square : ∀ p, operation (operation p) = p.swap
  vacuum_right : ∀ x, operation (x, 0) = N (x, 0)
  vacuum_left : ∀ x, operation (0, x) = N (0, x)
  profile_fst : ∀ p, Complex.normSq (operation p).1 = Complex.normSq (N p).1
  profile_snd : ∀ p, Complex.normSq (operation p).2 = Complex.normSq (N p).2

def m (D : Contract) (x y : ℂ) : ℂ := (D.operation (x, y)).1
def A (D : Contract) (x : ℂ) : ℂ := (D.operation (x, 0)).1
def B (D : Contract) (x : ℂ) : ℂ := (D.operation (x, 0)).2

def defect (D : Contract) (x y z : ℂ) : ℝ :=
  Complex.normSq (m D (D.operation (x, y)).1 (A D z)) +
    Complex.normSq (m D (D.operation (x, y)).2 (B D z)) -
    Complex.normSq (m D x z) - Complex.normSq (A D y)

def selfDefect (D : Contract) (p : ℂ × ℂ) : ℝ :=
  defect D p.1 p.2 (A D p.1)

def outputError (D : Contract) (p : ℂ × ℂ) : ℝ :=
  Complex.normSq ((D.operation p).1 - (N p).1) +
    Complex.normSq ((D.operation p).2 - (N p).2)

theorem operation_swap (D : Contract) (p : ℂ × ℂ) :
    D.operation p.swap = (D.operation p).swap := by
  rw [← D.square p, D.square (D.operation p)]

theorem A_native (D : Contract) (x : ℂ) : A D x = a * x := by
  simp [A, D.vacuum_right, mixer_fst]

theorem B_native (D : Contract) (x : ℂ) : B D x = b * x := by
  simp [B, D.vacuum_right, mixer_snd]

theorem m_profile (D : Contract) (x y : ℂ) :
    Complex.normSq (m D x y) = Complex.normSq (a * x + b * y) := by
  simpa only [m, mixer_fst] using D.profile_fst (x, y)

theorem defect_native_formula (D : Contract) (x y z : ℂ) :
    defect D x y z =
      Complex.normSq (a * (D.operation (x, y)).1 + b * (a * z)) +
        Complex.normSq (a * (D.operation (x, y)).2 + b * (b * z)) -
        Complex.normSq (a * x + b * z) - Complex.normSq (a * y) := by
  simp only [defect, m_profile, A_native, B_native]

/-- Four actual self-tests give an exact squared distance to the native mixer. -/
theorem four_defect_identity (D : Contract) (p : ℂ × ℂ) :
    selfDefect D p + selfDefect D p.swap + selfDefect D (D.operation p) +
      selfDefect D (D.operation p).swap = -outputError D p / 2 := by
  rcases p with ⟨x, y⟩
  have hs : D.operation (y, x) =
      ((D.operation (x, y)).2, (D.operation (x, y)).1) := operation_swap D (x, y)
  simp only [selfDefect, A_native, defect_native_formula, Prod.swap_prod_mk,
    Prod.mk.eta, operation_swap, D.square, outputError, mixer_fst, mixer_snd, hs]
  norm_num [a, b, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]
  ring

theorem outputError_nonnegative (D : Contract) (p : ℂ × ℂ) :
    0 ≤ outputError D p :=
  add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

theorem error_zero_iff_operation_eq_at (D : Contract) (p : ℂ × ℂ) :
    outputError D p = 0 ↔ D.operation p = N p := by
  constructor
  · intro h
    have h1 := Complex.normSq_nonneg ((D.operation p).1 - (N p).1)
    have h2 := Complex.normSq_nonneg ((D.operation p).2 - (N p).2)
    have he1 : Complex.normSq ((D.operation p).1 - (N p).1) = 0 := by
      unfold outputError at h
      linarith
    have he2 : Complex.normSq ((D.operation p).2 - (N p).2) = 0 := by
      unfold outputError at h
      linarith
    apply Prod.ext
    · exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp he1)
    · exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp he2)
  · intro h
    simp [outputError, h]

/-- Independent bounds at the four tested inputs control the local error. -/
theorem outputError_le_of_four_bounds (D : Contract) (p : ℂ × ℂ)
    (ε₁ ε₂ ε₃ ε₄ : ℝ)
    (h₁ : -ε₁ ≤ selfDefect D p)
    (h₂ : -ε₂ ≤ selfDefect D p.swap)
    (h₃ : -ε₃ ≤ selfDefect D (D.operation p))
    (h₄ : -ε₄ ≤ selfDefect D (D.operation p).swap) :
    outputError D p ≤ 2 * (ε₁ + ε₂ + ε₃ + ε₄) := by
  have hi := four_defect_identity D p
  linarith

theorem outputError_le_of_uniform_self_bound (D : Contract) (ε : ℝ)
    (h : ∀ p, -ε ≤ selfDefect D p) (p : ℂ × ℂ) :
    outputError D p ≤ 8 * ε := by
  have hb := outputError_le_of_four_bounds D p ε ε ε ε
    (h p) (h p.swap) (h (D.operation p)) (h (D.operation p).swap)
  linarith

theorem operation_eq_native_of_self_nonnegative (D : Contract)
    (h : ∀ p, 0 ≤ selfDefect D p) : D.operation = N := by
  funext p
  apply (error_zero_iff_operation_eq_at D p).mp
  have hi := four_defect_identity D p
  have h0 := outputError_nonnegative D p
  have h1 := h p
  have h2 := h p.swap
  have h3 := h (D.operation p)
  have h4 := h (D.operation p).swap
  linarith

theorem operation_eq_native_of_self_zero (D : Contract)
    (h : ∀ p, selfDefect D p = 0) : D.operation = N :=
  operation_eq_native_of_self_nonnegative D (fun p => le_of_eq (h p).symm)

theorem negative_selfDefect_of_positive_error (D : Contract) (p : ℂ × ℂ)
    (h : 0 < outputError D p) :
    selfDefect D p < 0 ∨ selfDefect D p.swap < 0 ∨
      selfDefect D (D.operation p) < 0 ∨ selfDefect D (D.operation p).swap < 0 := by
  have hi := four_defect_identity D p
  by_contra hn
  push Not at hn
  rcases hn with ⟨h1, h2, h3, h4⟩
  linarith

def SparseLaw (D : Contract) : Prop := ∀ x y z, defect D x y z = 0
def SelfLaw (D : Contract) : Prop := ∀ p, selfDefect D p = 0

theorem sparseLaw_of_operation_eq_native (D : Contract) (h : D.operation = N) :
    SparseLaw D := by
  intro x y z
  rw [defect_native_formula, h]
  norm_num [mixer_fst, mixer_snd, a, b, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

theorem sparseLaw_iff_selfLaw (D : Contract) : SparseLaw D ↔ SelfLaw D := by
  constructor
  · intro h p
    exact h p.1 p.2 (A D p.1)
  · intro h
    exact sparseLaw_of_operation_eq_native D (operation_eq_native_of_self_zero D h)

theorem selfLaw_iff_operation_eq_native (D : Contract) :
    SelfLaw D ↔ D.operation = N := by
  constructor
  · exact operation_eq_native_of_self_zero D
  · intro h p
    exact sparseLaw_of_operation_eq_native D h p.1 p.2 (A D p.1)

theorem sparseLaw_iff_operation_eq_native (D : Contract) :
    SparseLaw D ↔ D.operation = N :=
  (sparseLaw_iff_selfLaw D).trans (selfLaw_iff_operation_eq_native D)

/-- The supplied native mixer inhabits the recorded class. -/
def nativeContract : Contract where
  operation := N
  square := NativeMixerEventConeExclusion.mixer_square
  vacuum_right _ := rfl
  vacuum_left _ := rfl
  profile_fst _ := rfl
  profile_snd _ := rfl

theorem native_sparseLaw : SparseLaw nativeContract :=
  sparseLaw_of_operation_eq_native nativeContract rfl

end

end IDT.QMClosure.RawSparseSelfReferenceSelector
