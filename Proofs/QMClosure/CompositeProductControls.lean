import Proofs.QMClosure.MixerRecordNaturality
import Proofs.QMClosure.QuadraticHermitianKernel

namespace IDT.QMClosure.CompositeProductControls

noncomputable section

/-!
Fixed mathematical countermodels on supplied complex coordinate spaces. Complex
scalars here are controls, not reconstructed physical preparation primitives.
These results neither upgrade manifest status nor derive physical composition,
probabilities, entangled preparation availability, monoidal coherence, Bell, or
full QM. The three controls distinguish separate phase compatibility, full
product factorization, and normalization of raw mixer signs.
-/

namespace ConjugateSlot

def product (z w : ℂ) : ℂ := z * star w

def hermitian (z w : ℂ) : ℂ := star z * w

def standardPhase : QuadraticHermitianKernel.QuadraticPhase
    (Complex.normSq : ℂ → ℝ) where
  J :=
    { toFun := fun z => Complex.I * z
      map_zero' := by simp
      map_add' := by intro x y; exact mul_add _ _ _ }
  square := by
    intro z
    change Complex.I * (Complex.I * z) = -z
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  preserves := by
    intro z
    change Complex.normSq (Complex.I * z) = Complex.normSq z
    rw [Complex.normSq_mul]
    simp

theorem norm_positiveQuadratic :
    QuadraticRecordRefinement.PositiveQuadratic (Complex.normSq : ℂ → ℝ) :=
  MixerRecordNaturality.Controls.complex_norm_positive_quadratic

/-- The control uses precisely the reconstructed kernel and orientation. -/
theorem reconstructed_kernel_eq (z w : ℂ) :
    QuadraticHermitianKernel.kernel standardPhase z w = hermitian z w := by
  apply Complex.ext <;>
    simp [QuadraticHermitianKernel.kernel, standardPhase,
      PositiveQuadraticPolarization.polarization, Complex.normSq_apply,
      hermitian, Complex.mul_re, Complex.mul_im] <;> ring

theorem additive_left (x x' y : ℂ) :
    product (x + x') y = product x y + product x' y := by
  simp [product, add_mul]

theorem additive_right (x y y' : ℂ) :
    product x (y + y') = product x y + product x y' := by
  simp [product, mul_add]

theorem multiplicative_norm (x y : ℂ) :
    Complex.normSq (product x y) = Complex.normSq x * Complex.normSq y := by
  simp [product, Complex.normSq_mul]

theorem phase_left (x y : ℂ) :
    product (Complex.I * x) y = Complex.I * product x y := by
  simp [product, mul_assoc]

theorem phase_right_reversed (x y : ℂ) :
    product x (Complex.I * y) = -Complex.I * product x y := by
  simp [product, mul_left_comm]

theorem common_phase_right_fails :
    product 1 (Complex.I * 1) ≠ Complex.I * product 1 1 := by
  intro h
  have hi := congrArg Complex.im h
  norm_num [product] at hi

theorem output_kernel_value :
    hermitian (product 1 1) (product 1 Complex.I) = -Complex.I := by
  simp [hermitian, product]

theorem factor_kernel_value :
    hermitian 1 1 * hermitian 1 Complex.I = Complex.I := by
  simp [hermitian]

theorem kernel_factorization_fails :
    hermitian (product 1 1) (product 1 Complex.I) ≠
      hermitian 1 1 * hermitian 1 Complex.I := by
  rw [output_kernel_value, factor_kernel_value]
  intro h
  have hi := congrArg Complex.im h
  norm_num at hi

theorem reconstructed_kernel_factorization_fails :
    QuadraticHermitianKernel.kernel standardPhase (product 1 1) (product 1 Complex.I) ≠
      QuadraticHermitianKernel.kernel standardPhase 1 1 *
        QuadraticHermitianKernel.kernel standardPhase 1 Complex.I := by
  simpa only [reconstructed_kernel_eq] using kernel_factorization_fails

end ConjugateSlot

namespace ReferenceSlices

abbrev C2 := ℂ × ℂ
abbrev C4 := (ℂ × ℂ) × (ℂ × ℂ)

def norm2 (x : C2) : ℝ := Complex.normSq x.1 + Complex.normSq x.2

def norm4 (z : C4) : ℝ :=
  Complex.normSq z.1.1 + Complex.normSq z.1.2 +
    Complex.normSq z.2.1 + Complex.normSq z.2.2

/-- Coordinate order is 00, 01, 10, 11. The fixed 3/5, 4/5 pair
preserves every basis-product norm while introducing an off-axis overlap. -/
def product (x y : C2) : C4 :=
  ((x.1 * y.1 + (3 / 5 : ℂ) * x.2 * y.2, x.1 * y.2),
    (x.2 * y.1, (4 / 5 : ℂ) * x.2 * y.2))

def e0 : C2 := (1, 0)
def e1 : C2 := (0, 1)

theorem additive_left (x x' y : C2) :
    product (x + x') y = product x y + product x' y := by
  apply Prod.ext <;> apply Prod.ext <;> dsimp [product] <;> ring

theorem additive_right (x y y' : C2) :
    product x (y + y') = product x y + product x y' := by
  apply Prod.ext <;> apply Prod.ext <;> dsimp [product] <;> ring

theorem scalar_left (a : ℂ) (x y : C2) :
    product (a • x) y = a • product x y := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [product, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem scalar_right (a : ℂ) (x y : C2) :
    product x (a • y) = a • product x y := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [product, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem common_phase_left (x y : C2) :
    product (Complex.I • x) y = Complex.I • product x y := scalar_left _ _ _

theorem common_phase_right (x y : C2) :
    product x (Complex.I • y) = Complex.I • product x y := scalar_right _ _ _

theorem basis_product_norms :
    norm4 (product e0 e0) = 1 ∧ norm4 (product e0 e1) = 1 ∧
      norm4 (product e1 e0) = 1 ∧ norm4 (product e1 e1) = 1 := by
  norm_num [norm4, product, e0, e1, Complex.normSq_apply,
    Complex.div_re, Complex.div_im]

/-- Universal reference-slice statements, not just tests at basis points. -/
theorem full_left_reference_slice (x : C2) :
    norm4 (product x e0) = norm2 x * norm2 e0 := by
  simp [norm4, norm2, product, e0]

theorem full_right_reference_slice (y : C2) :
    norm4 (product e0 y) = norm2 e0 * norm2 y := by
  simp [norm4, norm2, product, e0]

theorem off_axis_value : norm4 (product (1, 1) (1, 1)) = 26 / 5 := by
  norm_num [norm4, product, Complex.normSq_apply, Complex.div_re, Complex.div_im]

theorem off_axis_factor_value : norm2 (1, 1) * norm2 (1, 1) = 4 := by
  norm_num [norm2]

theorem full_factorization_fails :
    ¬ ∀ x y, norm4 (product x y) = norm2 x * norm2 y := by
  intro h
  have hh := h (1, 1) (1, 1)
  rw [off_axis_value, off_axis_factor_value] at hh
  norm_num at hh

end ReferenceSlices

namespace RawSign

def n (x y : ℂ) : ℂ := ((1 + Complex.I) * x + (1 - Complex.I) * y) / 2

def N (p : ℂ × ℂ) : ℂ × ℂ := (n p.1 p.2, n p.2 p.1)

def rawB (p : ℂ × ℂ) : ℂ × ℂ := -N p

def mB (x y : ℂ) : ℂ := -n x y

def diagonalB (x : ℂ) : ℂ := mB x x

theorem n_re (x y : ℂ) :
    (n x y).re = (x.re - x.im + y.re + y.im) / 2 := by
  norm_num [n, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
  ring

theorem n_im (x y : ℂ) :
    (n x y).im = (x.re + x.im - y.re + y.im) / 2 := by
  norm_num [n, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
  ring

theorem n_diagonal (x : ℂ) : n x x = x := by
  apply Complex.ext <;> simp only [n_re, n_im] <;> ring

theorem n_neg (x y : ℂ) : n (-x) (-y) = -n x y := by
  simp only [n, mul_neg, ← neg_add, neg_div]

theorem N_neg (p : ℂ × ℂ) : N (-p) = -N p := by
  apply Prod.ext <;> exact n_neg _ _

theorem N_square (p : ℂ × ℂ) : N (N p) = p.swap := by
  apply Prod.ext <;> apply Complex.ext <;>
    simp only [N, Prod.fst_swap, Prod.snd_swap, n_re, n_im] <;> ring

theorem rawB_square (p : ℂ × ℂ) : rawB (rawB p) = p.swap := by
  simp only [rawB, N_neg, neg_neg, N_square]

theorem first_channel_medial (x y z w : ℂ) :
    n (n x y) (n z w) = n (n x z) (n y w) := by
  apply Complex.ext <;> simp only [n_re, n_im] <;> ring

theorem rawB_first_channel_medial (x y z w : ℂ) :
    mB (mB x y) (mB z w) = mB (mB x z) (mB y w) := by
  simp only [mB, n_neg, neg_neg, first_channel_medial]

theorem norm_conservation (p : ℂ × ℂ) :
    Complex.normSq (N p).1 + Complex.normSq (N p).2 =
      Complex.normSq p.1 + Complex.normSq p.2 := by
  simp only [N, Complex.normSq_apply, n_re, n_im]
  ring

theorem rawB_norm_conservation (p : ℂ × ℂ) :
    Complex.normSq (rawB p).1 + Complex.normSq (rawB p).2 =
      Complex.normSq p.1 + Complex.normSq p.2 := by
  simpa only [rawB, Prod.fst_neg, Prod.snd_neg, Complex.normSq_neg] using
    norm_conservation p

theorem diagonalB_eq_neg (x : ℂ) : diagonalB x = -x := by
  simp [diagonalB, mB, n_diagonal]

theorem normalized_rawB (x y : ℂ) : diagonalB (mB x y) = n x y := by
  simp [diagonalB_eq_neg, mB]

def product (x y : ℂ) : ℂ := x * y

theorem normalized_naturality_left (x x' y : ℂ) :
    product (n x x') y = n (product x y) (product x' y) := by
  dsimp [product, n]
  ring

theorem normalized_naturality_right (x y y' : ℂ) :
    product x (n y y') = n (product x y) (product x y') := by
  dsimp [product, n]
  ring

theorem normalized_rawB_naturality_right (x y y' : ℂ) :
    product x (diagonalB (mB y y')) = n (product x y) (product x y') := by
  rw [normalized_rawB]
  exact normalized_naturality_right _ _ _

theorem rawB_left_value : product 1 (mB 1 1) = -1 := by
  simp [product, mB, n_diagonal]

theorem rawB_right_value : n (product 1 1) (product 1 1) = 1 := by
  simp [product, n_diagonal]

/-- With raw A=C=N and raw B=-N, the raw second-slot intertwining law
fails although both normalized first-channel laws above hold. Consequently
raw naturality is sufficient in the main route but is not necessary. -/
theorem raw_naturality_fails :
    ¬ ∀ x y y', product x (mB y y') = n (product x y) (product x y') := by
  intro h
  have hh := h 1 1 1
  rw [rawB_left_value, rawB_right_value] at hh
  have hr := congrArg Complex.re hh
  norm_num at hr

end RawSign

end

end IDT.QMClosure.CompositeProductControls
