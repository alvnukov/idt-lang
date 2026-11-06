import Proofs.QMClosure.PositiveQuadraticGram
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.Complex.BigOperators

namespace IDT.QMClosure.QuadraticHermitianKernel

open QuadraticRecordRefinement PositiveQuadraticPolarization PositiveQuadraticGram
open scoped BigOperators ComplexOrder

noncomputable section

variable {V : Type*} [AddCommGroup V] {Q : V → ℝ}

/-- Supplied additive quarter-turn, preserving the supplied quadratic readout. -/
structure QuadraticPhase (Q : V → ℝ) where
  J : V →+ V
  square : ∀ x, J (J x) = -x
  preserves : ∀ x, Q (J x) = Q x

variable (h : PositiveQuadratic Q) (phase : QuadraticPhase Q)

theorem polarization_phase (x y : V) :
    polarization Q (phase.J x) (phase.J y) = polarization Q x y := by
  simp only [polarization, ← map_add, phase.preserves]

include h in
theorem polarization_neg_left (x y : V) :
    polarization Q (-x) y = -polarization Q x y := by
  simpa using zsmul_left h (-1) x y

include h in
theorem phase_skew (x y : V) :
    polarization Q x (phase.J y) = -polarization Q (phase.J x) y := by
  have he := polarization_phase phase (phase.J x) y
  rw [phase.square, polarization_neg_left h] at he
  linarith

/-- Convention: conjugate-linear in the first feature, linear in the second. -/
def kernel (x y : V) : ℂ :=
  (polarization Q x y : ℂ) + Complex.I * (polarization Q (phase.J x) y : ℂ)

omit h in
theorem kernel_re (x y : V) : (kernel phase x y).re = polarization Q x y := by
  simp [kernel]

omit h in
theorem kernel_im (x y : V) : (kernel phase x y).im = polarization Q (phase.J x) y := by
  simp [kernel]

include h in
theorem hermitian (x y : V) : star (kernel phase y x) = kernel phase x y := by
  apply Complex.ext <;>
    simp [kernel, symmetric y x, symmetric (phase.J y) x, phase_skew h phase x y]

include h in
theorem diagonal (x : V) : kernel phase x x = (Q x : ℂ) := by
  have he := phase_skew h phase x x
  rw [symmetric x (phase.J x)] at he
  have hz : polarization Q (phase.J x) x = 0 := by linarith
  simp [kernel, hz, PositiveQuadraticPolarization.diagonal h]

include h in
theorem add_left (x y z : V) :
    kernel phase (x + y) z = kernel phase x z + kernel phase y z := by
  simp only [kernel, map_add, PositiveQuadraticPolarization.add_left h, Complex.ofReal_add]
  ring

include h in
theorem add_right (x y z : V) :
    kernel phase x (y + z) = kernel phase x y + kernel phase x z := by
  simp only [kernel, PositiveQuadraticPolarization.add_right h, Complex.ofReal_add]
  ring

include h in
theorem phase_left (x y : V) : kernel phase (phase.J x) y = -Complex.I * kernel phase x y := by
  simp only [kernel, phase.square, polarization_neg_left h, Complex.ofReal_neg]
  ring_nf
  simp

include h in
theorem phase_right (x y : V) : kernel phase x (phase.J y) = Complex.I * kernel phase x y := by
  simp only [kernel]
  rw [polarization_phase phase x y, phase_skew h phase x y]
  simp only [Complex.ofReal_neg]
  ring_nf
  simp

/-- Real doubled family used only as an auxiliary finite coefficient polynomial. -/
def doubled {ι : Type*} (v : ι → V) : ι ⊕ ι → V := Sum.elim v (fun i => phase.J (v i))

def doubledCoefficients {ι : Type*} (c : ι → ℂ) : ι ⊕ ι → ℝ :=
  Sum.elim (fun i => (c i).re) (fun i => (c i).im)

include h in
/-- The real part of the complex Gram form equals a full doubled real Gram form. -/
theorem complex_gram_re {ι : Type*} [Fintype ι] (v : ι → V) (c : ι → ℂ) :
    (∑ i, ∑ j, star (c i) * kernel phase (v i) (v j) * c j).re =
      gram (Q := Q) (doubled phase v) (doubledCoefficients c) := by
  have ht (i j : ι) :
      (star (c i) * kernel phase (v i) (v j) * c j).re =
        (c i).re * (c j).re * polarization Q (v i) (v j) -
        (c i).re * (c j).im * polarization Q (phase.J (v i)) (v j) +
        (c i).im * (c j).re * polarization Q (phase.J (v i)) (v j) +
        (c i).im * (c j).im * polarization Q (v i) (v j) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, kernel_re, kernel_im]
    ring
  simp only [Complex.re_sum]
  simp_rw [ht]
  simp only [gram, Fintype.sum_sum_type, doubled, doubledCoefficients, Sum.elim_inl,
    Sum.elim_inr, phase_skew h phase, phase.square,
    polarization_neg_left h, mul_neg, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

include h in
/-- Hermitian symmetry makes every finite complex Gram value real. -/
theorem complex_gram_im {ι : Type*} [Fintype ι] (v : ι → V) (c : ι → ℂ) :
    (∑ i, ∑ j, star (c i) * kernel phase (v i) (v j) * c j).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  change star (∑ i, ∑ j, star (c i) * kernel phase (v i) (v j) * c j) = _
  simp only [star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hermitian h phase]
  ring

include h in
/-- Full finite complex Gram positivity with no Gram-positivity premise. -/
theorem complex_gram_nonnegative {ι : Type*} [Fintype ι] (v : ι → V) (c : ι → ℂ) :
    0 ≤ ∑ i, ∑ j, star (c i) * kernel phase (v i) (v j) * c j := by
  rw [Complex.nonneg_iff, complex_gram_re h phase, complex_gram_im h phase]
  exact ⟨gram_nonnegative h _ _, rfl⟩

include h in
/-- The feature kernel is positive semidefinite for arbitrary finite support. -/
theorem posSemidef : Matrix.PosSemidef (kernel phase) := by
  classical
  refine ⟨?_, ?_⟩
  · ext x y
    exact hermitian h phase x y
  · intro c
    have he := complex_gram_nonnegative h phase
      (fun i : c.support => (i : V)) (fun i : c.support => c i)
    have hi (i : V) :
        (∑ j : c.support, star (c i) * kernel phase i j * c j) =
          ∑ j ∈ c.support, star (c i) * kernel phase i j * c j :=
      Finset.sum_coe_sort c.support (fun j => star (c i) * kernel phase i j * c j)
    simp_rw [hi] at he
    rw [Finset.sum_coe_sort c.support
      (fun i => ∑ j ∈ c.support, star (c i) * kernel phase i j * c j)] at he
    exact he

/-- Explicit scientific boundary of the conditional kernel construction. -/
inductive BoundaryRole where
  | suppliedPositiveQuadraticReadout
  | suppliedAdditiveQuadraticPreservingQuarterTurn
  | provedArbitraryFiniteComplexGramPositivity
  | noCarrierScalarsTopologyOrDivisibilityPremise
  | coefficientPlaneTopologyOnly
  | doesNotProvePhysicalAvailabilityOrStateCompleteness
  | doesNotProveBornActualizationTensorDynamicsOrFullQM
  | doesNotUpgradeManifestStatus
  deriving DecidableEq, Repr

def boundaryRoles : List BoundaryRole := [
  .suppliedPositiveQuadraticReadout,
  .suppliedAdditiveQuadraticPreservingQuarterTurn,
  .provedArbitraryFiniteComplexGramPositivity,
  .noCarrierScalarsTopologyOrDivisibilityPremise,
  .coefficientPlaneTopologyOnly,
  .doesNotProvePhysicalAvailabilityOrStateCompleteness,
  .doesNotProveBornActualizationTensorDynamicsOrFullQM,
  .doesNotUpgradeManifestStatus]

end

end IDT.QMClosure.QuadraticHermitianKernel
