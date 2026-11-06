import Proofs.QMClosure.GeneratedEventConeControl
import Proofs.QMClosure.CompositeProductControls
import Proofs.QMClosure.MixerGeneratedProcessWall

/-!
# A supplied native-mixer event outside the old coordinate cone

This finite control uses the existing circuit grammar with the supplied complex
scalar wire encoding, not a physical-wire adapter. A dyadic classical mixture
of two three-gate circuits has a positive-contraction selected-port weight F
outside the previous generated cone. Total weight is conserved at all ports.

The extension obstruction additionally uses two explicit arbitrary-real
classical-mixture accounting laws and effect noncontextuality (one function on
coordinates). Those laws are hypotheses, not a consequence of dyadic mixing.
No physical availability, Born actualization, random selector, universal test
availability, circuit minimality, or full QM closure is asserted.
-/

namespace IDT.QMClosure.NativeMixerEventConeExclusion

noncomputable section

open ContextualActualizationControl
open GeneratedEventConeControl
open MixerGeneratedProcessWall
open scoped BigOperators

abbrev Raw := CompositeProductControls.RawSign.N

/-- The exact existing normalized mixer, packaged for the existing grammar. -/
def mixer : (ℂ × ℂ) →+ (ℂ × ℂ) where
  toFun := Raw
  map_zero' := by
    apply Prod.ext <;> apply Complex.ext <;>
      norm_num [Raw, CompositeProductControls.RawSign.N,
        CompositeProductControls.RawSign.n_re, CompositeProductControls.RawSign.n_im]
  map_add' p q := by
    apply Prod.ext <;> apply Complex.ext <;>
      simp [Raw, CompositeProductControls.RawSign.N,
        CompositeProductControls.RawSign.n_re, CompositeProductControls.RawSign.n_im]
      <;> ring

theorem mixer_transparent (z : ℂ) : mixer (z, z) = (z, z) := by
  apply Prod.ext <;> exact CompositeProductControls.RawSign.n_diagonal z

theorem mixer_square (p : ℂ × ℂ) : mixer (mixer p) = p.swap :=
  CompositeProductControls.RawSign.N_square p

theorem mixer_conserves (z w : ℂ) :
    Complex.normSq (mixer (z, w)).1 + Complex.normSq (mixer (z, w)).2 =
      Complex.normSq z + Complex.normSq w :=
  CompositeProductControls.RawSign.norm_conservation (z, w)

abbrev NativeCircuit := Circuit (ι := Fin 3) mixer

def gate01 : NativeCircuit := .pair 0 1 (by decide)
def gate02 : NativeCircuit := .pair 0 2 (by decide)
def gate12 : NativeCircuit := .pair 1 2 (by decide)

/-- Chronological word (01,02,01); seq evaluates its second argument last. -/
def cPlus : NativeCircuit := .seq (.seq gate01 gate02) gate01
/-- Chronological word (01,12,02). -/
def cMinus : NativeCircuit := .seq (.seq gate01 gate12) gate02

def input (z w : ℂ) : Fin 3 → ℂ := ![z, w, 0]

theorem cPlus_selected (z w : ℂ) :
    cPlus.eval (input z w) 0 =
      -(1 + Complex.I) * z / 4 + (3 + Complex.I) * w / 4 := by
  change CompositeProductControls.RawSign.n
    (CompositeProductControls.RawSign.n (CompositeProductControls.RawSign.n z w) 0)
    (CompositeProductControls.RawSign.n w z) = _
  apply Complex.ext <;>
    norm_num [cPlus, gate01, gate02, Circuit.eval, pairGate, pairReplace,
      mixer, Raw, CompositeProductControls.RawSign.N, input,
      CompositeProductControls.RawSign.n_re, CompositeProductControls.RawSign.n_im,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring

theorem cMinus_selected (z w : ℂ) :
    cMinus.eval (input z w) 0 =
      -(1 - Complex.I) * z / 4 + (3 - Complex.I) * w / 4 := by
  change CompositeProductControls.RawSign.n (CompositeProductControls.RawSign.n z w)
    (CompositeProductControls.RawSign.n 0 (CompositeProductControls.RawSign.n w z)) = _
  apply Complex.ext <;>
    norm_num [cMinus, gate01, gate02, gate12, Circuit.eval, pairGate, pairReplace,
      mixer, Raw, CompositeProductControls.RawSign.N, input,
      CompositeProductControls.RawSign.n_re, CompositeProductControls.RawSign.n_im,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring

theorem native_total_weight (c : NativeCircuit) (z w : ℂ) :
    ∑ k, Complex.normSq (c.eval (input z w) k) =
      Complex.normSq z + Complex.normSq w := by
  have h := c.preserves_readout Complex.normSq mixer_conserves (input z w)
  simpa [totalReadout, input, Fin.sum_univ_succ] using h

def compressedWeight (z w : ℂ) (k : Fin 3) : ℝ :=
  (Complex.normSq (cPlus.eval (input z w) k) +
    Complex.normSq (cMinus.eval (input z w) k)) / 2

theorem compressed_total_weight (z w : ℂ) :
    ∑ k, compressedWeight z w k = Complex.normSq z + Complex.normSq w := by
  change (∑ k, (Complex.normSq (cPlus.eval (input z w) k) +
    Complex.normSq (cMinus.eval (input z w) k)) / 2) = _
  rw [← Finset.sum_div, Finset.sum_add_distrib, native_total_weight, native_total_weight]
  ring

def F : SymmetricCoordinates := ⟨1 / 8, 5 / 8, -1 / 4⟩

/-- The selected-port identity holds for every complex pair, not just real inputs. -/
theorem native_selected_weight (z w : ℂ) :
    compressedWeight z w 0 = (complexExpectation F z w).re := by
  rw [compressedWeight, cPlus_selected, cMinus_selected, complexExpectation_real]
  norm_num [Complex.normSq_apply, quadratic, F,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

theorem F_quadratic (x y : ℝ) :
    quadratic F x y = ((x - 2 * y) ^ 2 + y ^ 2) / 8 := by
  simp only [quadratic, F]
  ring

theorem F_complement_quadratic (x y : ℝ) :
    quadratic (complementCoordinates F) x y =
      ((2 * x + y) ^ 2 + 3 * x ^ 2 + 2 * y ^ 2) / 8 := by
  simp only [quadratic, F, complementCoordinates]
  ring

theorem F_positive_contraction (x y : ℝ) :
    0 ≤ quadratic F x y ∧ quadratic F x y ≤ x ^ 2 + y ^ 2 := by
  constructor
  · rw [F_quadratic]; positivity
  · have h : 0 ≤ quadratic (complementCoordinates F) x y := by
      rw [F_complement_quadratic]; positivity
    rw [quadratic_complement] at h
    linarith

theorem F_complex_positive_contraction (z w : ℂ) :
    0 ≤ (complexExpectation F z w).re ∧
    (complexExpectation F z w).re ≤ Complex.normSq z + Complex.normSq w ∧
    (complexExpectation F z w).im = 0 := by
  rw [complexExpectation_real]
  refine ⟨add_nonneg (F_positive_contraction _ _).1
    (F_positive_contraction _ _).1, ?_, complexExpectation_imaginary F z w⟩
  simpa only [Complex.normSq_apply, pow_two, add_assoc, add_left_comm, add_comm] using
    add_le_add (F_positive_contraction z.re w.re).2
      (F_positive_contraction z.im w.im).2

def epsilon : ℝ := 1 / (4 * Real.sqrt 3) - 1 / 8
def r : ℝ := 1 / Real.sqrt 3
def s : ℝ := 5 / 8 - 3 / (4 * Real.sqrt 3)

private theorem reciprocal_bounds : (1 / 2 : ℝ) < 1 / Real.sqrt 3 ∧
    1 / Real.sqrt 3 < (2 / 3 : ℝ) := by
  have hp : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsq : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  constructor
  · apply (lt_div_iff₀ hp).2
    nlinarith
  · apply (div_lt_iff₀ hp).2
    nlinarith

theorem coefficient_bounds : 0 < epsilon ∧ 0 < r ∧ 0 < s ∧
    (1 + epsilon) / 2 ≤ 1 ∧ (r + s) / 2 ≤ 1 := by
  obtain ⟨hl, hu⟩ := reciprocal_bounds
  have he : epsilon = (1 / Real.sqrt 3) / 4 - 1 / 8 := by
    simp only [epsilon]; ring
  have hs : s = 5 / 8 - 3 / 4 * (1 / Real.sqrt 3) := by
    simp only [s]; ring
  rw [he, hs]
  dsimp only [r]
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem L_F : L F = 1 / 8 - 1 / (4 * Real.sqrt 3) := by
  simp only [L, F]
  ring

theorem L_F_negative : L F < 0 := by
  rw [L_F]
  have h := coefficient_bounds.1
  dsimp only [epsilon] at h
  linarith

theorem F_not_inCone : ¬ InCone F := by
  intro h
  exact (not_le_of_gt L_F_negative) (cone_L_nonnegative h)

theorem F_not_inDomain : ¬ InDomain F := fun h => F_not_inCone h.1

def P0 : SymmetricCoordinates := projector .zero
def Qplus : SymmetricCoordinates := complementCoordinates (projector .plus)
def Q0 : SymmetricCoordinates := complementCoordinates (projector .zero)

theorem old_event_probabilities : L P0 = 1 ∧ L Qplus = 0 ∧ L Q0 = 0 := by
  simp [P0, Qplus, Q0, L_complement, L_projector]

/-- Exact finite identity; no global extension or imaginary response is assumed. -/
theorem extension_operator_identity :
    add F (scale epsilon P0) = add (scale r Qplus) (scale s Q0) := by
  have hn : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  ext <;> simp [add, scale, F, epsilon, r, s, P0, Qplus, Q0,
    projector, complementCoordinates] <;> field_simp <;> ring

def leftMixture : SymmetricCoordinates := scale (1 / 2) (add F (scale epsilon P0))
def rightMixture : SymmetricCoordinates :=
  scale (1 / 2) (add (scale r Qplus) (scale s Q0))

theorem mixture_operator_identity : leftMixture = rightMixture := by
  exact congrArg (scale (1 / 2)) extension_operator_identity

/-- Four nonzero mixture coefficients and the two zero-padding coefficients. -/
theorem mixture_weights_valid :
    0 ≤ (1 / 2 : ℝ) ∧ 0 ≤ epsilon / 2 ∧ 0 ≤ r / 2 ∧ 0 ≤ s / 2 ∧
    0 ≤ 1 - (1 + epsilon) / 2 ∧ 0 ≤ 1 - (r + s) / 2 := by
  obtain ⟨he, hr, hs, hl, hh⟩ := coefficient_bounds
  exact ⟨by norm_num, by positivity, by positivity, by positivity,
    by linarith, by linarith⟩

def paddedMixture (a b : ℝ) (A B : SymmetricCoordinates) : SymmetricCoordinates :=
  add (add (scale a A) (scale b B)) (scale (1 - a - b) zeroCoordinates)

theorem left_zero_padding : leftMixture =
    paddedMixture (1 / 2) (epsilon / 2) F P0 := by
  ext <;> simp [leftMixture, paddedMixture, add, scale, zeroCoordinates] <;> ring

theorem right_zero_padding : rightMixture =
    paddedMixture (r / 2) (s / 2) Qplus Q0 := by
  ext <;> simp [rightMixture, paddedMixture, add, scale, zeroCoordinates] <;> ring

theorem padding_normalizes (a b : ℝ) : a + b + (1 - a - b) = 1 := by ring

/-- Conditional finite obstruction: a single coordinate assignment matching the
old three probabilities cannot obey both explicit real-mixture accounting laws
while assigning a nonnegative value to the newly available port event. These
premises do not assert global linearity, physical availability, or Born's rule.
The zero-padding event contributes zero in the displayed accounting laws. -/
theorem no_nonnegative_extension (p : SymmetricCoordinates → ℝ)
    (hF : 0 ≤ p F) (hP : p P0 = 1) (hQplus : p Qplus = 0) (hQ0 : p Q0 = 0)
    (hleft : p leftMixture = (p F + epsilon * p P0) / 2)
    (hright : p rightMixture = (r * p Qplus + s * p Q0) / 2) : False := by
  have heq : p leftMixture = p rightMixture := congrArg p mixture_operator_identity
  rw [hleft, hright, hP, hQplus, hQ0] at heq
  have he := coefficient_bounds.1
  nlinarith

end

end IDT.QMClosure.NativeMixerEventConeExclusion
