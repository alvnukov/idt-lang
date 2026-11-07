import Proofs.QMClosure.NativeGaussianResponse
import Proofs.QMClosure.NativeGaussianDyadicClosure

/-!
# Conditional probability uniqueness for actual finite native circuits

Every signed family satisfying the all-finite-width `SignedHalvingLaw`
assigns the squared complex amplitude to every output of every actual native
circuit prepared from its marked basis source. The Gaussian response is
constructed from actual damped events, then classified algebraically; native
Gaussian-dyadic closure applies that classification to the original output.

No calibration, scalar sufficiency, mixture law, continuity, or arbitrary input
probability extension is added as a premise here. Selected-vacuum halving is
explicit in the signed contract; the adapter from the original positive `Law`
derives it. The Gaussian classification does not use nonnegativity. The
consistency witness `canonicalLaw` occurs only in a corollary after selection
has been proved.

This is a conditional uniqueness theorem for the supplied native grammar and
probability-family contract. It does not derive that contract from IDT's
primitive base, establish physical actualization, select arbitrary complex
preparations, or prove full QM closure.
-/

namespace IDT.QMClosure.NativeProbabilityUniqueness

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open NativeSignedAccounting
open NativeVacuumProbabilityFamily NativeGaussianResponse NativeGaussianDyadicClosure

theorem normSq_gaussian (g : GaussianInt) :
    Complex.normSq (g : ℂ) = (g.re : ℝ)^2 + (g.im : ℝ)^2 := by
  rw [Complex.normSq_apply, ← GaussianInt.intCast_re, ← GaussianInt.intCast_im]
  simp only [pow_two]

theorem normSq_gaussian_dyadic (g : GaussianInt) (k : ℕ) :
    Complex.normSq ((g : ℂ) / (2 : ℂ)^k) =
      ((g.re : ℝ)^2 + (g.im : ℝ)^2) / (4 : ℝ)^k := by
  rw [Complex.normSq_div, map_pow, normSq_gaussian]
  norm_num

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- No quadratic readout is supplied: the response laws are obtained from the
actual-circuit probability family and its native extensions. -/
theorem signedHalving_response_eq_gaussian_norm (L : SignedHalvingLaw)
    (s : ι) (g : GaussianInt) :
    response L s g = (g.re : ℝ)^2 + (g.im : ℝ)^2 :=
  GaussianIntegerQuadraticSelection.gaussian_integer_quadratic_selection
    (response L s) (response_zero L s) (response_one L s)
    (response_rotate L s) (response_parallelogram L s) g

/-- Conditional exact selection on every actual basis-prepared native output. -/
theorem signedHalving_probability_eq_normSq (L : SignedHalvingLaw)
    (s : ι) (c : Native ι) (i : ι) :
    L.prob s c i = Complex.normSq (c.eval (source s) i) := by
  obtain ⟨k, g, hg⟩ := native_output_gaussian_dyadic s c i
  have hw := response_native_output L s c i g k hg
  have hq := signedHalving_response_eq_gaussian_norm L s g
  have hm : (4 : ℝ)^k * L.prob s c i = (g.re : ℝ)^2 + (g.im : ℝ)^2 :=
    hw.symm.trans hq
  have hden : (4 : ℝ)^k ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [hg, normSq_gaussian_dyadic]
  apply (eq_div_iff hden).2
  simpa only [mul_comm] using hm

/-- The original positive-law response interface is preserved through the adapter. -/
theorem response_eq_gaussian_norm (L : Law) (s : ι) (g : GaussianInt) :
    response L s g = (g.re : ℝ)^2 + (g.im : ℝ)^2 :=
  signedHalving_response_eq_gaussian_norm (ofLaw L) s g

/-- The original positive-law public selection interface. -/
theorem native_probability_eq_normSq (L : Law) (s : ι) (c : Native ι) (i : ι) :
    L.prob s c i = Complex.normSq (c.eval (source s) i) :=
  signedHalving_probability_eq_normSq (ofLaw L) s c i

/-- Any two supplied laws agree on every actual native circuit event. -/
theorem native_probabilities_equal (L M : Law) (s : ι) (c : Native ι) (i : ι) :
    L.prob s c i = M.prob s c i :=
  (native_probability_eq_normSq L s c i).trans
    (native_probability_eq_normSq M s c i).symm

/-- Extensional uniqueness concerns exactly the circuit-indexed probability
field of `Law`, not probabilities on an enlarged preparation domain. -/
theorem probability_fields_equal (L M : Law) : @Law.prob L = @Law.prob M := by
  funext α instF instD s c i
  exact native_probabilities_equal L M s c i

/-- The previously defined consistency witness agrees with every law only
after the independent selection theorem above. -/
theorem native_probability_eq_canonical (L : Law) (s : ι) (c : Native ι) (i : ι) :
    L.prob s c i = canonicalLaw.prob s c i := by
  change L.prob s c i = Complex.normSq (c.eval (source s) i)
  exact native_probability_eq_normSq L s c i

end

end IDT.QMClosure.NativeProbabilityUniqueness
