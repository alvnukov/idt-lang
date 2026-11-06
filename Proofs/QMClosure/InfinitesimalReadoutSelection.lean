import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

namespace IDT.QMClosure.InfinitesimalReadoutSelection

noncomputable section

/-!
# Conditional selection by infinitesimal conservation of an additive response

The identical scalar response for two distinguishable channels, additive raw
output, fixed native coherent addition defining linearity, differentiability,
accessibility of every real input, accessible nonzero exchange, and conservation
of THIS response are supplied operational bridges. Normalized probability sums
are not the conserved quantity here. No quadratic ansatz, Hessian assumption,
special rotation, monotonic derivative, or continuously differentiable response
is assumed.

This classifies a supplied linear infinitesimal balance and arbitrary
differentiable response simultaneously. It does not implement dynamics or derive
Born readout from IDT primitives, and proves no complex/Hilbert/tensor structure,
detector actualization, or physical constants.
-/

/-- Conservation of the raw additive response under a supplied fixed linear
generator. The coefficients themselves are classified by the theorem below. -/
def Balance (f : ℝ → ℝ) (a b c d : ℝ) : Prop :=
  ∀ x y, deriv f x * (a * x + b * y) +
    deriv f y * (c * x + d * y) = 0

/-- Integrating a globally linear derivative needs differentiability, not a
continuous derivative or a second derivative. -/
theorem quadratic_of_linear_derivative (f : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hzero : f 0 = 0)
    (k : ℝ) (hlinear : ∀ x, deriv f x = k * x) :
    ∀ x, f x = k / 2 * x ^ 2 := by
  have hpoly (x : ℝ) :
      HasDerivAt (fun t : ℝ => k / 2 * t ^ 2) (k * x) x := by
    convert (((hasDerivAt_id x).pow 2).const_mul (k / 2)) using 1
    simp only [id_eq]
    ring
  let g : ℝ → ℝ := fun x => f x - k / 2 * x ^ 2
  have hg : Differentiable ℝ g := by
    intro x
    exact ((hf x).hasDerivAt.sub (hpoly x)).differentiableAt
  have hgzero : ∀ x, deriv g x = 0 := by
    intro x
    have h : HasDerivAt g 0 x := by
      convert ((hf x).hasDerivAt.sub (hpoly x)) using 1
      rw [hlinear]; ring
    exact h.deriv
  intro x
  have h := is_const_of_deriv_eq_zero hg hgzero x 0
  dsimp [g] at h
  rw [hzero] at h
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] at h
  linarith

/-- Algebraic and calculus core; the public theorem derives both derivative
hypotheses from nonnegativity and strict response at one. -/
theorem classify_of_derivative_witness (f : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hzero : f 0 = 0)
    (hdzero : deriv f 0 = 0) (r : ℝ) (hr : 0 < r)
    (hdr : deriv f r ≠ 0) (a b c d : ℝ)
    (exchange : b ≠ 0 ∨ c ≠ 0) (balance : Balance f a b c d) :
    a = 0 ∧ d = 0 ∧ c = -b ∧ b ≠ 0 ∧
      ∀ x, f x = f 1 * x ^ 2 := by
  have ha : a = 0 := by
    have h := balance r 0
    simp only [hdzero, mul_zero, add_zero, zero_mul] at h
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hdr)).resolve_right hr.ne'
  have hd : d = 0 := by
    have h := balance 0 r
    simp only [hdzero, mul_zero, zero_add, zero_mul] at h
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hdr)).resolve_right hr.ne'
  have hbc : b + c = 0 := by
    have h := balance r r
    rw [ha, hd] at h
    have hprod : deriv f r * r * (b + c) = 0 := by nlinarith [h]
    exact (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero hdr hr.ne')
  have hc : c = -b := by linarith
  have hb : b ≠ 0 := by
    intro h
    rcases exchange with h' | h'
    · exact h' h
    · apply h'; rw [hc, h, neg_zero]
  let k : ℝ := deriv f r / r
  have hlinear : ∀ x, deriv f x = k * x := by
    intro x
    have h := balance x r
    rw [ha, hd, hc] at h
    have hp : b * (r * deriv f x - deriv f r * x) = 0 := by nlinarith [h]
    have heq := (mul_eq_zero.mp hp).resolve_left hb
    dsimp [k]
    field_simp
    nlinarith [heq]
  have hquad := quadratic_of_linear_derivative f hf hzero k hlinear
  have hk : k / 2 = f 1 := by simpa using (hquad 1).symm
  exact ⟨ha, hd, hc, hb, fun x => by rw [hquad x, hk]⟩

/-- Exact conditional classification for an arbitrary differentiable response;
neither a quadratic response nor a rotation generator is assumed. -/
theorem differentiable_balance_selects_quadratic (f : ℝ → ℝ)
    (hf : Differentiable ℝ f) (nonnegative : ∀ x, 0 ≤ f x)
    (zero : f 0 = 0) (onePositive : 0 < f 1) (a b c d : ℝ)
    (exchange : b ≠ 0 ∨ c ≠ 0) (balance : Balance f a b c d) :
    a = 0 ∧ d = 0 ∧ c = -b ∧ b ≠ 0 ∧
      ∀ x, f x = f 1 * x ^ 2 := by
  have hmin : IsLocalMin f 0 := by
    exact Filter.Eventually.of_forall (fun x => by rw [zero]; exact nonnegative x)
  obtain ⟨r, hr, hdr⟩ := exists_deriv_eq_slope f (by norm_num : (0 : ℝ) < 1)
    hf.continuous.continuousOn hf.differentiableOn
  have hdr' : deriv f r = f 1 := by simpa [zero] using hdr
  exact classify_of_derivative_witness f hf zero hmin.deriv_eq_zero r hr.1
    (by rw [hdr']; exact ne_of_gt onePositive) a b c d exchange balance

/-- Every quadratic response satisfies balance for the displayed exchange
 generators. -/
theorem quadratic_balance (q b : ℝ) :
    Balance (fun x : ℝ => q * x ^ 2) 0 b (-b) 0 := by
  intro x y
  have hderiv (t : ℝ) : deriv (fun z : ℝ => q * z ^ 2) t = q * (2 * t) := by
    convert (((hasDerivAt_id t).pow 2).const_mul q).deriv using 1
    simp only [id_eq]
    ring
  rw [hderiv x, hderiv y]
  ring

/-- Exact obstruction, quantified over every fixed linear generator with nonzero
off-diagonal exchange. -/
theorem quartic_has_no_nontrivial_linear_balance (a b c d : ℝ)
    (exchange : b ≠ 0 ∨ c ≠ 0) :
    ¬ Balance (fun x : ℝ => x ^ 4) a b c d := by
  intro balance
  have h := differentiable_balance_selects_quadratic (fun x : ℝ => x ^ 4)
    (differentiable_id.pow 4) (fun x => by positivity) (by norm_num)
    (by norm_num) a b c d exchange balance
  have htwo := h.2.2.2.2 2
  norm_num at htwo

/-- Dropping linearity permits quartic conservation; this is only an algebraic
control, not a proposed physical implementation. -/
theorem nonlinear_exchange_preserves_quartic (x y : ℝ) :
    (4 * x ^ 3) * y ^ 3 + (4 * y ^ 3) * (-x ^ 3) = 0 := by ring

/-- The standard linear exchange fails quartic raw conservation at exact inputs. -/
theorem linear_exchange_quartic_violation :
    (4 * (1 : ℝ) ^ 3) * 2 + (4 * (2 : ℝ) ^ 3) * (-1) = -24 := by norm_num

end

end IDT.QMClosure.InfinitesimalReadoutSelection
