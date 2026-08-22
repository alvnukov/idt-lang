import Mathlib.Tactic
import Proofs.QMClosure.ThreeAlternativeRepresentation

namespace IDT
namespace QMClosure

/-!
# The orientation-covariance wall

The candidate Weyl-style derivation of the Born/Hilbert layer from the
oriented-comparison primitive was: demand that the event readout be
nonnegative at EVERY phase orientation of the comparison family
(phase-rotated contexts as inheritance; covariance of comparisons;
fringe nonnegativity at every phase setting), and try to derive
Hermitian PSD from that covariance demand.

**This file kills that route at n = 3** (`orientation_nonneg_not_born`).
There is a real comparison family — norms `a = (1, 1, 321/200)`,
overlaps `b = (0, 9/10, 9/10)` — such that:

* at EVERY sub-event and EVERY phase orientation the oriented readout
  is `≥ 0` (worst case `1/200`, at the full support with both cross
  terms anti-aligned), yet
* NO real amplitudes realize the family: the transitivity bound of
  `exists_amplitudes_three_iff` fails, `(2889/2000)^2 > 159/200`.

The witness is not a knife-edge: it is an interior point of an open
family `g02 = g12 = t`, `a2 = 4t - 2 + ε` with `t ∈ (1/2, 1)`,
`0 < ε < 2(t - 1)²` (machine-checked numerically over the family; the
Lean theorem fixes one rational point).

An orientation `z` encodes a sub-event with phases: entry `z i` of
squared norm `0` excludes alternative `i`; squared norm `1` includes
it with phase `arg (z i)`.  The oriented readout is the interference
intensity of the selected sub-event at the selected phases; its
cross-terms use `Re (conj (z i) * z j)`, written here as `crossZ`.

**Landscape after this wall.**

* n = 2: the all-orientation minimum is `a0 + a1 - 2|b01| ≥ 0`, i.e.
  exactly the Cauchy-Schwarz cap, which by `born_iff_nonneg_and_cap`
  is Born representability.  Phase covariance CLOSES the gap at n = 2
  (remark; not re-formalized as an equivalence of the two statements).
* n = 3: phase-only covariance is strictly weaker than Born — this
  file.  What closes the gap at n = 3 is the TRANSITIVITY bound
  (`ThreeAlternativeRepresentation`): alignment is transitive up to
  geometric slack.  The operational demand of the primitive at n = 3
  must be transitivity, not covariance.
* Adding local attenuation (arbitrary radius rescaling of each
  alternative) to the orientation family makes the demand literally
  `∀ x, Re (x† G x) ≥ 0`, i.e. PSD by definition-unfolding — a
  disguise, with no derivation content (remark; not formalized here).
* Unit-modulus-only comparisons (visibility forced to 1) force rank-1
  Gram matrices by Cauchy-Schwarz equality, so the primitive must
  carry visibility in `[0, 1]` alongside phase, not on the unit circle
  (remark; not formalized here).
* Genuinely phase-holonomic content — 4-cycle holonomy that no
  orientation gauge removes — first becomes irreducible at n = 4.

So the corrected shape of bridge family 1 is: caps + transitivity
(the n = 2 and n = 3 theorems), with phase/holonomy demands entering
from n = 4 on; covariance alone never carries the Born layer.
-/

/-- Squared modulus of a complex number, in components. -/
def normZ (z : ℂ) : ℝ := z.re * z.re + z.im * z.im

/-- Real part of the comparison `conj a * b`, in components:
`Re (conj a * b) = a.re * b.re + a.im * b.im`. -/
def crossZ (a b : ℂ) : ℝ := a.re * b.re + a.im * b.im

@[simp] theorem normZ_zero : normZ 0 = 0 := by simp [normZ]

@[simp] theorem crossZ_zero_left (b : ℂ) : crossZ 0 b = 0 := by
  simp [crossZ]

@[simp] theorem crossZ_zero_right (a : ℂ) : crossZ a 0 = 0 := by
  simp [crossZ]

theorem neg_one_le_of_sq_le_one {x : ℝ} (hx : x * x ≤ 1) : -1 ≤ x := by
  by_contra hcon
  push Not at hcon
  have h1 : x + 1 < 0 := by linarith
  have h2 : x - 1 < 0 := by linarith
  have hprod : 0 < (x + 1) * (x - 1) := mul_pos_of_neg_of_neg h1 h2
  have hring : x * x = (x + 1) * (x - 1) + 1 := by ring
  linarith

theorem zero_of_normZ_zero {z : ℂ} (h : normZ z = 0) : z = 0 := by
  have h' : z.re * z.re + z.im * z.im = 0 := h
  have hr : z.re = 0 := by nlinarith [h', sq_nonneg z.re, sq_nonneg z.im]
  have hi : z.im = 0 := by nlinarith [h', sq_nonneg z.re, sq_nonneg z.im]
  exact Complex.ext hr hi

/-- Cauchy-Schwarz in components (Lagrange identity): the comparison
of two unit-modulus orientations is bounded below by `-1`. -/
theorem crossZ_ge_neg_one {a b : ℂ} (ha : normZ a = 1) (hb : normZ b = 1) :
    -1 ≤ crossZ a b := by
  have h1 : a.re * a.re + a.im * a.im = 1 := ha
  have h2 : b.re * b.re + b.im * b.im = 1 := hb
  have hid : (a.re * b.re + a.im * b.im) * (a.re * b.re + a.im * b.im)
      + (a.re * b.im - a.im * b.re) * (a.re * b.im - a.im * b.re)
      = (a.re * a.re + a.im * a.im) * (b.re * b.re + b.im * b.im) := by
    ring
  have hl : 0 ≤ (a.re * b.im - a.im * b.re)
      * (a.re * b.im - a.im * b.re) := mul_self_nonneg _
  have hsq : crossZ a b * crossZ a b ≤ 1 := by
    have hc : crossZ a b * crossZ a b
        + (a.re * b.im - a.im * b.re)
            * (a.re * b.im - a.im * b.re) = 1 := by
      have hc' : (a.re * b.re + a.im * b.im) * (a.re * b.re + a.im * b.im)
          + (a.re * b.im - a.im * b.re)
              * (a.re * b.im - a.im * b.re) = 1 := by
        rw [hid, h1, h2]
        ring
      exact hc'
    nlinarith [hc, hl]
  exact neg_one_le_of_sq_le_one hsq

/-- Oriented event readout of a real 2-additive comparison family
`(a_i, g_ij)` at the orientation `z`: entry `z i` of squared norm `0`
excludes alternative `i`, entry of squared norm `1` includes it with
phase `arg (z i)`.  This is the interference intensity of the selected
sub-event with the selected phases. -/
def orientedReadout (a0 a1 a2 g01 g02 g12 : ℝ) (z : Fin 3 → ℂ) : ℝ :=
  a0 * normZ (z 0) + a1 * normZ (z 1) + a2 * normZ (z 2)
    + 2 * (g01 * crossZ (z 0) (z 1)
        + g02 * crossZ (z 0) (z 2)
        + g12 * crossZ (z 1) (z 2))

/-- **The orientation-covariance wall.**  Nonnegativity of the
oriented readout at every sub-event and every phase orientation does
not imply Born representability at three alternatives. -/
theorem orientation_nonneg_not_born :
    (∀ z : Fin 3 → ℂ,
        (∀ i, normZ (z i) = 0 ∨ normZ (z i) = 1) →
        0 ≤ orientedReadout 1 1 (321 / 200) 0 (9 / 10) (9 / 10) z) ∧
      ¬ ∃ ψ0 ψ1 ψ2 : Fin 3 → ℝ,
          norm3 ψ0 = 1 ∧ norm3 ψ1 = 1 ∧ norm3 ψ2 = 321 / 200 ∧
            dot3 ψ0 ψ1 = 0 ∧ dot3 ψ0 ψ2 = 9 / 10 ∧
            dot3 ψ1 ψ2 = 9 / 10 := by
  constructor
  · intro z hz
    rcases hz 0 with e0 | e0 <;> rcases hz 1 with e1 | e1 <;>
      rcases hz 2 with e2 | e2
    · -- (0, 0, 0): empty event
      simp [orientedReadout, zero_of_normZ_zero e0,
        zero_of_normZ_zero e1, zero_of_normZ_zero e2]
    · -- (0, 0, 1): singleton, intensity a2
      simp [orientedReadout, zero_of_normZ_zero e0,
        zero_of_normZ_zero e1, e2]
      norm_num
    · -- (0, 1, 0): singleton, intensity a1
      simp [orientedReadout, zero_of_normZ_zero e0,
        zero_of_normZ_zero e2, e1]
    · -- (0, 1, 1): pair {1, 2}
      have z0' : z 0 = 0 := zero_of_normZ_zero e0
      have b12 := crossZ_ge_neg_one e1 e2
      simp only [orientedReadout, e1, e2, z0']
      norm_num
      linarith
    · -- (1, 0, 0): singleton, intensity a0
      simp [orientedReadout, zero_of_normZ_zero e1,
        zero_of_normZ_zero e2, e0]
    · -- (1, 0, 1): pair {0, 2}
      have z1' : z 1 = 0 := zero_of_normZ_zero e1
      have b02 := crossZ_ge_neg_one e0 e2
      simp only [orientedReadout, e0, e2, z1']
      norm_num
      linarith
    · -- (1, 1, 0): pair {0, 1}, no overlap term (g01 = 0)
      have z2' : z 2 = 0 := zero_of_normZ_zero e2
      simp [orientedReadout, z2', e0, e1]
    · -- (1, 1, 1): full support, the binding case: 1/200 slack
      have b02 := crossZ_ge_neg_one e0 e2
      have b12 := crossZ_ge_neg_one e1 e2
      simp only [orientedReadout, e0, e1, e2]
      norm_num
      linarith
  · rintro ⟨ψ0, ψ1, ψ2, n0, n1, n2, d01, d02, d12⟩
    have hiff := (exists_amplitudes_three_iff 1 1 (321 / 200) 0
      (9 / 10) (9 / 10) (by norm_num) (by norm_num)).mp
      ⟨ψ0, ψ1, ψ2, n0, n1, n2, d01, d02, d12⟩
    norm_num at hiff

end QMClosure
end IDT
