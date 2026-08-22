import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation

namespace IDT
namespace QMClosure

/-!
# Three-alternative representation: caps plus one transitivity bound

The two-alternative gap theorem (`BornConeGap`) showed that on two
alternatives, Born representability is exactly the Cauchy-Schwarz cap.
This file settles three alternatives.  Write the pair data as overlaps
`b_ij` (for a weight, `q_ij = 2 * b_ij`); the machine obstruction
classes found in the previous cluster were saturation inconsistency
and partial-correlation violation.  Here the second becomes a theorem.

**Main result** (`exists_amplitudes_three_iff`): for three
alternatives with `0 < a0` and a nondegenerate anchor pair
(`b01 ^ 2 < a0 * a1`), real amplitudes with norms `a_i` and overlaps
`b_ij` exist IF AND ONLY IF the single transitivity bound

    (a0 * b12 - b01 * b02) ^ 2 ≤ (a0 * a1 - b01 ^ 2) * (a0 * a2 - b02 ^ 2)

holds.  In normalized form (caps `c_ij = b_ij / √(a_i a_j)`):
`|c12 - c01 * c02| ≤ √((1 - c01²)(1 - c02²))` — two alternatives
strongly aligned with a third cannot be strongly anti-aligned with
each other: alignment is transitive up to the geometric slack.
Sufficiency is an explicit construction in ℝ³; necessity is the
orthogonal decomposition with respect to the anchor plus
Cauchy-Schwarz (`cs_three`, Lagrange identity by hand).

**Reading for the oriented-comparison primitive.**  At n = 3 the
criterion is REAL.  The same bound characterizes complex Hermitian PSD
completions with the given real parts: the imaginary-part freedom is
absorbed by Cauchy-Schwarz on the two-dimensional (Im part,
Re-orthogonal part) decomposition (remark, not formalized here).  The
genuinely complex content of the oriented comparison structure — phase
holonomy around cycles — first becomes irreducible on FOUR
alternatives (4-cycles), which is where the primitive Q earns its
unit-modulus vocabulary.  At n = 3, cap-plus-transitivity is pure real
geometry.

**Corollary** (`partial_correlation_witness_not_born`): the machine
obstruction `(a, b) = ((1, 1, 1), (1/2, 1/2, -19/20))` — all pairwise
caps strict — is NOT representable, now as a theorem:
`(-19/20 - 1/4) ^ 2 = 36/25 > 9/16`.

Scope.  Generic case only: `0 < a0`, `b01 ^ 2 < a0 * a1`.  Degenerate
saturation cases (a collapsed pair `b_ij ^ 2 = a_i * a_j`, or a zero
anchor) are the forced-phase logic recorded in the research ledger;
excluded here, not settled.  Coefficients over ℝ.
-/

/-- Dot product of two real 3-vectors. -/
def dot3 (v w : Fin 3 → ℝ) : ℝ := v 0 * w 0 + v 1 * w 1 + v 2 * w 2

/-- Squared norm of a real 3-vector. -/
def norm3 (v : Fin 3 → ℝ) : ℝ := dot3 v v

theorem dot3_symm (v w : Fin 3 → ℝ) : dot3 v w = dot3 w v := by
  show v 0 * w 0 + v 1 * w 1 + v 2 * w 2
      = w 0 * v 0 + w 1 * v 1 + w 2 * v 2
  ring

/-- Cauchy-Schwarz for real 3-vectors, by hand: the slack is the sum
of the three coordinate-pair squares (Lagrange identity). -/
theorem cs_three (v w : Fin 3 → ℝ) :
    (dot3 v w) ^ 2 ≤ norm3 v * norm3 w := by
  have h1 : (v 0 * w 1 - v 1 * w 0) ^ 2 ≥ 0 := sq_nonneg _
  have h2 : (v 0 * w 2 - v 2 * w 0) ^ 2 ≥ 0 := sq_nonneg _
  have h3 : (v 1 * w 2 - v 2 * w 1) ^ 2 ≥ 0 := sq_nonneg _
  show (v 0 * w 0 + v 1 * w 1 + v 2 * w 2) ^ 2
      ≤ (v 0 * v 0 + v 1 * v 1 + v 2 * v 2) * (w 0 * w 0 + w 1 * w 1 + w 2 * w 2)
  nlinarith [h1, h2, h3]

/-- Bilinearity of `dot3` in the second argument, subtraction form. -/
theorem dot3_sub_left (u v w : Fin 3 → ℝ) (k : ℝ) :
    dot3 u (fun i => v i - k * w i) = dot3 u v - k * dot3 u w := by
  show u 0 * (v 0 - k * w 0) + u 1 * (v 1 - k * w 1) + u 2 * (v 2 - k * w 2)
      = (u 0 * v 0 + u 1 * v 1 + u 2 * v 2)
        - k * (u 0 * w 0 + u 1 * w 1 + u 2 * w 2)
  ring

/-- Bilinearity of `dot3` in both arguments, subtraction form. -/
theorem dot3_sub_both (v1 v2 w1 w2 : Fin 3 → ℝ) (k m : ℝ) :
    dot3 (fun i => v1 i - k * w1 i) (fun i => v2 i - m * w2 i)
      = dot3 v1 v2 - m * dot3 v1 w2 - k * dot3 w1 v2 + k * m * dot3 w1 w2 := by
  show (v1 0 - k * w1 0) * (v2 0 - m * w2 0)
        + (v1 1 - k * w1 1) * (v2 1 - m * w2 1)
        + (v1 2 - k * w1 2) * (v2 2 - m * w2 2)
      = (v1 0 * v2 0 + v1 1 * v2 1 + v1 2 * v2 2)
        - m * (v1 0 * w2 0 + v1 1 * w2 1 + v1 2 * w2 2)
        - k * (w1 0 * v2 0 + w1 1 * v2 1 + w1 2 * v2 2)
        + k * m * (w1 0 * w2 0 + w1 1 * w2 1 + w1 2 * w2 2)
  ring

/-- **The three-alternative criterion.**  With a positive anchor `a0`
and a nondegenerate anchor pair, amplitudes exist exactly when the
transitivity bound at the anchor holds. -/
theorem exists_amplitudes_three_iff (a0 a1 a2 b01 b02 b12 : ℝ)
    (ha0 : 0 < a0) (hst : b01 ^ 2 < a0 * a1) :
    (∃ ψ0 ψ1 ψ2 : Fin 3 → ℝ,
        norm3 ψ0 = a0 ∧ norm3 ψ1 = a1 ∧ norm3 ψ2 = a2 ∧
          dot3 ψ0 ψ1 = b01 ∧ dot3 ψ0 ψ2 = b02 ∧ dot3 ψ1 ψ2 = b12) ↔
      (a0 * b12 - b01 * b02) ^ 2
        ≤ (a0 * a1 - b01 ^ 2) * (a0 * a2 - b02 ^ 2) := by
  constructor
  · rintro ⟨ψ0, ψ1, ψ2, n0, n1, n2, d01, d02, d12⟩
    have n0' : dot3 ψ0 ψ0 = a0 := n0
    have d10 : dot3 ψ1 ψ0 = b01 := dot3_symm ψ1 ψ0 ▸ d01
    have d20 : dot3 ψ2 ψ0 = b02 := dot3_symm ψ2 ψ0 ▸ d02
    have n1' : dot3 ψ1 ψ1 = a1 := n1
    have n2' : dot3 ψ2 ψ2 = a2 := n2
    have hperp1 : dot3 ψ0 (fun i => ψ1 i - (b01 / a0) * ψ0 i) = 0 := by
      rw [dot3_sub_left, d01, n0']
      field_simp
      ring
    have hperp2 : dot3 ψ0 (fun i => ψ2 i - (b02 / a0) * ψ0 i) = 0 := by
      rw [dot3_sub_left, d02, n0']
      field_simp
      ring
    have hn1 : dot3 (fun i => ψ1 i - (b01 / a0) * ψ0 i)
        (fun i => ψ1 i - (b01 / a0) * ψ0 i) = a1 - b01 ^ 2 / a0 := by
      rw [dot3_sub_both ψ1 ψ1 ψ0 ψ0 (b01 / a0) (b01 / a0), n1', d10, d01,
        n0']
      field_simp
      ring
    have hn2 : dot3 (fun i => ψ2 i - (b02 / a0) * ψ0 i)
        (fun i => ψ2 i - (b02 / a0) * ψ0 i) = a2 - b02 ^ 2 / a0 := by
      rw [dot3_sub_both ψ2 ψ2 ψ0 ψ0 (b02 / a0) (b02 / a0), n2', d20, d02,
        n0']
      field_simp
      ring
    have hd : dot3 (fun i => ψ1 i - (b01 / a0) * ψ0 i)
        (fun i => ψ2 i - (b02 / a0) * ψ0 i) = b12 - b01 * b02 / a0 := by
      rw [dot3_sub_both ψ1 ψ2 ψ0 ψ0 (b01 / a0) (b02 / a0), d12, d10,
        d02, n0']
      field_simp
      ring
    have hcs := cs_three (fun i => ψ1 i - (b01 / a0) * ψ0 i)
      (fun i => ψ2 i - (b02 / a0) * ψ0 i)
    simp only [norm3] at hcs
    rw [hn1, hn2, hd] at hcs
    field_simp at hcs
    nlinarith [hcs, ha0]
  · intro hbnd
    have key : ∀ x : ℝ, 0 ≤ x → Real.sqrt x * Real.sqrt x = x := fun x hx => by
      have := Real.sq_sqrt hx
      nlinarith [this]
    have ha1 : 0 < a1 := by nlinarith [hst]
    have s0pos : 0 < Real.sqrt a0 := Real.sqrt_pos.mpr ha0
    have hs0 : Real.sqrt a0 * Real.sqrt a0 = a0 := key a0 ha0.le
    have hA1pos : 0 < a1 - b01 ^ 2 / a0 := by
      have h : b01 ^ 2 / a0 < a1 := by
        rw [div_lt_iff₀ ha0]
        nlinarith [hst]
      linarith
    have hsA1 : Real.sqrt (a1 - b01 ^ 2 / a0) * Real.sqrt (a1 - b01 ^ 2 / a0)
        = a1 - b01 ^ 2 / a0 := key _ hA1pos.le
    have hsA1pos : 0 < Real.sqrt (a1 - b01 ^ 2 / a0) :=
      Real.sqrt_pos.mpr hA1pos
    have hbnd' : (b12 - b01 * b02 / a0) ^ 2
        ≤ (a1 - b01 ^ 2 / a0) * (a2 - b02 ^ 2 / a0) := by
      have hL : a0 ^ 2 * (b12 - b01 * b02 / a0) ^ 2
          = (a0 * b12 - b01 * b02) ^ 2 := by
        field_simp
      have hR : a0 ^ 2 * ((a1 - b01 ^ 2 / a0) * (a2 - b02 ^ 2 / a0))
          = (a0 * a1 - b01 ^ 2) * (a0 * a2 - b02 ^ 2) := by
        field_simp
      rw [← hL, ← hR] at hbnd
      by_contra hcon
      have hpos2 : 0 < a0 ^ 2 := by nlinarith [ha0]
      have hlt : a0 ^ 2 * ((a1 - b01 ^ 2 / a0) * (a2 - b02 ^ 2 / a0))
          < a0 ^ 2 * (b12 - b01 * b02 / a0) ^ 2 := by
        nlinarith [hcon, hpos2]
      linarith
    have hresnn : 0 ≤ (a2 - b02 ^ 2 / a0)
        - (b12 - b01 * b02 / a0) ^ 2 / (a1 - b01 ^ 2 / a0) := by
      by_contra hcon
      have hlt : (a2 - b02 ^ 2 / a0) * (a1 - b01 ^ 2 / a0)
          < (b12 - b01 * b02 / a0) ^ 2 := by
        rw [← lt_div_iff₀ hA1pos]
        linarith
      linarith
    have hsres : Real.sqrt ((a2 - b02 ^ 2 / a0)
          - (b12 - b01 * b02 / a0) ^ 2 / (a1 - b01 ^ 2 / a0))
        * Real.sqrt ((a2 - b02 ^ 2 / a0)
          - (b12 - b01 * b02 / a0) ^ 2 / (a1 - b01 ^ 2 / a0))
        = (a2 - b02 ^ 2 / a0)
          - (b12 - b01 * b02 / a0) ^ 2 / (a1 - b01 ^ 2 / a0) :=
      key _ hresnn
    refine ⟨![Real.sqrt a0, 0, 0],
      ![b01 / Real.sqrt a0, Real.sqrt (a1 - b01 ^ 2 / a0), 0],
      ![b02 / Real.sqrt a0,
        (b12 - b01 * b02 / a0) / Real.sqrt (a1 - b01 ^ 2 / a0),
        Real.sqrt ((a2 - b02 ^ 2 / a0)
          - (b12 - b01 * b02 / a0) ^ 2 / (a1 - b01 ^ 2 / a0))],
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Real.sqrt a0 * Real.sqrt a0 + 0 * 0 + 0 * 0 = a0
      rw [hs0]
      ring
    · show (b01 / Real.sqrt a0) * (b01 / Real.sqrt a0)
          + Real.sqrt (a1 - b01 ^ 2 / a0) * Real.sqrt (a1 - b01 ^ 2 / a0)
          + 0 * 0 = a1
      have h1 : (b01 / Real.sqrt a0) * (b01 / Real.sqrt a0)
          = b01 ^ 2 / a0 := by
        rw [← pow_two, div_pow, Real.sq_sqrt ha0.le]
      rw [h1, hsA1]
      ring
    · show (b02 / Real.sqrt a0) * (b02 / Real.sqrt a0)
          + ((b12 - b01 * b02 / a0) / Real.sqrt (a1 - b01 ^ 2 / a0))
            * ((b12 - b01 * b02 / a0) / Real.sqrt (a1 - b01 ^ 2 / a0))
          + Real.sqrt ((a2 - b02 ^ 2 / a0)
              - (b12 - b01 * b02 / a0) ^ 2 / (a1 - b01 ^ 2 / a0))
            * Real.sqrt ((a2 - b02 ^ 2 / a0)
              - (b12 - b01 * b02 / a0) ^ 2 / (a1 - b01 ^ 2 / a0)) = a2
      have h1 : (b02 / Real.sqrt a0) * (b02 / Real.sqrt a0)
          = b02 ^ 2 / a0 := by
        rw [← pow_two, div_pow, Real.sq_sqrt ha0.le]
      have h2 : ((b12 - b01 * b02 / a0) / Real.sqrt (a1 - b01 ^ 2 / a0))
            * ((b12 - b01 * b02 / a0) / Real.sqrt (a1 - b01 ^ 2 / a0))
          = (b12 - b01 * b02 / a0) ^ 2 / (a1 - b01 ^ 2 / a0) := by
        rw [← pow_two, div_pow, Real.sq_sqrt hA1pos.le]
      rw [h1, h2, hsres]
      ring
    · show Real.sqrt a0 * (b01 / Real.sqrt a0) + 0 * _
          + 0 * _ = b01
      rw [← mul_div_assoc]
      simp only [zero_mul, add_zero]
      field_simp
    · show Real.sqrt a0 * (b02 / Real.sqrt a0) + 0 * _
          + 0 * _ = b02
      rw [← mul_div_assoc]
      simp only [zero_mul, add_zero]
      field_simp
    · show (b01 / Real.sqrt a0) * (b02 / Real.sqrt a0)
          + Real.sqrt (a1 - b01 ^ 2 / a0)
            * ((b12 - b01 * b02 / a0) / Real.sqrt (a1 - b01 ^ 2 / a0))
          + 0 * _ = b12
      have h1 : (b01 / Real.sqrt a0) * (b02 / Real.sqrt a0)
          = b01 * b02 / a0 := by
        rw [div_mul_div_comm, hs0]
      have h2 : Real.sqrt (a1 - b01 ^ 2 / a0)
            * ((b12 - b01 * b02 / a0) / Real.sqrt (a1 - b01 ^ 2 / a0))
          = b12 - b01 * b02 / a0 := by
        have gen : ∀ x y : ℝ, x ≠ 0 → x * (y / x) = y := by
          intro x y hxy
          field_simp
        exact gen _ _ (ne_of_gt hsA1pos)
      rw [h1, h2]
      ring

/-- **The partial-correlation witness is not Born**: caps strict on
all three pairs, yet no amplitudes exist. -/
theorem partial_correlation_witness_not_born :
    ¬ ∃ ψ0 ψ1 ψ2 : Fin 3 → ℝ,
      norm3 ψ0 = 1 ∧ norm3 ψ1 = 1 ∧ norm3 ψ2 = 1 ∧
        dot3 ψ0 ψ1 = 1 / 2 ∧ dot3 ψ0 ψ2 = 1 / 2 ∧
        dot3 ψ1 ψ2 = -19 / 20 := by
  intro h
  have hiff := (exists_amplitudes_three_iff 1 1 1 (1 / 2) (1 / 2)
    (-19 / 20) (by norm_num) (by norm_num)).mp h
  norm_num at hiff

end QMClosure
end IDT
