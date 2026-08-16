import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation

namespace IDT
namespace QMClosure

/-!
# The Born cone is exactly the nonnegative cone cut by the Cauchy-Schwarz cap

The representation bridge of the QM closure route asks why a pairwise
weight calculus should take the Born form at all: which primitive demand
forces weights to be squared norms of summed amplitudes?  This file pins
the exact mathematical gap on two alternatives, in both directions, and
exhibits a weight that falls into it.

For two alternatives with singleton weights `a0, a1` and pair
interference `q` (the weight is `twoAltWeight a0 a1 q`, manifestly
2-additive), three facts are proved:

* `twoAltWeight_nonneg_iff`: nonnegativity on every event is exactly
  `0 ≤ a0`, `0 ≤ a1`, `0 ≤ a0 + a1 + q`.
* `exists_amplitudes_iff`: a real amplitude representation exists if and
  only if `0 ≤ a0`, `0 ≤ a1`, `q ^ 2 ≤ 4 * a0 * a1` — the Gram matrix is
  PSD, which for two alternatives is Cauchy-Schwarz.  Both directions:
  necessity from the by-hand `cs_two_dim`, sufficiency by explicit
  vectors with `Real.sqrt`.
* `no_complex_amplitudes`: complex amplitudes in an arbitrary inner
  product space do not help; the triangle inequality already forbids
  them for the counterexample below.

`born_iff_nonneg_and_cap` fuses the two: on two alternatives,
**Born-representable ⟺ nonnegative on all events ∧ Cauchy-Schwarz cap**.
The gap between the two cones is exactly the cap `q ^ 2 ≤ 4 a0 a1`
(fringe contrast ≤ 1), and the cap fails on BOTH sides: the witness
`(a0, a1, q) = (1, 1, 3)` is nonnegative on every event
(`twoAltWeight 1 1 3` on the four subsets is `0, 1, 1, 5`) but has
`q ^ 2 = 9 > 4`, so it is not Born-representable over the reals
(`super_visibility_not_born`) nor over any complex inner product space.

Reading for the closure route.  Nonnegativity of the weight calculus --
the demand the whole gluing campaign works with -- does not by itself
select the Born readout.  The missing demand is a bound on interference
visibility, which this repository already lists as the
bounded-correlations obligation (`V7BoundedCorrelations`, currently an
empty artifact).  The finite probe recorded alongside this file
(matched-mass Fin 2 grid census plus a Fin 3 battery, see the research
ledger) shows that composability does not close the gap either:
super-visibility weights glue with every probed equal-mass partner,
including other super-visibility weights, with certified witnesses.
Arity, nonnegativity and composite closure therefore underdetermine the
readout; the representation bridge must import a visibility/spectral
demand.

Scope.  Two alternatives, arithmetic over ℝ (the counterexample is
integral).  The sufficiency construction uses real square roots.  This
file derives no Born rule and assumes no Hilbert space;
`no_complex_amplitudes` is a negative statement about arbitrary inner
product spaces.
-/

/-- Dot product of two real 2-vectors. -/
def dot (v w : Fin 2 → ℝ) : ℝ := v 0 * w 0 + v 1 * w 1

/-- Squared norm of a real 2-vector. -/
def norm2 (v : Fin 2 → ℝ) : ℝ := dot v v

/-- Cauchy-Schwarz for real 2-vectors, by hand: the slack is the square
`(v 0 * w 1 - v 1 * w 0) ^ 2`. -/
theorem cs_two_dim (v w : Fin 2 → ℝ) :
    (dot v w) ^ 2 ≤ norm2 v * norm2 w := by
  have h : (v 0 * w 1 - v 1 * w 0) ^ 2 ≥ 0 := sq_nonneg _
  show (v 0 * w 0 + v 1 * w 1) ^ 2
      ≤ (v 0 * v 0 + v 1 * v 1) * (w 0 * w 0 + w 1 * w 1)
  nlinarith [h]

theorem norm2_nonneg (v : Fin 2 → ℝ) : 0 ≤ norm2 v := by
  have h1 : (v 0) ^ 2 ≥ 0 := sq_nonneg _
  have h2 : (v 1) ^ 2 ≥ 0 := sq_nonneg _
  show 0 ≤ v 0 * v 0 + v 1 * v 1
  nlinarith

/-- Merging two amplitudes adds the interference term. -/
theorem norm2_add (v w : Fin 2 → ℝ) :
    norm2 (v + w) = norm2 v + norm2 w + 2 * dot v w := by
  show (v 0 + w 0) * (v 0 + w 0) + (v 1 + w 1) * (v 1 + w 1)
      = (v 0 * v 0 + v 1 * v 1) + (w 0 * w 0 + w 1 * w 1)
        + 2 * (v 0 * w 0 + v 1 * w 1)
  ring

/-- The two-alternative weight: singleton values `a0, a1`, pair
interference `q`.  Manifestly 2-additive (kernel `a = (a0, a1)`,
`b = q` off the diagonal); see `TwoDecomposable` in
`SorkinGradeIffPairwiseGeneration` for the general vocabulary, which is
stated over ℚ. -/
def twoAltWeight (a0 a1 q : ℝ) : Finset (Fin 2) → ℝ :=
  fun S =>
    (∑ i ∈ S, if i = 0 then a0 else a1)
      + if (0 : Fin 2) ∈ S ∧ (1 : Fin 2) ∈ S then q else 0

theorem twoAltWeight_nonneg_iff (a0 a1 q : ℝ) :
    (∀ S : Finset (Fin 2), 0 ≤ twoAltWeight a0 a1 q S) ↔
      0 ≤ a0 ∧ 0 ≤ a1 ∧ 0 ≤ a0 + a1 + q := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa [twoAltWeight] using h {(0 : Fin 2)}
    · simpa [twoAltWeight] using h {(1 : Fin 2)}
    · simpa [twoAltWeight, Fin.sum_univ_two] using
        h ({(0 : Fin 2)} ∪ {(1 : Fin 2)})
  · rintro ⟨h0, h1, h01⟩ S
    by_cases e0 : (0 : Fin 2) ∈ S
    · by_cases e1 : (1 : Fin 2) ∈ S
      · have hS : S = Finset.univ := by
          apply Finset.ext
          intro x
          fin_cases x <;> simp [e0, e1]
        rw [hS]
        simpa [twoAltWeight, Fin.sum_univ_two] using h01
      · have hS : S = {(0 : Fin 2)} := by
          apply Finset.ext
          intro x
          fin_cases x <;> simp [e0, e1]
        rw [hS]
        simpa [twoAltWeight] using h0
    · by_cases e1 : (1 : Fin 2) ∈ S
      · have hS : S = {(1 : Fin 2)} := by
          apply Finset.ext
          intro x
          fin_cases x <;> simp [e0, e1]
        rw [hS]
        simpa [twoAltWeight] using h1
      · have hS : S = ∅ := by
          apply Finset.ext
          intro x
          fin_cases x <;> simp [e0, e1]
        rw [hS]
        simp [twoAltWeight]

/-- **The Born characterization on two alternatives**: a real amplitude
representation exists exactly when the Gram data is PSD, which for two
alternatives is the Cauchy-Schwarz cap `q ^ 2 ≤ 4 * a0 * a1`. -/
theorem exists_amplitudes_iff (a0 a1 q : ℝ) :
    (∃ v w : Fin 2 → ℝ,
        norm2 v = a0 ∧ norm2 w = a1 ∧ norm2 (v + w) = a0 + a1 + q) ↔
      0 ≤ a0 ∧ 0 ≤ a1 ∧ q ^ 2 ≤ 4 * a0 * a1 := by
  constructor
  · rintro ⟨v, w, hv, hw, hs⟩
    have hadd := norm2_add v w
    have hq2 : q = 2 * dot v w := by linarith
    have hcs := cs_two_dim v w
    rw [hv, hw] at hcs
    have hvn := norm2_nonneg v
    have hwn := norm2_nonneg w
    refine ⟨by linarith, by linarith, ?_⟩
    rw [hq2]
    nlinarith [hcs]
  · rintro ⟨ha0, ha1, hq⟩
    have key : ∀ x : ℝ, 0 ≤ x → Real.sqrt x * Real.sqrt x = x := by
      intro x hx
      have h := Real.sq_sqrt hx
      nlinarith [h]
    by_cases hz : a0 = 0
    · have hq0 : q = 0 := by
        have hle : q * q ≤ 0 := by nlinarith [hq, hz]
        have hsq : 0 ≤ q * q := by nlinarith [sq_nonneg q]
        exact mul_self_eq_zero.mp (le_antisymm hle hsq)
      refine ⟨![0, 0], ![Real.sqrt a1, 0], ?_, ?_, ?_⟩
      · show (0 : ℝ) * 0 + 0 * 0 = a0
        simp only [mul_zero, add_zero]
        exact hz.symm
      · show Real.sqrt a1 * Real.sqrt a1 + 0 * 0 = a1
        rw [key a1 ha1]; ring
      · show norm2 (![0, 0] + ![Real.sqrt a1, 0]) = a0 + a1 + q
        have h1 : norm2 (![0, 0] : Fin 2 → ℝ) = 0 := by
          show (0 : ℝ) * 0 + 0 * 0 = 0; ring
        have h2 : norm2 (![Real.sqrt a1, 0] : Fin 2 → ℝ) = a1 := by
          show Real.sqrt a1 * Real.sqrt a1 + 0 * 0 = a1
          rw [key a1 ha1]; ring
        have h3 : dot (![0, 0] : Fin 2 → ℝ) (![Real.sqrt a1, 0]) = 0 := by
          show (0 : ℝ) * Real.sqrt a1 + 0 * 0 = 0; ring
        rw [norm2_add, h1, h2, h3]
        rw [hz, hq0]; ring
    · have ha0' : 0 < a0 := lt_of_le_of_ne ha0 (Ne.symm hz)
      have k0 : Real.sqrt a0 * Real.sqrt a0 = a0 := key a0 ha0
      have k0pos : (0 : ℝ) < Real.sqrt a0 := Real.sqrt_pos.mpr ha0'
      have htt : q / (2 * Real.sqrt a0) * (q / (2 * Real.sqrt a0))
          = q * q / (4 * a0) := by
        have h2 : (2 * Real.sqrt a0) * (2 * Real.sqrt a0) = 4 * a0 := by
          nlinarith [k0]
        field_simp
        nlinarith [h2]
      have htle : q / (2 * Real.sqrt a0) * (q / (2 * Real.sqrt a0))
          ≤ a1 := by
        rw [htt, div_le_iff₀ (by nlinarith : (0 : ℝ) < 4 * a0)]
        nlinarith [hq]
      have hru : 0 ≤ a1 - q / (2 * Real.sqrt a0)
          * (q / (2 * Real.sqrt a0)) := by nlinarith
      have htsq : q / (2 * Real.sqrt a0) * (q / (2 * Real.sqrt a0))
          + (a1 - q / (2 * Real.sqrt a0)
            * (q / (2 * Real.sqrt a0))) = a1 := by ring
      refine ⟨![Real.sqrt a0, 0],
        ![q / (2 * Real.sqrt a0),
          Real.sqrt (a1 - q / (2 * Real.sqrt a0)
            * (q / (2 * Real.sqrt a0)))], ?_, ?_, ?_⟩
      · show Real.sqrt a0 * Real.sqrt a0 + 0 * 0 = a0
        rw [k0]; ring
      · show q / (2 * Real.sqrt a0) * (q / (2 * Real.sqrt a0))
            + Real.sqrt (a1 - q / (2 * Real.sqrt a0)
              * (q / (2 * Real.sqrt a0)))
              * Real.sqrt (a1 - q / (2 * Real.sqrt a0)
                * (q / (2 * Real.sqrt a0))) = a1
        rw [key _ hru]
        ring
      · have h1 : norm2 (![Real.sqrt a0, 0] : Fin 2 → ℝ) = a0 := by
          show Real.sqrt a0 * Real.sqrt a0 + 0 * 0 = a0
          rw [k0]; ring
        have h2 : norm2 (![q / (2 * Real.sqrt a0),
            Real.sqrt (a1 - q / (2 * Real.sqrt a0)
              * (q / (2 * Real.sqrt a0)))] : Fin 2 → ℝ) = a1 := by
          show q / (2 * Real.sqrt a0) * (q / (2 * Real.sqrt a0))
              + Real.sqrt (a1 - q / (2 * Real.sqrt a0)
                * (q / (2 * Real.sqrt a0)))
                * Real.sqrt (a1 - q / (2 * Real.sqrt a0)
                  * (q / (2 * Real.sqrt a0))) = a1
          rw [key _ hru]; ring
        have h3 : dot (![Real.sqrt a0, 0] : Fin 2 → ℝ)
            ![q / (2 * Real.sqrt a0),
              Real.sqrt (a1 - q / (2 * Real.sqrt a0)
                * (q / (2 * Real.sqrt a0)))] = q / 2 := by
          have hne : (2 : ℝ) * Real.sqrt a0 ≠ 0 := by
            apply ne_of_gt; nlinarith [k0pos]
          show Real.sqrt a0 * (q / (2 * Real.sqrt a0))
              + 0 * Real.sqrt (a1 - q / (2 * Real.sqrt a0)
                * (q / (2 * Real.sqrt a0))) = q / 2
          rw [zero_mul, add_zero]
          field_simp
        rw [norm2_add, h1, h2, h3]
        ring

/-- **The gap witness**: `(1, 1, 3)` is nonnegative on every event but
not Born-representable over the reals. -/
theorem super_visibility_nonneg :
    ∀ S : Finset (Fin 2), 0 ≤ twoAltWeight 1 1 3 S := by
  rw [twoAltWeight_nonneg_iff]
  norm_num

theorem super_visibility_not_born :
    ¬ ∃ v w : Fin 2 → ℝ,
      norm2 v = 1 ∧ norm2 w = 1 ∧ norm2 (v + w) = 5 := by
  rintro ⟨v, w, hv, hw, hs⟩
  have hadd : norm2 (v + w) = norm2 v + norm2 w + 2 * dot v w :=
    norm2_add v w
  have hcs := cs_two_dim v w
  rw [hv, hw] at hcs
  have hdot : dot v w = 3 / 2 := by linarith
  rw [hdot] at hcs
  norm_num at hcs

/-- **Complex amplitudes do not help**: in an arbitrary complex inner
product space, two amplitudes with unit norms cannot merge to norm
squared `5`; the triangle inequality forbids it. -/
theorem no_complex_amplitudes {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (ψ : Fin 2 → V) :
    ¬ (‖ψ 0‖ ^ 2 = 1 ∧ ‖ψ 1‖ ^ 2 = 1 ∧ ‖(ψ 0 + ψ 1)‖ ^ 2 = 5) := by
  rintro ⟨h0, h1, h2⟩
  have hn := norm_add_le (ψ 0) (ψ 1)
  have nnn : 0 ≤ ‖ψ 0 + ψ 1‖ := norm_nonneg _
  have e0 : ‖ψ 0‖ = 1 := by
    nlinarith [norm_nonneg (ψ 0), sq_nonneg (‖ψ 0‖ - 1)]
  have e1 : ‖ψ 1‖ = 1 := by
    nlinarith [norm_nonneg (ψ 1), sq_nonneg (‖ψ 1‖ - 1)]
  have n2 : ‖ψ 0 + ψ 1‖ * ‖ψ 0 + ψ 1‖ ≤ 4 := by
    nlinarith [hn, nnn]
  nlinarith [n2, h2]

/-- **The gap theorem**: on two alternatives, Born-representability is
exactly nonnegativity on all events together with the Cauchy-Schwarz cap
on interference.  The weight-calculus demand of nonnegativity alone
underdetermines the readout by exactly one inequality. -/
theorem born_iff_nonneg_and_cap (a0 a1 q : ℝ) :
    (∃ v w : Fin 2 → ℝ,
        norm2 v = a0 ∧ norm2 w = a1 ∧ norm2 (v + w) = a0 + a1 + q) ↔
      ((∀ S : Finset (Fin 2), 0 ≤ twoAltWeight a0 a1 q S)
        ∧ q ^ 2 ≤ 4 * a0 * a1) := by
  rw [exists_amplitudes_iff, twoAltWeight_nonneg_iff]
  constructor
  · rintro ⟨h0, h1, hq⟩
    refine ⟨⟨h0, h1, ?_⟩, hq⟩
    by_contra hcon
    have hnlt : a0 + a1 + q < 0 := lt_of_not_ge hcon
    have hqa : (a0 - a1) ^ 2 ≥ 0 := sq_nonneg _
    have hsu : 0 ≤ a0 + a1 := by linarith
    have h1' : 0 < -q := by linarith
    have h2 : a0 + a1 < -q := by linarith
    have hqq : (a0 + a1) * (a0 + a1) < q * q := by
      nlinarith [h1', h2, hsu]
    have haa : 4 * a0 * a1 ≤ (a0 + a1) * (a0 + a1) := by nlinarith [hqa]
    nlinarith [hqq, haa, hq]
  · rintro ⟨⟨h0, h1, h01⟩, hq⟩
    exact ⟨h0, h1, hq⟩

end QMClosure
end IDT

