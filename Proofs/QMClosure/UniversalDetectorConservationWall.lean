import Proofs.QMClosure.DetectorEffectOperations
import Mathlib.Tactic

/-!
Universal detector-product conservation constrains the unordered pair of full
preparation measures. A common transport and a square-root-of-swap operation
then force equality of the two input preparations. The transport is an arbitrary
function of full measures and carries no linearity or Markov hypothesis.
-/
namespace IDT.QMClosure.UniversalDetectorConservationWall

noncomputable section
open MeasureTheory ProbabilityTheory
open InvariantEffectReadoutBridge DetectorEffectOperations

universe u v
variable {Ω : Type v} [MeasurableSpace Ω]

/-- Sure-detector mixtures recover the sum from conserved detector products. -/
theorem acceptance_sum_of_products {μ ν α β : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (h : ∀ g : Effect Ω,
      g.acceptance α * g.acceptance β = g.acceptance μ * g.acceptance ν)
    (g : Effect Ω) :
    g.acceptance α + g.acceptance β = g.acceptance μ + g.acceptance ν := by
  have hp := h g
  have hm := h (average sure g)
  simp only [acceptance_average, acceptance_sure] at hm
  nlinarith

/-- Scalar sums and products identify an unordered pair. -/
private theorem scalar_pair {a b m n : ℝ}
    (hs : a + b = m + n) (hp : a * b = m * n) : a = m ∨ a = n := by
  have hb : b = m + n - a := by linarith
  rw [hb] at hp
  have hz : (a - m) * (a - n) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with hm | hn
  · exact Or.inl (sub_eq_zero.mp hm)
  · exact Or.inr (sub_eq_zero.mp hn)

/-- Universal detector products identify the unordered pair of probability laws. -/
theorem unordered_measures_of_products {μ ν α β : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (h : ∀ g : Effect Ω,
      g.acceptance α * g.acceptance β = g.acceptance μ * g.acceptance ν) :
    (α = μ ∧ β = ν) ∨ (α = ν ∧ β = μ) := by
  have hs := acceptance_sum_of_products h
  by_cases ha : α = μ
  · left
    refine ⟨ha, measure_ext_of_acceptance_eq fun g => ?_⟩
    have hh := hs g
    rw [ha] at hh
    linarith
  · have hex : ∃ g : Effect Ω, g.acceptance α ≠ g.acceptance μ := by
      by_contra hn
      push Not at hn
      exact ha (measure_ext_of_acceptance_eq hn)
    obtain ⟨g, hg⟩ := hex
    have hag : g.acceptance α = g.acceptance ν :=
      (scalar_pair (hs g) (h g)).resolve_left hg
    have hbg : g.acceptance β = g.acceptance μ := by
      have hh := hs g
      linarith
    have hgn : g.acceptance ν - g.acceptance μ ≠ 0 := by
      intro hz
      exact hg (hag.trans (sub_eq_zero.mp hz))
    have han : α = ν := by
      apply measure_ext_of_acceptance_eq
      intro k
      have hk := h k
      have hsk := hs k
      have hm := h (average g k)
      simp only [acceptance_average] at hm
      rw [hag, hbg] at hm
      have hb : k.acceptance β = k.acceptance μ + k.acceptance ν -
          k.acceptance α := by linarith
      rw [hb] at hk hm
      have hz : (g.acceptance ν - g.acceptance μ) *
          (k.acceptance α - k.acceptance ν) = 0 := by nlinarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hgn)
    right
    refine ⟨han, measure_ext_of_acceptance_eq fun k => ?_⟩
    have hh := hs k
    rw [han] at hh
    linarith

/-- One common function cannot distinguish equal full laws along a four-cycle. -/
theorem four_cycle_transport {L : Type*} (Φ : L → L) (a b c d : L)
    (hab : Φ a = b) (hbc : Φ b = c) (hcd : Φ c = d) (hda : Φ d = a)
    (hchoice : b = a ∨ b = c) : c = a := by
  rcases hchoice with hba | hbc'
  · calc
      c = Φ b := hbc.symm
      _ = Φ a := congrArg Φ hba
      _ = b := hab
      _ = a := hba
  · have hcc : Φ c = c := by simpa only [hbc'] using hbc
    have hdc : d = c := hcd.symm.trans hcc
    calc
      c = Φ c := hcc.symm
      _ = Φ d := congrArg Φ hdc.symm
      _ = a := hda

/-- Full-law transport plus universal conservation at one input forces equal preparations. -/
theorem preparations_equal_of_universal_products {V : Type u}
    (K : V → Measure Ω) (hK : ∀ x, IsProbabilityMeasure (K x))
    (F : V × V → V × V) (hF : ∀ p, F (F p) = p.swap)
    (Φ : Measure (Ω × Ω) → Measure (Ω × Ω))
    (hΦ : ∀ p, Φ ((K p.1).prod (K p.2)) = (K (F p).1).prod (K (F p).2))
    (p : V × V)
    (hconserve : ∀ g : Effect Ω,
      g.acceptance (K (F p).1) * g.acceptance (K (F p).2) =
        g.acceptance (K p.1) * g.acceptance (K p.2)) : K p.1 = K p.2 := by
  letI (x : V) : IsProbabilityMeasure (K x) := hK x
  let law (q : V × V) := (K q.1).prod (K q.2)
  have h4 : F (F (F (F p))) = p := by rw [hF, hF]; rfl
  have hchoice : law (F p) = law p ∨ law (F p) = law (F (F p)) := by
    rcases unordered_measures_of_products hconserve with hh | hh
    · left
      simp only [law, hh.1, hh.2]
    · right
      simp only [law, hF, Prod.swap, hh.1, hh.2]
  have heq : law (F (F p)) = law p :=
    four_cycle_transport Φ (law p) (law (F p)) (law (F (F p)))
      (law (F (F (F p)))) (hΦ p) (hΦ (F p)) (hΦ (F (F p)))
      (by simpa only [h4] using hΦ (F (F (F p)))) hchoice
  have hm := congrArg (Measure.map (Prod.fst : Ω × Ω → Ω)) heq
  simpa only [law, hF, Prod.swap, Measure.map_fst_prod,
    measure_univ, one_smul] using hm.symm


/-- In particular, a single actual latent kernel supplies the common transport. -/
theorem preparations_equal_of_common_kernel {V : Type u}
    (K : V → Measure Ω) (hK : ∀ x, IsProbabilityMeasure (K x))
    (F : V × V → V × V) (hF : ∀ p, F (F p) = p.swap)
    (channel : ProbabilityTheory.Kernel (Ω × Ω) (Ω × Ω))
    (hchannel : ∀ p, channel ∘ₘ ((K p.1).prod (K p.2)) =
      (K (F p).1).prod (K (F p).2))
    (p : V × V)
    (hconserve : ∀ g : Effect Ω,
      g.acceptance (K (F p).1) * g.acceptance (K (F p).2) =
        g.acceptance (K p.1) * g.acceptance (K p.2)) : K p.1 = K p.2 :=
  preparations_equal_of_universal_products K hK F hF
    (fun μ => channel ∘ₘ μ) hchannel p hconserve

end
end IDT.QMClosure.UniversalDetectorConservationWall
