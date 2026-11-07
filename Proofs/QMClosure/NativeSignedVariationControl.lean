import Proofs.QMClosure.NativeSignedVariationSelection
import Proofs.QMClosure.NativeProbabilityPremiseIndependence

/-!
# Exact growth of the existing signed real-amplitude control

The already established real-amplitude field satisfies all five signed
accounting requirements. Its selected-leaf variation grows exactly as
`4^k / 2`, while the number of selected leaves is `2 * 16^k`. Thus even growth
of order the square root of the selected leaf count does not force halving.
These signed accounting values are not declared physical probabilities.
-/

namespace IDT.QMClosure.NativeSignedVariationControl

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily NativeBinaryLeaves
open NativeBinaryRefinement NativeSignedAccounting NativeSignedVariationSelection
open scoped BigOperators

def realPartLaw : SignedLaw where
  prob := NativeProbabilityPremiseIndependence.realPart
  normalized := NativeProbabilityPremiseIndependence.realPart_normalized
  prepared_eq := NativeProbabilityPremiseIndependence.realPart_prepared
  output_perm := NativeProbabilityPremiseIndependence.realPart_permutation
  spectator_pair := NativeProbabilityPremiseIndependence.realPart_spectator
  vacuum := NativeProbabilityPremiseIndependence.realPart_vacuum

def witnessCircuit : Native (Fin 2) := .pair 0 1 (by decide)

theorem witness_amplitude : witnessCircuit.eval (source 0) 0 =
    NativeAttenuationCircuit.a := by
  simp [witnessCircuit, Circuit.eval, pairGate, pairReplace,
    NativeAttenuationCircuit.mixer_fst, source, single]

theorem witness_parent_value : realPartLaw.prob (0 : Fin 2) witnessCircuit 0 = 1 / 2 := by
  change (witnessCircuit.eval (source 0) 0).re = _
  rw [witness_amplitude]
  norm_num [NativeAttenuationCircuit.a, Complex.div_re, Complex.div_im]

theorem witness_split_value :
    realPartLaw.prob (.inl (0 : Fin 2)) (split witnessCircuit 0) (.inl 0) = 0 := by
  change ((split witnessCircuit 0).eval (source (.inl 0)) (.inl 0)).re = _
  rw [split_retained_amplitude, witness_amplitude]
  norm_num [NativeAttenuationCircuit.a, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]

theorem witness_halving_defect :
    |realPartLaw.prob (.inl (0 : Fin 2)) (split witnessCircuit 0) (.inl 0) -
      realPartLaw.prob 0 witnessCircuit 0 / 2| = 1 / 4 := by
  rw [witness_split_value, witness_parent_value]
  norm_num

theorem a_four : NativeAttenuationCircuit.a ^ 4 = ((-1 / 4 : ℝ) : ℂ) := by
  apply Complex.ext <;>
    norm_num [NativeAttenuationCircuit.a, pow_succ, Complex.mul_re,
      Complex.mul_im, Complex.div_re, Complex.div_im]

theorem a_two : NativeAttenuationCircuit.a ^ 2 = Complex.I / 2 := by
  apply Complex.ext <;>
    norm_num [NativeAttenuationCircuit.a, pow_two, Complex.mul_re,
      Complex.mul_im, Complex.div_re, Complex.div_im]

theorem a_four_mul_add_two (k : ℕ) : NativeAttenuationCircuit.a ^ (4 * k + 2) =
    (((-1 / 4 : ℝ) ^ k : ℝ) : ℂ) * (Complex.I / 2) := by
  rw [pow_add, pow_mul, a_four, a_two, Complex.ofReal_pow]

theorem witness_leaf_value (k : ℕ) (w : Leaf (4 * k + 1)) :
    signedLeafProbability realPartLaw (0 : Fin 2) witnessCircuit 0 (4 * k + 1) w =
      (((((-1 / 4 : ℝ) ^ k : ℝ) : ℂ) * (Complex.I / 2)) *
        phaseFactor (phase (4 * k + 1) w)).re := by
  change ((tree witnessCircuit 0 (4 * k + 1)).eval
    (source (sourceAt 0 (4 * k + 1))) (leafPort 0 (4 * k + 1) w)).re = _
  rw [leaf_amplitude, witness_amplitude]
  have he : NativeAttenuationCircuit.a ^ (4 * k + 1) *
      phaseFactor (phase (4 * k + 1) w) * NativeAttenuationCircuit.a =
      NativeAttenuationCircuit.a ^ (4 * k + 2) *
        phaseFactor (phase (4 * k + 1) w) := by
    rw [show 4 * k + 2 = (4 * k + 1) + 1 by omega, pow_succ]
    ring
  rw [he, a_four_mul_add_two]

def phaseVariation (k : ℕ) (j : Fin 4) : ℝ :=
  if j = 1 ∨ j = 3 then 1 / (2 * (4 : ℝ)^k) else 0

theorem abs_phase_value (k : ℕ) (j : Fin 4) :
    |(((((-1 / 4 : ℝ) ^ k : ℝ) : ℂ) * (Complex.I / 2)) * phaseFactor j).re| =
      phaseVariation k j := by
  have hp : |(-1 / 4 : ℝ)^k| = 1 / (4 : ℝ)^k := by
    calc
      _ = (1 / 4 : ℝ)^k := by rw [abs_pow]; norm_num
      _ = _ := by rw [div_pow, one_pow]
  have hx : ∀ x : ℝ, |(((x : ℂ) * (Complex.I / 2)) * phaseFactor j).re| =
      if j = 1 ∨ j = 3 then |x| / 2 else 0 := by
    intro x
    fin_cases j <;>
      simp [phaseFactor, Complex.mul_re, Complex.mul_im, abs_mul, div_eq_mul_inv]
  rw [hx, hp]
  unfold phaseVariation
  split_ifs <;> ring

theorem witness_leaf_abs (k : ℕ) (w : Leaf (4 * k + 1)) :
    |signedLeafProbability realPartLaw (0 : Fin 2) witnessCircuit 0 (4 * k + 1) w| =
      phaseVariation k (phase (4 * k + 1) w) := by
  rw [witness_leaf_value]
  exact abs_phase_value k _

/-- Exact variation on actual selected leaves at every required depth. -/
theorem witness_selectedVariation (k : ℕ) (hk : 1 ≤ k) :
    selectedVariation realPartLaw (0 : Fin 2) witnessCircuit 0 k = (4 : ℝ)^k / 2 := by
  unfold selectedVariation
  simp_rw [witness_leaf_abs]
  rw [sum_by_phase]
  change (∑ j, NativeBinaryPhaseCounting.realCount (4 * k + 1) j *
    phaseVariation k j) = _
  rw [NativeBinaryPhaseCounting.phaseCount_four_add_one k hk]
  simp [Fin.sum_univ_succ, NativeBinaryPhaseCounting.nextForm, phaseVariation]
  rw [NativeBinaryPhaseCounting.four_pow_square]
  field_simp
  ring

theorem leaf_card (n : ℕ) : Fintype.card (Leaf n) = 2^n := by
  induction n with
  | zero => simp [Leaf]
  | succ n ih =>
    calc
      Fintype.card (Leaf (n + 1)) = Fintype.card (Leaf n × Bool) :=
        Fintype.card_congr (Equiv.refl _)
      _ = 2 ^ (n + 1) := by rw [Fintype.card_prod, Fintype.card_bool, ih, pow_succ]

/-- These are selected leaf ports, injectively embedded in the retained output. -/
theorem witness_leaf_count (k : ℕ) :
    Fintype.card (Leaf (4 * k + 1)) = 2 * 16^k := by
  rw [leaf_card, pow_add, pow_mul]
  norm_num
  ring

/-- Algebraic square-root growth, paired with a nonzero halving defect. -/
theorem witness_variation_squared (k : ℕ) (hk : 1 ≤ k) :
    8 * (selectedVariation realPartLaw (0 : Fin 2) witnessCircuit 0 k)^2 =
      (Fintype.card (Leaf (4 * k + 1)) : ℝ) := by
  rw [witness_selectedVariation k hk, witness_leaf_count]
  push_cast
  rw [NativeBinaryPhaseCounting.four_pow_square]
  ring

theorem witness_variation_unbounded :
    ¬ ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k →
      selectedVariation realPartLaw (0 : Fin 2) witnessCircuit 0 k ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * C)
  have hb := hC (n + 1) (by omega)
  rw [witness_selectedVariation (n + 1) (by omega)] at hb
  have hp := NativeBinaryPhaseCounting.nat_add_one_le_four_pow (n + 1)
  push_cast at hp
  nlinarith

theorem realPart_not_eventwiseBoundedVariation : ¬ EventwiseBoundedVariation realPartLaw := by
  intro h
  exact witness_variation_unbounded (h (0 : Fin 2) witnessCircuit 0)

end
end IDT.QMClosure.NativeSignedVariationControl
