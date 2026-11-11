import Proofs.QMClosure.FiniteTranslationNormSelection

/-!
# Conditional Gaussian norm selection from multiplicativity and one calibration

The supplied readout is globally multiplicative on every pair of Gaussian
integers. Together with four-probe all-real-weight mixture congruence and the
single calibration `f (2, 0) = 4`, this determines the raw real readout as the
squared integer norm. Nonnegativity, rotation and doubling are conclusions.

Global Gaussian multiplicativity includes coherent sums represented by arbitrary
integer pairs. A multiplicative serial-word response alone supplies no such
extension. The conclusions here are raw algebraic identities on integer pairs.
They do not supply a normalized probability rule or a physical Born theorem.
-/

noncomputable section

namespace IDT.MultiplicativeMixtureReadout

open FiniteMixtureContinuationRank

/-- Gaussian multiplication on the integer lattice, with cross terms. -/
def gaussianMul (z w : IntegerLattice) : IntegerLattice :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- The supplied law ranges over all Gaussian integer pairs. -/
def GaussianMultiplicative (f : IntegerLattice → ℝ) : Prop :=
  ∀ z w, f (gaussianMul z w) = f z * f w

section Calibration

variable (f : IntegerLattice → ℝ)
variable (hmul : GaussianMultiplicative f) (hcal : f (2, 0) = 4)

include hmul hcal

/-- The nonzero calibration forces the multiplicative unit to read one. -/
theorem unit_readout_eq_one : f (1, 0) = 1 := by
  have h := hmul (2, 0) (1, 0)
  norm_num [gaussianMul] at h
  rw [hcal] at h
  linarith

/-- The real square of the imaginary-unit response excludes the negative root
for the response at negative one. -/
theorem negative_unit_readout_eq_one : f (-1, 0) = 1 := by
  have hunit := unit_readout_eq_one f hmul hcal
  have hsquare := hmul (-1, 0) (-1, 0)
  norm_num [gaussianMul] at hsquare
  rw [hunit] at hsquare
  have himag := hmul (0, 1) (0, 1)
  norm_num [gaussianMul] at himag
  have hnonneg : 0 ≤ f (-1, 0) := by
    rw [himag]
    exact mul_self_nonneg _
  have hfactor : (f (-1, 0) - 1) * (f (-1, 0) + 1) = 0 := by
    nlinarith [hsquare]
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith
  · linarith

/-- Squaring `(1,1)` gives `(0,2)`, whose response is four times the imaginary
unit response. Its real-square nonnegativity excludes the remaining negative root. -/
theorem imaginary_unit_readout_eq_one : f (0, 1) = 1 := by
  have hnegative := negative_unit_readout_eq_one f hmul hcal
  have hsquare := hmul (0, 1) (0, 1)
  norm_num [gaussianMul] at hsquare
  rw [hnegative] at hsquare
  have hdiagonal := hmul (1, 1) (1, 1)
  norm_num [gaussianMul] at hdiagonal
  have hdouble := hmul (2, 0) (0, 1)
  norm_num [gaussianMul] at hdouble
  rw [hcal] at hdouble
  have hnonneg : 0 ≤ f (0, 1) := by
    nlinarith [mul_self_nonneg (f (1, 1))]
  have hfactor : (f (0, 1) - 1) * (f (0, 1) + 1) = 0 := by
    nlinarith [hsquare]
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith
  · linarith

/-- Quarter-turn invariance is derived from global Gaussian multiplicativity. -/
theorem quarter_turn_invariant (z : IntegerLattice) :
    f (FiniteTranslationSmallRankSupport.turn z) = f z := by
  have hi := imaginary_unit_readout_eq_one f hmul hcal
  have h := hmul (0, 1) z
  simpa [gaussianMul, FiniteTranslationSmallRankSupport.turn, hi] using h

/-- The supplied calibration and multiplication give exact quadratic doubling. -/
theorem doubling_readout (z : IntegerLattice) : f (z + z) = 4 * f z := by
  have h := hmul (2, 0) z
  rw [hcal] at h
  simpa [gaussianMul, two_mul] using h

end Calibration

section NormSelection

variable (P : IntegerLattice → Fin 4 → ℝ)
variable (hlocal : ∀ j, MixtureCongruent P (fun z => z + localStep j))
variable (hmul : GaussianMultiplicative (fun z => P z 0))
variable (hcal : P (2, 0) 0 = 4)

include hlocal hmul hcal

/-- The four-probe readout is selected by local real-mixture congruence, global
Gaussian multiplicativity and the sole calibration at `(2,0)`. -/
theorem four_probe_readout_eq_norm :
    ∀ z : IntegerLattice, P z 0 = (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 := by
  exact TranslationRankGap.four_probe_readout_eq_norm_of_calibrated P hlocal
    (doubling_readout (fun z => P z 0) hmul hcal)
    (quarter_turn_invariant (fun z => P z 0) hmul hcal)
    (unit_readout_eq_one (fun z => P z 0) hmul hcal)

/-- Nonnegativity follows after selection, without an order assumption on `P`. -/
theorem readout_nonnegative (z : IntegerLattice) : 0 ≤ P z 0 := by
  rw [four_probe_readout_eq_norm P hlocal hmul hcal]
  positivity

/-- Conjugation preserves the selected raw readout. -/
theorem conjugation_invariant (z : IntegerLattice) : P (z.1, -z.2) 0 = P z 0 := by
  simp [four_probe_readout_eq_norm P hlocal hmul hcal]

/-- Along nonnegative integer counts, the selected raw weight is monotone. -/
theorem natural_count_readout_mono {m n : ℕ} (hmn : m ≤ n) :
    P ((m : ℤ), 0) 0 ≤ P ((n : ℤ), 0) 0 := by
  have hreal : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hproduct : 0 ≤ ((n : ℝ) - (m : ℝ)) * ((n : ℝ) + (m : ℝ)) :=
    mul_nonneg (sub_nonneg.mpr hreal) (by positivity)
  simp only [four_probe_readout_eq_norm P hlocal hmul hcal]
  norm_num only [Prod.fst, Prod.snd, Int.cast_natCast, Int.cast_zero, zero_pow,
    add_zero]
  nlinarith [hproduct]

/-- The selected readout obeys the raw parallelogram identity. -/
theorem readout_parallelogram (x y : IntegerLattice) :
    P (x + y) 0 + P (x - y) 0 = 2 * P x 0 + 2 * P y 0 := by
  simp [four_probe_readout_eq_norm P hlocal hmul hcal] <;> ring

/-- Raw third-order inclusion-exclusion vanishes on integer-pair additions. -/
theorem readout_three_way_inclusion_exclusion (x y z : IntegerLattice) :
    P (x + y + z) 0 - P (x + y) 0 - P (x + z) 0 - P (y + z) 0 +
      P x 0 + P y 0 + P z 0 - P (0, 0) 0 = 0 := by
  simp [four_probe_readout_eq_norm P hlocal hmul hcal] <;> ring

end NormSelection

section ConcreteWitness

/-- The concrete squared norm has the supplied Gaussian multiplicativity. -/
theorem normReadout_gaussianMultiplicative : GaussianMultiplicative normReadout := by
  intro z w
  simp [normReadout, gaussianMul]
  ring

/-- The zeroth corner probe is the unshifted squared norm. -/
theorem normProbes_zero (z : IntegerLattice) : normProbes z 0 = normReadout z := by
  change normReadout (z + 0) = normReadout z
  rw [add_zero]

/-- A concrete four-probe instance satisfies exactly the three supplied contracts. -/
theorem normProbes_contract :
    (∀ j, MixtureCongruent normProbes (fun z => z + localStep j)) ∧
      GaussianMultiplicative (fun z => normProbes z 0) ∧
      normProbes (2, 0) 0 = 4 := by
  refine ⟨fun j => normProbes_mixtureCongruent (localStep j), ?_, ?_⟩
  · simpa only [normProbes_zero] using normReadout_gaussianMultiplicative
  · norm_num [normProbes_zero, normReadout]

/-- The supplied contract is inhabited by the existing concrete norm probes. -/
theorem exists_four_probe_contract :
    ∃ P : IntegerLattice → Fin 4 → ℝ,
      (∀ j, MixtureCongruent P (fun z => z + localStep j)) ∧
        GaussianMultiplicative (fun z => P z 0) ∧ P (2, 0) 0 = 4 :=
  ⟨normProbes, normProbes_contract⟩

end ConcreteWitness

end IDT.MultiplicativeMixtureReadout
