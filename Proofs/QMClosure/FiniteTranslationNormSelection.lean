import Proofs.QMClosure.FiniteTranslationSmallRankSupport
import Proofs.QMClosure.QuadraticPolynomialDyadicSelection
import Proofs.QMClosure.FiniteTranslationExponentialPolynomial
import Proofs.QMClosure.MixtureProbeComplexRank

/-!
# Conditional norm selection at small complex translate rank

Finite dimension, complex translate rank below eight, exact quarter-turn
invariance, and exact dyadic scaling select a scalar squared norm on the integer
lattice. The real four-probe application derives the required complex rank bound
from supplied real-ensemble mean congruence. Unit calibration fixes the scalar.
-/

noncomputable section

namespace IDT.TranslationRankGap

open FiniteTranslationSpectrum
open FiniteTranslationDilationSupport
open FiniteTranslationSmallRankSupport
open scoped BigOperators

section ComplexReadout

variable (f : G → ℂ) [FiniteDimensional ℂ (TranslationSpace f)]

/-- Summing the actual components puts the original readout in the trivial
joint block. This includes zero functions and empty actual support. -/
theorem original_mem_trivial_jointBlock_of_finrank_lt_eight
    (hscale : ∀ z, f (z + z) = 4 * f z)
    (hrot : ∀ z, f (turn z) = f z)
    (hrank : Module.finrank ℂ (TranslationSpace f) < 8) :
    original f ∈ jointBlock f (fun _ => 1) := by
  classical
  rw [← sum_readoutComponents f]
  apply (jointBlock f (fun _ => 1)).sum_mem
  intro χ hχ
  have hχone : χ = fun _ => 1 :=
    supported_eq_one_of_finrank_lt_eight f hscale hrot hrank
      (show χ ∈ support f from hχ)
  rw [← hχone]
  exact readoutComponents_mem f χ

/-- The trivial character removes all exponential factors globally. -/
theorem exists_polynomial_of_finrank_lt_eight_dyadic_rotation
    (hscale : ∀ z, f (z + z) = 4 * f z)
    (hrot : ∀ z, f (turn z) = f z)
    (hrank : Module.finrank ℂ (TranslationSpace f) < 8) :
    ∃ P : MvPolynomial (Fin 2) ℂ,
      ∀ m n : ℤ, f (m, n) = MvPolynomial.eval ![(m : ℂ), (n : ℂ)] P := by
  obtain ⟨P, hP⟩ := exists_polynomial_of_jointBlock_mem f (fun _ => 1)
    (by intro i; norm_num) (original f)
    (original_mem_trivial_jointBlock_of_finrank_lt_eight f hscale hrot hrank)
  refine ⟨P, ?_⟩
  intro m n
  simpa [latticeCharacter, original] using hP m n

/-- The bound below eight is sufficient. No sharp-gap assertion is made. -/
theorem readout_eq_scalar_norm_of_finrank_lt_eight_dyadic_rotation
    (hscale : ∀ z, f (z + z) = 4 * f z)
    (hrot : ∀ z, f (turn z) = f z)
    (hrank : Module.finrank ℂ (TranslationSpace f) < 8) :
    ∀ z : G, f z = f (1, 0) * ((z.1 : ℂ) ^ 2 + (z.2 : ℂ) ^ 2) := by
  obtain ⟨P, hP⟩ :=
    exists_polynomial_of_finrank_lt_eight_dyadic_rotation f hscale hrot hrank
  apply polynomial_readout_eq_scalar_norm_of_dyadic_rotation f P hP hscale
  intro m n
  exact hrot (m, n)

theorem readout_eq_norm_of_finrank_lt_eight_dyadic_rotation_of_calibrated
    (hscale : ∀ z, f (z + z) = 4 * f z)
    (hrot : ∀ z, f (turn z) = f z)
    (hrank : Module.finrank ℂ (TranslationSpace f) < 8)
    (hcal : f (1, 0) = 1) :
    ∀ z : G, f z = (z.1 : ℂ) ^ 2 + (z.2 : ℂ) ^ 2 := by
  simpa [hcal] using
    readout_eq_scalar_norm_of_finrank_lt_eight_dyadic_rotation f hscale hrot hrank

end ComplexReadout

section RealFourProbeReadout

open FiniteMixtureContinuationRank

/-- Four real probes and all-real-weight mean congruence provide the complex
rank hypothesis. Rotation and dyadic scaling remain supplied readout laws. -/
theorem four_probe_readout_eq_scalar_norm
    (P : IntegerLattice → Fin 4 → ℝ)
    (hlocal : ∀ j, MixtureCongruent P (fun z => z + localStep j))
    (hscale : ∀ z, P (z + z) 0 = 4 * P z 0)
    (hrot : ∀ z, P (turn z) 0 = P z 0) :
    ∀ z : IntegerLattice,
      P z 0 = P (1, 0) 0 * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) := by
  let f : G → ℂ := fun z => (P z 0 : ℂ)
  letI : FiniteDimensional ℂ (TranslationSpace f) :=
    MixtureProbeComplexRank.translationSpanC_finiteDimensional P hlocal 0
  have hrank : Module.finrank ℂ (TranslationSpace f) < 8 := by
    have hle := MixtureProbeComplexRank.finrank_translationSpanC_le P hlocal 0
    change Module.finrank ℂ (TranslationSpace f) ≤ 4 + 1 at hle
    omega
  have hs : ∀ z, f (z + z) = 4 * f z := by
    intro z
    have h := congrArg Complex.ofReal (hscale z)
    simpa only [f, Complex.ofReal_mul, Complex.ofReal_ofNat] using h
  have hr : ∀ z, f (turn z) = f z := by
    intro z
    exact congrArg Complex.ofReal (hrot z)
  have hselected :=
    readout_eq_scalar_norm_of_finrank_lt_eight_dyadic_rotation f hs hr hrank
  intro z
  apply Complex.ofReal_injective
  simpa only [f, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_pow,
    Complex.ofReal_intCast] using hselected z

theorem four_probe_readout_eq_norm_of_calibrated
    (P : IntegerLattice → Fin 4 → ℝ)
    (hlocal : ∀ j, MixtureCongruent P (fun z => z + localStep j))
    (hscale : ∀ z, P (z + z) 0 = 4 * P z 0)
    (hrot : ∀ z, P (turn z) 0 = P z 0)
    (hcal : P (1, 0) 0 = 1) :
    ∀ z : IntegerLattice, P z 0 = (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 := by
  simpa [hcal] using four_probe_readout_eq_scalar_norm P hlocal hscale hrot

end RealFourProbeReadout

end IDT.TranslationRankGap
