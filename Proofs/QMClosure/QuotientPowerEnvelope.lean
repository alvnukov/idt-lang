import Proofs.QMClosure.ComplexAtomicitySpectralBoundary
import Proofs.QMClosure.ComplementaryPowerEnvelope
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Power envelopes descend along a supplied surjective continuous linear
intertwiner to a complete target. Banach–Steinhaus converts pointwise bounds
into a uniform operator bound, so the source space requires no completeness.
The general quotient rate bound applies over real or complex scalars without
finite-dimensionality. Quotient operators, surjectivity, intertwining, and their
complement identity are supplied. Construction of a physical quotient, real
complexification, and Lie-theoretic atomicity remain separate obligations. -/

namespace IDT.QMClosure.QuotientPowerEnvelope

section Intertwining

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A continuous linear intertwiner also intertwines every natural power. -/
theorem intertwining_power (π : E →L[𝕜] F) (T : E →L[𝕜] E) (S : F →L[𝕜] F)
    (intertwines : π.comp T = S.comp π) (n : ℕ) :
    π.comp (T ^ n) = (S ^ n).comp π := by
  induction n with
  | zero => ext x; simp
  | succ n ih =>
      ext x
      have hstep (u : E) : π (T u) = S (π u) :=
        DFunLike.congr_fun intertwines u
      have hin (u : E) : π ((T ^ n) u) = (S ^ n) (π u) :=
        DFunLike.congr_fun ih u
      simp only [pow_succ', ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply]
      rw [hstep, hin]

end Intertwining

section PowerEnvelope

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- Uniform power envelopes descend to a complete surjective image.
The source normed space may be incomplete. -/
theorem surjective_power_envelope (π : E →L[𝕜] F)
    (T : E →L[𝕜] E) (S : F →L[𝕜] F)
    (surjective : Function.Surjective π)
    (intertwines : π.comp T = S.comp π)
    {q C : ℝ} (hq : 0 < q)
    (bound : ∀ n : ℕ, ‖T ^ n‖ ≤ C * q ^ n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, ‖S ^ n‖ ≤ D * q ^ n := by
  let g : ℕ → F →L[𝕜] F := fun n => ((q : 𝕜) ^ n)⁻¹ • (S ^ n)
  have normalize_apply (n : ℕ) (y : F) :
      ‖g n y‖ = ‖(S ^ n) y‖ / q ^ n := by
    dsimp [g]
    simp only [norm_smul, norm_inv, norm_pow,
      RCLike.norm_ofReal, abs_of_pos hq]
    rw [div_eq_inv_mul]
  have normalize_operator (n : ℕ) : ‖g n‖ = ‖S ^ n‖ / q ^ n := by
    dsimp [g]
    rw [norm_smul, norm_inv, norm_pow, RCLike.norm_ofReal, abs_of_pos hq,
      div_eq_inv_mul]
  have pointwise : ∀ y : F, ∃ D : ℝ, ∀ n : ℕ, ‖g n y‖ ≤ D := by
    intro y
    obtain ⟨x, hx⟩ := surjective y
    refine ⟨‖π‖ * C * ‖x‖, ?_⟩
    intro n
    rw [normalize_apply]
    apply (div_le_iff₀ (pow_pos hq n)).mpr
    have transport : (S ^ n) y = π ((T ^ n) x) := by
      have h := DFunLike.congr_fun (intertwining_power π T S intertwines n) x
      simpa only [ContinuousLinearMap.comp_apply, hx] using h.symm
    calc
      ‖(S ^ n) y‖ = ‖π ((T ^ n) x)‖ := congrArg norm transport
      _ ≤ ‖π‖ * ‖(T ^ n) x‖ := π.le_opNorm _
      _ ≤ ‖π‖ * (‖T ^ n‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left ((T ^ n).le_opNorm x) (norm_nonneg π)
      _ ≤ ‖π‖ * ((C * q ^ n) * ‖x‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (bound n) (norm_nonneg x)) (norm_nonneg π)
      _ = (‖π‖ * C * ‖x‖) * q ^ n := by ring
  obtain ⟨D, hD⟩ := banach_steinhaus pointwise
  refine ⟨D, (norm_nonneg (g 0)).trans (hD 0), ?_⟩
  intro n
  apply (div_le_iff₀ (pow_pos hq n)).mp
  rw [← normalize_operator]
  exact hD n

/-- Complementary quotient operators inherit the sum-of-rates bound from original
operator envelopes. Completeness and nontriviality are needed only on the target. -/
theorem quotient_complementary_rate_bound [Nontrivial F]
    (π : E →L[𝕜] F) (A B : E →L[𝕜] E) (quotientA quotientB : F →L[𝕜] F)
    (surjective : Function.Surjective π)
    (intertwinesA : π.comp A = quotientA.comp π)
    (intertwinesB : π.comp B = quotientB.comp π)
    {c : 𝕜} {qA qB CA CB : ℝ} (hqA : 0 < qA) (hqB : 0 < qB)
    (boundA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * qA ^ n)
    (boundB : ∀ n : ℕ, ‖B ^ n‖ ≤ CB * qB ^ n)
    (complement : quotientA + quotientB = c • (1 : F →L[𝕜] F)) :
    ‖c‖ ≤ qA + qB := by
  obtain ⟨DA, _, hA⟩ := surjective_power_envelope π A quotientA
    surjective intertwinesA hqA boundA
  obtain ⟨DB, _, hB⟩ := surjective_power_envelope π B quotientB
    surjective intertwinesB hqB boundB
  exact ComplementaryPowerEnvelope.complementary_operator_rate_bound
    quotientA quotientB c DA DB qA qB hqA hqB complement hA hB

end PowerEnvelope

section FiniteComplexQuotient

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F] [Nontrivial F]

/-- The finite complex scalar bound follows from power envelopes on the original
operators and a supplied surjective intertwining quotient. -/
theorem finite_complex_quotient_scalar_bound
    (π : E →L[ℂ] F) (A B : E →L[ℂ] E) (quotientA quotientB : F →L[ℂ] F)
    (surjective : Function.Surjective π)
    (intertwinesA : π.comp A = quotientA.comp π)
    (intertwinesB : π.comp B = quotientB.comp π)
    {q c CA CB : ℝ} (hq : 0 < q)
    (boundA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * q ^ n)
    (boundB : ∀ n : ℕ, ‖B ^ n‖ ≤ CB * q ^ n)
    (complement : quotientA + quotientB = (c : ℂ) • (1 : F →L[ℂ] F)) :
    c ≤ 2 * q := by
  obtain ⟨DA, _, hA⟩ := surjective_power_envelope π A quotientA
    surjective intertwinesA hq boundA
  obtain ⟨DB, _, hB⟩ := surjective_power_envelope π B quotientB
    surjective intertwinesB hq boundB
  exact ComplexAtomicitySpectralBoundary.finite_dimensional_complementary_operator_scalar_bound
    quotientA quotientB complement hq hA hB

end FiniteComplexQuotient

end IDT.QMClosure.QuotientPowerEnvelope
