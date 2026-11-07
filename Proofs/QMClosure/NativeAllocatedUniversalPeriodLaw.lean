import Proofs.QMClosure.NativeAllocatedContextAttenuation
import Proofs.QMClosure.NativeAllocatedStableObservation

/-!
# The exact common-period criterion for the generated response law

Full contextual separation is equivalent to the absence of one positive
reference-iteration period shared by every generated reference and input.
Individual orbits may have their own periods: no individually nonperiodic-orbit
necessity is asserted. The condition retains infinite time and family
quantifiers and is not a finite empirical certificate.

Affine context evaluation intertwines reference iteration as an equality of
selected generated values. This gives neither full retained-array equality nor
resource equality. Transformed references are generated known values and must
be separately prepared and charged. No topology or finite-codomain premise is
used. The existing single-basis law transports any supplied scalar family's
whole probability field unchanged; no detector, probability provenance,
physical availability, multi-source probability extension, actualization, or
QM closure is established.
-/

namespace IDT.QMClosure.NativeAllocatedUniversalPeriodLaw

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open OperationalContextQuotient ResponseContextQuotient
open NativeAllocatedObservationBoundary NativeAllocatedStableObservation
open NativeAllocatedSignatureLaw
open NativeAttenuationCircuit (a)

variable {Ω : Type*}

/-- One length is a signature period simultaneously for every reference/input. -/
def UniversalPeriod (σ : G → Ω) (L : ℕ) : Prop :=
  ∀ z x : G, σ ((referenceStep z)^[L] x) = σ x

def NoCommonPositivePeriod (σ : G → Ω) : Prop :=
  ∀ L : ℕ, 0 < L → ∃ z x : G, σ ((referenceStep z)^[L] x) ≠ σ x

theorem universalPeriod_zero (σ : G → Ω) : UniversalPeriod σ 0 := by
  intro z x
  rfl

/-- This equality concerns selected scalar values and generated references,
without asserting equality of full retained outputs or preparation costs. -/
theorem context_reference_iterate (C : Context G) (z x : G) (n : ℕ) :
    C.eval operationG ((referenceStep z)^[n] x) =
      (referenceStep (C.eval operationG z))^[n] (C.eval operationG x) := by
  apply Subtype.ext
  simp only [NativeAllocatedContextAttenuation.eval_affine, referenceStep_iterate_coe]
  ring

/-- Global bare-signature periodicity is stable under every stated context. -/
theorem responseEq_reference_iterate_of_universalPeriod (σ : G → Ω) (L : ℕ)
    (h : UniversalPeriod σ L) (z x : G) :
    ResponseEq operationG σ x ((referenceStep z)^[L] x) := by
  intro C
  rw [context_reference_iterate]
  exact (h (C.eval operationG z) (C.eval operationG x)).symm

private theorem normSq_a : Complex.normSq a = (1 / 2 : ℝ) := by
  norm_num [a, Complex.normSq_apply, Complex.div_re, Complex.div_im]

private theorem a_pow_ne_one (L : ℕ) (hL : 0 < L) : a^L ≠ 1 := by
  intro h
  have hn := congrArg Complex.normSq h
  rw [map_pow, normSq_a, map_one] at hn
  have hlt : (1 / 2 : ℝ)^L < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (Nat.ne_of_gt hL)
  exact (ne_of_lt hlt) hn

theorem reference_iterate_unit_zero_ne_zero (L : ℕ) (hL : 0 < L) :
    (referenceStep unitG)^[L] zeroG ≠ zeroG := by
  intro h
  have hv := congrArg Subtype.val h
  rw [referenceStep_iterate_coe, val_unitG, val_zeroG] at hv
  apply a_pow_ne_one L hL
  apply sub_eq_zero.mp
  calc
    a^L - 1 = -(1 + a^L * (0 - 1)) := by ring
    _ = 0 := by rw [hv]; ring

theorem separates_iff_noCommonPositivePeriod (σ : G → Ω) :
    Separates σ ↔ NoCommonPositivePeriod σ := by
  constructor
  · intro hsep L hL
    by_contra hn
    have hp : UniversalPeriod σ L := by
      intro z x
      by_contra hzx
      exact hn ⟨z, x, hzx⟩
    have heq := hsep zeroG ((referenceStep unitG)^[L] zeroG)
      (responseEq_reference_iterate_of_universalPeriod σ L hp unitG zeroG)
    exact reference_iterate_unit_zero_ne_zero L hL heq.symm
  · intro h x y hxy
    by_contra hne
    obtain ⟨L, hL, hret⟩ := common_contextual_return_of_distinct_responseEq σ hne hxy
    obtain ⟨z, w, hzw⟩ := h L hL
    exact hzw (signature_eq (hret z w)).symm

theorem nonconstant_of_noCommonPositivePeriod (σ : G → Ω)
    (h : NoCommonPositivePeriod σ) : ∃ x y : G, σ x ≠ σ y := by
  obtain ⟨z, x, hzx⟩ := h 1 (by decide)
  exact ⟨(referenceStep z)^[1] x, x, hzx⟩

theorem law_nonempty_iff_noCommonPositivePeriod (σ : G → Ω) :
    Nonempty (ResponseNativeProbabilitySelection.Law (signatureData σ) unitG) ↔
      NoCommonPositivePeriod σ :=
  (law_nonempty_iff_separates σ).trans (separates_iff_noCommonPositivePeriod σ)

def lawOfScalarOfNoCommonPositivePeriod (σ : G → Ω) (h : NoCommonPositivePeriod σ)
    (L : NativeVacuumProbabilityFamily.Law) :
    ResponseNativeProbabilitySelection.Law (signatureData σ) unitG :=
  NativeAllocatedSignatureLaw.lawOfScalar σ
    ((separates_iff_noCommonPositivePeriod σ).mpr h) L

theorem lawOfScalarOfNoCommonPositivePeriod_probability (σ : G → Ω)
    (h : NoCommonPositivePeriod σ) (L : NativeVacuumProbabilityFamily.Law) :
    @ResponseNativeProbabilitySelection.Law.prob G Ω (signatureData σ) unitG
        (lawOfScalarOfNoCommonPositivePeriod σ h L) =
      @NativeVacuumProbabilityFamily.Law.prob L := rfl

end
end IDT.QMClosure.NativeAllocatedUniversalPeriodLaw
