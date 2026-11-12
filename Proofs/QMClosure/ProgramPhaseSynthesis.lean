import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Tactic

/-! Conditional phase synthesis from mixed-program linearity and one recoverable
response. The recovery map, its left-inverse equation and its normalized-base
preservation are supplied premises. Normalization of a controlled process alone
does not establish recovery. The module leaves operational construction of the
responses and their complete destructive-branch identification external.
-/

namespace IDT.QMClosure.ProgramPhaseSynthesis

section Ring

variable {D : Type*} [Ring D]

/-- A left recovery fixes every vector already fixed by its response. -/
theorem recovery_fixes_destructive (F R E : D)
    (hrecover : R * F = 1) (hfix : F * E = E) : R * E = E := by
  calc
    R * E = R * (F * E) := by rw [hfix]
    _ = E := by rw [← mul_assoc, hrecover, one_mul]

/-- One recoverable response and the mixed-response sum determine an involutive
relative phase. The second response requires no inverse premise. -/
theorem recoverable_phase_package (Fplus Fminus R E : D)
    (hsum : Fplus + Fminus = 2 * E)
    (hrecover : R * Fplus = 1) (hfix : Fplus * E = E)
    (hidempotent : E * E = E) :
    R * Fminus = 2 * E - 1 ∧
      (R * Fminus) * (R * Fminus) = 1 ∧ 1 + R * Fminus = 2 * E := by
  have hRE := recovery_fixes_destructive Fplus R E hrecover hfix
  have hminus : Fminus = 2 * E - Fplus := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hsum
  have hphase : R * Fminus = 2 * E - 1 := by
    rw [hminus, mul_sub, ← mul_assoc R 2 E]
    have htwo : R * (2 : D) = 2 * R := by noncomm_ring
    rw [htwo, mul_assoc, hRE, hrecover]
  refine ⟨hphase, ?_, ?_⟩
  · rw [hphase]
    noncomm_ring [hidempotent]
  · rw [hphase]
    noncomm_ring

/-- Binary pointer fixation supplies fixation of the summed destructive range. -/
theorem binary_pointer_range_fixed (F P Q : D)
    (hP : F * P = P) (hQ : F * Q = Q) : F * (P + Q) = P + Q := by
  rw [mul_add, hP, hQ]

/-- An orthogonal binary projector table makes the destructive sum idempotent. -/
theorem binary_projector_idempotent (P Q : D)
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) :
    (P + Q) * (P + Q) = P + Q := by
  noncomm_ring [hP, hQ, hPQ, hQP]

end Ring

section Programs

variable {T V : Type*} [AddCommGroup T] [Module ℝ T]
  [AddCommGroup V] [Module ℝ V]

/-- Equal mixed programs give the exact sum of the two control responses. -/
theorem program_response_sum
    (Φ : T →ₗ[ℝ] Module.End ℝ V) (tplus tminus yplus yminus : T)
    (Fplus Fminus E : Module.End ℝ V)
    (hmixed : tplus + tminus = yplus + yminus)
    (htplus : Φ tplus = Fplus) (htminus : Φ tminus = Fminus)
    (hyplus : Φ yplus = E) (hyminus : Φ yminus = E) :
    Fplus + Fminus = 2 * E := by
  simpa only [map_add, htplus, htminus, hyplus, hyminus, two_mul] using congrArg Φ hmixed

/-- Mixed-program linearity and a supplied left recovery synthesize the sharp
phase formula, its involution and the half-sum projector identity. -/
theorem program_phase_package
    (Φ : T →ₗ[ℝ] Module.End ℝ V) (tplus tminus yplus yminus : T)
    (Fplus Fminus R E : Module.End ℝ V)
    (hmixed : tplus + tminus = yplus + yminus)
    (htplus : Φ tplus = Fplus) (htminus : Φ tminus = Fminus)
    (hyplus : Φ yplus = E) (hyminus : Φ yminus = E)
    (hrecover : R * Fplus = 1) (hfix : Fplus * E = E)
    (hidempotent : E * E = E) :
    R * Fminus = 2 * E - 1 ∧
      (R * Fminus) * (R * Fminus) = 1 ∧
      (1 / 2 : ℝ) • (1 + R * Fminus) = E := by
  have hsum := program_response_sum Φ tplus tminus yplus yminus Fplus Fminus E
    hmixed htplus htminus hyplus hyminus
  obtain ⟨hphase, hinvol, hdouble⟩ :=
    recoverable_phase_package Fplus Fminus R E hsum hrecover hfix hidempotent
  refine ⟨hphase, hinvol, ?_⟩
  rw [hdouble, two_mul]
  module

/-- Preservation of the supplied set K follows by composition. It can model a
normalized base. Cone positivity requires preservation of the actual cone or a
separate generating argument. Involution supplies the same set-preserving inverse. -/
theorem normalized_recovered_phase
    (K : Set V) (Fminus R : Module.End ℝ V)
    (hminus : Set.MapsTo Fminus K K) (hR : Set.MapsTo R K K)
    (hinvol : (R * Fminus) * (R * Fminus) = 1) :
    ∃ J : V ≃ₗ[ℝ] V, J.toLinearMap = R * Fminus ∧
      Set.MapsTo J K K ∧ Set.MapsTo J.symm K K ∧
      J.toLinearMap * J.toLinearMap = 1 := by
  let f := R * Fminus
  have hf : ∀ v, f (f v) = v := DFunLike.congr_fun hinvol
  let J : V ≃ₗ[ℝ] V := { f with invFun := f, left_inv := hf, right_inv := hf }
  refine ⟨J, rfl, ?_, ?_, hinvol⟩
  · intro v hv
    exact hR (hminus hv)
  · intro v hv
    exact hR (hminus hv)

end Programs

end IDT.QMClosure.ProgramPhaseSynthesis
