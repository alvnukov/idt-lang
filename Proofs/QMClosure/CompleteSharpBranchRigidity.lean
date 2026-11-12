import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic

/-! Conditional complete sharp-branch uniqueness from atomic factorization and
all-reference effect interchange. Separating reference effects are supplied.
No joint-state tomography is assumed. The all-effect interchange contract
requires an operational justification beyond discard naturality.
-/

namespace IDT.QMClosure.CompleteSharpBranchRigidity

open Set

variable {V R X : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup R] [Module ℝ R] [AddCommGroup X] [Module ℝ X]

/-- Normalized atomicity extends to zero-inclusive unnormalized outputs when
the normalization effect is strictly positive on every nonzero cone element.
Faithfulness is supplied explicitly. -/
theorem unnormalized_atomicity_of_normalized
    (KX : Set X) (localMarg : X →ₗ[ℝ] V) (refMarg : X →ₗ[ℝ] R)
    (append : R →ₗ[ℝ] X) (p : V) (u : V →ₗ[ℝ] ℝ) (hunit : u p = 1)
    (hscale : ∀ a : ℝ, 0 ≤ a → ∀ z ∈ KX, a • z ∈ KX)
    (hfaithful : ∀ z ∈ KX, z ≠ 0 → 0 < u (localMarg z))
    (hnormalized : ∀ z ∈ KX, u (localMarg z) = 1 → localMarg z = p →
      z = append (refMarg z)) :
    ∀ z ∈ KX, localMarg z = u (localMarg z) • p → z = append (refMarg z) := by
  intro z hz hpointer
  by_cases hzero : z = 0
  · simp [hzero]
  let a := u (localMarg z)
  have ha : 0 < a := hfaithful z hz hzero
  let v := a⁻¹ • z
  have hv : v ∈ KX := hscale _ (inv_nonneg.mpr ha.le) _ hz
  have hlocal : localMarg v = p := by
    change localMarg (a⁻¹ • z) = p
    rw [map_smul, hpointer, smul_smul]
    change (a⁻¹ * a) • p = p
    rw [inv_mul_cancel₀ (ne_of_gt ha), one_smul]
  have hnorm : u (localMarg v) = 1 := by rw [hlocal, hunit]
  have hfactor := hnormalized v hv hnorm hlocal
  have hrestore := congrArg (fun w : X => a • w) hfactor
  simpa only [v, map_smul, smul_smul, mul_inv_cancel₀ (ne_of_gt ha), one_smul] using hrestore

/-- Two positive complete lifts of one rank-one local branch agree when every
reference effect interchanges with both lifts and output atomicity holds. -/
theorem complete_sharp_branch_unique
    (KX : Set X) (hspan : Submodule.span ℝ KX = ⊤)
    (localMarg : X →ₗ[ℝ] V) (refMarg : X →ₗ[ℝ] R) (append : R →ₗ[ℝ] X)
    (p : V) (u e : V →ₗ[ℝ] ℝ) (hunit : u p = 1)
    (H : Set (R →ₗ[ℝ] ℝ)) (slice : (R →ₗ[ℝ] ℝ) → X →ₗ[ℝ] V)
    (hseparate : ∀ r s : R, (∀ h ∈ H, h r = h s) → r = s)
    (hproduct : ∀ h ∈ H, ∀ r : R, slice h (append r) = h r • p)
    (hatomic : ∀ z ∈ KX,
      localMarg z = u (localMarg z) • p → z = append (refMarg z))
    (M N : X →ₗ[ℝ] X) (L : V →ₗ[ℝ] V)
    (hM : MapsTo M KX KX) (hN : MapsTo N KX KX)
    (hrank : ∀ v : V, L v = e v • p)
    (hlocalM : localMarg.comp M = L.comp localMarg)
    (hlocalN : localMarg.comp N = L.comp localMarg)
    (heffectM : ∀ h ∈ H, (slice h).comp M = L.comp (slice h))
    (heffectN : ∀ h ∈ H, (slice h).comp N = L.comp (slice h)) : M = N := by
  apply LinearMap.ext_on hspan
  intro x hx
  have hLM : localMarg (M x) = e (localMarg x) • p := by
    have h := DFunLike.congr_fun hlocalM x
    exact h.trans (hrank _)
  have hLN : localMarg (N x) = e (localMarg x) • p := by
    have h := DFunLike.congr_fun hlocalN x
    exact h.trans (hrank _)
  have hMx : M x = append (refMarg (M x)) := by
    apply hatomic _ (hM hx)
    rw [hLM, map_smul, hunit]
    simp
  have hNx : N x = append (refMarg (N x)) := by
    apply hatomic _ (hN hx)
    rw [hLN, map_smul, hunit]
    simp
  have href : refMarg (M x) = refMarg (N x) := by
    apply hseparate
    intro h hh
    have hSM : slice h (M x) = e (slice h x) • p := by
      exact (DFunLike.congr_fun (heffectM h hh) x).trans (hrank _)
    have hSN : slice h (N x) = e (slice h x) • p := by
      exact (DFunLike.congr_fun (heffectN h hh) x).trans (hrank _)
    have hreadM := congrArg u hSM
    have hreadN := congrArg u hSN
    rw [hMx, hproduct h hh] at hreadM
    rw [hNx, hproduct h hh] at hreadN
    simp only [map_smul, hunit, smul_eq_mul, mul_one] at hreadM hreadN
    exact hreadM.trans hreadN.symm
  rw [hMx, hNx, href]

end IDT.QMClosure.CompleteSharpBranchRigidity
