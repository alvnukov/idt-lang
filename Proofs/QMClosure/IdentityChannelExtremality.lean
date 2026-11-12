import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Identity extremality for a compact convex spanning normalized state base.
The operational interpretation of a map preserving this base is supplied by the caller.
No quantum representation or physical origin is asserted here. -/

namespace IDT.QMClosure

open Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- A linear map fixed on all extreme points is fixed on a compact convex base. -/
theorem fixed_on_compact_convex_of_extreme
    {Ω : Set V} (hc : IsCompact Ω) (hv : Convex ℝ Ω)
    (F : V →ₗ[ℝ] V) (hF : ∀ x ∈ Ω.extremePoints ℝ, F x = x) :
    ∀ x ∈ Ω, F x = x := by
  let K := LinearMap.ker (F - LinearMap.id)
  have hclosed : IsClosed (K : Set V) := by
    exact isClosed_eq (F - LinearMap.id).continuous_of_finiteDimensional continuous_const
  have hsub : Ω.extremePoints ℝ ⊆ (K : Set V) := by
    intro x hx
    change F x - x = 0
    exact sub_eq_zero.mpr (hF x hx)
  have hHull : closure (convexHull ℝ (Ω.extremePoints ℝ)) ⊆ (K : Set V) :=
    closure_minimal (convexHull_min hsub K.convex) hclosed
  rw [closure_convexHull_extremePoints hc hv] at hHull
  intro x hx
  exact sub_eq_zero.mp (hHull hx)

/-- The identity is extreme among linear maps preserving a compact convex spanning base.
Preserving the normalized state base packages the positivity/normalization bridge. -/
theorem identity_channel_extreme
    {Ω : Set V} (hc : IsCompact Ω) (hv : Convex ℝ Ω)
    (hspan : Submodule.span ℝ Ω = ⊤)
    (F G : V →ₗ[ℝ] V) (hF : MapsTo F Ω Ω) (hG : MapsTo G Ω Ω)
    (haverage : (1 / 2 : ℝ) • (F + G) = LinearMap.id) :
    F = LinearMap.id ∧ G = LinearMap.id := by
  have hext : ∀ x ∈ Ω.extremePoints ℝ, F x = x ∧ G x = x := by
    intro x hx
    have havg : (1 / 2 : ℝ) • (F x + G x) = x :=
      DFunLike.congr_fun haverage x
    have hmid : x ∈ openSegment ℝ (F x) (G x) := by
      have hm : midpoint ℝ (F x) (G x) = x := by
        simpa [midpoint_eq_smul_add] using havg
      have hmemb := midpoint_mem_openSegment (𝕜 := ℝ) (F x) (G x)
      rw [hm] at hmemb
      exact hmemb
    exact (mem_extremePoints.mp hx).2 _ (hF hx.1) _ (hG hx.1) hmid
  constructor
  · exact LinearMap.ext_on hspan
      (fixed_on_compact_convex_of_extreme hc hv F fun x hx => (hext x hx).1)
  · exact LinearMap.ext_on hspan
      (fixed_on_compact_convex_of_extreme hc hv G fun x hx => (hext x hx).2)

end IDT.QMClosure
