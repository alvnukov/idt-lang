import Proofs.QMClosure.DetectorEffectOperations
import Proofs.QMClosure.ClassicalStatisticalProcessBridge
import Proofs.QMClosure.NativeIsotropicGaussianFamily

/-!
# Endpoint support rigidity for common detectors

A common kernel preserves absolute continuity by Mathlib's measure-composition
lemma. Consequently a common bounded detector has the same exact zero and one
endpoints throughout a mutually absolutely continuous probability family.
Finite directed pairwise KL supplies this support premise. The interior case
is pointwise strict and does not assert a uniform margin. These statements concern
ordinary event probabilities. Identifying a target response with a particular
physical readout is an additional obligation.
-/
namespace IDT.QMClosure.DetectorEndpointSupportWall

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open InvariantEffectReadoutBridge DetectorEffectOperations
open scoped ENNReal NNReal

universe u v w
variable {Ω : Type u} {Y : Type v} {V : Type w}
variable [MeasurableSpace Ω] [MeasurableSpace Y]

/-- Null output events transfer through any common kernel, using the existing
absolute-continuity composition theorem. -/
theorem kernel_event_zero_of_absolutelyContinuous {μ ν : Measure Ω}
    (hμν : μ ≪ ν) (κ : Kernel Ω Y) (s : Set Y)
    (hs : (κ ∘ₘ ν) s = 0) : (κ ∘ₘ μ) s = 0 :=
  (hμν.comp_right κ) hs

/-- A common output event cannot be certain under one preparation and null
under a preparation dominating it. -/
theorem kernel_event_not_one_zero {μ ν : Measure Ω}
    (hμν : μ ≪ ν) (κ : Kernel Ω Y) (s : Set Y) :
    ¬ ((κ ∘ₘ μ) s = 1 ∧ (κ ∘ₘ ν) s = 0) := by
  rintro ⟨hone, hzero⟩
  have h := kernel_event_zero_of_absolutelyContinuous hμν κ s hzero
  rw [hone] at h
  exact one_ne_zero h

/-- A zero acceptance response transfers in the direction of absolute continuity. -/
theorem acceptance_zero_of_absolutelyContinuous {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (g : Effect Ω) (hzero : g.acceptance ν = 0) :
    g.acceptance μ = 0 := by
  have hv : (g.binaryKernel ∘ₘ ν) {true} = 0 := by
    rw [g.binaryKernel_comp_true, hzero, ENNReal.ofReal_zero]
  have hm := kernel_event_zero_of_absolutelyContinuous hμν g.binaryKernel {true} hv
  rw [g.binaryKernel_comp_true, ENNReal.ofReal_eq_zero] at hm
  exact le_antisymm hm (g.acceptance_nonnegative μ)

/-- Apply zero-response transfer to the complementary effect. -/
theorem acceptance_one_of_absolutelyContinuous {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (g : Effect Ω) (hone : g.acceptance ν = 1) :
    g.acceptance μ = 1 := by
  have hv : (complement g).acceptance ν = 0 := by
    rw [acceptance_complement, hone, sub_self]
  have hm := acceptance_zero_of_absolutelyContinuous hμν (complement g) hv
  rw [acceptance_complement] at hm
  linarith

theorem acceptance_zero_iff {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ) (g : Effect Ω) :
    g.acceptance μ = 0 ↔ g.acceptance ν = 0 :=
  ⟨acceptance_zero_of_absolutelyContinuous hνμ g,
    acceptance_zero_of_absolutelyContinuous hμν g⟩

theorem acceptance_one_iff {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ) (g : Effect Ω) :
    g.acceptance μ = 1 ↔ g.acceptance ν = 1 :=
  ⟨acceptance_one_of_absolutelyContinuous hνμ g,
    acceptance_one_of_absolutelyContinuous hμν g⟩

/-- Every common effect is either identically zero, identically one, or strictly
interior at each preparation. No uniform margin is claimed. -/
theorem acceptance_trichotomy (K : V → Measure Ω)
    (hprob : ∀ x, IsProbabilityMeasure (K x))
    (hac : ∀ x y, K x ≪ K y) (g : Effect Ω) :
    (∀ x, g.acceptance (K x) = 0) ∨
      (∀ x, g.acceptance (K x) = 1) ∨
      (∀ x, 0 < g.acceptance (K x) ∧ g.acceptance (K x) < 1) := by
  classical
  letI (x : V) : IsProbabilityMeasure (K x) := hprob x
  by_cases hz : ∃ x, g.acceptance (K x) = 0
  · obtain ⟨x, hx⟩ := hz
    exact Or.inl (fun y => acceptance_zero_of_absolutelyContinuous (hac y x) g hx)
  by_cases ho : ∃ x, g.acceptance (K x) = 1
  · obtain ⟨x, hx⟩ := ho
    exact Or.inr (Or.inl (fun y => acceptance_one_of_absolutelyContinuous (hac y x) g hx))
  exact Or.inr (Or.inr (fun x =>
    ⟨lt_of_le_of_ne (g.acceptance_nonnegative _) (fun h => hz ⟨x, h.symm⟩),
      lt_of_le_of_ne (g.acceptance_le_one _) (fun h => ho ⟨x, h⟩)⟩))

/-- Finite directed pairwise relative entropy supplies absolute continuity. -/
theorem absolutelyContinuous_of_finiteEntropy (K : V → Measure Ω)
    (hfinite : ∀ x y, klDiv (K x) (K y) ≠ ∞) (x y : V) : K x ≪ K y :=
  (klDiv_ne_top_iff.mp (hfinite x y)).1

theorem acceptance_trichotomy_of_finiteEntropy (K : V → Measure Ω)
    (hprob : ∀ x, IsProbabilityMeasure (K x))
    (hfinite : ∀ x y, klDiv (K x) (K y) ≠ ∞) (g : Effect Ω) :
    (∀ x, g.acceptance (K x) = 0) ∨
      (∀ x, g.acceptance (K x) = 1) ∨
      (∀ x, 0 < g.acceptance (K x) ∧ g.acceptance (K x) < 1) :=
  acceptance_trichotomy K hprob (absolutelyContinuous_of_finiteEntropy K hfinite) g

/-- Only probability and finite-entropy fields of this process contract are used. -/
theorem process_acceptance_trichotomy
    (D : ClassicalStatisticalProcessBridge.Contract V Ω) (g : Effect Ω) :
    (∀ x, g.acceptance (D.preparation x) = 0) ∨
      (∀ x, g.acceptance (D.preparation x) = 1) ∨
      (∀ x, 0 < g.acceptance (D.preparation x) ∧ g.acceptance (D.preparation x) < 1) :=
  acceptance_trichotomy_of_finiteEntropy D.preparation D.probability D.finiteEntropy g

/-- Exact matching to a target with a zero and a nonzero value is impossible
for one common bounded effect on this support class. -/
theorem no_effect_matching_zero_target (K : V → Measure Ω)
    (hprob : ∀ x, IsProbabilityMeasure (K x)) (hac : ∀ x y, K x ≪ K y)
    (p : V → ℝ) {x y : V} (hx : p x = 0) (hy : p y ≠ 0) :
    ¬ ∃ g : Effect Ω, ∀ z, g.acceptance (K z) = p z := by
  letI (z : V) : IsProbabilityMeasure (K z) := hprob z
  rintro ⟨g, hg⟩
  apply hy
  rw [← hg y]
  exact acceptance_zero_of_absolutelyContinuous (hac y x) g ((hg x).trans hx)

/-- The complementary endpoint gives the same exact target-matching obstruction. -/
theorem no_effect_matching_one_target (K : V → Measure Ω)
    (hprob : ∀ x, IsProbabilityMeasure (K x)) (hac : ∀ x y, K x ≪ K y)
    (p : V → ℝ) {x y : V} (hx : p x = 1) (hy : p y ≠ 1) :
    ¬ ∃ g : Effect Ω, ∀ z, g.acceptance (K z) = p z := by
  letI (z : V) : IsProbabilityMeasure (K z) := hprob z
  rintro ⟨g, hg⟩
  apply hy
  rw [← hg y]
  exact acceptance_one_of_absolutelyContinuous (hac y x) g ((hg x).trans hx)

/-- Supplied nonzero isotropic variance gives the endpoint rigidity at every
mean. Zero variance is outside this theorem's hypothesis. -/
theorem native_acceptance_trichotomy (v : ℝ≥0) (hv : v ≠ 0)
    (g : Effect NativeGaussianStatisticalProcess.Sample) :
    (∀ m, g.acceptance (NativeIsotropicGaussianFamily.preparation v m) = 0) ∨
      (∀ m, g.acceptance (NativeIsotropicGaussianFamily.preparation v m) = 1) ∨
      (∀ m, 0 < g.acceptance (NativeIsotropicGaussianFamily.preparation v m) ∧
        g.acceptance (NativeIsotropicGaussianFamily.preparation v m) < 1) :=
  acceptance_trichotomy_of_finiteEntropy _ (fun _ => inferInstance)
    (NativeIsotropicGaussianFamily.klDiv_preparation_ne_top v hv) g

end
end IDT.QMClosure.DetectorEndpointSupportWall
