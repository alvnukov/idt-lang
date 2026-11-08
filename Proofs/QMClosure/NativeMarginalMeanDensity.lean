import Proofs.QMClosure.NativeMarginalProcessBridge
import Proofs.QMClosure.NativeGaussianDyadicDensity

/-!
# Dense actual means in a nonconstant first-marginal family

For the supplied real two-coordinate carrier and native mixing channel, two
distinct preparation laws force dense range of the actual complex coordinate
means. The proof transports the existing finite Gaussian-dyadic approximation
programs through the normalized mean image. Finite resource budgets may grow
with the requested approximation. Exact surjectivity is not asserted.

No non-Dirac member or finite-relative-entropy hypothesis is needed. Complex
arithmetic, topology, and the channel geometry remain supplied. This result
does not establish physical access to limits or a uniform resource bound.
-/

namespace IDT.QMClosure.NativeMarginalMeanDensity

noncomputable section

open OperationalContextQuotient
open NativeVacuumProbabilityFamily
open NativeMixerEventConeExclusion (mixer)
open NativeAttenuationCircuit (a b mixer_fst mixer_snd)
open WeightFreeRawProbability (evalRaw)

/-- Membership propagates through every finite raw circuit constructor. -/
theorem evalRaw_mem {α : Type*} {ι : Type} [DecidableEq ι]
    (T : α × α → α × α) (S : Set α)
    (hT : ∀ x ∈ S, ∀ y ∈ S, (T (x, y)).1 ∈ S ∧ (T (x, y)).2 ∈ S)
    (c : Native ι) (v : ι → α) (hv : ∀ i, v i ∈ S) :
    ∀ i, evalRaw T c v i ∈ S := by
  induction c generalizing v with
  | identity => exact hv
  | pair i j hij =>
    intro k
    have hm := hT (v i) (hv i) (v j) (hv j)
    by_cases hki : k = i
    · simpa [evalRaw, hki] using hm.1
    by_cases hkj : k = j
    · simpa [evalRaw, hki, hkj, Ne.symm hij] using hm.2
    · simpa [evalRaw, hki, hkj] using hv k
  | permute e => exact fun i => hv (e i)
  | seq c e hc he => exact he _ (hc _ hv)

/-- Allocated programs stay in a set containing their supplied inputs and
closed under both outputs of the raw operation. -/
theorem eval_mem {α L : Type*} (T : α × α → α × α) (S : Set α)
    (hT : ∀ x ∈ S, ∀ y ∈ S, (T (x, y)).1 ∈ S ∧ (T (x, y)).2 ∈ S)
    (zero : α) (stock : L → α) (hzero : zero ∈ S) (hstock : ∀ l, stock l ∈ S)
    (p : AllocatedPreparation.Program L) :
    AllocatedPreparation.eval T zero stock p ∈ S := by
  apply evalRaw_mem T S hT p.circuit _ _ p.cursor
  intro w
  cases h : p.input w with
  | none => simpa [AllocatedPreparation.inputState, h] using hzero
  | some l => simpa [AllocatedPreparation.inputState, h] using hstock l

universe u

variable {V : Type u}

/-- The actual coordinate means, viewed in the supplied complex plane. -/
def complexMean (D : NativeMarginalProcessBridge.Contract V) (x : V) : ℂ :=
  ⟨(D.mean x).1, (D.mean x).2⟩

@[simp] theorem coordinates_complexMean (D : NativeMarginalProcessBridge.Contract V)
    (x : V) : NativeGaussianStatisticalProcess.coordinates (complexMean D x) = D.mean x :=
  Prod.eta _

theorem complexMean_eq_iff_preparation_eq (D : NativeMarginalProcessBridge.Contract V)
    (x y : V) : complexMean D x = complexMean D y ↔ D.preparation x = D.preparation y := by
  rw [← D.mean_eq_iff_preparation_eq]
  constructor
  · intro h
    simpa only [coordinates_complexMean] using
      congrArg NativeGaussianStatisticalProcess.coordinates h
  · intro h
    exact congrArg (fun s : NativeMarginalProcessBridge.Sample => (⟨s.1, s.2⟩ : ℂ)) h

/-- Both outputs of the raw operation intertwine the actual coordinate means. -/
theorem complexMean_compatibility (D : NativeMarginalProcessBridge.Contract V) (p : V × V) :
    mixer (complexMean D p.1, complexMean D p.2) =
      (complexMean D (D.operation p).1, complexMean D (D.operation p).2) := by
  have h := NativeGaussianStatisticalProcess.mean_compatibility
    (complexMean D p.1, complexMean D p.2)
  simp only [coordinates_complexMean] at h
  have h' := h.symm.trans (D.mean_compatibility p)
  apply Prod.ext
  · apply Complex.ext
    · exact congrArg (fun q => q.1.1) h'
    · exact congrArg (fun q => q.1.2) h'
  · apply Complex.ext
    · exact congrArg (fun q => q.2.1) h'
    · exact congrArg (fun q => q.2.2) h'

/-- Affine normalization preserves the supplied native mixer. -/
theorem mixer_affine (z w c d : ℂ) :
    mixer ((z - c) / d, (w - c) / d) =
      (((mixer (z, w)).1 - c) / d, ((mixer (z, w)).2 - c) / d) := by
  apply Prod.ext
  · simp only [mixer_fst]
    unfold a b
    ring
  · simp only [mixer_snd]
    unfold a b
    ring

def normalizedMean (D : NativeMarginalProcessBridge.Contract V) (x₀ x₁ x : V) : ℂ :=
  (complexMean D x - complexMean D x₀) / (complexMean D x₁ - complexMean D x₀)

theorem normalizedMean_compatibility (D : NativeMarginalProcessBridge.Contract V)
    (x₀ x₁ : V) (p : V × V) :
    mixer (normalizedMean D x₀ x₁ p.1, normalizedMean D x₀ x₁ p.2) =
      (normalizedMean D x₀ x₁ (D.operation p).1,
        normalizedMean D x₀ x₁ (D.operation p).2) := by
  unfold normalizedMean
  rw [mixer_affine, complexMean_compatibility]

/-- Every existing finite scalar program occurs in the normalized mean image. -/
theorem scalarProgram_mem_normalizedRange (D : NativeMarginalProcessBridge.Contract V)
    (x₀ x₁ : V) (h : D.preparation x₀ ≠ D.preparation x₁)
    (p : NativeAllocatedSourceArithmetic.ScalarProgram) :
    NativeAllocatedSourceArithmetic.value p ∈ Set.range (normalizedMean D x₀ x₁) := by
  have hd : complexMean D x₁ - complexMean D x₀ ≠ 0 := by
    intro hz
    apply h
    exact (complexMean_eq_iff_preparation_eq D x₀ x₁).mp (sub_eq_zero.mp hz).symm
  apply eval_mem mixer (Set.range (normalizedMean D x₀ x₁)) _ 0 (fun _ : Unit => 1) _ _ p
  · intro z hz w hw
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, rfl⟩ := hw
    have hm := normalizedMean_compatibility D x₀ x₁ (x, y)
    exact ⟨⟨(D.operation (x, y)).1, (congrArg Prod.fst hm).symm⟩,
      ⟨(D.operation (x, y)).2, (congrArg Prod.snd hm).symm⟩⟩
  · exact ⟨x₀, by simp [normalizedMean]⟩
  · intro l
    exact ⟨x₁, by simp [normalizedMean, hd]⟩

/-- Two distinct preparation laws force dense range of the actual complex means.
The preexisting scalar compiler supplies finite approximation witnesses. -/
theorem denseRange_complexMean_of_ne (D : NativeMarginalProcessBridge.Contract V)
    (x₀ x₁ : V) (h : D.preparation x₀ ≠ D.preparation x₁) :
    DenseRange (complexMean D) := by
  have hd : complexMean D x₁ - complexMean D x₀ ≠ 0 := by
    intro hz
    apply h
    exact (complexMean_eq_iff_preparation_eq D x₀ x₁).mp (sub_eq_zero.mp hz).symm
  have hnorm : 0 < ‖complexMean D x₁ - complexMean D x₀‖ := norm_pos_iff.mpr hd
  apply Metric.denseRange_iff.mpr
  intro z ε hε
  obtain ⟨p, hp⟩ := NativeGaussianDyadicDensity.exists_program_approx
    ((z - complexMean D x₀) / (complexMean D x₁ - complexMean D x₀))
    (ε / ‖complexMean D x₁ - complexMean D x₀‖) (div_pos hε hnorm)
  obtain ⟨x, hx⟩ := scalarProgram_mem_normalizedRange D x₀ x₁ h p
  have heq : complexMean D x - z =
      (NativeAllocatedSourceArithmetic.value p -
        (z - complexMean D x₀) / (complexMean D x₁ - complexMean D x₀)) *
        (complexMean D x₁ - complexMean D x₀) := by
    rw [← hx]
    unfold normalizedMean
    field_simp [hd]
    ring
  refine ⟨x, ?_⟩
  rw [dist_eq_norm, norm_sub_rev, heq, norm_mul]
  exact (lt_div_iff₀ hnorm).mp hp

theorem denseRange_complexMean (D : NativeMarginalProcessBridge.Contract V)
    (h : ∃ x₀ x₁, D.preparation x₀ ≠ D.preparation x₁) :
    DenseRange (complexMean D) := by
  obtain ⟨x₀, x₁, h⟩ := h
  exact denseRange_complexMean_of_ne D x₀ x₁ h

/-- Exact coverage follows only with the additional closed-image premise. -/
theorem surjective_complexMean_of_closed (D : NativeMarginalProcessBridge.Contract V)
    (h : ∃ x₀ x₁, D.preparation x₀ ≠ D.preparation x₁)
    (hclosed : IsClosed (Set.range (complexMean D))) :
    Function.Surjective (complexMean D) := by
  intro z
  have hz : z ∈ closure (Set.range (complexMean D)) := denseRange_complexMean D h z
  rw [hclosed.closure_eq] at hz
  exact hz

end
end IDT.QMClosure.NativeMarginalMeanDensity
