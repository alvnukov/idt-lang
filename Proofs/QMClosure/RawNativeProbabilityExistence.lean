import Proofs.QMClosure.RawNativeProbabilitySelection

/-!
# Exact existence boundary for raw native probability families

The six-field raw probability contract is consistent exactly when the Gaussian
integer action on the chosen reference is injective. Equivalently, that
reference has infinite additive order in the reconstructed carrier. This is a
condition on its generated orbit, not on the whole raw type or feature map.

Necessity uses actual native numerator witnesses, raw coordinate swaps, and
fresh zero ports. The previously proved conditional selection theorem is used
without any consistency witness. Sufficiency constructs a separate canonical
law only after exact raw equality has been shown to preserve scalar amplitudes.

Positive reference weight suffices, but is not asserted necessary. The zero
reference cannot support this contract. No physical availability, probability
actualization, normalization control, or full QM closure is established.
-/

namespace IDT.QMClosure.RawNativeProbabilityExistence

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open RawOperationalHilbert RawNativeScalarCircuitBridge
open RawNativeDyadicSemantics RawNativeProbabilitySelection
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open NativeGaussianResponse

variable {V : Type*} (d : Data V) (v : Data.Carrier d)

section NativeEvents

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Literal vacuum padding retains the old raw coordinates. -/
theorem rawPrepared_pad_inl (s : ι) (c : Native ι) (i : ι) :
    rawPrepared d v (Sum.inl s) (padCircuit κ c) (Sum.inl i) =
      rawPrepared d v s c i := by
  have h := native_output_related d v (Sum.inl s) (padCircuit κ c) (Sum.inl i)
  rw [pad_prepared] at h
  exact related_raw_unique d v h (native_output_related d v s c i)

/-- Every newly padded raw coordinate is the reconstructed zero. -/
theorem rawPrepared_pad_inr (s : ι) (c : Native ι) (j : κ) :
    rawPrepared d v (Sum.inl s) (padCircuit κ c) (Sum.inr j) = 0 := by
  have h := native_output_related d v (Sum.inl s) (padCircuit κ c) (Sum.inr j)
  rw [pad_prepared] at h
  exact related_raw_unique d v h (related_zero d v)

/-- A swap of equal literal raw coordinates fixes the entire raw array. -/
theorem raw_equal_coordinate_probabilities (L : RawLaw d v)
    (s : ι) (c : Native ι) (i j : ι)
    (hcoord : rawPrepared d v s c i = rawPrepared d v s c j) :
    L.prob s c i = L.prob s c j := by
  have he : rawPrepared d v s (.seq c (.permute (Equiv.swap i j))) =
      rawPrepared d v s c := by
    ext k
    change rawPrepared d v s c (Equiv.swap i j k) = rawPrepared d v s c k
    by_cases hki : k = i
    · subst k
      simpa only [Equiv.swap_apply_left] using hcoord.symm
    by_cases hkj : k = j
    · subst k
      simpa only [Equiv.swap_apply_right] using hcoord
    · simp only [Equiv.swap_apply_def, if_neg hki, if_neg hkj]
  have hs := congrFun (L.prepared_eq s (.seq c (.permute (Equiv.swap i j))) c he) i
  have hp := L.output_perm s c (Equiv.swap i j) i
  rw [Equiv.swap_apply_left] at hp
  exact hs.symm.trans hp

/-- A zero raw output has zero probability by comparison with a fresh zero port. -/
theorem raw_zero_probability_zero (L : RawLaw d v)
    (s : ι) (c : Native ι) (i : ι) (hz : rawPrepared d v s c i = 0) :
    L.prob s c i = 0 := by
  have he : rawPrepared d v (Sum.inl s) (padCircuit PUnit c) (Sum.inl i) =
      rawPrepared d v (Sum.inl s) (padCircuit PUnit c) (Sum.inr PUnit.unit) := by
    rw [rawPrepared_pad_inl, rawPrepared_pad_inr, hz]
  have hp := raw_equal_coordinate_probabilities d v L (Sum.inl s) (padCircuit PUnit c)
    (Sum.inl i) (Sum.inr PUnit.unit) he
  rw [L.vacuum] at hp
  exact hp.trans (vacuum_probability_zero L.toScalarLaw s c PUnit.unit)

end NativeEvents

/-- Every Gaussian numerator is represented by an actual native event. If its
raw action vanished, raw zero-port consistency and selection force it to be zero. -/
theorem gaussianAction_kernel_trivial_of_rawLaw (L : RawLaw d v) (g : GaussianInt)
    (hg : gaussianAction d v g = 0) : g = 0 := by
  obtain ⟨w⟩ := all_numerators_realizable (PUnit.unit : PUnit) g
  let s := sourceAt PUnit.unit w.event.level
  let c := w.event.circuit
  let i := w.event.port
  have h := native_output_related d v s c i
  change Related d v (amplitude PUnit.unit w.event) (rawPrepared d v s c i) at h
  rw [w.representation] at h
  have hz : Related d v ((g : ℂ) / (2 : ℂ)^w.exponent) 0 := by
    refine ⟨w.exponent, g, rfl, ?_⟩
    rw [smul_zero, hg]
  have hraw := related_raw_unique d v h hz
  have hp := raw_zero_probability_zero d v L s c i hraw
  rw [raw_probability_eq_normSq L s c i] at hp
  change Complex.normSq (amplitude PUnit.unit w.event) = 0 at hp
  rw [w.representation] at hp
  have hc := Complex.normSq_eq_zero.mp hp
  have hn := (eq_div_iff
    (pow_ne_zero w.exponent (by norm_num : (2 : ℂ) ≠ 0))).mp hc.symm
  apply GaussianInt.toComplex_injective
  simpa only [map_zero, zero_mul] using hn.symm

/-- Existence forces faithfulness only on the Gaussian orbit of this reference. -/
theorem gaussianAction_injective_of_rawLaw (L : RawLaw d v) :
    Function.Injective (gaussianAction d v) := by
  intro g h hgh
  apply sub_eq_zero.mp
  apply gaussianAction_kernel_trivial_of_rawLaw d v L (g-h)
  rw [map_sub, hgh, sub_self]

/-- Under faithful reference action, one raw value has at most one correlated
scalar amplitude. No feature injectivity is used. -/
theorem related_scalar_unique (injective : Function.Injective (gaussianAction d v))
    {z w : ℂ} {x : Data.Carrier d} (hz : Related d v z x) (hw : Related d v w x) :
    z = w := by
  obtain ⟨k, g, hz, hx⟩ := hz
  obtain ⟨l, h, hw, hy⟩ := hw
  have hg : (2 : ℕ)^l • g = (2 : ℕ)^k • h := by
    apply injective
    calc
      gaussianAction d v ((2 : ℕ)^l • g) =
          (2 : ℕ)^l • gaussianAction d v g := map_nsmul _ _ _
      _ = (2 : ℕ)^l • ((2 : ℕ)^k • x) := by rw [hx]
      _ = (2 : ℕ)^k • ((2 : ℕ)^l • x) := by
        rw [← mul_nsmul, ← mul_nsmul, Nat.mul_comm ((2 : ℕ)^k) ((2 : ℕ)^l)]
      _ = (2 : ℕ)^k • gaussianAction d v h := by rw [hy]
      _ = gaussianAction d v ((2 : ℕ)^k • h) := (map_nsmul _ _ _).symm
  rw [hz, hw]
  apply (div_eq_div_iff
    (pow_ne_zero k (by norm_num : (2 : ℂ) ≠ 0))
    (pow_ne_zero l (by norm_num : (2 : ℂ) ≠ 0))).2
  have hc := congrArg GaussianInt.toComplex hg
  simpa only [nsmul_eq_mul, map_mul, map_pow, map_ofNat, Nat.cast_pow,
    Nat.cast_ofNat, mul_comm] using hc

section Sufficient

variable {ι : Type} [DecidableEq ι]

/-- Faithful reference action reflects prepared-array equality into coordinates. -/
theorem raw_prepared_eq_scalar (injective : Function.Injective (gaussianAction d v))
    (s : ι) (c e : Native ι) (h : rawPrepared d v s c = rawPrepared d v s e) :
    c.eval (source s) = e.eval (source s) := by
  funext i
  have hc := native_output_related d v s c i
  have he := native_output_related d v s e i
  change Related d v (c.eval (source s) i) (rawPrepared d v s c i) at hc
  rw [h] at hc
  exact related_scalar_unique d v injective hc he

end Sufficient

/-- A separate consistency witness. The probability-selection theorem does not
depend on this construction or on its injectivity premise. -/
def canonicalRawLaw (injective : Function.Injective (gaussianAction d v)) : RawLaw d v where
  prob := canonicalLaw.prob
  nonnegative := canonicalLaw.nonnegative
  normalized := canonicalLaw.normalized
  prepared_eq s c e h :=
    canonicalLaw.prepared_eq s c e (raw_prepared_eq_scalar d v injective s c e h)
  output_perm := canonicalLaw.output_perm
  spectator_pair := canonicalLaw.spectator_pair
  vacuum := canonicalLaw.vacuum

/-- Exact existence criterion for the unchanged six-field raw contract. -/
theorem rawLaw_nonempty_iff_gaussianAction_injective :
    Nonempty (RawLaw d v) ↔ Function.Injective (gaussianAction d v) := by
  constructor
  · rintro ⟨L⟩
    exact gaussianAction_injective_of_rawLaw d v L
  · intro h
    exact ⟨canonicalRawLaw d v h⟩

/-- Integer faithfulness of this one reference, not torsion-freeness of the carrier. -/
def ReferenceInfiniteOrder : Prop := ∀ n : ℤ, n • v = 0 → n = 0

private theorem gaussianAction_norm_annihilates (g : GaussianInt)
    (hg : gaussianAction d v g = 0) : (g.re^2 + g.im^2) • v = 0 := by
  have hj : d.phase.J (gaussianAction d v g) =
      g.re • d.phase.J v - g.im • v := by
    change d.phase.J (g.re • v + g.im • d.phase.J v) = _
    rw [map_add, map_zsmul, map_zsmul, d.phase.square, smul_neg]
    rfl
  calc
    (g.re^2 + g.im^2) • v =
        g.re • gaussianAction d v g - g.im • d.phase.J (gaussianAction d v g) := by
      rw [hj]
      change (g.re^2 + g.im^2) • v =
        g.re • (g.re • v + g.im • d.phase.J v) -
          g.im • (g.re • d.phase.J v - g.im • v)
      simp only [add_smul, smul_add, smul_sub, smul_smul, pow_two]
      rw [Int.mul_comm g.im g.re]
      abel
    _ = 0 := by rw [hg, map_zero, smul_zero, smul_zero, sub_zero]

theorem gaussianAction_injective_iff_referenceInfiniteOrder :
    Function.Injective (gaussianAction d v) ↔ ReferenceInfiniteOrder d v := by
  constructor
  · intro injective n hn
    have h : gaussianAction d v (⟨n, 0⟩ : GaussianInt) = gaussianAction d v 0 := by
      simpa [gaussianAction] using hn
    have he := congrArg (fun g : GaussianInt => g.re) (injective h)
    simpa using he
  · intro infiniteOrder
    have kernel (g : GaussianInt) (hg : gaussianAction d v g = 0) : g = 0 := by
      have hn := infiniteOrder (g.re^2 + g.im^2)
        (gaussianAction_norm_annihilates d v g hg)
      have hr : g.re = 0 := by nlinarith [sq_nonneg g.im]
      have hi : g.im = 0 := by nlinarith [sq_nonneg g.re]
      ext <;> assumption
    intro g h hgh
    apply sub_eq_zero.mp
    apply kernel (g-h)
    rw [map_sub, hgh, sub_self]

theorem rawLaw_nonempty_iff_referenceInfiniteOrder :
    Nonempty (RawLaw d v) ↔ ReferenceInfiniteOrder d v :=
  (rawLaw_nonempty_iff_gaussianAction_injective d v).trans
    (gaussianAction_injective_iff_referenceInfiniteOrder d v)

/-- Positive reference weight is sufficient by the already proved absolute
weight identity. This theorem does not assert that positivity is necessary. -/
def positiveWeightRawLaw (positive : 0 < d.weight v) : RawLaw d v where
  prob := canonicalLaw.prob
  nonnegative := canonicalLaw.nonnegative
  normalized := canonicalLaw.normalized
  prepared_eq s c e h := by
    funext i
    change Complex.normSq (c.eval (source s) i) = Complex.normSq (e.eval (source s) i)
    apply mul_right_cancel₀ (ne_of_gt positive)
    calc
      Complex.normSq (c.eval (source s) i) * d.weight v =
          d.weight (rawPrepared d v s c i) := (single_circuit_weight d c s v i).symm
      _ = d.weight (rawPrepared d v s e i) := congrArg d.weight (congrFun h i)
      _ = Complex.normSq (e.eval (source s) i) * d.weight v :=
        single_circuit_weight d e s v i
  output_perm := canonicalLaw.output_perm
  spectator_pair := canonicalLaw.spectator_pair
  vacuum := canonicalLaw.vacuum

theorem rawLaw_nonempty_of_positive_weight (positive : 0 < d.weight v) :
    Nonempty (RawLaw d v) := ⟨positiveWeightRawLaw d v positive⟩

theorem gaussianAction_injective_of_positive_weight (positive : 0 < d.weight v) :
    Function.Injective (gaussianAction d v) :=
  gaussianAction_injective_of_rawLaw d v (positiveWeightRawLaw d v positive)

/-- Literal zero references cannot support the all-width raw probability contract. -/
theorem no_rawLaw_zero : ¬ Nonempty (RawLaw d (0 : Data.Carrier d)) := by
  rintro ⟨L⟩
  have h := gaussianAction_kernel_trivial_of_rawLaw d (0 : Data.Carrier d) L 1
    (by simp [gaussianAction])
  exact one_ne_zero h

end

end IDT.QMClosure.RawNativeProbabilityExistence
