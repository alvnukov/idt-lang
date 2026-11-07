import Proofs.QMClosure.RawNativeScalarCircuitBridge
import Proofs.QMClosure.NativeVacuumProbabilityFamily
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# Exact Gaussian-dyadic semantics on the reconstructed raw carrier

Every actual normalized native circuit has correlated scalar and raw semantics:
a coordinate with scalar numerator `m + i*n` and denominator `2^k` is the
`k`-fold reconstructed half of `m` copies of the reference plus `n` copies of
its reconstructed phase. Equal scalar coordinates therefore give equal raw
coordinates. This implication does not require feature injectivity, feature
quotient probability descent, or a positive reference weight.

All additive operations, phase, and half belong to `Data.Carrier d` and are
reconstructed from the supplied raw operational contract. No algebraic
structure is added as a premise on the original raw type. The syntax is lifted
to the reconstructed normalized operation, which may differ from the original
raw operation. No physical normalization control, gate availability, outcome
probability, arbitrary complex preparation, or full QM closure is established.
-/

namespace IDT.QMClosure.RawNativeDyadicSemantics

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open RawOperationalHilbert RawNativeScalarCircuitBridge
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily

variable {V : Type*} (d : Data V)

/-- Integer Gaussian coefficients act only through reconstructed addition and phase. -/
def gaussianAction (v : Data.Carrier d) : GaussianInt →+ Data.Carrier d where
  toFun g := g.re • (v : Data.Carrier d) + g.im • d.phase.J v
  map_zero' := by simp
  map_add' g h := by
    simp only [Zsqrtd.re_add, Zsqrtd.im_add, add_zsmul]
    abel

/-- The actual repeated half, not an assumed scalar action on the raw type. -/
def halfPower : ℕ → (Data.Carrier d →+ Data.Carrier d)
  | 0 => AddMonoidHom.id _
  | k + 1 => (RawOperationalSeparation.half d).comp (halfPower k)

theorem halfPower_two_pow (k : ℕ) (x : Data.Carrier d) :
    halfPower d k ((2 : ℕ)^k • x) = x := by
  induction k generalizing x with
  | zero => simp [halfPower]
  | succ k ih =>
    change RawOperationalSeparation.half d
      (halfPower d k ((2 : ℕ)^(k+1) • x)) = x
    rw [pow_succ, Nat.mul_comm ((2 : ℕ)^k) 2, mul_nsmul, ih, two_nsmul, map_add]
    exact d.reconstruction.halves x

theorem two_pow_nsmul_injective (k : ℕ) :
    Function.Injective (fun x : Data.Carrier d => (2 : ℕ)^k • x) := by
  intro x y h
  simpa only [halfPower_two_pow] using congrArg (halfPower d k) h

private def rotate (g : GaussianInt) : GaussianInt := ⟨-g.im, g.re⟩

private theorem rotate_complex (g : GaussianInt) :
    (rotate g : ℂ) = Complex.I * (g : ℂ) := by
  rw [GaussianInt.toComplex_def, GaussianInt.toComplex_def]
  change ((-g.im : ℤ) : ℂ) + (g.re : ℂ) * Complex.I =
    Complex.I * ((g.re : ℂ) + (g.im : ℂ) * Complex.I)
  rw [Int.cast_neg]
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem gaussianAction_rotate (v : Data.Carrier d) (g : GaussianInt) :
    gaussianAction d v (rotate g) = d.phase.J (gaussianAction d v g) := by
  change (-g.im) • (v : Data.Carrier d) + g.re • d.phase.J v =
    d.phase.J (g.re • (v : Data.Carrier d) + g.im • d.phase.J v)
  rw [map_add, map_zsmul, map_zsmul, d.phase.square]
  simp only [neg_zsmul, smul_neg]
  abel

/-- One shared numerator certifies scalar semantics and exact raw semantics
after clearing a power-of-two denominator. -/
def Related (v : Data.Carrier d) (z : ℂ) (x : Data.Carrier d) : Prop :=
  ∃ k : ℕ, ∃ g : GaussianInt,
    z = (g : ℂ) / (2 : ℂ)^k ∧ (2 : ℕ)^k • x = gaussianAction d v g

theorem related_zero (v : Data.Carrier d) : Related d v 0 0 := by
  refine ⟨0, 0, ?_, ?_⟩
  · simp only [GaussianInt.toComplex_zero, pow_zero, zero_div]
  · simp [gaussianAction]

theorem related_one (v : Data.Carrier d) : Related d v 1 v := by
  refine ⟨0, 1, ?_, ?_⟩
  · simp only [GaussianInt.toComplex_one, pow_zero, div_one]
  · simp [gaussianAction]

theorem related_neg (v : Data.Carrier d) {z : ℂ} {x : Data.Carrier d}
    (h : Related d v z x) : Related d v (-z) (-x) := by
  obtain ⟨k, g, hz, hx⟩ := h
  refine ⟨k, -g, ?_, ?_⟩
  · rw [GaussianInt.toComplex_neg, hz, neg_div]
  · rw [smul_neg, hx, map_neg]

theorem related_add (v : Data.Carrier d) {z w : ℂ} {x y : Data.Carrier d}
    (hx : Related d v z x) (hy : Related d v w y) :
    Related d v (z + w) (x + y) := by
  obtain ⟨k, g, hz, hx⟩ := hx
  obtain ⟨l, h, hw, hy⟩ := hy
  refine ⟨k+l, (2 : ℕ)^l • g + (2 : ℕ)^k • h, ?_, ?_⟩
  · change z+w = GaussianInt.toComplex (_ + _) / (2 : ℂ)^(k+l)
    rw [map_add, map_nsmul, map_nsmul, hz, hw, pow_add]
    simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  · calc
      (2 : ℕ)^(k+l) • (x+y) =
          (2 : ℕ)^l • ((2 : ℕ)^k • x) +
          (2 : ℕ)^k • ((2 : ℕ)^l • y) := by
        rw [pow_add, nsmul_add]
        congr 1
        · rw [mul_nsmul]
        · rw [Nat.mul_comm ((2 : ℕ)^k) ((2 : ℕ)^l), mul_nsmul]
      _ = (2 : ℕ)^l • gaussianAction d v g +
          (2 : ℕ)^k • gaussianAction d v h := by rw [hx, hy]
      _ = gaussianAction d v ((2 : ℕ)^l • g + (2 : ℕ)^k • h) := by
        rw [map_add, map_nsmul, map_nsmul]

theorem related_sub (v : Data.Carrier d) {z w : ℂ} {x y : Data.Carrier d}
    (hx : Related d v z x) (hy : Related d v w y) :
    Related d v (z-w) (x-y) := by
  simpa only [sub_eq_add_neg] using related_add d v hx (related_neg d v hy)

theorem related_phase (v : Data.Carrier d) {z : ℂ} {x : Data.Carrier d}
    (h : Related d v z x) : Related d v (Complex.I*z) (d.phase.J x) := by
  obtain ⟨k, g, hz, hx⟩ := h
  refine ⟨k, rotate g, ?_, ?_⟩
  · rw [rotate_complex, hz, mul_div_assoc]
  · rw [← map_nsmul, hx, ← gaussianAction_rotate]

theorem related_half (v : Data.Carrier d) {z : ℂ} {x : Data.Carrier d}
    (h : Related d v z x) :
    Related d v (z/2) (RawOperationalSeparation.half d x) := by
  obtain ⟨k, g, hz, hx⟩ := h
  refine ⟨k+1, g, ?_, ?_⟩
  · rw [hz, pow_succ]
    field_simp
  · rw [pow_succ, Nat.mul_comm ((2 : ℕ)^k) 2, mul_nsmul, two_nsmul,
      d.reconstruction.halves, hx]

/-- Exact raw and scalar mixer operations preserve the same coefficient certificate. -/
theorem related_mixer (v : Data.Carrier d) {z w : ℂ} {x y : Data.Carrier d}
    (hx : Related d v z x) (hy : Related d v w y) :
    Related d v (NativeMixerEventConeExclusion.mixer (z,w)).1
        (d.normalizedOperation (x,y)).1 ∧
    Related d v (NativeMixerEventConeExclusion.mixer (z,w)).2
        (d.normalizedOperation (x,y)).2 := by
  have hxA := related_half d v (related_add d v hx (related_phase d v hx))
  have hxB := related_half d v (related_sub d v hx (related_phase d v hx))
  have hyA := related_half d v (related_add d v hy (related_phase d v hy))
  have hyB := related_half d v (related_sub d v hy (related_phase d v hy))
  constructor
  · convert related_add d v hxA hyB using 1
    · rw [NativeAttenuationCircuit.mixer_fst]
      dsimp [NativeAttenuationCircuit.a, NativeAttenuationCircuit.b]
      ring
    · rw [RawOperationalSeparation.normalized_route]
      rfl
  · convert related_add d v hxB hyA using 1
    · rw [NativeAttenuationCircuit.mixer_snd]
      dsimp [NativeAttenuationCircuit.a, NativeAttenuationCircuit.b]
      ring
    · rw [RawOperationalSeparation.normalized_route]
      rfl

variable {ι : Type} [DecidableEq ι]

/-- Constructorwise correlation; no enlarged preparation availability is supplied. -/
theorem circuit_related (v : Data.Carrier d) (c : Native ι)
    (z : ι → ℂ) (x : ι → Data.Carrier d)
    (h : ∀ i, Related d v (z i) (x i)) :
    ∀ i, Related d v (c.eval z i) ((liftCircuit d c).eval x i) := by
  induction c generalizing z x with
  | identity => exact h
  | pair i j hij =>
    have hm := related_mixer d v (h i) (h j)
    intro k
    by_cases hki : k = i
    · subst k
      simpa [liftCircuit, Circuit.eval, pairGate, pairReplace] using hm.1
    · by_cases hkj : k = j
      · subst k
        simpa [liftCircuit, Circuit.eval, pairGate, pairReplace, Ne.symm hij] using hm.2
      · simpa [liftCircuit, Circuit.eval, pairGate, pairReplace, hki, hkj] using h k
  | permute e => exact fun k => h (e k)
  | seq c e hc he => exact he (c.eval z) ((liftCircuit d c).eval x) (hc z x h)

theorem source_related (v : Data.Carrier d) (s : ι) :
    ∀ i, Related d v (source s i) (single (V := Data.Carrier d) s v i) := by
  intro i
  by_cases hi : i = s
  · simpa [source, single, hi] using related_one d v
  · simpa [source, single, hi] using related_zero d v

theorem native_output_related (v : Data.Carrier d) (s : ι) (c : Native ι) (i : ι) :
    Related d v (c.eval (source s) i)
      ((liftCircuit d c).eval (single (V := Data.Carrier d) s v) i) :=
  circuit_related d v c _ _ (source_related d v s) i

/-- The same Gaussian numerator describes the actual scalar and raw output. -/
theorem native_output_gaussian_correlated (v : Data.Carrier d) (s : ι) (c : Native ι) (i : ι) :
    ∃ k : ℕ, ∃ g : GaussianInt,
      c.eval (source s) i = (g : ℂ)/(2 : ℂ)^k ∧
      (liftCircuit d c).eval (single (V := Data.Carrier d) s v) i =
        halfPower d k (gaussianAction d v g) := by
  obtain ⟨k, g, hz, hx⟩ := native_output_related d v s c i
  refine ⟨k, g, hz, ?_⟩
  rw [← hx, halfPower_two_pow]

/-- Explicit integer coordinates, with all raw operations reconstructed from `d`. -/
theorem native_output_correlated (v : Data.Carrier d) (s : ι) (c : Native ι) (i : ι) :
    ∃ k : ℕ, ∃ m n : ℤ,
      c.eval (source s) i = ((m : ℂ)+(n : ℂ)*Complex.I)/(2 : ℂ)^k ∧
      (liftCircuit d c).eval (single (V := Data.Carrier d) s v) i =
        halfPower d k (m • (v : Data.Carrier d) + n • d.phase.J v) := by
  obtain ⟨k, g, hz, hx⟩ := native_output_gaussian_correlated d v s c i
  exact ⟨k, g.re, g.im, (by simpa only [GaussianInt.toComplex_def] using hz), hx⟩

/-- Scalar equality determines the raw value on this correlated generated domain.
The raw feature map may still be noninjective on the complete carrier. -/
theorem related_raw_unique (v : Data.Carrier d) {z : ℂ} {x y : Data.Carrier d}
    (hx : Related d v z x) (hy : Related d v z y) : x = y := by
  obtain ⟨k, g, hz, hx⟩ := hx
  obtain ⟨l, h, hw, hy⟩ := hy
  have hc : (g : ℂ)/(2 : ℂ)^k = (h : ℂ)/(2 : ℂ)^l := hz.symm.trans hw
  have he := (div_eq_div_iff
    (pow_ne_zero k (by norm_num : (2 : ℂ) ≠ 0))
    (pow_ne_zero l (by norm_num : (2 : ℂ) ≠ 0))).mp hc
  have hg : (2 : ℕ)^l • g = (2 : ℕ)^k • h := by
    apply GaussianInt.toComplex_injective
    rw [map_nsmul, map_nsmul]
    simpa only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm] using he
  apply two_pow_nsmul_injective d (k+l)
  calc
    (2 : ℕ)^(k+l) • x = (2 : ℕ)^l • gaussianAction d v g := by
      rw [pow_add, mul_nsmul, hx]
    _ = gaussianAction d v ((2 : ℕ)^l • g) := (map_nsmul _ _ _).symm
    _ = gaussianAction d v ((2 : ℕ)^k • h) := congrArg (gaussianAction d v) hg
    _ = (2 : ℕ)^k • gaussianAction d v h := map_nsmul _ _ _
    _ = (2 : ℕ)^(k+l) • y := by
      rw [pow_add, Nat.mul_comm ((2 : ℕ)^k) ((2 : ℕ)^l), mul_nsmul, hy]

/-- Equal selected amplitudes imply exact equal raw values, including null references. -/
theorem same_amplitude_same_raw_output (v : Data.Carrier d) (s : ι) (c e : Native ι) (i j : ι)
    (h : c.eval (source s) i = e.eval (source s) j) :
    (liftCircuit d c).eval (single (V := Data.Carrier d) s v) i =
      (liftCircuit d e).eval (single (V := Data.Carrier d) s v) j := by
  have hc := native_output_related d v s c i
  rw [h] at hc
  exact related_raw_unique d v hc (native_output_related d v s e j)

/-- The exact bridge needed to pull raw prepared-state equivalence into the scalar law. -/
theorem scalar_prepared_eq_raw (v : Data.Carrier d) (s : ι) (c e : Native ι)
    (h : c.eval (source s) = e.eval (source s)) :
    (liftCircuit d c).eval (single (V := Data.Carrier d) s v) =
      (liftCircuit d e).eval (single (V := Data.Carrier d) s v) := by
  funext i
  exact same_amplitude_same_raw_output d v s c e i i (congrFun h i)

inductive BoundaryRole where
  | algebraOnCarrierIsReconstructedNotSuppliedOnRawType
  | correlatedExactGaussianDyadicSemanticsForActualNativeWords
  | scalarEqualityImpliesExactRawEqualityOnGeneratedDomain
  | noFeatureInjectivityOrProbabilityDescentPremise
  | nullReferenceAndAllNullModelsRemainAllowed
  | normalizedOperationMayDifferFromOriginalRawOperation
  | noPhysicalNormalizationControlOrGateAvailability
  | noOutcomeProbabilityOrArbitraryComplexPreparation
  | doesNotProveFullQMOrUpgradeManifestStatus
  deriving DecidableEq, Repr

def boundaryRoles : List BoundaryRole := [
  .algebraOnCarrierIsReconstructedNotSuppliedOnRawType,
  .correlatedExactGaussianDyadicSemanticsForActualNativeWords,
  .scalarEqualityImpliesExactRawEqualityOnGeneratedDomain,
  .noFeatureInjectivityOrProbabilityDescentPremise,
  .nullReferenceAndAllNullModelsRemainAllowed,
  .normalizedOperationMayDifferFromOriginalRawOperation,
  .noPhysicalNormalizationControlOrGateAvailability,
  .noOutcomeProbabilityOrArbitraryComplexPreparation,
  .doesNotProveFullQMOrUpgradeManifestStatus]

end

end IDT.QMClosure.RawNativeDyadicSemantics
