import Proofs.QMClosure.WeightFreeRawProbability

/-!
# The finite native one-reference reachability wall

Each preparation starts with one basis reference and otherwise zero inputs.
Every finite width is covered. Two separately reachable coefficients need not
be simultaneously available: the unattenuated first mixer output on `1` and
`a = (1+i)/2` has squared norm `5/4`, beyond any one-source output.

The raw theorem needs only square-swap, first-channel mediality, a chosen zero,
and infinite additive order of this reference in the reconstructed group. Its
proof uses exact Gaussian-dyadic correlation, with no probability-law premise,
supplied positive weight, or faithful feature map. The constant-zero weight is
only an adapter to existing algebraic proofs and carries no readout information.

The positive control retains every ancillary output and uses one source split
into two attenuated branches. Its alignment scope is the canonical tower above
one common source/type. No alignment of unrelated existential witnesses is
silently assumed. Normalized semantics need an explicit evaluator bridge to
interpret the original raw gate. This is a reachability statement, not a
physical no-cloning or energy theorem. Additional independent sources change
the accounting; port coordinates are not subsystem particle states. No matter,
probability actualization, Hilbert, or full-QM conclusion follows.
-/

namespace IDT.QMClosure.NativeSingleSourceReferenceWall

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open scoped BigOperators
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open NativeMixerEventConeExclusion NativeAttenuationCircuit
open RawOperationalHilbert RawNativeDyadicSemantics
open WeightFreeRawProbability

/-- Actual selected coefficients, with arbitrary finite wire types. -/
def ScalarReachable (z : ℂ) : Prop :=
  ∃ (ι : Type) (hi : Fintype ι) (hd : DecidableEq ι),
    letI := hi
    letI := hd
    ∃ (s i : ι) (c : Native ι), c.eval (source s) i = z

/-- Conservation of the algebraic squared-norm readout, before selecting any law. -/
theorem source_readout {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) :
    ∑ i, Complex.normSq (c.eval (source s) i) = 1 := by
  have h := c.preserves_readout Complex.normSq mixer_conserves (source s)
  simpa [totalReadout, source, single] using h

/-- The bound holds for every finite width, source, circuit, and output. -/
theorem output_normSq_le_one {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (i : ι) :
    Complex.normSq (c.eval (source s) i) ≤ 1 := by
  have h := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
      Complex.normSq_nonneg (c.eval (source s) j)) (Finset.mem_univ i)
  simpa only [source_readout s c] using h

theorem scalarReachable_normSq_le_one {z : ℂ} (hz : ScalarReachable z) :
    Complex.normSq z ≤ 1 := by
  obtain ⟨ι, hi, hd, s, i, c, hc⟩ := hz
  letI := hi
  letI := hd
  rw [← hc]
  exact output_normSq_le_one s c i

theorem one_reachable : ScalarReachable 1 := by
  refine ⟨Fin 2, inferInstance, inferInstance, 0, 0, .identity, ?_⟩
  simp [Circuit.eval, source, single]

theorem a_reachable : ScalarReachable a := by
  refine ⟨Fin 2, inferInstance, inferInstance, 0, 0,
    .pair 0 1 (by decide), ?_⟩
  simp [Circuit.eval, pairGate, pairReplace, source, single, mixer_fst]

theorem mixer_one_a : (mixer (1, a)).1 = 1 + Complex.I / 2 := by
  rw [mixer_fst]
  apply Complex.ext <;>
    norm_num [a, b, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im]

theorem mixer_one_a_normSq : Complex.normSq (mixer (1, a)).1 = 5 / 4 := by
  rw [mixer_one_a]
  norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im]

theorem mixer_one_a_not_reachable : ¬ ScalarReachable (mixer (1, a)).1 := by
  intro h
  have hb := scalarReachable_normSq_le_one h
  rw [mixer_one_a_normSq] at hb
  norm_num at hb

/-- Separately reachable inputs are not closed under unattenuated mixing. -/
theorem scalar_reachable_not_closed :
    ∃ z w : ℂ, ScalarReachable z ∧ ScalarReachable w ∧
      ¬ ScalarReachable (mixer (z, w)).1 :=
  ⟨1, a, one_reachable, a_reachable, mixer_one_a_not_reachable⟩

/-- The counterexample respects conservation: its joint input already exceeds one. -/
theorem counterexample_accounting :
    Complex.normSq (1 : ℂ) + Complex.normSq a = 3 / 2 ∧
    Complex.normSq (mixer (1, a)).1 = 5 / 4 ∧
    Complex.normSq (mixer (1, a)).2 = 1 / 4 ∧
    Complex.normSq (mixer (1, a)).1 +
      Complex.normSq (mixer (1, a)).2 = 3 / 2 := by
  have ha : Complex.normSq a = 1 / 2 := by
    norm_num [a, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  have hb : Complex.normSq (mixer (1, a)).2 = 1 / 4 := by
    rw [mixer_snd]
    norm_num [a, b, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im]
  rw [ha, mixer_one_a_normSq, hb]
  norm_num

/-- Distinct ports of a single one-source preparation cannot carry both inputs. -/
theorem one_a_not_jointly_prepared {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (i j : ι) (hij : i ≠ j)
    (hi : c.eval (source s) i = 1) (hj : c.eval (source s) j = a) : False := by
  apply mixer_one_a_not_reachable
  refine ⟨ι, inferInstance, inferInstance, s, i, .seq c (.pair i j hij), ?_⟩
  simp [Circuit.eval, pairGate, pairReplace, hi, hj]

section Raw

variable {V : Type*} (r : RawOperationalData V) (v : r.Carrier)

def firstMix : V := (r.normalizedOperation (v, r.chosenZero)).1

def secondMix : V := (r.normalizedOperation (v, firstMix r v)).1

/-- Literal selected raw outputs, over every finite native wire type. -/
def RawReachable (x : V) : Prop :=
  ∃ (ι : Type) (hi : Fintype ι) (hd : DecidableEq ι),
    letI := hi
    letI := hd
    ∃ (s i : ι) (c : Native ι), prepared r v s c i = x

theorem reference_raw_reachable : RawReachable r v v := by
  refine ⟨Fin 2, inferInstance, inferInstance, 0, 0, .identity, ?_⟩
  simp [prepared, evalRaw, basisInput]

theorem firstMix_raw_reachable : RawReachable r v (firstMix r v) := by
  refine ⟨Fin 2, inferInstance, inferInstance, 0, 0,
    .pair 0 1 (by decide), ?_⟩
  simp [prepared, evalRaw, basisInput, firstMix]

/-- Direct transport of the two raw mixer evaluations to their exact coefficient. -/
theorem secondMix_related :
    Related r.zeroWeightData v (1 + Complex.I / 2) (secondMix r v) := by
  have hfirst := (related_mixer r.zeroWeightData v
    (related_one r.zeroWeightData v) (related_zero r.zeroWeightData v)).1
  have hfirst' : Related r.zeroWeightData v a (firstMix r v) := by
    simpa [mixer_fst, firstMix] using hfirst
  have hsecond := (related_mixer r.zeroWeightData v
    (related_one r.zeroWeightData v) hfirst').1
  simpa only [mixer_one_a] using hsecond

/-- No literal finite one-source normalized preparation reaches this raw value.
Only this reference's infinite order is needed; no probability law is used. -/
theorem secondMix_not_prepared
    (infiniteOrder : WeightFreeRawProbability.ReferenceInfiniteOrder r v)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (i : ι) :
    prepared r v s c i ≠ secondMix r v := by
  intro heq
  have houtput := native_output_related r.zeroWeightData v s c i
  change Related r.zeroWeightData v (c.eval (source s) i)
    (RawNativeProbabilitySelection.rawPrepared r.zeroWeightData v s c i) at houtput
  rw [rawPrepared_eq_prepared, heq] at houtput
  have hinjective :=
    (RawNativeProbabilityExistence.gaussianAction_injective_iff_referenceInfiniteOrder
      r.zeroWeightData v).2 infiniteOrder
  have hscalar := RawNativeProbabilityExistence.related_scalar_unique
    r.zeroWeightData v hinjective houtput (secondMix_related r v)
  have hbound := output_normSq_le_one s c i
  rw [hscalar] at hbound
  have hnorm : Complex.normSq (1 + Complex.I / 2) = 5 / 4 := by
    rw [← mixer_one_a]
    exact mixer_one_a_normSq
  rw [hnorm] at hbound
  norm_num at hbound

theorem secondMix_not_raw_reachable
    (infiniteOrder : WeightFreeRawProbability.ReferenceInfiniteOrder r v) :
    ¬ RawReachable r v (secondMix r v) := by
  rintro ⟨ι, hi, hd, s, i, c, hc⟩
  letI := hi
  letI := hd
  exact secondMix_not_prepared r v infiniteOrder s c i hc

/-- Raw nonclosure follows from literal reachable witnesses, without a supplied weight. -/
theorem raw_reachable_not_closed
    (infiniteOrder : WeightFreeRawProbability.ReferenceInfiniteOrder r v) :
    ∃ x y : V, RawReachable r v x ∧ RawReachable r v y ∧
      ¬ RawReachable r v (r.normalizedOperation (x, y)).1 :=
  ⟨v, firstMix r v, reference_raw_reachable r v, firstMix_raw_reachable r v,
    secondMix_not_raw_reachable r v infiniteOrder⟩

end Raw

/-- Positive control at its exact alignment scope: arbitrary event levels above
one fixed source/type. Both selected outputs belong to one retained circuit. -/
theorem aligned_sum_difference {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (e f : NativeGaussianResponse.Event ι) :
    ∃ n : ℕ, ∃ c : Native (NativeGaussianResponse.Tower ι (n + 1)),
      ∃ i j : NativeGaussianResponse.Tower ι (n + 1), i ≠ j ∧
      c.eval (source (NativeGaussianResponse.sourceAt s (n + 1))) i =
        (NativeGaussianResponse.amplitude s e + NativeGaussianResponse.amplitude s f) / 2 ∧
      c.eval (source (NativeGaussianResponse.sourceAt s (n + 1))) j =
        Complex.I *
          (NativeGaussianResponse.amplitude s e - NativeGaussianResponse.amplitude s f) / 2 := by
  obtain ⟨n, c, d, i, j, hc, hd, _, _⟩ :=
    NativeGaussianResponse.exists_common_level s e f
  refine ⟨n, NativeGaussianResponse.sumDifferenceCircuit c d i j,
    .inr j, .inl i, by simp, ?_, ?_⟩
  · simpa only [NativeGaussianResponse.sourceAt, hc, hd] using
      (NativeGaussianResponse.sumDifference_amplitudes
        (NativeGaussianResponse.sourceAt s n) c d i j).2
  · simpa only [NativeGaussianResponse.sourceAt, hc, hd] using
      (NativeGaussianResponse.sumDifference_amplitudes
        (NativeGaussianResponse.sourceAt s n) c d i j).1

end
end IDT.QMClosure.NativeSingleSourceReferenceWall
