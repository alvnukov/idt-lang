import Proofs.QMClosure.WeightFreeRawProbability

/-!
# Naturality of literal native preparations

Both-output covariance transports raw finite circuit words without any supplied
algebra on their carriers. Diagonal normalization is term-defined and preserves
that covariance. Prepared-state transport additionally preserves the chosen zero.

The law adapters concern literal arrays. Pullback needs equality preservation;
the forward adapter needs only reflection of equal prepared arrays for the same
reference, source and width. Injectivity is a sufficient reflection condition,
not an asserted necessary criterion for law existence. Both adapters retain the
entire supplied probability field and all six law conditions. Their construction
uses neither probability selection nor a canonical probability witness.

Common negation uses the reconstructed group and normalized operation. It acts
on every coordinate and the reference together. The original operation requires
its own covariance proof or a transparency bridge. Quarter-turn transport is
outside this artifact.

A covariance map need not be executable, native, physically available, unitary,
or a gauge transformation. Literal-array injectivity does not establish response-
context preservation or reflection. No response-Law transport, independent wire
quotient, U(1) symmetry, physical preparation availability, actualization or full
QM is asserted. The raw operational data retain their own structural fields.
-/

namespace IDT.QMClosure.NativePreparationNaturality

noncomputable section

open WeightFreeRawProbability
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily

variable {V W : Type*}

/-- Covariance of both outputs under one common map. -/
def MapsOperation (T : V × V → V × V) (S : W × W → W × W) (f : V → W) : Prop :=
  ∀ x y, (f (T (x, y)).1, f (T (x, y)).2) = S (f x, f y)

/-- Function-only circuit covariance, including arbitrary input arrays. -/
theorem evalRaw_covariance (T : V × V → V × V) (S : W × W → W × W) (f : V → W)
    (h : MapsOperation T S f) {ι : Type} [DecidableEq ι]
    (c : Native ι) (x : ι → V) :
    evalRaw S c (f ∘ x) = f ∘ evalRaw T c x := by
  induction c generalizing x with
  | identity => rfl
  | pair i j hij =>
    have hpair : S (f (x i), f (x j)) = (f (T (x i, x j)).1, f (T (x i, x j)).2) :=
      (h (x i) (x j)).symm
    funext k
    by_cases hki : k = i
    · simp [evalRaw, Function.comp_apply, hki, hpair]
    · by_cases hkj : k = j
      · simp [evalRaw, Function.comp_apply, hkj, hpair, hij.symm]
      · simp [evalRaw, Function.comp_apply, hki, hkj]
  | permute e => rfl
  | seq c e hc he =>
    change evalRaw S e (evalRaw S c (f ∘ x)) = f ∘ evalRaw T e (evalRaw T c x)
    rw [hc, he]

/-- Original-operation covariance survives term-defined diagonal normalization. -/
theorem normalizedOperation_covariance (r : RawOperationalData V) (s : RawOperationalData W)
    (f : V → W) (h : MapsOperation r.operation s.operation f) :
    MapsOperation r.normalizedOperation s.normalizedOperation f := by
  have hfirst (x y : V) :
      f (MedialSwapRoot.firstChannel r.operation x y) =
        MedialSwapRoot.firstChannel s.operation (f x) (f y) :=
    congrArg Prod.fst (h x y)
  intro x y
  apply Prod.ext <;>
    simp only [RawOperationalData.normalizedOperation, MedialSwapRoot.DiagonalNormalization.normalized,
      MedialSwapRoot.DiagonalNormalization.diagonal, hfirst]

/-- A zero-preserving map transports the complete basis input literally. -/
theorem basisInput_covariance (r : RawOperationalData V) (s : RawOperationalData W)
    (f : V → W) (h0 : f r.chosenZero = s.chosenZero) (v : V)
    {ι : Type} [DecidableEq ι] (source : ι) :
    basisInput s (f v) source = f ∘ basisInput r v source := by
  funext i
  by_cases hi : i = source <;>
    simp [basisInput, Function.comp_apply, hi, h0]

/-- Normalized preparation covariance requires no original-gate transparency. -/
theorem prepared_covariance (r : RawOperationalData V) (s : RawOperationalData W)
    (f : V → W) (h0 : f r.chosenZero = s.chosenZero)
    (hnorm : MapsOperation r.normalizedOperation s.normalizedOperation f) (v : V)
    {ι : Type} [DecidableEq ι] (source : ι) (c : Native ι) :
    prepared s (f v) source c = f ∘ prepared r v source c := by
  unfold prepared
  rw [basisInput_covariance r s f h0 v source]
  exact evalRaw_covariance r.normalizedOperation s.normalizedOperation f hnorm c _

/-- Equality preservation is sufficient for pulling a target law back. -/
theorem prepared_equality_preserved (r : RawOperationalData V) (s : RawOperationalData W)
    (f : V → W) (h0 : f r.chosenZero = s.chosenZero)
    (hnorm : MapsOperation r.normalizedOperation s.normalizedOperation f) (v : V)
    {ι : Type} [DecidableEq ι] (source : ι) (c e : Native ι)
    (h : prepared r v source c = prepared r v source e) :
    prepared s (f v) source c = prepared s (f v) source e := by
  rw [prepared_covariance r s f h0 hnorm v source c,
    prepared_covariance r s f h0 hnorm v source e, h]

/-- Reflection is limited to equal preparations at the same source/reference/width. -/
def PreparedEqualityReflecting (r : RawOperationalData V) (s : RawOperationalData W)
    (f : V → W) (v : V) : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (source : ι) (c e : Native ι),
    prepared s (f v) source c = prepared s (f v) source e →
      prepared r v source c = prepared r v source e

theorem preparedEqualityReflecting_of_injective
    (r : RawOperationalData V) (s : RawOperationalData W) (f : V → W)
    (h0 : f r.chosenZero = s.chosenZero)
    (hnorm : MapsOperation r.normalizedOperation s.normalizedOperation f)
    (hf : Function.Injective f) (v : V) : PreparedEqualityReflecting r s f v := by
  intro ι instF instD source c e h
  rw [prepared_covariance r s f h0 hnorm v source c,
    prepared_covariance r s f h0 hnorm v source e] at h
  funext i
  apply hf
  exact congrFun h i

/-- Pullback changes only the literal-array equality proof. -/
def pullLaw (r : RawOperationalData V) (s : RawOperationalData W) (f : V → W) (v : V)
    (h0 : f r.chosenZero = s.chosenZero)
    (hnorm : MapsOperation r.normalizedOperation s.normalizedOperation f)
    (L : Law s (f v)) : Law r v where
  prob := L.prob
  nonnegative := L.nonnegative
  normalized := L.normalized
  prepared_eq source c e h := by
    apply L.prepared_eq source c e
    have hsource : prepared r v source c = prepared r v source e := by
      simpa only [rawPrepared_eq_prepared] using h
    simpa only [rawPrepared_eq_prepared] using
      prepared_equality_preserved r s f h0 hnorm v source c e hsource
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

/-- Forward transport adds only the stated prepared-equality reflection condition. -/
def mapLaw (r : RawOperationalData V) (s : RawOperationalData W) (f : V → W) (v : V)
    (hreflect : PreparedEqualityReflecting r s f v) (L : Law r v) : Law s (f v) where
  prob := L.prob
  nonnegative := L.nonnegative
  normalized := L.normalized
  prepared_eq source c e h := by
    apply L.prepared_eq source c e
    have htarget : prepared s (f v) source c = prepared s (f v) source e := by
      simpa only [rawPrepared_eq_prepared] using h
    simpa only [rawPrepared_eq_prepared] using hreflect source c e htarget
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

/-- The adapters are inverse contracts with the complete same supplied probability field. -/
def lawEquiv (r : RawOperationalData V) (s : RawOperationalData W) (f : V → W) (v : V)
    (h0 : f r.chosenZero = s.chosenZero)
    (hnorm : MapsOperation r.normalizedOperation s.normalizedOperation f)
    (hreflect : PreparedEqualityReflecting r s f v) : Law r v ≃ Law s (f v) where
  toFun := mapLaw r s f v hreflect
  invFun := pullLaw r s f v h0 hnorm
  left_inv L := by cases L; rfl
  right_inv L := by cases L; rfl

theorem pullLaw_probability (r : RawOperationalData V) (s : RawOperationalData W)
    (f : V → W) (v : V) (h0 : f r.chosenZero = s.chosenZero)
    (hnorm : MapsOperation r.normalizedOperation s.normalizedOperation f)
    (L : Law s (f v)) :
    @RawNativeProbabilitySelection.RawLaw.prob V r.zeroWeightData v
        (pullLaw r s f v h0 hnorm L) =
      @RawNativeProbabilitySelection.RawLaw.prob W s.zeroWeightData (f v) L := rfl

theorem mapLaw_probability (r : RawOperationalData V) (s : RawOperationalData W)
    (f : V → W) (v : V)
    (hreflect : PreparedEqualityReflecting r s f v) (L : Law r v) :
    @RawNativeProbabilitySelection.RawLaw.prob W s.zeroWeightData (f v)
        (mapLaw r s f v hreflect L) =
      @RawNativeProbabilitySelection.RawLaw.prob V r.zeroWeightData v L := rfl

/-- Negation is computed in the reconstructed group, with no raw algebra supplied. -/
def negMap (r : RawOperationalData V) (x : V) : V :=
  @Neg.neg r.Carrier inferInstance x

theorem negMap_zero (r : RawOperationalData V) : negMap r r.chosenZero = r.chosenZero := by
  simpa only [negMap, RawOperationalHilbert.Data.carrier_zero] using
    (neg_zero : -(0 : r.Carrier) = (0 : r.Carrier))

theorem negMap_injective (r : RawOperationalData V) : Function.Injective (negMap r) :=
  (neg_injective : Function.Injective (Neg.neg : r.Carrier → r.Carrier))

/-- The normalized gate is an additive homomorphism on the reconstructed carrier. -/
theorem negMap_normalized_covariance (r : RawOperationalData V) :
    MapsOperation r.normalizedOperation r.normalizedOperation (negMap r) := by
  intro x y
  let p : r.Carrier × r.Carrier := (x, y)
  change -(r.zeroWeightData.normalizedOperation p) =
    r.zeroWeightData.normalizedOperation (-p)
  exact (r.zeroWeightData.normalizedOperation.map_neg p).symm

theorem prepared_neg (r : RawOperationalData V) (v : r.Carrier)
    {ι : Type} [DecidableEq ι] (source : ι) (c : Native ι) :
    prepared r (-v) source c = negMap r ∘ prepared r v source c :=
  prepared_covariance r r (negMap r) (negMap_zero r) (negMap_normalized_covariance r)
    v source c

/-- Common sign transport negates every coordinate and the same reference together. -/
def negLawEquiv (r : RawOperationalData V) (v : r.Carrier) : Law r v ≃ Law r (-v) :=
  lawEquiv r r (negMap r) v (negMap_zero r) (negMap_normalized_covariance r)
    (preparedEqualityReflecting_of_injective r r (negMap r) (negMap_zero r)
      (negMap_normalized_covariance r) (negMap_injective r) v)

theorem negLawEquiv_probability (r : RawOperationalData V) (v : r.Carrier) (L : Law r v) :
    @RawNativeProbabilitySelection.RawLaw.prob V r.zeroWeightData (-v) (negLawEquiv r v L) =
      @RawNativeProbabilitySelection.RawLaw.prob V r.zeroWeightData v L := rfl

end

end IDT.QMClosure.NativePreparationNaturality
