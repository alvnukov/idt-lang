import Proofs.QMClosure.RawOperationalSeparation

/-!
# Affine diagonal and orthogonal sign decomposition of the original raw gate

The chosen raw zero need not be fixed by the original diagonal. Its displacement
is retained explicitly as a null vector. The diagonal's additive part is an
involution commuting with the reconstructed phase and half; its two algebraic
sign subgroups give complementary, weight-orthogonal projections.

After translation by a derived fixed null center, the original operation is
the normalized operation on the positive subgroup and its negative on the
negative subgroup. All addition, inverses, phase, half and subgroup structure
belong to the carrier reconstructed from `RawOperationalHilbert.Data`.
No raw algebra, zero-fixing, feature injectivity or torsion-freeness is supplied.

The projections and centering are mathematical terms, not physical controls,
copying procedures or measurements. The null offset is not identified with raw
zero. No circuit synthesis, probability classification, actualization, or full
QM closure is established.
-/

namespace IDT.QMClosure.RawDiagonalDecomposition

noncomputable section

open RawOperationalHilbert
open RawOperationalSeparation (diagonal half normalized_transparent normalized_square)

variable {V : Type*} (d : Data V)

/-- Displacement of the chosen raw zero by the original diagonal. -/
def offset : Data.Carrier d := diagonal d 0

theorem offset_null : d.weight (offset d) = 0 :=
  (RawOperationalSeparation.diagonal_weight d 0).trans d.quadratic.zero

private theorem additive_diagonal_exists :
    ∃ L : Data.Carrier d →+ Data.Carrier d,
      (∀ x, diagonal d x = L x + offset d) ∧
      (∀ x, L (d.phase.J x) = d.phase.J (L x)) := by
  obtain ⟨L, affine, phase⟩ := (MixerRecordNaturality.affine_classification
    d.normalizedOperation d.normalizedOperation (normalized_transparent d)
    (normalized_square d) (normalized_transparent d) (normalized_square d)
    (diagonal d)).mp (RawOperationalSeparation.diagonal_intertwines d)
  exact ⟨L, affine, phase⟩

/-- The additive part of the diagonal. `linearDiagonal_apply` identifies its
underlying function with the explicit raw-diagonal difference. -/
def linearDiagonal : Data.Carrier d →+ Data.Carrier d :=
  Classical.choose (additive_diagonal_exists d)

theorem diagonal_affine (x : Data.Carrier d) :
    diagonal d x = linearDiagonal d x + offset d :=
  (Classical.choose_spec (additive_diagonal_exists d)).1 x

theorem linearDiagonal_apply (x : Data.Carrier d) :
    linearDiagonal d x = diagonal d x - offset d := by
  apply (eq_sub_iff_add_eq).2
  exact (diagonal_affine d x).symm

theorem linearDiagonal_phase (x : Data.Carrier d) :
    linearDiagonal d (d.phase.J x) = d.phase.J (linearDiagonal d x) :=
  (Classical.choose_spec (additive_diagonal_exists d)).2 x

theorem linearDiagonal_offset : linearDiagonal d (offset d) = -offset d := by
  have h := RawOperationalSeparation.diagonal_involutive d 0
  change diagonal d (offset d) = 0 at h
  rw [diagonal_affine] at h
  calc
    linearDiagonal d (offset d) =
        linearDiagonal d (offset d) + offset d - offset d := by abel
    _ = -offset d := by rw [h, zero_sub]

theorem linearDiagonal_involutive (x : Data.Carrier d) :
    linearDiagonal d (linearDiagonal d x) = x := by
  have h := RawOperationalSeparation.diagonal_involutive d x
  simp only [diagonal_affine, map_add] at h
  simpa only [linearDiagonal_offset, add_assoc, neg_add_cancel, add_zero] using h

theorem linearDiagonal_half (x : Data.Carrier d) :
    linearDiagonal d (half d x) = half d (linearDiagonal d x) :=
  MixerRecordNaturality.additive_half_compatibility
    d.normalizedOperation d.normalizedOperation (normalized_transparent d)
    (normalized_square d) (normalized_transparent d) (normalized_square d)
    (linearDiagonal d) x

theorem linearDiagonal_weight (x : Data.Carrier d) :
    d.weight (linearDiagonal d x) = d.weight x := by
  have h := RawOperationalSeparation.diagonal_weight d x
  rw [diagonal_affine, d.quadratic.null_translate _ _ (offset_null d)] at h
  exact h

private theorem half_double (x : Data.Carrier d) : half d (x + x) = x := by
  rw [map_add]
  exact d.reconstruction.halves x

private theorem phase_half (x : Data.Carrier d) :
    d.phase.J (half d x) = half d (d.phase.J x) :=
  MixerRecordNaturality.additive_half_compatibility
    d.normalizedOperation d.normalizedOperation (normalized_transparent d)
    (normalized_square d) (normalized_transparent d) (normalized_square d)
    d.phase.J x

/-- A fixed point of the raw diagonal; it may differ from the chosen raw zero. -/
def fixedCenter : Data.Carrier d := half d (offset d)

theorem fixedCenter_double : fixedCenter d + fixedCenter d = offset d :=
  d.reconstruction.halves (offset d)

theorem linearDiagonal_fixedCenter :
    linearDiagonal d (fixedCenter d) = -fixedCenter d := by
  rw [fixedCenter, linearDiagonal_half, linearDiagonal_offset, map_neg]

theorem fixedCenter_null : d.weight (fixedCenter d) = 0 := by
  rw [fixedCenter, d.reconstruction.half_scaling, offset_null, zero_div]

theorem diagonal_fixedCenter : diagonal d (fixedCenter d) = fixedCenter d := by
  rw [diagonal_affine, linearDiagonal_fixedCenter, ← fixedCenter_double d]
  abel

theorem fixedCenter_translation_weight (x : Data.Carrier d) :
    d.weight (x + fixedCenter d) = d.weight x :=
  d.quadratic.null_translate x (fixedCenter d) (fixedCenter_null d)

/-- Exact recovery of the original operation from its diagonal-normalized one. -/
theorem original_eq_diagonal_normalized (x y : Data.Carrier d) :
    d.operation (x, y) =
      (diagonal d (d.normalizedOperation (x, y)).1,
        diagonal d (d.normalizedOperation (x, y)).2) := by
  apply Prod.ext
  · rw [RawOperationalSeparation.raw_first,
      RawOperationalSeparation.normalized_route,
      RawOperationalSeparation.portA_eq, RawOperationalSeparation.portB_eq]
    rfl
  · rw [RawOperationalSeparation.raw_second,
      RawOperationalSeparation.normalized_route,
      RawOperationalSeparation.portA_eq, RawOperationalSeparation.portB_eq]
    rfl

theorem original_affine (x y : Data.Carrier d) :
    d.operation (x, y) =
      (linearDiagonal d (d.normalizedOperation (x, y)).1 + offset d,
        linearDiagonal d (d.normalizedOperation (x, y)).2 + offset d) := by
  rw [original_eq_diagonal_normalized]
  simp only [diagonal_affine]

/-- The original operation conjugated by its derived fixed null center. -/
def centeredOperation : (Data.Carrier d × Data.Carrier d) →+
    (Data.Carrier d × Data.Carrier d) where
  toFun p :=
    (linearDiagonal d (d.normalizedOperation p).1,
      linearDiagonal d (d.normalizedOperation p).2)
  map_zero' := by simp
  map_add' p q := by simp

theorem centeredOperation_apply (x y : Data.Carrier d) :
    centeredOperation d (x, y) =
      (linearDiagonal d (d.normalizedOperation (x, y)).1,
        linearDiagonal d (d.normalizedOperation (x, y)).2) := rfl

theorem original_at_fixedCenter (x y : Data.Carrier d) :
    d.operation (x + fixedCenter d, y + fixedCenter d) =
      ((centeredOperation d (x, y)).1 + fixedCenter d,
        (centeredOperation d (x, y)).2 + fixedCenter d) := by
  have hn : d.normalizedOperation (x + fixedCenter d, y + fixedCenter d) =
      d.normalizedOperation (x, y) + (fixedCenter d, fixedCenter d) := by
    change d.normalizedOperation ((x, y) + (fixedCenter d, fixedCenter d)) = _
    rw [map_add, normalized_transparent]
  rw [original_affine, hn]
  apply Prod.ext <;>
    simp only [Prod.fst_add, Prod.snd_add, map_add, linearDiagonal_fixedCenter,
      centeredOperation_apply]
  all_goals rw [← fixedCenter_double d]; abel

/-- The centering equality is on literal raw values, not merely their features. -/
theorem centeredOperation_conjugacy (x y : Data.Carrier d) :
    centeredOperation d (x, y) =
      (d.difference (d.operation (x + fixedCenter d, y + fixedCenter d)).1 (fixedCenter d),
        d.difference (d.operation (x + fixedCenter d, y + fixedCenter d)).2 (fixedCenter d)) := by
  rw [original_at_fixedCenter]
  apply Prod.ext <;> simp [RawOperationalSeparation.difference_eq]

/-- Positive-sign projection, formed using only reconstructed addition and half. -/
def plus : Data.Carrier d →+ Data.Carrier d :=
  (half d).comp (AddMonoidHom.id _ + linearDiagonal d)

/-- Negative-sign projection of the additive diagonal, retaining its null offset. -/
def minus : Data.Carrier d →+ Data.Carrier d :=
  (half d).comp (AddMonoidHom.id _ - linearDiagonal d)

theorem plus_apply (x : Data.Carrier d) :
    plus d x = half d (x + linearDiagonal d x) := rfl

theorem minus_apply (x : Data.Carrier d) :
    minus d x = half d (x - linearDiagonal d x) := rfl

theorem plus_add_minus (x : Data.Carrier d) : plus d x + minus d x = x := by
  rw [plus_apply, minus_apply, ← map_add]
  calc
    half d ((x + linearDiagonal d x) + (x - linearDiagonal d x)) =
        half d (x + x) := by congr 1; abel
    _ = x := half_double d x

theorem linearDiagonal_plus (x : Data.Carrier d) :
    linearDiagonal d (plus d x) = plus d x := by
  rw [plus_apply, linearDiagonal_half, map_add, linearDiagonal_involutive]
  congr 1
  abel

theorem linearDiagonal_minus (x : Data.Carrier d) :
    linearDiagonal d (minus d x) = -minus d x := by
  rw [minus_apply, linearDiagonal_half, map_sub, linearDiagonal_involutive]
  calc
    half d (linearDiagonal d x - x) = half d (-(x - linearDiagonal d x)) := by
      congr 1
      abel
    _ = -half d (x - linearDiagonal d x) := map_neg _ _

theorem plus_linearDiagonal (x : Data.Carrier d) :
    plus d (linearDiagonal d x) = plus d x := by
  rw [plus_apply, plus_apply, linearDiagonal_involutive]
  congr 1
  abel

theorem minus_linearDiagonal (x : Data.Carrier d) :
    minus d (linearDiagonal d x) = -minus d x := by
  rw [minus_apply, minus_apply, linearDiagonal_involutive]
  calc
    half d (linearDiagonal d x - x) = half d (-(x - linearDiagonal d x)) := by
      congr 1
      abel
    _ = -half d (x - linearDiagonal d x) := map_neg _ _

theorem plus_of_fixed (x : Data.Carrier d) (hx : linearDiagonal d x = x) :
    plus d x = x := by rw [plus_apply, hx, half_double]

theorem minus_of_fixed (x : Data.Carrier d) (hx : linearDiagonal d x = x) :
    minus d x = 0 := by rw [minus_apply, hx, sub_self, map_zero]

theorem plus_of_neg (x : Data.Carrier d) (hx : linearDiagonal d x = -x) :
    plus d x = 0 := by rw [plus_apply, hx, add_neg_cancel, map_zero]

theorem minus_of_neg (x : Data.Carrier d) (hx : linearDiagonal d x = -x) :
    minus d x = x := by rw [minus_apply, hx, sub_neg_eq_add, half_double]

theorem plus_idempotent (x : Data.Carrier d) : plus d (plus d x) = plus d x :=
  plus_of_fixed d _ (linearDiagonal_plus d x)

theorem minus_idempotent (x : Data.Carrier d) : minus d (minus d x) = minus d x :=
  minus_of_neg d _ (linearDiagonal_minus d x)

theorem plus_minus_zero (x : Data.Carrier d) : plus d (minus d x) = 0 :=
  plus_of_neg d _ (linearDiagonal_minus d x)

theorem minus_plus_zero (x : Data.Carrier d) : minus d (plus d x) = 0 :=
  minus_of_fixed d _ (linearDiagonal_plus d x)

theorem plus_phase (x : Data.Carrier d) :
    plus d (d.phase.J x) = d.phase.J (plus d x) := by
  simp only [plus_apply, linearDiagonal_phase, phase_half, map_add]

theorem minus_phase (x : Data.Carrier d) :
    minus d (d.phase.J x) = d.phase.J (minus d x) := by
  simp only [minus_apply, linearDiagonal_phase, phase_half, map_sub]

theorem plus_half (x : Data.Carrier d) : plus d (half d x) = half d (plus d x) :=
  MixerRecordNaturality.additive_half_compatibility
    d.normalizedOperation d.normalizedOperation (normalized_transparent d)
    (normalized_square d) (normalized_transparent d) (normalized_square d) (plus d) x

theorem minus_half (x : Data.Carrier d) : minus d (half d x) = half d (minus d x) :=
  MixerRecordNaturality.additive_half_compatibility
    d.normalizedOperation d.normalizedOperation (normalized_transparent d)
    (normalized_square d) (normalized_transparent d) (normalized_square d) (minus d) x

theorem plus_offset : plus d (offset d) = 0 :=
  plus_of_neg d _ (linearDiagonal_offset d)

theorem minus_offset : minus d (offset d) = offset d :=
  minus_of_neg d _ (linearDiagonal_offset d)

/-- These are reconstructed algebraic subgroups, not physical superselection sectors. -/
def plusSector : AddSubgroup (Data.Carrier d) where
  carrier := {x | linearDiagonal d x = x}
  zero_mem' := by
    change linearDiagonal d 0 = 0
    exact map_zero _
  add_mem' := by
    intro x y hx hy
    change linearDiagonal d x = x at hx
    change linearDiagonal d y = y at hy
    change linearDiagonal d (x + y) = x + y
    rw [map_add, hx, hy]
  neg_mem' := by
    intro x hx
    change linearDiagonal d x = x at hx
    change linearDiagonal d (-x) = -x
    rw [map_neg, hx]

def minusSector : AddSubgroup (Data.Carrier d) where
  carrier := {x | linearDiagonal d x = -x}
  zero_mem' := by
    change linearDiagonal d 0 = -(0 : Data.Carrier d)
    simp
  add_mem' := by
    intro x y hx hy
    change linearDiagonal d x = -x at hx
    change linearDiagonal d y = -y at hy
    change linearDiagonal d (x + y) = -(x + y)
    rw [map_add, hx, hy, neg_add]
  neg_mem' := by
    intro x hx
    change linearDiagonal d x = -x at hx
    change linearDiagonal d (-x) = -(-x)
    rw [map_neg, hx]

/-- Exact product decomposition of the reconstructed additive carrier. -/
def splitEquiv : Data.Carrier d ≃+ (plusSector d × minusSector d) where
  toFun x := (⟨plus d x, linearDiagonal_plus d x⟩,
    ⟨minus d x, linearDiagonal_minus d x⟩)
  invFun p := (p.1 : Data.Carrier d) + (p.2 : Data.Carrier d)
  left_inv := plus_add_minus d
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change plus d ((p.1 : Data.Carrier d) + (p.2 : Data.Carrier d)) = p.1
      rw [map_add, plus_of_fixed d _ p.1.property, plus_of_neg d _ p.2.property, add_zero]
    · apply Subtype.ext
      change minus d ((p.1 : Data.Carrier d) + (p.2 : Data.Carrier d)) = p.2
      rw [map_add, minus_of_fixed d _ p.1.property, minus_of_neg d _ p.2.property, zero_add]
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext <;> exact map_add _ _ _

/-- Opposite signs are orthogonal for the supplied weight, including null directions. -/
theorem weight_orthogonal (x y : Data.Carrier d)
    (hx : linearDiagonal d x = x) (hy : linearDiagonal d y = -y) :
    d.weight (x + y) = d.weight x + d.weight y := by
  have he : d.weight (x + y) = d.weight (x - y) := by
    have h := linearDiagonal_weight d (x + y)
    rw [map_add, hx, hy] at h
    simpa only [sub_eq_add_neg] using h.symm
  have hp := d.quadratic.parallelogram x y
  rw [← he] at hp
  linarith

theorem plus_minus_weight (x y : Data.Carrier d) :
    d.weight (plus d x + minus d y) = d.weight (plus d x) + d.weight (minus d y) :=
  weight_orthogonal d _ _ (linearDiagonal_plus d x) (linearDiagonal_minus d y)

theorem weight_split (x : Data.Carrier d) :
    d.weight x = d.weight (plus d x) + d.weight (minus d x) := by
  calc
    d.weight x = d.weight (plus d x + minus d x) :=
      congrArg d.weight (plus_add_minus d x).symm
    _ = _ := plus_minus_weight d x x

theorem polarization_orthogonal (x y : Data.Carrier d)
    (hx : linearDiagonal d x = x) (hy : linearDiagonal d y = -y) :
    PositiveQuadraticPolarization.polarization (U := Data.Carrier d) d.weight x y = 0 := by
  rw [PositiveQuadraticPolarization.polarization, weight_orthogonal d x y hx hy]
  ring

theorem kernel_orthogonal (x y : Data.Carrier d)
    (hx : linearDiagonal d x = x) (hy : linearDiagonal d y = -y) :
    QuadraticHermitianKernel.kernel d.phase x y = 0 := by
  have hj : linearDiagonal d (d.phase.J x) = d.phase.J x := by
    rw [linearDiagonal_phase, hx]
  rw [QuadraticHermitianKernel.kernel, polarization_orthogonal d x y hx hy,
    polarization_orthogonal d (d.phase.J x) y hj hy]
  simp

theorem plus_minus_kernel (x y : Data.Carrier d) :
    QuadraticHermitianKernel.kernel d.phase (plus d x) (minus d y) = 0 :=
  kernel_orthogonal d _ _ (linearDiagonal_plus d x) (linearDiagonal_minus d y)

/-- Orthogonality of constructed features does not assert their injectivity. -/
theorem plus_minus_inner (x y : Data.Carrier d) :
    inner ℂ (d.feature (plus d x)) (d.feature (minus d y)) = 0 := by
  rw [d.inner_feature]
  exact plus_minus_kernel d x y

theorem plus_normalized (x y : Data.Carrier d) :
    (plus d (d.normalizedOperation (x, y)).1,
      plus d (d.normalizedOperation (x, y)).2) =
      d.normalizedOperation (plus d x, plus d y) :=
  MixerRecordNaturality.intertwines_of_additive_phase
    d.normalizedOperation d.normalizedOperation (normalized_transparent d)
    (normalized_square d) (normalized_transparent d) (normalized_square d)
    (plus d) (plus_phase d) x y

theorem minus_normalized (x y : Data.Carrier d) :
    (minus d (d.normalizedOperation (x, y)).1,
      minus d (d.normalizedOperation (x, y)).2) =
      d.normalizedOperation (minus d x, minus d y) :=
  MixerRecordNaturality.intertwines_of_additive_phase
    d.normalizedOperation d.normalizedOperation (normalized_transparent d)
    (normalized_square d) (normalized_transparent d) (normalized_square d)
    (minus d) (minus_phase d) x y

theorem plus_centered (x y : Data.Carrier d) :
    (plus d (centeredOperation d (x, y)).1,
      plus d (centeredOperation d (x, y)).2) =
      d.normalizedOperation (plus d x, plus d y) := by
  rw [centeredOperation_apply]
  simp only [plus_linearDiagonal]
  exact plus_normalized d x y

theorem minus_centered (x y : Data.Carrier d) :
    (minus d (centeredOperation d (x, y)).1,
      minus d (centeredOperation d (x, y)).2) =
      -d.normalizedOperation (minus d x, minus d y) := by
  rw [centeredOperation_apply]
  simp only [minus_linearDiagonal]
  exact congrArg Neg.neg (minus_normalized d x y)

theorem plus_original (x y : Data.Carrier d) :
    (plus d (d.operation (x, y)).1, plus d (d.operation (x, y)).2) =
      d.normalizedOperation (plus d x, plus d y) := by
  rw [original_affine]
  simp only [map_add, plus_linearDiagonal, plus_offset, add_zero]
  exact plus_normalized d x y

theorem minus_original (x y : Data.Carrier d) :
    (minus d (d.operation (x, y)).1, minus d (d.operation (x, y)).2) =
      -d.normalizedOperation (minus d x, minus d y) + (offset d, offset d) := by
  rw [original_affine]
  simp only [map_add, minus_linearDiagonal, minus_offset]
  change -(minus d (d.normalizedOperation (x, y)).1,
      minus d (d.normalizedOperation (x, y)).2) + (offset d, offset d) = _
  rw [minus_normalized]

/-- The original gate splits exactly into a normalized part and a negative
normalized part with the retained affine null displacement. -/
theorem original_sector_decomposition (x y : Data.Carrier d) :
    (plus d (d.operation (x, y)).1, plus d (d.operation (x, y)).2) =
        d.normalizedOperation (plus d x, plus d y) ∧
      (minus d (d.operation (x, y)).1, minus d (d.operation (x, y)).2) =
        -d.normalizedOperation (minus d x, minus d y) + (offset d, offset d) :=
  ⟨plus_original d x y, minus_original d x y⟩

inductive BoundaryRole where
  | rawDataOnlyWithReconstructedCarrierAlgebra
  | originalDiagonalMayMoveChosenZeroByNullOffset
  | additiveInvolutionAndFixedNullCenterAreDerived
  | complementaryAlgebraicSignSubgroupsAndExactProductDecomposition
  | weightAndConstructedComplexFeatureOrthogonality
  | literalAffineConjugacyAndOppositeNormalizedSectorOperations
  | noFeatureInjectivityOrWholeCarrierTorsionFreePremise
  | noPhysicalCenteringProjectionNormalizationOrGateControl
  | noCircuitSynthesisProbabilityClassificationOrActualization
  | doesNotProveFullQMOrUpgradeManifestStatus
  deriving DecidableEq, Repr

def boundaryRoles : List BoundaryRole := [
  .rawDataOnlyWithReconstructedCarrierAlgebra,
  .originalDiagonalMayMoveChosenZeroByNullOffset,
  .additiveInvolutionAndFixedNullCenterAreDerived,
  .complementaryAlgebraicSignSubgroupsAndExactProductDecomposition,
  .weightAndConstructedComplexFeatureOrthogonality,
  .literalAffineConjugacyAndOppositeNormalizedSectorOperations,
  .noFeatureInjectivityOrWholeCarrierTorsionFreePremise,
  .noPhysicalCenteringProjectionNormalizationOrGateControl,
  .noCircuitSynthesisProbabilityClassificationOrActualization,
  .doesNotProveFullQMOrUpgradeManifestStatus]

end

end IDT.QMClosure.RawDiagonalDecomposition
