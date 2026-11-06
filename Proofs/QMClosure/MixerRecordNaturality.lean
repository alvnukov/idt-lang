import Proofs.QMClosure.OperationalQuadraticReconstruction
import Proofs.QMClosure.QuadraticRecordRefinement

namespace IDT.QMClosure.MixerRecordNaturality

noncomputable section

open TransparentSwapRoot (portA portB reconstruct_operation operation_eq_symmetric_mixer
  commutes_with_swap)
open OperationalQuadraticReconstruction (phase half)

/-!
Exact order independence of a fixed unnormalized coherent channel and a mixer
is an additional operational bridge. External ports contain two copies of the
whole preparation carrier; they are not the internal preparation coordinates.
The results below classify that bridge algebraically and transfer readout laws.
They do not justify the bridge from prior IDT assumptions or actualize events.
-/

section Monoid
variable {V U : Type*} [AddCommMonoid V] [AddCommMonoid U]

def Intertwines (T : (V × V) →+ (V × V)) (S : (U × U) →+ (U × U))
    (L : V → U) : Prop :=
  ∀ x y, (L (T (x, y)).1, L (T (x, y)).2) = S (L x, L y)

def FirstOutputIntertwines (T : (V × V) →+ (V × V))
    (S : (U × U) →+ (U × U)) (L : V → U) : Prop :=
  ∀ x y, L (T (x, y)).1 = (S (L x, L y)).1

theorem first_output_iff (T : (V × V) →+ (V × V))
    (S : (U × U) →+ (U × U))
    (tSquare : ∀ p, T (T p) = p.swap) (sSquare : ∀ p, S (S p) = p.swap)
    (L : V → U) : FirstOutputIntertwines T S L ↔ Intertwines T S L := by
  constructor
  · intro h x y
    apply Prod.ext
    · exact h x y
    · have ht := congrArg Prod.fst (commutes_with_swap T tSquare (x, y))
      have hs := congrArg Prod.fst (commutes_with_swap S sSquare (L x, L y))
      simpa only [Prod.fst_swap, Prod.swap_prod_mk] using
        (congrArg L ht).symm.trans ((h y x).trans hs)
  · intro h x y
    exact congrArg Prod.fst (h x y)

theorem coefficient_identity (T : (V × V) →+ (V × V))
    (S : (U × U) →+ (U × U))
    (tSquare : ∀ p, T (T p) = p.swap) (sSquare : ∀ p, S (S p) = p.swap)
    (L : V → U) (h : Intertwines T S L) (x y : V) :
    L (portA T x + portB T y) = portA S (L x) + portB S (L y) := by
  have hh := congrArg Prod.fst (h x y)
  rw [congrFun (operation_eq_symmetric_mixer T tSquare),
    congrFun (operation_eq_symmetric_mixer S sSquare)] at hh
  exact hh

theorem axis_compatibility (T : (V × V) →+ (V × V))
    (S : (U × U) →+ (U × U))
    (tSquare : ∀ p, T (T p) = p.swap) (sSquare : ∀ p, S (S p) = p.swap)
    (L : V → U) (h0 : L 0 = 0) (h : Intertwines T S L) :
    (∀ x, L (portA T x) = portA S (L x)) ∧
      (∀ x, L (portB T x) = portB S (L x)) := by
  constructor <;> intro x
  · simpa only [map_zero, add_zero, h0] using
      coefficient_identity T S tSquare sSquare L h x 0
  · simpa only [map_zero, zero_add, h0] using
      coefficient_identity T S tSquare sSquare L h 0 x

theorem coefficient_preimages (T : (V × V) →+ (V × V))
    (transparent : ∀ x, T (x, x) = (x, x)) (square : ∀ p, T (T p) = p.swap)
    (x : V) :
    portA T (portB T x + portB T x) = x ∧
      portB T (portA T x + portA T x) = x := by
  have r := (reconstruct_operation T transparent square).1
  constructor
  · simpa only [map_add] using r.halves x
  · have hh := r.halves x
    change portA T (portB T x) + portA T (portB T x) = x at hh
    have hc : portA T (portB T x) = portB T (portA T x) := r.commute x
    rw [hc] at hh
    simpa only [map_add] using hh

theorem additive_of_vacuum_intertwines (T : (V × V) →+ (V × V))
    (S : (U × U) →+ (U × U))
    (tTransparent : ∀ x, T (x, x) = (x, x))
    (tSquare : ∀ p, T (T p) = p.swap) (sSquare : ∀ p, S (S p) = p.swap)
    (L : V → U) (h0 : L 0 = 0) (h : Intertwines T S L) (x y : V) :
    L (x + y) = L x + L y := by
  obtain ⟨ha, hb⟩ := axis_compatibility T S tSquare sSquare L h0 h
  have hh := coefficient_identity T S tSquare sSquare L h
    (portB T x + portB T x) (portA T y + portA T y)
  rw [← ha, ← hb, (coefficient_preimages T tTransparent tSquare x).1,
    (coefficient_preimages T tTransparent tSquare y).2] at hh
  exact hh

def toAddMonoidHom (T : (V × V) →+ (V × V)) (S : (U × U) →+ (U × U))
    (tTransparent : ∀ x, T (x, x) = (x, x))
    (tSquare : ∀ p, T (T p) = p.swap) (sSquare : ∀ p, S (S p) = p.swap)
    (L : V → U) (h0 : L 0 = 0) (h : Intertwines T S L) : V →+ U where
  toFun := L
  map_zero' := h0
  map_add' := additive_of_vacuum_intertwines T S tTransparent tSquare sSquare L h0 h

theorem phase_compatibility (T : (V × V) →+ (V × V))
    (S : (U × U) →+ (U × U))
    (tTransparent : ∀ x, T (x, x) = (x, x))
    (tSquare : ∀ p, T (T p) = p.swap) (sSquare : ∀ p, S (S p) = p.swap)
    (L : V → U) (h0 : L 0 = 0) (h : Intertwines T S L) (x : V) :
    L (phase T x) = phase S (L x) := by
  have ha := (axis_compatibility T S tSquare sSquare L h0 h).1
  change L (portA T (portA T x) + portA T (portA T x)) =
    portA S (portA S (L x)) + portA S (portA S (L x))
  rw [additive_of_vacuum_intertwines T S tTransparent tSquare sSquare L h0 h, ha, ha]

/-- Genuine halves commute with any additive map between these carriers. -/
theorem additive_half_compatibility (T : (V × V) →+ (V × V))
    (S : (U × U) →+ (U × U))
    (tTransparent : ∀ x, T (x, x) = (x, x))
    (tSquare : ∀ p, T (T p) = p.swap)
    (sTransparent : ∀ x, S (x, x) = (x, x))
    (sSquare : ∀ p, S (S p) = p.swap) (L : V →+ U) (x : V) :
    L (half T x) = half S (L x) := by
  have rt := (reconstruct_operation T tTransparent tSquare).1
  have rs := (reconstruct_operation S sTransparent sSquare).1
  apply PhaseMixerCancellation.doubling_injective (half S) rs.halves
  change L (half T x) + L (half T x) = half S (L x) + half S (L x)
  rw [← map_add]
  exact (congrArg L (rt.halves x)).trans (rs.halves (L x)).symm

theorem vacuum_half_compatibility (T : (V × V) →+ (V × V))
    (S : (U × U) →+ (U × U))
    (tTransparent : ∀ x, T (x, x) = (x, x))
    (tSquare : ∀ p, T (T p) = p.swap)
    (sTransparent : ∀ x, S (x, x) = (x, x))
    (sSquare : ∀ p, S (S p) = p.swap)
    (L : V → U) (h0 : L 0 = 0) (h : Intertwines T S L) (x : V) :
    L (half T x) = half S (L x) :=
  additive_half_compatibility T S tTransparent tSquare sTransparent sSquare
    (toAddMonoidHom T S tTransparent tSquare sSquare L h0 h) x

theorem intertwines_of_additive_phase (T : (V × V) →+ (V × V))
    (S : (U × U) →+ (U × U))
    (tTransparent : ∀ x, T (x, x) = (x, x))
    (tSquare : ∀ p, T (T p) = p.swap)
    (sTransparent : ∀ x, S (x, x) = (x, x))
    (sSquare : ∀ p, S (S p) = p.swap) (L : V →+ U)
    (hp : ∀ x, L (phase T x) = phase S (L x)) : Intertwines T S L := by
  intro x y
  rw [congrFun (reconstruct_operation T tTransparent tSquare).2,
    congrFun (reconstruct_operation S sTransparent sSquare).2]
  have hh := additive_half_compatibility T S tTransparent tSquare sTransparent sSquare L
  change (L (PhaseMixerCancellation.mixer (phase T) (half T) (x, y)).1,
    L (PhaseMixerCancellation.mixer (phase T) (half T) (x, y)).2) =
      PhaseMixerCancellation.mixer (phase S) (half S) (L x, L y)
  apply Prod.ext <;>
    simp only [PhaseMixerCancellation.mixer, PhaseMixerCancellation.coefficientA,
      PhaseMixerCancellation.coefficientB, map_add, hh, hp]

theorem vacuum_intertwines_iff (T : (V × V) →+ (V × V))
    (S : (U × U) →+ (U × U))
    (tTransparent : ∀ x, T (x, x) = (x, x))
    (tSquare : ∀ p, T (T p) = p.swap)
    (sTransparent : ∀ x, S (x, x) = (x, x))
    (sSquare : ∀ p, S (S p) = p.swap) (L : V → U) :
    (L 0 = 0 ∧ Intertwines T S L) ↔
      ∃ M : V →+ U, (∀ x, M x = L x) ∧
        (∀ x, M (phase T x) = phase S (M x)) := by
  constructor
  · rintro ⟨h0, h⟩
    exact ⟨toAddMonoidHom T S tTransparent tSquare sSquare L h0 h, fun _ => rfl,
      phase_compatibility T S tTransparent tSquare sSquare L h0 h⟩
  · rintro ⟨M, hm, hp⟩
    have heq : L = M := funext fun x => (hm x).symm
    rw [heq]
    exact ⟨M.map_zero, intertwines_of_additive_phase T S tTransparent tSquare
      sTransparent sSquare M hp⟩

theorem translate_intertwines (T : (V × V) →+ (V × V))
    (S : (U × U) →+ (U × U))
    (sTransparent : ∀ x, S (x, x) = (x, x))
    (L : V → U) (h : Intertwines T S L) (c : U) :
    Intertwines T S (fun x => L x + c) := by
  intro x y
  change (L (T (x, y)).1, L (T (x, y)).2) + (c, c) = S (L x + c, L y + c)
  rw [h x y, ← sTransparent c, ← map_add]
  rfl

def centered (S : (U × U) →+ (U × U)) (L : V → U) (x : V) : U :=
  L x + phase S (phase S (L 0))

theorem centered_vacuum_intertwines (T : (V × V) →+ (V × V))
    (S : (U × U) →+ (U × U))
    (sTransparent : ∀ x, S (x, x) = (x, x))
    (sSquare : ∀ p, S (S p) = p.swap) (L : V → U) (h : Intertwines T S L) :
    centered S L 0 = 0 ∧ Intertwines T S (centered S L) := by
  exact ⟨(reconstruct_operation S sTransparent sSquare).1.cancellation (L 0),
    translate_intertwines T S sTransparent L h _⟩

theorem affine_classification (T : (V × V) →+ (V × V))
    (S : (U × U) →+ (U × U))
    (tTransparent : ∀ x, T (x, x) = (x, x))
    (tSquare : ∀ p, T (T p) = p.swap)
    (sTransparent : ∀ x, S (x, x) = (x, x))
    (sSquare : ∀ p, S (S p) = p.swap) (L : V → U) :
    Intertwines T S L ↔
      ∃ M : V →+ U, (∀ x, L x = M x + L 0) ∧
        (∀ x, M (phase T x) = phase S (M x)) := by
  constructor
  · intro h
    obtain ⟨h0, hc⟩ := centered_vacuum_intertwines T S sTransparent sSquare L h
    let M := toAddMonoidHom T S tTransparent tSquare sSquare (centered S L) h0 hc
    refine ⟨M, ?_, phase_compatibility T S tTransparent tSquare sSquare
      (centered S L) h0 hc⟩
    intro x
    change L x = (L x + phase S (phase S (L 0))) + L 0
    have hz : L 0 + phase S (phase S (L 0)) = 0 :=
      (reconstruct_operation S sTransparent sSquare).1.cancellation (L 0)
    rw [add_assoc, add_comm (phase S (phase S (L 0))), hz, add_zero]
  · rintro ⟨M, hm, hp⟩
    have hh := translate_intertwines T S sTransparent M
      (intertwines_of_additive_phase T S tTransparent tSquare sTransparent sSquare M hp) (L 0)
    have heq : L = fun x => M x + L 0 := funext hm
    rw [heq]
    exact hh

/-- Output conservation transfers directly; no target root laws are needed. -/
theorem pullback_conservation (T : (V × V) →+ (V × V))
    (S : (U × U) →+ (U × U)) (L : V → U) (h : Intertwines T S L)
    (W : U → ℝ)
    (conserve : ∀ x y, W (S (x, y)).1 + W (S (x, y)).2 = W x + W y)
    (x y : V) :
    W (L (T (x, y)).1) + W (L (T (x, y)).2) = W (L x) + W (L y) := by
  have hh := conserve (L x) (L y)
  rw [← h x y] at hh
  exact hh

theorem reconstruct_record_weight (T : (V × V) →+ (V × V))
    (S : (U × U) →+ (U × U))
    (tTransparent : ∀ x, T (x, x) = (x, x))
    (tSquare : ∀ p, T (T p) = p.swap)
    (L : V → U) (h : Intertwines T S L) (W : U → ℝ)
    (vacuum : W (L 0) = 0) (positive : ∀ x, 0 ≤ W x)
    (conserve : ∀ x y, W (S (x, y)).1 + W (S (x, y)).2 = W x + W y) :
    OperationalQuadraticReconstruction.Reconstruction T (fun x => W (L x)) :=
  OperationalQuadraticReconstruction.reconstruct_positive_operation T tTransparent tSquare
    (fun x => W (L x)) vacuum (fun x => positive (L x))
    (pullback_conservation T S L h W conserve)

theorem finite_branch_vacuum {ι : Type*} [Fintype ι]
    (F : ι → V → ℝ) (W : V → ℝ) (positive : ∀ i x, 0 ≤ F i x)
    (resolution : ∀ x, ∑ i, F i x = W x) (vacuum : W 0 = 0) (i : ι) :
    F i 0 = 0 := by
  have hs : ∑ j, F j 0 = 0 := (resolution 0).trans vacuum
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => positive j 0)).mp hs i
    (Finset.mem_univ i)

end Monoid

section Group
variable {V U : Type*} [AddCommGroup V] [AddCommGroup U]

/-- Observed zero vacuum weight suffices even for an affine channel. -/
theorem positive_quadratic_pullback (T : (V × V) →+ (V × V))
    (S : (U × U) →+ (U × U))
    (tTransparent : ∀ x, T (x, x) = (x, x))
    (tSquare : ∀ p, T (T p) = p.swap)
    (sTransparent : ∀ x, S (x, x) = (x, x))
    (sSquare : ∀ p, S (S p) = p.swap)
    (L : V → U) (h : Intertwines T S L) (Q : U → ℝ)
    (hq : QuadraticRecordRefinement.PositiveQuadratic Q) (vacuum : Q (L 0) = 0) :
    QuadraticRecordRefinement.PositiveQuadratic (fun x => Q (L x)) := by
  obtain ⟨M, hm, _hp⟩ := (affine_classification T S tTransparent tSquare
    sTransparent sSquare L).mp h
  have heq (x : V) : Q (L x) = Q (M x) := by
    rw [hm x]
    exact hq.null_translate (M x) (L 0) vacuum
  constructor
  · intro x; exact hq.nonnegative (L x)
  · intro x y
    simp only [heq, map_add, map_sub]
    exact hq.parallelogram (M x) (M y)

end Group

section WholeCarrierCopies
variable {V : Type*} [AddCommMonoid V]

/-- Mix two external copies coordinatewise, preserving internal port roles. -/
def componentwiseLift (T : (V × V) →+ (V × V)) :
    ((V × V) × (V × V)) →+ ((V × V) × (V × V)) where
  toFun p := (((T (p.1.1, p.2.1)).1, (T (p.1.2, p.2.2)).1),
    ((T (p.1.1, p.2.1)).2, (T (p.1.2, p.2.2)).2))
  map_zero' := by
    change (((T 0).1, (T 0).1), ((T 0).2, (T 0).2)) = 0
    rw [map_zero]
    rfl
  map_add' p q := by
    have ha : (p.1.1 + q.1.1, p.2.1 + q.2.1) =
        (p.1.1, p.2.1) + (q.1.1, q.2.1) := rfl
    have hb : (p.1.2 + q.1.2, p.2.2 + q.2.2) =
        (p.1.2, p.2.2) + (q.1.2, q.2.2) := rfl
    simp only [Prod.fst_add, Prod.snd_add, ha, hb, map_add]
    rfl

theorem componentwise_transparent (T : (V × V) →+ (V × V))
    (transparent : ∀ x, T (x, x) = (x, x)) (x : V × V) :
    componentwiseLift T (x, x) = (x, x) := by
  simp [componentwiseLift, transparent]

theorem componentwise_square (T : (V × V) →+ (V × V))
    (square : ∀ p, T (T p) = p.swap) (p : (V × V) × (V × V)) :
    componentwiseLift T (componentwiseLift T p) = p.swap := by
  simp only [componentwiseLift, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  change (((T (T (p.1.1, p.2.1))).1, (T (T (p.1.2, p.2.2))).1),
    ((T (T (p.1.1, p.2.1))).2, (T (T (p.1.2, p.2.2))).2)) = p.swap
  simp only [square, Prod.fst_swap, Prod.snd_swap]
  rfl

theorem proper_projection_intertwines (T : (V × V) →+ (V × V)) :
    Intertwines (componentwiseLift T) T (Prod.fst : V × V → V) := by
  intro x y
  rfl

theorem proper_projection_identifies_distinct_inputs (a b : V) (hab : a ≠ b) :
    ∃ p q : V × V, p ≠ q ∧ p.1 = q.1 := by
  refine ⟨(0, a), (0, b), ?_, rfl⟩
  intro hh
  exact hab (congrArg Prod.snd hh)

end WholeCarrierCopies

namespace Controls

theorem translation_intertwines {V : Type*} [AddCommMonoid V]
    (T : (V × V) →+ (V × V)) (transparent : ∀ x, T (x, x) = (x, x)) (c : V) :
    Intertwines T T (fun x => x + c) :=
  translate_intertwines T T transparent id (fun _ _ => rfl) c

theorem nonzero_translation_not_vacuum {V : Type*} [AddCommMonoid V]
    (c : V) (hc : c ≠ 0) : (fun x => x + c) 0 ≠ 0 := by simpa using hc

/-- Additivity and an ordinary norm-preserving vacuum do not imply naturality. -/
def conjugation : ℂ →+ ℂ := (starRingEnd ℂ).toAddMonoidHom

theorem conjugation_vacuum : conjugation 0 = 0 := conjugation.map_zero

theorem conjugation_norm (z : ℂ) :
    Complex.normSq (conjugation z) = Complex.normSq z := by
  simp [conjugation]

theorem complex_norm_positive_quadratic :
    QuadraticRecordRefinement.PositiveQuadratic (Complex.normSq : ℂ → ℝ) := by
  constructor
  · exact Complex.normSq_nonneg
  · intro x y
    simp [Complex.normSq_apply]
    ring

theorem conjugation_quadratic_pullback :
    QuadraticRecordRefinement.PositiveQuadratic (fun z : ℂ => Complex.normSq (conjugation z)) := by
  simpa only [conjugation_norm] using complex_norm_positive_quadratic

theorem conjugation_not_same_orientation :
    ¬ Intertwines OperationalQuadraticReconstruction.ConsistencyWitness.operation
      OperationalQuadraticReconstruction.ConsistencyWitness.operation conjugation := by
  intro h
  have hh := congrArg Complex.im (congrArg Prod.fst (h 1 0))
  norm_num [conjugation, OperationalQuadraticReconstruction.ConsistencyWitness.operation,
    OperationalPhaseMixerReconstruction.selectedMixer, PhaseMixerCancellation.mixer,
    PhaseMixerCancellation.coefficientA, PhaseMixerCancellation.coefficientB,
    OperationalPhaseMixerReconstruction.phase, OperationalPhaseMixerWitness.half,
    map_ofNat, Complex.div_im] at hh

theorem square_map_vacuum : (fun z : ℂ => z ^ 2) 0 = 0 := by simp

theorem square_map_not_intertwines :
    ¬ Intertwines OperationalQuadraticReconstruction.ConsistencyWitness.operation
      OperationalQuadraticReconstruction.ConsistencyWitness.operation (fun z : ℂ => z ^ 2) := by
  intro h
  have hh := congrArg Complex.re (congrArg Prod.fst (h 1 0))
  norm_num [OperationalQuadraticReconstruction.ConsistencyWitness.operation,
    OperationalPhaseMixerReconstruction.selectedMixer, PhaseMixerCancellation.mixer,
    PhaseMixerCancellation.coefficientA, PhaseMixerCancellation.coefficientB,
    OperationalPhaseMixerReconstruction.phase, OperationalPhaseMixerWitness.half,
    pow_two, Complex.mul_re, Complex.div_re, Complex.div_im] at hh

theorem square_norm_pullback_not_quadratic :
    ¬ QuadraticRecordRefinement.PositiveQuadratic (fun z : ℂ => Complex.normSq (z ^ 2)) := by
  intro h
  have hh := h.parallelogram 1 1
  norm_num at hh

end Controls

inductive BridgeBoundary where
  | suppliedFixedUnnormalizedCoherentChannelOrderIndependence
  | externalPortsAreCopiesOfWholePreparationCarrier
  | exactNaturalityAdditionalToPriorIDT
  | vacuumNaturalityEquivalentToAdditivePhaseCompatibleMaps
  | affineClassificationWithoutStrictVacuum
  | onlyCenteredMapHasPhaseAndHalfCompatibility
  | genuineHalfCompatibilityNeedsNoIndependentBridge
  | suppliedOutputReadoutConservation
  | perRecordConservationFollowsFromNaturalityAndOutputConservation
  | totalInputConservationAloneInsufficientForBranches
  | observedVacuumWeightSufficesForQuadraticPullback
  | nonnegativeFiniteResolutionSuppliesBranchVacuumWeight
  | recordWeightResolutionStillSupplied
  | classicalWaveFiltersAlsoFit
  | stochasticClickSelectionNotAutomaticallyCoherentMap
  | normalizedPostselectionNotAutomaticallyCoherentMap
  | noExclusiveEventsOrProbabilityActualization
  | noAnalyticComplexLinearityOrHilbertFullness
  | noCompositesDynamicsOrFullQM
  | noScientificStatusUpgrade
  deriving DecidableEq, Repr

def bridgeLedger : List BridgeBoundary := [
  .suppliedFixedUnnormalizedCoherentChannelOrderIndependence,
  .externalPortsAreCopiesOfWholePreparationCarrier,
  .exactNaturalityAdditionalToPriorIDT,
  .vacuumNaturalityEquivalentToAdditivePhaseCompatibleMaps,
  .affineClassificationWithoutStrictVacuum,
  .onlyCenteredMapHasPhaseAndHalfCompatibility,
  .genuineHalfCompatibilityNeedsNoIndependentBridge,
  .suppliedOutputReadoutConservation,
  .perRecordConservationFollowsFromNaturalityAndOutputConservation,
  .totalInputConservationAloneInsufficientForBranches,
  .observedVacuumWeightSufficesForQuadraticPullback,
  .nonnegativeFiniteResolutionSuppliesBranchVacuumWeight,
  .recordWeightResolutionStillSupplied,
  .classicalWaveFiltersAlsoFit,
  .stochasticClickSelectionNotAutomaticallyCoherentMap,
  .normalizedPostselectionNotAutomaticallyCoherentMap,
  .noExclusiveEventsOrProbabilityActualization,
  .noAnalyticComplexLinearityOrHilbertFullness,
  .noCompositesDynamicsOrFullQM,
  .noScientificStatusUpgrade]

end
end IDT.QMClosure.MixerRecordNaturality
