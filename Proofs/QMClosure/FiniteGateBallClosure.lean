import Proofs.QMClosure.FiniteGateCubicCoordinates
import Proofs.QMClosure.CubicRotationRadiality

/-!
# A positive-radius ball as mathematical preparation-image closure

The finite gate frame constructs invertible spatial coordinates on normalized
fibres. If any one actual binary average preserves preparations, the mathematical
closure of that spatial preparation image is a positive-radius Euclidean ball.
No topology is assumed on the original vector space. The theorem supplies no
physical availability of the added limit points or limiting operations.
-/

noncomputable section

namespace IDT.QMClosure.FiniteGateBallClosure

open Set FiniteGateFrameDimension FiniteGateCubicCoordinates
open FiniteGatePreparationClosure

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def coordinatePx (p : SpatialPoint) : SpatialPoint := (p.1, 0, 0)
def coordinatePy (p : SpatialPoint) : SpatialPoint := (0, p.2.1, 0)
def coordinatePz (p : SpatialPoint) : SpatialPoint := (0, 0, p.2.2)

private theorem continuous_az : Continuous CubicRotationCircleDensity.az := by
  unfold CubicRotationCircleDensity.az
  fun_prop

private theorem continuous_ax : Continuous CubicRotationCircleDensity.ax := by
  unfold CubicRotationCircleDensity.ax
  fun_prop

private theorem continuous_coordinatePx : Continuous coordinatePx := by
  unfold coordinatePx
  fun_prop

private theorem continuous_coordinatePy : Continuous coordinatePy := by
  unfold coordinatePy
  fun_prop

private theorem continuous_coordinatePz : Continuous coordinatePz := by
  unfold coordinatePz
  fun_prop

/-- Continuity preserves invariance after taking the mathematical closure. -/
theorem mapsTo_closure_of_continuous {P : Set SpatialPoint} {f : SpatialPoint → SpatialPoint}
    (hf : Continuous f) (hP : MapsTo f P P) : MapsTo f (closure P) (closure P) := by
  have hpre : P ⊆ f ⁻¹' closure P := fun _ hp => subset_closure (hP hp)
  exact closure_minimal hpre (isClosed_closure.preimage hf)

private def toTriple (p : SpatialPoint) : TwoCircleSphere.Vec3 := ⟨p.1, p.2.1, p.2.2⟩
private def fromTriple (p : TwoCircleSphere.Vec3) : SpatialPoint := (p.x, p.y, p.z)

private theorem fromTriple_toTriple (p : SpatialPoint) : fromTriple (toTriple p) = p := by
  rcases p with ⟨x, y, z⟩
  rfl

/-- The checked radial ball-fill theorem in the standard real-product coordinates. -/
theorem eq_ball_of_product_radial_one_axis_projection {K : Set SpatialPoint} {R : ℝ}
    (hR : 0 ≤ R)
    (hrad : ∀ p ∈ K, ∀ q, sqnorm q = sqnorm p → q ∈ K)
    (hmax : ∃ p ∈ K, sqnorm p = R ^ 2)
    (hbound : ∀ p ∈ K, sqnorm p ≤ R ^ 2)
    (hproj : MapsTo coordinatePx K K ∨ MapsTo coordinatePy K K ∨ MapsTo coordinatePz K K) :
    K = {p | sqnorm p ≤ R ^ 2} := by
  let E : Set TwoCircleSphere.Vec3 := fromTriple ⁻¹' K
  have hradE : TwoCircleSphere.Radial E := by
    intro p hp q hnorm
    exact hrad (fromTriple p) hp (fromTriple q) hnorm
  have hmaxE : ∃ p ∈ E, TwoCircleSphere.sqnorm p = R ^ 2 := by
    obtain ⟨p, hp, hnorm⟩ := hmax
    refine ⟨toTriple p, ?_, hnorm⟩
    change fromTriple (toTriple p) ∈ K
    rw [fromTriple_toTriple]
    exact hp
  have hboundE : ∀ p ∈ E, TwoCircleSphere.sqnorm p ≤ R ^ 2 := by
    intro p hp
    exact hbound (fromTriple p) hp
  have hprojE : (∀ p ∈ E, TwoCircleSphere.projectX p ∈ E) ∨
      (∀ p ∈ E, TwoCircleSphere.projectY p ∈ E) ∨
      (∀ p ∈ E, TwoCircleSphere.projectZ p ∈ E) := by
    rcases hproj with hX | hY | hZ
    · exact Or.inl (fun p hp => hX hp)
    · exact Or.inr (Or.inl (fun p hp => hY hp))
    · exact Or.inr (Or.inr (fun p hp => hZ hp))
  have hE := TwoCircleSphere.eq_ball_of_radial_one_axis_projection hR hradE hmaxE hboundE hprojE
  apply Set.Subset.antisymm
  · intro p hp
    have hpE : toTriple p ∈ E := by
      change fromTriple (toTriple p) ∈ K
      rw [fromTriple_toTriple]
      exact hp
    rw [hE] at hpE
    exact hpE
  · intro p hp
    have hpE : toTriple p ∈ E := by
      rw [hE]
      exact hp
    change fromTriple (toTriple p) ∈ K at hpE
    rw [fromTriple_toTriple] at hpE
    exact hpE

/-- The two finite gate actions make the mathematical coordinate closure radial. -/
theorem preparationClosure_radial {F : Frame V} (D : CubicCoordinateData F) :
    ∀ p ∈ preparationClosure F D.metric.coordinates D.metric.yScale D.metric.zScale,
      ∀ q, sqnorm q = sqnorm p →
        q ∈ preparationClosure F D.metric.coordinates D.metric.yScale D.metric.zScale := by
  apply CubicRotationRadiality.closed_cubic_invariant_radial
  · exact isClosed_closure
  · exact mapsTo_closure_of_continuous continuous_az D.az_preserves
  · exact mapsTo_closure_of_continuous continuous_ax D.ax_preserves

/-- An actual available average transports to its actual spatial projection. -/
theorem preparation_image_projection {F : Frame V} (D : CubicCoordinateData F)
    (hActual : (∀ v ∈ F.preparations, F.Ex v ∈ F.preparations) ∨
      (∀ v ∈ F.preparations, F.Ey v ∈ F.preparations) ∨
      (∀ v ∈ F.preparations, F.Ez v ∈ F.preparations)) :
    MapsTo coordinatePx (spatialPreparations F D.metric.coordinates D.metric.yScale D.metric.zScale)
      (spatialPreparations F D.metric.coordinates D.metric.yScale D.metric.zScale) ∨
    MapsTo coordinatePy (spatialPreparations F D.metric.coordinates D.metric.yScale D.metric.zScale)
      (spatialPreparations F D.metric.coordinates D.metric.yScale D.metric.zScale) ∨
    MapsTo coordinatePz (spatialPreparations F D.metric.coordinates D.metric.yScale D.metric.zScale)
      (spatialPreparations F D.metric.coordinates D.metric.yScale D.metric.zScale) := by
  rcases hActual with hX | hY | hZ
  · left
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨F.Ex v, hX v hv, D.Ex_compatible v⟩
  · right; left
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨F.Ey v, hY v hv, D.Ey_compatible v⟩
  · right; right
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨F.Ez v, hZ v hv, D.Ez_compatible v⟩

/-- The matching actual projection also preserves the mathematical closure. -/
theorem preparation_closure_projection {F : Frame V} (D : CubicCoordinateData F)
    (hActual : (∀ v ∈ F.preparations, F.Ex v ∈ F.preparations) ∨
      (∀ v ∈ F.preparations, F.Ey v ∈ F.preparations) ∨
      (∀ v ∈ F.preparations, F.Ez v ∈ F.preparations)) :
    MapsTo coordinatePx (preparationClosure F D.metric.coordinates D.metric.yScale D.metric.zScale)
      (preparationClosure F D.metric.coordinates D.metric.yScale D.metric.zScale) ∨
    MapsTo coordinatePy (preparationClosure F D.metric.coordinates D.metric.yScale D.metric.zScale)
      (preparationClosure F D.metric.coordinates D.metric.yScale D.metric.zScale) ∨
    MapsTo coordinatePz (preparationClosure F D.metric.coordinates D.metric.yScale D.metric.zScale)
      (preparationClosure F D.metric.coordinates D.metric.yScale D.metric.zScale) := by
  rcases preparation_image_projection D hActual with hX | hY | hZ
  · exact Or.inl (mapsTo_closure_of_continuous continuous_coordinatePx hX)
  · exact Or.inr (Or.inl (mapsTo_closure_of_continuous continuous_coordinatePy hY))
  · exact Or.inr (Or.inr (mapsTo_closure_of_continuous continuous_coordinatePz hZ))

/-- Constructed normalized-fibre coordinates and their positive-radius ball closure. -/
structure BallClosureData (F : Frame V) where
  coordinates : CubicCoordinateData F
  radius : ℝ
  radius_pos : 0 < radius
  closure_eq_ball :
    preparationClosure F coordinates.metric.coordinates coordinates.metric.yScale coordinates.metric.zScale =
      {p | sqnorm p ≤ radius ^ 2}

/-- A separately closed spatial preparation image already equals the ball. -/
theorem BallClosureData.image_eq_ball {F : Frame V} (B : BallClosureData F)
    (hclosed : IsClosed (spatialPreparations F B.coordinates.metric.coordinates
      B.coordinates.metric.yScale B.coordinates.metric.zScale)) :
    spatialPreparations F B.coordinates.metric.coordinates
      B.coordinates.metric.yScale B.coordinates.metric.zScale = {p | sqnorm p ≤ B.radius ^ 2} := by
  rw [← hclosed.closure_eq]
  exact B.closure_eq_ball

end IDT.QMClosure.FiniteGateBallClosure

namespace IDT.QMClosure.FiniteGateFrameDimension.Frame

open IDT.QMClosure.FiniteGateBallClosure
open IDT.QMClosure.FiniteGatePreparationClosure

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- One actual preparation-preserving average suffices for a constructed
positive-radius Euclidean ball as mathematical spatial preparation closure. -/
theorem exists_ball_closure (F : Frame V)
    (hActual : (∀ v ∈ F.preparations, F.Ex v ∈ F.preparations) ∨
      (∀ v ∈ F.preparations, F.Ey v ∈ F.preparations) ∨
      (∀ v ∈ F.preparations, F.Ez v ∈ F.preparations)) :
    Nonempty (BallClosureData F) := by
  obtain ⟨D⟩ := F.exists_cubic_coordinates
  obtain ⟨R, hR, hbound, hmax⟩ := preparationClosure_attained_positive_radius
    F D.metric.coordinates D.metric.yScale D.metric.zScale
  refine ⟨{ coordinates := D, radius := R, radius_pos := hR, closure_eq_ball := ?_ }⟩
  exact eq_ball_of_product_radial_one_axis_projection hR.le
    (preparationClosure_radial D) hmax hbound (preparation_closure_projection D hActual)

end IDT.QMClosure.FiniteGateFrameDimension.Frame
