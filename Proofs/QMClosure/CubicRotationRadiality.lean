import Proofs.QMClosure.CubicRotationCircleDensity
import Proofs.QMClosure.TwoCircleRadialBall

/-!
# Radiality of closed sets preserved by the two cubic coordinate rotations

An explicit orientation-preserving orthonormal frame transports the two circles
established by finite-word density to the concrete sphere-transitivity theorem.
The conclusion concerns closed state sets in real coordinate space.
-/

noncomputable section

namespace IDT.QMClosure.CubicRotationRadiality

open Set

abbrev Vec3 := CubicRotationCircleDensity.Vec3

private def rootThree : ℝ := Real.sqrt 3
private def rootFifth : ℝ := Real.sqrt (1 / 5 : ℝ)
private def rootThirtieth : ℝ := Real.sqrt (1 / 30 : ℝ)
private def frameScale : ℝ := 5 * rootFifth * rootThirtieth

private theorem rootThree_sq : rootThree ^ 2 = 3 := by
  exact Real.sq_sqrt (by norm_num)

private theorem rootThree_cube : rootThree ^ 3 = 3 * rootThree := by
  calc
    rootThree ^ 3 = rootThree ^ 2 * rootThree := by ring
    _ = 3 * rootThree := by rw [rootThree_sq]

private theorem rootFifth_sq : rootFifth ^ 2 = 1 / 5 := by
  exact Real.sq_sqrt (by norm_num)

private theorem rootFifth_cube : rootFifth ^ 3 = rootFifth / 5 := by
  calc
    rootFifth ^ 3 = rootFifth ^ 2 * rootFifth := by ring
    _ = rootFifth / 5 := by rw [rootFifth_sq]; ring

private theorem rootThirtieth_sq : rootThirtieth ^ 2 = 1 / 30 := by
  exact Real.sq_sqrt (by norm_num)

private theorem rootThirtieth_cube : rootThirtieth ^ 3 = rootThirtieth / 30 := by
  calc
    rootThirtieth ^ 3 = rootThirtieth ^ 2 * rootThirtieth := by ring
    _ = rootThirtieth / 30 := by rw [rootThirtieth_sq]; ring

private theorem axisN_coordinates :
    CubicRotationCircleDensity.axisN = (rootFifth, rootThree * rootFifth, rootFifth) := rfl

private theorem axisN'_coordinates :
    CubicRotationCircleDensity.axisN' = (-2 * rootFifth, 0, rootFifth) := rfl

/-- The standard squared Euclidean norm on product coordinates. -/
def squaredNorm (p : Vec3) : ℝ := p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2

/-- The explicit orthonormal frame aligns the first circle with the third axis. -/
def toFrame (p : Vec3) : TwoCircleSphere.Vec3 :=
  ⟨rootThirtieth / 2 * (-9 * p.1 + rootThree * p.2.1 + 6 * p.2.2),
   frameScale / 2 * (rootThree * p.1 - 3 * p.2.1 + 2 * rootThree * p.2.2),
   rootFifth * (p.1 + rootThree * p.2.1 + p.2.2)⟩

/-- The transpose frame is the inverse map. -/
def fromFrame (p : TwoCircleSphere.Vec3) : Vec3 :=
  ⟨-9 * rootThirtieth / 2 * p.x + rootThree * frameScale / 2 * p.y + rootFifth * p.z,
   rootThree * rootThirtieth / 2 * p.x - 3 * frameScale / 2 * p.y +
      rootThree * rootFifth * p.z,
   3 * rootThirtieth * p.x + rootThree * frameScale * p.y + rootFifth * p.z⟩

theorem fromFrame_toFrame (p : Vec3) : fromFrame (toFrame p) = p := by
  rcases p with ⟨x, y, z⟩
  ext <;> dsimp [fromFrame, toFrame, frameScale] <;> ring_nf <;>
    simp only [rootThree_sq, rootFifth_sq, rootThirtieth_sq] <;> ring

theorem toFrame_fromFrame (p : TwoCircleSphere.Vec3) : toFrame (fromFrame p) = p := by
  rcases p with ⟨x, y, z⟩
  ext <;> dsimp [fromFrame, toFrame, frameScale] <;> ring_nf <;>
    simp only [rootThree_sq, rootFifth_sq, rootThirtieth_sq] <;> ring

theorem toFrame_injective : Function.Injective toFrame := by
  intro p q hpq
  have h := congrArg fromFrame hpq
  simpa only [fromFrame_toFrame] using h

theorem toFrame_squaredNorm (p : Vec3) : TwoCircleSphere.sqnorm (toFrame p) = squaredNorm p := by
  rcases p with ⟨x, y, z⟩
  dsimp [TwoCircleSphere.sqnorm, squaredNorm, toFrame, frameScale]
  ring_nf
  simp only [rootThree_sq, rootFifth_sq, rootThirtieth_sq]
  ring

theorem fromFrame_squaredNorm (p : TwoCircleSphere.Vec3) :
    squaredNorm (fromFrame p) = TwoCircleSphere.sqnorm p := by
  rw [← toFrame_squaredNorm, toFrame_fromFrame]

/-- The second axis has a positive transverse component in this frame. -/
def tiltS : ℝ := 12 * rootThirtieth * rootFifth

def tiltC : ℝ := -1 / 5

theorem tiltS_pos : 0 < tiltS := by
  unfold tiltS rootThirtieth rootFifth
  positivity

theorem tilt_axis_unit : tiltS ^ 2 + tiltC ^ 2 = 1 := by
  dsimp [tiltS, tiltC]
  ring_nf
  simp only [rootThirtieth_sq, rootFifth_sq]
  norm_num

theorem toFrame_axisN : toFrame CubicRotationCircleDensity.axisN = ⟨0, 0, 1⟩ := by
  rw [axisN_coordinates]
  ext <;> dsimp [toFrame, frameScale] <;> ring_nf <;>
    simp only [rootThree_sq, rootFifth_sq] <;> ring

theorem toFrame_axisN' : toFrame CubicRotationCircleDensity.axisN' = ⟨tiltS, 0, tiltC⟩ := by
  rw [axisN'_coordinates]
  ext <;> dsimp [toFrame, frameScale, tiltS, tiltC] <;> ring_nf
  all_goals simp only [rootFifth_sq]; ring

/-- The entire first Rodrigues circle becomes the standard third-axis circle. -/
theorem first_circle_intertwiner (k l : ℝ) (p : Vec3) :
    toFrame (CubicRotationCircleDensity.rodrigues CubicRotationCircleDensity.axisN k l p) = TwoCircleSphere.rotZ k l (toFrame p) := by
  rw [axisN_coordinates]
  rcases p with ⟨x, y, z⟩
  ext <;> dsimp [toFrame, frameScale, CubicRotationCircleDensity.rodrigues, CubicRotationCircleDensity.dot, TwoCircleSphere.rotZ] <;>
    ring_nf <;>
    simp only [rootThree_sq, rootThree_cube, rootFifth_sq, rootFifth_cube] <;> ring

/-- The entire conjugated circle becomes the explicitly tilted circle. -/
theorem second_circle_intertwiner (k l : ℝ) (p : Vec3) :
    toFrame (CubicRotationCircleDensity.rodrigues CubicRotationCircleDensity.axisN' k l p) =
      TwoCircleSphere.rotTilt tiltS tiltC k l (toFrame p) := by
  rw [axisN'_coordinates]
  rcases p with ⟨x, y, z⟩
  ext <;>
    dsimp [toFrame, frameScale, CubicRotationCircleDensity.rodrigues, CubicRotationCircleDensity.dot, TwoCircleSphere.rotTilt,
      tiltS, tiltC] <;>
    ring_nf <;>
    simp only [rootFifth_sq, rootFifth_cube, rootThirtieth_sq, rootThirtieth_cube] <;> ring

/-- The two density circles give the exact invariance premises used by transitivity. -/
theorem full_circle_invariant_frame {C : Set Vec3}
    (hfirst : CubicRotationCircleDensity.FullCircleInvariant C CubicRotationCircleDensity.axisN)
    (hsecond : CubicRotationCircleDensity.FullCircleInvariant C CubicRotationCircleDensity.axisN') :
    TwoCircleSphere.FullCircleInvariant (toFrame '' C) tiltS tiltC := by
  constructor
  · rintro k l hcircle _ ⟨p, hp, rfl⟩
    refine ⟨CubicRotationCircleDensity.rodrigues CubicRotationCircleDensity.axisN k l p, hfirst k l hcircle hp, ?_⟩
    exact first_circle_intertwiner k l p
  · rintro k l hcircle _ ⟨p, hp, rfl⟩
    refine ⟨CubicRotationCircleDensity.rodrigues CubicRotationCircleDensity.axisN' k l p, hsecond k l hcircle hp, ?_⟩
    exact second_circle_intertwiner k l p

/-- Closed preservation by the two actual finite gates forces standard radiality. -/
theorem closed_cubic_invariant_radial {C : Set Vec3} (hclosed : IsClosed C)
    (haz : MapsTo CubicRotationCircleDensity.az C C) (hax : MapsTo CubicRotationCircleDensity.ax C C) :
    ∀ p ∈ C, ∀ q, squaredNorm q = squaredNorm p → q ∈ C := by
  obtain ⟨hfirst, hsecond⟩ :=
    CubicRotationCircleDensity.closed_cubic_invariant_two_circles hclosed haz hax
  have hframe := full_circle_invariant_frame hfirst hsecond
  have hradial := TwoCircleSphere.radial_of_full_circle_invariance tiltS_pos tilt_axis_unit hframe
  intro p hp q hnorm
  have hframeNorm : TwoCircleSphere.sqnorm (toFrame q) = TwoCircleSphere.sqnorm (toFrame p) := by
    simpa only [toFrame_squaredNorm] using hnorm
  have hqframe := hradial (toFrame p) ⟨p, hp, rfl⟩ (toFrame q) hframeNorm
  obtain ⟨q', hq', hq'eq⟩ := hqframe
  have hq'q : q' = q := toFrame_injective hq'eq
  simpa only [hq'q] using hq'

end IDT.QMClosure.CubicRotationRadiality
