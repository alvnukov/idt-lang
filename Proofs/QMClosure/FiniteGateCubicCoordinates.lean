import Proofs.QMClosure.FiniteGateInvariantMetric
import Proofs.QMClosure.FiniteGatePreparationClosure
import Proofs.QMClosure.CubicRotationCircleDensity

/-!
# Exact cubic gate coordinates constructed from a frame

An oriented rescaling of the derived spatial quadratic form transports the
actual T gate and a finite H/T word to the exact positive cubic rotations used
by the circle-density module. The rescaling retains the sign of the H exchange
coefficient and chooses its transverse orientation from the derived T block.
The binary averages become the three coordinate projections. Their action
equations supply no additional preparation-availability premise.

These are exact finite gate compatibilities and preparation-image invariances.
They establish no physical availability of limit gates or equality with a ball.
-/

noncomputable section

namespace IDT.QMClosure.FiniteGateCubicCoordinates

open CubicRotationCircleDensity

/-- Public scalar formula for the density module's exact third-axis gate. -/
theorem az_explicit (p : Vec3) : az p =
    (-p.1 / 2 - Real.sqrt 3 / 2 * p.2.1,
      Real.sqrt 3 / 2 * p.1 - p.2.1 / 2, p.2.2) := rfl

/-- Public scalar formula for the density module's exact first-axis gate. -/
theorem ax_explicit (p : Vec3) : ax p =
    (p.1, -p.2.1 / 2 - Real.sqrt 3 / 2 * p.2.2,
      Real.sqrt 3 / 2 * p.2.1 - p.2.2 / 2) := rfl

def exchange (beta : ℝ) (p : Vec3) : Vec3 := (p.2.2, beta * p.2.1, p.1)

theorem negative_exchange_word (p : Vec3) :
    exchange (-1) (az (exchange (-1) p)) = ax p := by
  rcases p with ⟨x, y, z⟩
  simp only [az_explicit, ax_explicit, exchange]
  ext <;> dsimp <;> ring

theorem positive_exchange_word (p : Vec3) :
    exchange 1 (az (az (exchange 1 p))) = ax p := by
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rcases p with ⟨x, y, z⟩
  simp only [az_explicit, ax_explicit, exchange]
  ext <;> dsimp <;> ring_nf <;> simp only [hsqrt] <;> ring

end IDT.QMClosure.FiniteGateCubicCoordinates

namespace IDT.QMClosure.FiniteGateInvariantMetric.InvariantMetricData

open FiniteGateFrameDimension FiniteGateFrameCoordinates FiniteGatePreparationClosure
open CubicRotationCircleDensity FiniteGateCubicCoordinates

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {F : Frame V} (M : InvariantMetricData F)

def yScale : ℝ := Real.sqrt 3 / (2 * M.coordinates.c)
def zScale : ℝ := M.coordinates.α

theorem c_ne_zero : M.coordinates.c ≠ 0 := by
  intro hc
  have h := M.bc_eq
  rw [hc, mul_zero] at h
  norm_num at h

theorem yScale_ne_zero : M.yScale ≠ 0 := by
  unfold yScale
  exact div_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))
    (mul_ne_zero (by norm_num) M.c_ne_zero)

theorem zScale_ne_zero : M.zScale ≠ 0 := M.coordinates.alpha_ne_zero

theorem yScale_mul_c : M.yScale * M.coordinates.c = Real.sqrt 3 / 2 := by
  unfold yScale
  field_simp [M.c_ne_zero]

theorem b_coefficient : M.coordinates.b = -(Real.sqrt 3 / 2) * M.yScale := by
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hbc := M.bc_eq
  unfold yScale
  field_simp [M.c_ne_zero]
  nlinarith

theorem b_div_yScale : M.coordinates.b / M.yScale = -(Real.sqrt 3 / 2) :=
  (div_eq_iff M.yScale_ne_zero).mpr M.b_coefficient

theorem yScale_sq : M.yScale ^ 2 = AxisCoordinates.planeWeight M.coordinates := by
  change M.yScale ^ 2 = -M.coordinates.b / M.coordinates.c
  apply (eq_div_iff M.c_ne_zero).mpr
  have h := M.b_coefficient
  rw [← M.yScale_mul_c] at h
  nlinarith

def rescaledSpatial (v : V) : SpatialPoint := spatial M.coordinates M.yScale M.zScale v

theorem rescaledSpatial_sqnorm (v : V) :
    sqnorm (M.rescaledSpatial v) = AxisCoordinates.spatialQuadratic M.coordinates v := by
  simp only [sqnorm, rescaledSpatial, spatial, mul_pow, M.yScale_sq, zScale,
    AxisCoordinates.spatialQuadratic]

theorem rescaledSpatial_T (v : V) :
    M.rescaledSpatial (F.T v) = az (M.rescaledSpatial v) := by
  have hy (x y : ℝ) :
      M.yScale * (M.coordinates.c * x + M.coordinates.d * y) =
        Real.sqrt 3 / 2 * x - (M.yScale * y) / 2 := by
    rw [M.d_eq]
    calc
      M.yScale * (M.coordinates.c * x + (-1 / 2) * y) =
          (M.yScale * M.coordinates.c) * x - (M.yScale * y) / 2 := by ring
      _ = Real.sqrt 3 / 2 * x - (M.yScale * y) / 2 := by rw [M.yScale_mul_c]
  rw [az_explicit]
  change (M.coordinates.equiv (F.T v) 1, M.yScale * M.coordinates.equiv (F.T v) 2,
      M.zScale * M.coordinates.equiv (F.T v) 3) = _
  simp only [M.coordinates.T_action, quad_one, quad_two, quad_three]
  rw [hy, M.a_eq, M.b_coefficient]
  ext <;> dsimp [rescaledSpatial, spatial]
  all_goals ring

theorem rescaledSpatial_H (v : V) :
    M.rescaledSpatial (F.H v) = exchange M.coordinates.β (M.rescaledSpatial v) := by
  have hcancel (x : ℝ) : M.coordinates.α * (M.coordinates.α⁻¹ * x) = x := by
    rw [← mul_assoc, mul_inv_cancel₀ M.coordinates.alpha_ne_zero, one_mul]
  simp only [rescaledSpatial, spatial, exchange, M.coordinates.H_action,
    quad_one, quad_two, quad_three, zScale, hcancel]
  ext <;> dsimp
  all_goals ring

theorem beta_sign : M.coordinates.β = 1 ∨ M.coordinates.β = -1 := by
  have hfactor : (M.coordinates.β - 1) * (M.coordinates.β + 1) = 0 := by
    nlinarith [M.coordinates.beta_sq]
  rcases mul_eq_zero.mp hfactor with hp | hn
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- A finite actual word gives the positive first-axis cubic rotation in
either permitted H orientation. -/
def xWord : Module.End ℝ V :=
  if M.coordinates.β = -1 then F.H.comp (F.T.comp F.H)
  else F.H.comp (F.T.comp (F.T.comp F.H))

theorem xWord_available : ∀ v ∈ F.preparations, M.xWord v ∈ F.preparations := by
  unfold xWord
  split_ifs
  · intro v hv
    exact F.H_available _ (F.T_available _ (F.H_available v hv))
  · intro v hv
    exact F.H_available _ (F.T_available _ (F.T_available _ (F.H_available v hv)))

theorem rescaledSpatial_xWord (v : V) :
    M.rescaledSpatial (M.xWord v) = ax (M.rescaledSpatial v) := by
  unfold xWord
  split_ifs with hneg
  · simp only [LinearMap.comp_apply, M.rescaledSpatial_H, M.rescaledSpatial_T, hneg]
    exact negative_exchange_word (M.rescaledSpatial v)
  · have hpos : M.coordinates.β = 1 := M.beta_sign.resolve_right hneg
    simp only [LinearMap.comp_apply, M.rescaledSpatial_H, M.rescaledSpatial_T, hpos]
    exact positive_exchange_word (M.rescaledSpatial v)

theorem az_mapsTo_preparations :
    Set.MapsTo az (spatialPreparations F M.coordinates M.yScale M.zScale)
      (spatialPreparations F M.coordinates M.yScale M.zScale) := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨F.T v, F.T_available v hv, M.rescaledSpatial_T v⟩

theorem ax_mapsTo_preparations :
    Set.MapsTo ax (spatialPreparations F M.coordinates M.yScale M.zScale)
      (spatialPreparations F M.coordinates M.yScale M.zScale) := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨M.xWord v, M.xWord_available v hv, M.rescaledSpatial_xWord v⟩

theorem rescaledSpatial_Ex (v : V) :
    M.rescaledSpatial (F.Ex v) = ((M.rescaledSpatial v).1, 0, 0) := by
  simp [rescaledSpatial, spatial, M.coordinates.Ex_action, px]

theorem rescaledSpatial_Ey (v : V) :
    M.rescaledSpatial (F.Ey v) = (0, (M.rescaledSpatial v).2.1, 0) := by
  simp [rescaledSpatial, spatial, M.coordinates.Ey_action, py]

theorem rescaledSpatial_Ez (v : V) :
    M.rescaledSpatial (F.Ez v) = (0, 0, (M.rescaledSpatial v).2.2) := by
  simp [rescaledSpatial, spatial, M.coordinates.Ez_action, pz]

/-- Spatial coordinates are injective within any fixed normalization fibre. -/
theorem rescaledSpatial_injective_fibre {v w : V}
    (hu : F.normalization v = F.normalization w)
    (hspatial : M.rescaledSpatial v = M.rescaledSpatial w) : v = w := by
  have hx : M.coordinates.equiv v 1 = M.coordinates.equiv w 1 :=
    congrArg Prod.fst hspatial
  have hy : M.yScale * M.coordinates.equiv v 2 = M.yScale * M.coordinates.equiv w 2 :=
    congrArg (fun p : SpatialPoint => p.2.1) hspatial
  have hz : M.zScale * M.coordinates.equiv v 3 = M.zScale * M.coordinates.equiv w 3 :=
    congrArg (fun p : SpatialPoint => p.2.2) hspatial
  have hy' := mul_left_cancel₀ M.yScale_ne_zero hy
  have hz' := mul_left_cancel₀ M.zScale_ne_zero hz
  apply M.coordinates.equiv.injective
  ext i
  fin_cases i
  · change M.coordinates.equiv v 0 = M.coordinates.equiv w 0
    rw [M.coordinates.normalized, M.coordinates.normalized, hu]
  · exact hx
  · exact hy'
  · exact hz'

end IDT.QMClosure.FiniteGateInvariantMetric.InvariantMetricData

namespace IDT.QMClosure.FiniteGateCubicCoordinates

open FiniteGateFrameDimension FiniteGateFrameCoordinates FiniteGateInvariantMetric
open FiniteGatePreparationClosure CubicRotationCircleDensity

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The rescaling and finite-word implementation are constructed with the
derived metric. The image is exactly the preparation-closure module's image. -/
structure CubicCoordinateData (F : Frame V) where
  metric : InvariantMetricData F
  yScale_ne_zero : metric.yScale ≠ 0
  zScale_ne_zero : metric.zScale ≠ 0
  yScale_sq : metric.yScale ^ 2 = AxisCoordinates.planeWeight metric.coordinates
  sqnorm_eq : ∀ v, sqnorm (metric.rescaledSpatial v) =
    AxisCoordinates.spatialQuadratic metric.coordinates v
  T_compatible : ∀ v, metric.rescaledSpatial (F.T v) = az (metric.rescaledSpatial v)
  H_compatible : ∀ v, metric.rescaledSpatial (F.H v) =
    exchange metric.coordinates.β (metric.rescaledSpatial v)
  xWord_available : ∀ v ∈ F.preparations, metric.xWord v ∈ F.preparations
  xWord_compatible : ∀ v,
    metric.rescaledSpatial (metric.xWord v) = ax (metric.rescaledSpatial v)
  az_preserves : Set.MapsTo az
    (spatialPreparations F metric.coordinates metric.yScale metric.zScale)
    (spatialPreparations F metric.coordinates metric.yScale metric.zScale)
  ax_preserves : Set.MapsTo ax
    (spatialPreparations F metric.coordinates metric.yScale metric.zScale)
    (spatialPreparations F metric.coordinates metric.yScale metric.zScale)
  Ex_compatible : ∀ v,
    metric.rescaledSpatial (F.Ex v) = ((metric.rescaledSpatial v).1, 0, 0)
  Ey_compatible : ∀ v,
    metric.rescaledSpatial (F.Ey v) = (0, (metric.rescaledSpatial v).2.1, 0)
  Ez_compatible : ∀ v,
    metric.rescaledSpatial (F.Ez v) = (0, 0, (metric.rescaledSpatial v).2.2)
  injective_fibre : ∀ v w, F.normalization v = F.normalization w →
    metric.rescaledSpatial v = metric.rescaledSpatial w → v = w

end IDT.QMClosure.FiniteGateCubicCoordinates

namespace IDT.QMClosure.FiniteGateFrameDimension.Frame

open IDT.QMClosure.FiniteGateCubicCoordinates

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The original frame constructs matched Euclidean gate coordinates and two
actual positive cubic rotations on its spatial preparation image. -/
theorem exists_cubic_coordinates (F : Frame V) : Nonempty (CubicCoordinateData F) := by
  obtain ⟨M⟩ := F.exists_invariant_metric
  exact ⟨{
    metric := M
    yScale_ne_zero := M.yScale_ne_zero
    zScale_ne_zero := M.zScale_ne_zero
    yScale_sq := M.yScale_sq
    sqnorm_eq := M.rescaledSpatial_sqnorm
    T_compatible := M.rescaledSpatial_T
    H_compatible := M.rescaledSpatial_H
    xWord_available := M.xWord_available
    xWord_compatible := M.rescaledSpatial_xWord
    az_preserves := M.az_mapsTo_preparations
    ax_preserves := M.ax_mapsTo_preparations
    Ex_compatible := M.rescaledSpatial_Ex
    Ey_compatible := M.rescaledSpatial_Ey
    Ez_compatible := M.rescaledSpatial_Ez
    injective_fibre := fun v w => M.rescaledSpatial_injective_fibre }⟩

end IDT.QMClosure.FiniteGateFrameDimension.Frame
