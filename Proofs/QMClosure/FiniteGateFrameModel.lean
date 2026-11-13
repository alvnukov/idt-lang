import Proofs.QMClosure.FiniteGateFrameDimension
import Mathlib.Data.Real.Sqrt

/-!
# An explicit real-ball model of the finite gate frame

This construction supplies real coordinates and the closed unit ball as model
inputs. It verifies consistency and nonvacuity of the conditional frame
premises. The construction derives no physical state geometry.
-/

namespace IDT.QMClosure.FiniteGateFrameModel

open Module FiniteGateFrameDimension

noncomputable section

abbrev V := Fin 4 → ℝ

def coord (t x y z : ℝ) : V := ![t, x, y, z]

@[simp] theorem coord_zero (t x y z : ℝ) : coord t x y z 0 = t := rfl
@[simp] theorem coord_one (t x y z : ℝ) : coord t x y z 1 = x := rfl
@[simp] theorem coord_two (t x y z : ℝ) : coord t x y z 2 = y := rfl
@[simp] theorem coord_three (t x y z : ℝ) : coord t x y z 3 = z := rfl

def preparations : Set V :=
  {v | v 0 = 1 ∧ (v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2 ≤ 1}

def center : V := coord 1 0 0 0
def xPointer (a : ℝ) : V := coord 1 a 0 0
def yPointer (a : ℝ) : V := coord 1 0 a 0
def zPointer (a : ℝ) : V := coord 1 0 0 a

@[simp] theorem center_mem : center ∈ preparations := by
  norm_num [preparations, center]

@[simp] theorem xPointer_mem (a : ℝ) (h : a ^ 2 ≤ 1) :
    xPointer a ∈ preparations := by
  simpa [preparations, xPointer] using h

@[simp] theorem yPointer_mem (a : ℝ) (h : a ^ 2 ≤ 1) :
    yPointer a ∈ preparations := by
  simpa [preparations, yPointer] using h

@[simp] theorem zPointer_mem (a : ℝ) (h : a ^ 2 ≤ 1) :
    zPointer a ∈ preparations := by
  simpa [preparations, zPointer] using h

def normalization : V →ₗ[ℝ] ℝ where
  toFun v := v 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def Jx : V →ₗ[ℝ] V where
  toFun v := coord (v 0) (v 1) (-v 2) (-v 3)
  map_add' v w := by
    ext i
    fin_cases i <;> simp  <;> ring
  map_smul' c v := by
    ext i
    fin_cases i <;> simp

def Jz : V →ₗ[ℝ] V where
  toFun v := coord (v 0) (-v 1) (-v 2) (v 3)
  map_add' v w := by
    ext i
    fin_cases i <;> simp  <;> ring
  map_smul' c v := by
    ext i
    fin_cases i <;> simp

def H : V →ₗ[ℝ] V where
  toFun v := coord (v 0) (v 3) (v 2) (v 1)
  map_add' v w := by
    ext i
    fin_cases i <;> simp
  map_smul' c v := by
    ext i
    fin_cases i <;> simp

def T : V →ₗ[ℝ] V where
  toFun v := coord (v 0)
    (-(v 1) / 2 - Real.sqrt 3 * v 2 / 2)
    (Real.sqrt 3 * v 1 / 2 - v 2 / 2) (v 3)
  map_add' v w := by
    ext i
    fin_cases i <;> simp  <;> ring
  map_smul' c v := by
    ext i
    fin_cases i <;> simp  <;> ring

theorem sqrt_three_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
  Real.sq_sqrt (by norm_num)

theorem sqrt_three_pos : 0 < Real.sqrt (3 : ℝ) :=
  Real.sqrt_pos.2 (by norm_num)

theorem sqrt_three_cube : (Real.sqrt (3 : ℝ)) ^ 3 = 3 * Real.sqrt 3 := by
  rw [pow_succ, sqrt_three_sq]

theorem coordinate_bounds {v : V} (hv : v ∈ preparations) :
    (-1 ≤ v 1 ∧ v 1 ≤ 1) ∧ (-1 ≤ v 2 ∧ v 2 ≤ 1) ∧
      (-1 ≤ v 3 ∧ v 3 ≤ 1) := by
  have hs := hv.2
  have h1 := sq_nonneg (v 1)
  have h2 := sq_nonneg (v 2)
  have h3 := sq_nonneg (v 3)
  constructor
  · constructor <;> nlinarith [sq_nonneg (v 1 - 1), sq_nonneg (v 1 + 1)]
  constructor
  · constructor <;> nlinarith [sq_nonneg (v 2 - 1), sq_nonneg (v 2 + 1)]
  · constructor <;> nlinarith [sq_nonneg (v 3 - 1), sq_nonneg (v 3 + 1)]

theorem spanning : Submodule.span ℝ preparations = ⊤ := by
  apply top_unique
  intro v _
  let P := Submodule.span ℝ preparations
  have hc : center ∈ P := Submodule.subset_span center_mem
  have hx : xPointer 1 ∈ P := Submodule.subset_span (xPointer_mem 1 (by norm_num))
  have hy : yPointer 1 ∈ P := Submodule.subset_span (yPointer_mem 1 (by norm_num))
  have hz : zPointer 1 ∈ P := Submodule.subset_span (zPointer_mem 1 (by norm_num))
  have heq : v = v 0 • center + v 1 • (xPointer 1 - center) +
      v 2 • (yPointer 1 - center) + v 3 • (zPointer 1 - center) := by
    ext i
    fin_cases i <;> simp [center, xPointer, yPointer, zPointer]
  rw [heq]
  exact P.add_mem
    (P.add_mem (P.add_mem (P.smul_mem _ hc) (P.smul_mem _ (P.sub_mem hx hc)))
      (P.smul_mem _ (P.sub_mem hy hc))) (P.smul_mem _ (P.sub_mem hz hc))

theorem Jx_involutive (v : V) : Jx (Jx v) = v := by
  ext i
  fin_cases i <;> simp [Jx]

theorem Jz_involutive (v : V) : Jz (Jz v) = v := by
  ext i
  fin_cases i <;> simp [Jz]

theorem commute (v : V) : Jz (Jx v) = Jx (Jz v) := by
  ext i
  fin_cases i <;> simp [Jx, Jz]

theorem H_involutive (v : V) : H (H v) = v := by
  ext i
  fin_cases i <;> simp [H]

theorem H_conjugates (v : V) : H (Jz (H v)) = Jx v := by
  ext i
  fin_cases i <;> simp [H, Jx, Jz]

theorem T_cube (v : V) : T (T (T v)) = v := by
  ext i
  fin_cases i <;> simp [T] <;>
    ring_nf <;> simp [sqrt_three_cube] <;> ring

theorem T_commutes (v : V) : Jz (T v) = T (Jz v) := by
  ext i
  fin_cases i <;> simp [T, Jz] <;> ring

theorem T_nontrivial : T ≠ LinearMap.id := by
  intro h
  have hh := congrArg (fun A : V →ₗ[ℝ] V => A (xPointer 1) 1) h
  norm_num [T, xPointer] at hh

theorem rotation_radius (v : V) :
    (T v 1) ^ 2 + (T v 2) ^ 2 + (T v 3) ^ 2 =
      (v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2 := by
  simp [T]
  ring_nf
  simp
  ring

theorem Jx_available (v : V) (hv : v ∈ preparations) : Jx v ∈ preparations := by
  rcases hv with ⟨hn, hs⟩
  constructor
  · simpa [Jx] using hn
  · simpa [Jx] using hs

theorem Jz_available (v : V) (hv : v ∈ preparations) : Jz v ∈ preparations := by
  rcases hv with ⟨hn, hs⟩
  constructor
  · simpa [Jz] using hn
  · simpa [Jz] using hs

theorem H_available (v : V) (hv : v ∈ preparations) : H v ∈ preparations := by
  rcases hv with ⟨hn, hs⟩
  constructor
  · simpa [H] using hn
  · simp [H]
    nlinarith

theorem T_available (v : V) (hv : v ∈ preparations) : T v ∈ preparations := by
  constructor
  · simpa [T] using hv.1
  · rw [rotation_radius]
    exact hv.2

theorem average_x_apply (v : V) :
    average Jx v = coord (v 0) (v 1) 0 0 := by
  ext i
  fin_cases i <;> simp [average, Jx] <;> ring

theorem average_y_apply (v : V) :
    average (Jx.comp Jz) v = coord (v 0) 0 (v 2) 0 := by
  ext i
  fin_cases i <;> simp [average, Jx, Jz] <;> ring

theorem average_z_apply (v : V) :
    average Jz v = coord (v 0) 0 0 (v 3) := by
  ext i
  fin_cases i <;> simp [average, Jz] <;> ring

theorem binary_x : BinarySegment preparations (average Jx) := by
  refine ⟨xPointer (-1), xPointer_mem _ (by norm_num),
    xPointer 1, xPointer_mem _ (by norm_num), ?_⟩
  intro v hv
  have hb := (coordinate_bounds hv).1
  refine ⟨(1 + v 1) / 2, ⟨by linarith, by linarith⟩, ?_⟩
  rw [average_x_apply]
  ext i
  fin_cases i <;> simp [xPointer, hv.1]
  ring

theorem binary_y : BinarySegment preparations (average (Jx.comp Jz)) := by
  refine ⟨yPointer (-1), yPointer_mem _ (by norm_num),
    yPointer 1, yPointer_mem _ (by norm_num), ?_⟩
  intro v hv
  have hb := (coordinate_bounds hv).2.1
  refine ⟨(1 + v 2) / 2, ⟨by linarith, by linarith⟩, ?_⟩
  rw [average_y_apply]
  ext i
  fin_cases i <;> simp [yPointer, hv.1]
  ring

theorem binary_z : BinarySegment preparations (average Jz) := by
  refine ⟨zPointer (-1), zPointer_mem _ (by norm_num),
    zPointer 1, zPointer_mem _ (by norm_num), ?_⟩
  intro v hv
  have hb := (coordinate_bounds hv).2.2
  refine ⟨(1 + v 3) / 2, ⟨by linarith, by linarith⟩, ?_⟩
  rw [average_z_apply]
  ext i
  fin_cases i <;> simp [zPointer, hv.1]
  ring

/-- All three averages preserve the supplied preparation ball. These are
extra model properties beyond the conditional frame's segment premises. -/
theorem average_x_available (v : V) (hv : v ∈ preparations) :
    average Jx v ∈ preparations := by
  rw [average_x_apply]
  constructor
  · simpa  using hv.1
  · have hsquare : (v 1) ^ 2 ≤ 1 := by
      nlinarith [hv.2, sq_nonneg (v 2), sq_nonneg (v 3)]
    simpa  using hsquare

theorem average_y_available (v : V) (hv : v ∈ preparations) :
    average (Jx.comp Jz) v ∈ preparations := by
  rw [average_y_apply]
  constructor
  · simpa  using hv.1
  · have hsquare : (v 2) ^ 2 ≤ 1 := by
      nlinarith [hv.2, sq_nonneg (v 1), sq_nonneg (v 3)]
    simpa  using hsquare

theorem average_z_available (v : V) (hv : v ∈ preparations) :
    average Jz v ∈ preparations := by
  rw [average_z_apply]
  constructor
  · simpa  using hv.1
  · have hsquare : (v 3) ^ 2 ≤ 1 := by
      nlinarith [hv.2, sq_nonneg (v 1), sq_nonneg (v 2)]
    simpa  using hsquare

/-- The real coordinates and ball are explicit supplied model structure. -/
def model : Frame V where
  preparations := preparations
  nonempty := ⟨center, center_mem⟩
  normalization := normalization
  normalized := fun _ hv => hv.1
  spanning := spanning
  Jx := Jx
  Jz := Jz
  H := H
  T := T
  Jx_involutive := Jx_involutive
  Jz_involutive := Jz_involutive
  commute := commute
  Jx_available := Jx_available
  Jz_available := Jz_available
  H_available := H_available
  T_available := T_available
  binary_x := binary_x
  binary_y := binary_y
  binary_z := binary_z
  H_involutive := H_involutive
  H_conjugates := H_conjugates
  T_cube := T_cube
  T_commutes := T_commutes
  T_nontrivial := T_nontrivial

/-- The abstract dimension theorem applies to the constructed inhabitant. -/
theorem model_dimension_forced :
    FiniteDimensional ℝ V ∧ finrank ℝ V = 4 ∧
      finrank ℝ (LinearMap.ker model.normalization) = 3 ∧
      finrank ℝ (LinearMap.range model.Ex) = 2 ∧
      finrank ℝ (LinearMap.range model.Ey) = 2 ∧
      finrank ℝ (LinearMap.range model.Ez) = 2 ∧
      finrank ℝ (LinearMap.range model.R) = 1 ∧
      finrank ℝ (LinearMap.range model.Qx) = 1 ∧
      finrank ℝ (LinearMap.range model.Qy) = 1 ∧
      finrank ℝ (LinearMap.range model.Qz) = 1 :=
  model.dimension_forced

/-- A second explicit preparation set, with the same gate algebra. -/
def spherePreparations : Set V :=
  {v | v 0 = 1 ∧ (v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2 = 1}

theorem sphere_subset_ball : spherePreparations ⊆ preparations := by
  intro v hv
  exact ⟨hv.1, hv.2.le⟩

@[simp] theorem xPointer_sphere (a : ℝ) (h : a ^ 2 = 1) :
    xPointer a ∈ spherePreparations := by
  simpa [spherePreparations, xPointer] using h

@[simp] theorem yPointer_sphere (a : ℝ) (h : a ^ 2 = 1) :
    yPointer a ∈ spherePreparations := by
  simpa [spherePreparations, yPointer] using h

@[simp] theorem zPointer_sphere (a : ℝ) (h : a ^ 2 = 1) :
    zPointer a ∈ spherePreparations := by
  simpa [spherePreparations, zPointer] using h

theorem sphere_spanning : Submodule.span ℝ spherePreparations = ⊤ := by
  apply top_unique
  intro v _
  let P := Submodule.span ℝ spherePreparations
  have hx : xPointer 1 ∈ P := Submodule.subset_span (xPointer_sphere 1 (by norm_num))
  have hxm : xPointer (-1) ∈ P :=
    Submodule.subset_span (xPointer_sphere (-1) (by norm_num))
  have hy : yPointer 1 ∈ P := Submodule.subset_span (yPointer_sphere 1 (by norm_num))
  have hz : zPointer 1 ∈ P := Submodule.subset_span (zPointer_sphere 1 (by norm_num))
  have hc : center ∈ P := by
    have heq : center = (1 / 2 : ℝ) • (xPointer 1 + xPointer (-1)) := by
      ext i
      fin_cases i <;> simp [center, xPointer]
      norm_num
    rw [heq]
    exact P.smul_mem _ (P.add_mem hx hxm)
  have heq : v = v 0 • center + v 1 • (xPointer 1 - center) +
      v 2 • (yPointer 1 - center) + v 3 • (zPointer 1 - center) := by
    ext i
    fin_cases i <;> simp [center, xPointer, yPointer, zPointer]
  rw [heq]
  exact P.add_mem
    (P.add_mem (P.add_mem (P.smul_mem _ hc) (P.smul_mem _ (P.sub_mem hx hc)))
      (P.smul_mem _ (P.sub_mem hy hc))) (P.smul_mem _ (P.sub_mem hz hc))

theorem sphere_Jx_available (v : V) (hv : v ∈ spherePreparations) :
    Jx v ∈ spherePreparations := by
  constructor
  · simpa [Jx] using hv.1
  · simpa [Jx] using hv.2

theorem sphere_Jz_available (v : V) (hv : v ∈ spherePreparations) :
    Jz v ∈ spherePreparations := by
  constructor
  · simpa [Jz] using hv.1
  · simpa [Jz] using hv.2

theorem sphere_H_available (v : V) (hv : v ∈ spherePreparations) :
    H v ∈ spherePreparations := by
  constructor
  · simpa [H] using hv.1
  · simp [H]
    nlinarith [hv.2]

theorem sphere_T_available (v : V) (hv : v ∈ spherePreparations) :
    T v ∈ spherePreparations := by
  constructor
  · simpa [T] using hv.1
  · rw [rotation_radius]
    exact hv.2

theorem sphere_binary_x : BinarySegment spherePreparations (average Jx) := by
  refine ⟨xPointer (-1), xPointer_sphere _ (by norm_num),
    xPointer 1, xPointer_sphere _ (by norm_num), ?_⟩
  intro v hv
  have hb := (coordinate_bounds (sphere_subset_ball hv)).1
  refine ⟨(1 + v 1) / 2, ⟨by linarith, by linarith⟩, ?_⟩
  rw [average_x_apply]
  ext i
  fin_cases i <;> simp [xPointer, hv.1]
  ring

theorem sphere_binary_y : BinarySegment spherePreparations (average (Jx.comp Jz)) := by
  refine ⟨yPointer (-1), yPointer_sphere _ (by norm_num),
    yPointer 1, yPointer_sphere _ (by norm_num), ?_⟩
  intro v hv
  have hb := (coordinate_bounds (sphere_subset_ball hv)).2.1
  refine ⟨(1 + v 2) / 2, ⟨by linarith, by linarith⟩, ?_⟩
  rw [average_y_apply]
  ext i
  fin_cases i <;> simp [yPointer, hv.1]
  ring

theorem sphere_binary_z : BinarySegment spherePreparations (average Jz) := by
  refine ⟨zPointer (-1), zPointer_sphere _ (by norm_num),
    zPointer 1, zPointer_sphere _ (by norm_num), ?_⟩
  intro v hv
  have hb := (coordinate_bounds (sphere_subset_ball hv)).2.2
  refine ⟨(1 + v 3) / 2, ⟨by linarith, by linarith⟩, ?_⟩
  rw [average_z_apply]
  ext i
  fin_cases i <;> simp [zPointer, hv.1]
  ring

/-- This frame satisfies the same conditional dimension assumptions. -/
def sphereModel : Frame V where
  preparations := spherePreparations
  nonempty := ⟨xPointer 1, xPointer_sphere 1 (by norm_num)⟩
  normalization := normalization
  normalized := fun _ hv => hv.1
  spanning := sphere_spanning
  Jx := Jx
  Jz := Jz
  H := H
  T := T
  Jx_involutive := Jx_involutive
  Jz_involutive := Jz_involutive
  commute := commute
  Jx_available := sphere_Jx_available
  Jz_available := sphere_Jz_available
  H_available := sphere_H_available
  T_available := sphere_T_available
  binary_x := sphere_binary_x
  binary_y := sphere_binary_y
  binary_z := sphere_binary_z
  H_involutive := H_involutive
  H_conjugates := H_conjugates
  T_cube := T_cube
  T_commutes := T_commutes
  T_nontrivial := T_nontrivial

theorem center_not_sphere : center ∉ spherePreparations := by
  norm_num [center, spherePreparations]

theorem sphere_Ez_xPointer : sphereModel.Ez (xPointer 1) = center := by
  change average Jz (xPointer 1) = center
  rw [average_z_apply]
  ext i
  fin_cases i <;> norm_num [xPointer, center]

/-- The frame assumptions permit an average output outside the preparation set.
The witness applies to the stated frame, which has no average-availability field. -/
theorem sphere_Ez_unavailable :
    ∃ v ∈ sphereModel.preparations, sphereModel.Ez v ∉ sphereModel.preparations := by
  refine ⟨xPointer 1, xPointer_sphere 1 (by norm_num), ?_⟩
  rw [sphere_Ez_xPointer]
  exact center_not_sphere

/-- The dimension assumptions alone do not force the supplied preparations to
be the full ball in these explicit coordinates. -/
theorem sphere_preparations_ne_ball : sphereModel.preparations ≠ preparations := by
  intro h
  have hc : center ∈ sphereModel.preparations := by rw [h]; exact center_mem
  exact center_not_sphere hc

end

end IDT.QMClosure.FiniteGateFrameModel
