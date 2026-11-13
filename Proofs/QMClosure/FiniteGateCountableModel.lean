import Proofs.QMClosure.FiniteGateFrameModel
import Proofs.QMClosure.FiniteGateBallClosure
import Mathlib.Analysis.Real.Cardinality

/-!
# A countable operational preparation model

Preparations are evaluations of finite words in seven supplied real-coordinate
operations, starting at six axis pointers. This gives actual availability of
all three binary averages and a countable exact preparation set. The previously
proved selector constructs its ball closure from these assumptions.
-/

namespace IDT.QMClosure.FiniteGateCountableModel

open Module FiniteGateFrameDimension FiniteGateFrameModel
open FiniteGateBallClosure

noncomputable section

abbrev Word := Fin 6 × List (Fin 7)

/-- The six supplied initial preparations. -/
def seed (j : Fin 6) : V :=
  if j = 0 then xPointer 1 else
  if j = 1 then xPointer (-1) else
  if j = 2 then yPointer 1 else
  if j = 3 then yPointer (-1) else
  if j = 4 then zPointer 1 else zPointer (-1)

/-- The finite operational alphabet contains four gates and three averages. -/
def operation (k : Fin 7) : V →ₗ[ℝ] V :=
  if k = 0 then Jx else
  if k = 1 then Jz else
  if k = 2 then H else
  if k = 3 then T else
  if k = 4 then average Jx else
  if k = 5 then average (Jx.comp Jz) else average Jz

/-- The head letter is the outermost operation. -/
def evaluateFrom (v : V) : List (Fin 7) → V
  | [] => v
  | k :: rest => operation k (evaluateFrom v rest)

def evaluate (w : Word) : V := evaluateFrom (seed w.1) w.2

def generatedPreparations : Set V := Set.range evaluate

theorem generated_countable : generatedPreparations.Countable :=
  Set.countable_range evaluate

theorem seed_in_ball (j : Fin 6) : seed j ∈ preparations := by
  fin_cases j <;> simp [seed]

theorem operation_preserves_ball (k : Fin 7) (v : V) (hv : v ∈ preparations) :
    operation k v ∈ preparations := by
  fin_cases k
  · exact Jx_available v hv
  · exact Jz_available v hv
  · exact H_available v hv
  · exact T_available v hv
  · exact average_x_available v hv
  · exact average_y_available v hv
  · exact average_z_available v hv

theorem evaluateFrom_in_ball (v : V) (hv : v ∈ preparations) (w : List (Fin 7)) :
    evaluateFrom v w ∈ preparations := by
  induction w with
  | nil => exact hv
  | cons k rest ih => exact operation_preserves_ball k _ ih

theorem generated_subset_ball : generatedPreparations ⊆ preparations := by
  rintro _ ⟨⟨j, w⟩, rfl⟩
  exact evaluateFrom_in_ball _ (seed_in_ball j) w

theorem seed_available (j : Fin 6) : seed j ∈ generatedPreparations :=
  ⟨(j, []), rfl⟩

/-- Prefixing a word witnesses availability of each alphabet operation. -/
theorem operation_available (k : Fin 7) (v : V) (hv : v ∈ generatedPreparations) :
    operation k v ∈ generatedPreparations := by
  obtain ⟨⟨j, w⟩, rfl⟩ := hv
  exact ⟨(j, k :: w), rfl⟩

@[simp] theorem x_plus_available : xPointer 1 ∈ generatedPreparations :=
  seed_available 0

@[simp] theorem x_minus_available : xPointer (-1) ∈ generatedPreparations :=
  seed_available 1

@[simp] theorem y_plus_available : yPointer 1 ∈ generatedPreparations :=
  seed_available 2

@[simp] theorem y_minus_available : yPointer (-1) ∈ generatedPreparations :=
  seed_available 3

@[simp] theorem z_plus_available : zPointer 1 ∈ generatedPreparations :=
  seed_available 4

@[simp] theorem z_minus_available : zPointer (-1) ∈ generatedPreparations :=
  seed_available 5

theorem generated_Jx_available (v : V) (hv : v ∈ generatedPreparations) :
    Jx v ∈ generatedPreparations := operation_available 0 v hv

theorem generated_Jz_available (v : V) (hv : v ∈ generatedPreparations) :
    Jz v ∈ generatedPreparations := operation_available 1 v hv

theorem generated_H_available (v : V) (hv : v ∈ generatedPreparations) :
    H v ∈ generatedPreparations := operation_available 2 v hv

theorem generated_T_available (v : V) (hv : v ∈ generatedPreparations) :
    T v ∈ generatedPreparations := operation_available 3 v hv

theorem generated_average_x_available (v : V) (hv : v ∈ generatedPreparations) :
    average Jx v ∈ generatedPreparations := operation_available 4 v hv

theorem generated_average_y_available (v : V) (hv : v ∈ generatedPreparations) :
    average (Jx.comp Jz) v ∈ generatedPreparations := operation_available 5 v hv

theorem generated_average_z_available (v : V) (hv : v ∈ generatedPreparations) :
    average Jz v ∈ generatedPreparations := operation_available 6 v hv

@[simp] theorem center_available : center ∈ generatedPreparations := by
  have h := generated_average_z_available (xPointer 1) x_plus_available
  simpa [average_z_apply, xPointer, center] using h

theorem generated_spanning : Submodule.span ℝ generatedPreparations = ⊤ := by
  apply top_unique
  intro v _
  let P := Submodule.span ℝ generatedPreparations
  have hc : center ∈ P := Submodule.subset_span center_available
  have hx : xPointer 1 ∈ P := Submodule.subset_span x_plus_available
  have hy : yPointer 1 ∈ P := Submodule.subset_span y_plus_available
  have hz : zPointer 1 ∈ P := Submodule.subset_span z_plus_available
  have heq : v = v 0 • center + v 1 • (xPointer 1 - center) +
      v 2 • (yPointer 1 - center) + v 3 • (zPointer 1 - center) := by
    ext i
    fin_cases i <;> simp [center, xPointer, yPointer, zPointer]
  rw [heq]
  exact P.add_mem
    (P.add_mem (P.add_mem (P.smul_mem _ hc) (P.smul_mem _ (P.sub_mem hx hc)))
      (P.smul_mem _ (P.sub_mem hy hc))) (P.smul_mem _ (P.sub_mem hz hc))

theorem generated_binary_x : BinarySegment generatedPreparations (average Jx) := by
  refine ⟨xPointer (-1), x_minus_available, xPointer 1, x_plus_available, ?_⟩
  intro v hv
  have hball := generated_subset_ball hv
  have hb := (coordinate_bounds hball).1
  refine ⟨(1 + v 1) / 2, ⟨by linarith, by linarith⟩, ?_⟩
  rw [average_x_apply]
  ext i
  fin_cases i <;> simp [xPointer, hball.1]
  ring

theorem generated_binary_y :
    BinarySegment generatedPreparations (average (Jx.comp Jz)) := by
  refine ⟨yPointer (-1), y_minus_available, yPointer 1, y_plus_available, ?_⟩
  intro v hv
  have hball := generated_subset_ball hv
  have hb := (coordinate_bounds hball).2.1
  refine ⟨(1 + v 2) / 2, ⟨by linarith, by linarith⟩, ?_⟩
  rw [average_y_apply]
  ext i
  fin_cases i <;> simp [yPointer, hball.1]
  ring

theorem generated_binary_z : BinarySegment generatedPreparations (average Jz) := by
  refine ⟨zPointer (-1), z_minus_available, zPointer 1, z_plus_available, ?_⟩
  intro v hv
  have hball := generated_subset_ball hv
  have hb := (coordinate_bounds hball).2.2
  refine ⟨(1 + v 3) / 2, ⟨by linarith, by linarith⟩, ?_⟩
  rw [average_z_apply]
  ext i
  fin_cases i <;> simp [zPointer, hball.1]
  ring

/-- A countable preparation frame with all seven operations actual. -/
def generatedFrame : Frame V where
  preparations := generatedPreparations
  nonempty := ⟨xPointer 1, x_plus_available⟩
  normalization := normalization
  normalized := fun _ hv => (generated_subset_ball hv).1
  spanning := generated_spanning
  Jx := Jx
  Jz := Jz
  H := H
  T := T
  Jx_involutive := Jx_involutive
  Jz_involutive := Jz_involutive
  commute := commute
  Jx_available := generated_Jx_available
  Jz_available := generated_Jz_available
  H_available := generated_H_available
  T_available := generated_T_available
  binary_x := generated_binary_x
  binary_y := generated_binary_y
  binary_z := generated_binary_z
  H_involutive := H_involutive
  H_conjugates := H_conjugates
  T_cube := T_cube
  T_commutes := T_commutes
  T_nontrivial := T_nontrivial

theorem generated_all_averages_actual :
    (∀ v ∈ generatedFrame.preparations, generatedFrame.Ex v ∈ generatedFrame.preparations) ∧
    (∀ v ∈ generatedFrame.preparations, generatedFrame.Ey v ∈ generatedFrame.preparations) ∧
    (∀ v ∈ generatedFrame.preparations, generatedFrame.Ez v ∈ generatedFrame.preparations) :=
  ⟨generated_average_x_available, generated_average_y_available, generated_average_z_available⟩

theorem xPointer_injective : Function.Injective xPointer := by
  intro a b h
  simpa [xPointer] using congrFun h 1

/-- The supplied full real ball contains an uncountable axis segment. -/
theorem ball_not_countable : ¬ preparations.Countable := by
  intro hc
  have hinterval : (Set.Icc (-1 : ℝ) 1).Countable := by
    apply (hc.preimage xPointer_injective).mono
    intro a ha
    apply xPointer_mem
    have hprod := mul_nonneg (sub_nonneg.mpr ha.2) (by linarith [ha.1] : 0 ≤ 1 + a)
    nlinarith
  have hnot : ¬ (Set.Icc (-1 : ℝ) 1).Countable := by norm_num
  exact hnot hinterval

theorem generated_preparations_ne_ball : generatedFrame.preparations ≠ preparations := by
  intro h
  apply ball_not_countable
  rw [← h]
  exact generated_countable

/-- The derived ball-closure theorem applies while exact preparations are countable. -/
theorem generated_has_ball_closure : Nonempty (BallClosureData generatedFrame) :=
  generatedFrame.exists_ball_closure (Or.inl generated_all_averages_actual.1)

/-- Exact preparations can remain a countable proper subset of the supplied
real ball while satisfying the frame and all three actual-average premises. -/
theorem exact_preparation_control :
    generatedFrame.preparations.Countable ∧
    (∀ v ∈ generatedFrame.preparations, generatedFrame.Ex v ∈ generatedFrame.preparations) ∧
    (∀ v ∈ generatedFrame.preparations, generatedFrame.Ey v ∈ generatedFrame.preparations) ∧
    (∀ v ∈ generatedFrame.preparations, generatedFrame.Ez v ∈ generatedFrame.preparations) ∧
    Nonempty (BallClosureData generatedFrame) ∧ generatedFrame.preparations ≠ preparations :=
  ⟨generated_countable, generated_all_averages_actual.1,
    generated_all_averages_actual.2.1, generated_all_averages_actual.2.2,
    generated_has_ball_closure, generated_preparations_ne_ball⟩

end

end IDT.QMClosure.FiniteGateCountableModel
