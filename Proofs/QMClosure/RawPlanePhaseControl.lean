import Proofs.QMClosure.RawPlanePhaseGeometry

/-!
# Actual plane-dependent phase operation

The explicit operation agrees with one fixed member of the phase family on
each ordinary complex two-plane. Its sparse readout identity is proved only
for triples in one such plane. This is a mathematical countercontrol.
-/

namespace IDT.QMClosure.RawPlanePhaseControl

noncomputable section

open RawPlanePhaseFamily RawPlanePhaseGeometry

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

def m (x y : Vec) : Vec := familyM (parameter x y) x y

def operation (p : Vec × Vec) : Vec × Vec :=
  (m p.1 p.2, m p.2 p.1)

theorem m_eq_family_of_inPlane {x y z w : Vec}
    (hz : InPlane x y z) (hw : InPlane x y w) :
    m z w = familyM (parameter x y) z w :=
  familyM_parameter_locality hz hw

theorem inPlane_m {x y z w : Vec}
    (hz : InPlane x y z) (hw : InPlane x y w) : InPlane x y (m z w) :=
  inPlane_familyM _ hz hw

theorem operation_eq_family (p : Vec × Vec) :
    operation p = familyOperation (parameter p.1 p.2) p := by
  simp only [operation, familyOperation, m, parameter_swap p.1 p.2]

theorem operation_eq_family_of_inPlane {x y z w : Vec}
    (hz : InPlane x y z) (hw : InPlane x y w) :
    operation (z, w) = familyOperation (parameter x y) (z, w) := by
  apply Prod.ext
  · exact m_eq_family_of_inPlane hz hw
  · exact m_eq_family_of_inPlane hw hz

theorem operation_square (p : Vec × Vec) :
    operation (operation p) = p.swap := by
  have hx := inPlane_left p.1 p.2
  have hy := inPlane_right p.1 p.2
  have hh := operation_eq_family_of_inPlane (inPlane_m hx hy) (inPlane_m hy hx)
  change operation (operation p) = familyOperation (parameter p.1 p.2) (operation p) at hh
  rw [hh, operation_eq_family p]
  exact familyOperation_square _ p

theorem operation_transparent (x : Vec) : operation (x, x) = (x, x) := by
  rw [operation_eq_family]
  exact familyOperation_transparent _ x

def contract : RawSparseConservationSelection.Contract Vec where
  chosenZero := 0
  operation := operation
  weight := W
  vacuum := W_zero
  square := operation_square
  transparent := operation_transparent

theorem contract_m (x y : Vec) : RawSparseConservationSelection.m contract x y = m x y := rfl

theorem A_eq (x : Vec) : RawSparseConservationSelection.A contract x = a • x := by
  change familyM (parameter x 0) x 0 = a • x
  exact family_A _ x

theorem B_eq (x : Vec) : RawSparseConservationSelection.B contract x = b • x := by
  change familyM (parameter 0 x) 0 x = b • x
  exact family_B _ x

theorem inPlane_A {x y z : Vec} (hz : InPlane x y z) :
    InPlane x y (RawSparseConservationSelection.A contract z) := by
  rw [A_eq]
  exact inPlane_smul _ hz

theorem inPlane_B {x y z : Vec} (hz : InPlane x y z) :
    InPlane x y (RawSparseConservationSelection.B contract z) := by
  rw [B_eq]
  exact inPlane_smul _ hz

theorem sparse_inPlane {x y r s t : Vec}
    (hr : InPlane x y r) (hs : InPlane x y s) (ht : InPlane x y t) :
    RawSparseConservationTests.SparseAt contract r s t := by
  change W (m (m r s) (RawSparseConservationSelection.A contract t)) +
      W (m (m s r) (RawSparseConservationSelection.B contract t)) =
    W (m r t) + W (RawSparseConservationSelection.A contract s)
  rw [A_eq, B_eq, A_eq]
  rw [m_eq_family_of_inPlane (inPlane_m hr hs) (inPlane_smul a ht),
    m_eq_family_of_inPlane (inPlane_m hs hr) (inPlane_smul b ht),
    m_eq_family_of_inPlane hr ht,
    m_eq_family_of_inPlane hr hs, m_eq_family_of_inPlane hs hr]
  simpa only [family_m, family_A, family_B] using familySparse (parameter x y) r s t

/-- Every displayed family has at most two independent vector inputs. -/
theorem tests : RawSparseConservationTests.Tests contract where
  vacuum_diagonal := fun t =>
    sparse_inPlane (inPlane_zero t t) (inPlane_left t t) (inPlane_right t t)
  vacuum_reference := fun x y =>
    sparse_inPlane (inPlane_left x y) (inPlane_right x y) (inPlane_zero x y)
  diagonal := fun t z =>
    sparse_inPlane (inPlane_left t z) (inPlane_left t z) (inPlane_right t z)
  split_forward := fun t z =>
    sparse_inPlane (inPlane_A (inPlane_left t z))
      (inPlane_B (inPlane_left t z)) (inPlane_right t z)
  split_reverse := fun t z =>
    sparse_inPlane (inPlane_B (inPlane_left t z))
      (inPlane_A (inPlane_left t z)) (inPlane_right t z)
  vacuum_second := fun t z =>
    sparse_inPlane (inPlane_left t z) (inPlane_zero t z) (inPlane_right t z)

theorem selfSparse (x y : Vec) : RawSparseConservationTests.SparseAt contract x y
    (RawSparseConservationSelection.A contract x) :=
  sparse_inPlane (inPlane_left x y) (inPlane_right x y) (inPlane_A (inPlane_left x y))

theorem weight_nonnegative (x : Vec) : 0 ≤ contract.weight x := W_nonnegative x

theorem weight_eq_zero_iff (x : Vec) : contract.weight x = 0 ↔ x = contract.chosenZero :=
  W_eq_zero_iff x

theorem pair_conserved : RawSparseConservationSelection.PairConserved contract :=
  RawSparseConservationTests.pair_conserved_of_tests contract tests weight_nonnegative

/-- Simultaneous scalar multiplication stays in the original input plane. -/
theorem m_smul (c : ℂ) (x y : Vec) : m (c • x) (c • y) = c • m x y := by
  rw [m_eq_family_of_inPlane (inPlane_smul c (inPlane_left x y))
    (inPlane_smul c (inPlane_right x y)), familyM_smul]
  rfl

theorem operation_smul (c : ℂ) (p : Vec × Vec) : operation (c • p) = c • operation p := by
  apply Prod.ext <;> exact m_smul c _ _

end
end IDT.QMClosure.RawPlanePhaseControl
