import Proofs.QMClosure.RawSparseMarginalReconstruction

/-!
# Sparse readout selects pair conservation

A pointed set, square-swap pair operation, transparent diagonal, and real weight
with zero vacuum weight form the raw contract. The actual sparse marginal law
and global weight nonnegativity remain explicit theorem premises. The sparse
law first gives vacuum conservation, then a signed-residual recurrence. Global
nonnegativity eliminates that residual and forces vacuum half-weight and total
pair conservation. The conserved contract then supplies the existing quotient
representation and its arbitrary-reference finite one-hole observations.

The representation may be degenerate, including identically zero weight.
No raw medial equality, generated context availability, physical locality or
independence, actualization, Born selection, IDT primitive derivation, or full
QM/GR closure is asserted.
-/

namespace IDT.QMClosure.RawSparseConservationSelection

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 10000000
open OperationalContextQuotient
open RawNetworkMedialWall (Quad rows columns)
open RawObservableMedialWall (rowReadout)

universe u

/-- Conservation, nonnegativity, and vacuum half-weight are not input fields. -/
structure Contract (V : Type u) where
  chosenZero : V
  operation : V × V → V × V
  weight : V → ℝ
  vacuum : weight chosenZero = 0
  square : ∀ p, operation (operation p) = p.swap
  transparent : ∀ x, operation (x, x) = (x, x)

variable {V : Type u}

def m (D : Contract V) (x y : V) : V := (D.operation (x, y)).1
def A (D : Contract V) (x : V) : V := m D x D.chosenZero
def B (D : Contract V) (x : V) : V := m D D.chosenZero x

def u (D : Contract V) (x : V) : ℝ := D.weight (A D x)
def v (D : Contract V) (x : V) : ℝ := D.weight (B D x)

def K (D : Contract V) (x z : V) : ℝ :=
  D.weight (m D x z) - u D x - v D z

def KernelEq (D : Contract V) (x y : V) : Prop := ∀ z, K D x z = K D y z

/-- The actual sparse readout equation, with no balanced-vacuum substitution. -/
def SparseMarginalLaw (D : Contract V) : Prop :=
  ∀ x y z, D.weight (m D (m D x y) (A D z)) +
      D.weight (m D (m D y x) (B D z)) =
    D.weight (m D x z) + D.weight (A D y)

def KernelMarginalLaw (D : Contract V) : Prop :=
  ∀ x y z, K D (m D x y) (A D z) + K D (m D y x) (B D z) = K D x z

/-- Exact total pair-weight conservation is a conclusion under positivity. -/
def PairConserved (D : Contract V) : Prop :=
  ∀ x y, D.weight (D.operation (x, y)).1 + D.weight (D.operation (x, y)).2 =
    D.weight x + D.weight y

def ObservedMedial (D : Contract V) : Prop :=
  ∀ a b c d, ObservationalEq D.operation D.weight
    (m D (m D a b) (m D c d)) (m D (m D a c) (m D b d))

theorem operation_swap (D : Contract V) (x y : V) :
    D.operation (y, x) = ((D.operation (x, y)).2, (D.operation (x, y)).1) := by
  have hs := D.square (D.operation (x, y))
  rw [D.square (x, y)] at hs
  exact hs

theorem second_eq_reverse (D : Contract V) (x y : V) :
    (D.operation (x, y)).2 = m D y x :=
  (congrArg Prod.fst (operation_swap D x y)).symm

theorem operation_eq (D : Contract V) (x y : V) :
    D.operation (x, y) = (m D x y, m D y x) :=
  Prod.ext rfl (second_eq_reverse D x y)

theorem m_diagonal (D : Contract V) (x : V) : m D x x = x :=
  congrArg Prod.fst (D.transparent x)

theorem A_zero (D : Contract V) : A D D.chosenZero = D.chosenZero :=
  m_diagonal D D.chosenZero

theorem B_zero (D : Contract V) : B D D.chosenZero = D.chosenZero :=
  m_diagonal D D.chosenZero

theorem u_zero (D : Contract V) : u D D.chosenZero = 0 := by
  unfold u
  rw [A_zero D, D.vacuum]

theorem v_zero (D : Contract V) : v D D.chosenZero = 0 := by
  unfold v
  rw [B_zero D, D.vacuum]

theorem u_conserved (D : Contract V) (hs : SparseMarginalLaw D) (x y : V) :
    u D (m D x y) + u D (m D y x) = u D x + u D y := by
  have hh := hs x y D.chosenZero
  rw [A_zero D, B_zero D] at hh
  exact hh

theorem vacuum_square (D : Contract V) (x : V) :
    D.operation (A D x, B D x) = (D.chosenZero, x) := by
  have hs := D.square (x, D.chosenZero)
  rw [operation_eq D x D.chosenZero] at hs
  exact hs

theorem m_A_B (D : Contract V) (x : V) : m D (A D x) (B D x) = D.chosenZero :=
  congrArg Prod.fst (vacuum_square D x)

theorem m_B_A (D : Contract V) (x : V) : m D (B D x) (A D x) = x := by
  have hs := congrArg Prod.snd (vacuum_square D x)
  rw [second_eq_reverse D] at hs
  exact hs

/-- The sparse test at `(0,x,x)` forces conservation at a vacuum input. -/
theorem u_add_v (D : Contract V) (hs : SparseMarginalLaw D) (x : V) :
    u D x + v D x = D.weight x := by
  have hh := hs D.chosenZero x x
  change D.weight (m D (B D x) (A D x)) +
      D.weight (m D (A D x) (B D x)) = v D x + u D x at hh
  rw [m_B_A D, m_A_B D, D.vacuum] at hh
  linarith

/-- Only vacuum-input conservation of the second auxiliary weight is needed. -/
theorem v_vacuum_conserved (D : Contract V) (hs : SparseMarginalLaw D) (z : V) :
    v D (A D z) + v D (B D z) = v D z := by
  have hu := u_conserved D hs z D.chosenZero
  change u D (A D z) + u D (B D z) = u D z + u D D.chosenZero at hu
  rw [u_zero D] at hu
  have ha := u_add_v D hs (A D z)
  have hb := u_add_v D hs (B D z)
  have hz := u_add_v D hs z
  change u D (A D z) + v D (A D z) = u D z at ha
  change u D (B D z) + v D (B D z) = v D z at hb
  linarith

theorem K_right_zero (D : Contract V) (x : V) : K D x D.chosenZero = 0 := by
  change u D x - u D x - v D D.chosenZero = 0
  rw [v_zero D]
  ring

theorem K_left_zero (D : Contract V) (x : V) : K D D.chosenZero x = 0 := by
  change v D x - u D D.chosenZero - v D x = 0
  rw [u_zero D]
  ring

theorem K_diagonal (D : Contract V) (hs : SparseMarginalLaw D) (x : V) : K D x x = 0 := by
  have hx := u_add_v D hs x
  unfold K
  rw [m_diagonal D]
  linarith

/-- Auxiliary vacuum-weight conservation follows from the actual sparse law. -/
theorem sparse_implies_kernel (D : Contract V) (hs : SparseMarginalLaw D) :
    KernelMarginalLaw D := by
  intro x y z
  have hh := hs x y z
  have hu := u_conserved D hs x y
  have hv := v_vacuum_conserved D hs z
  unfold K
  change D.weight (m D (m D x y) (A D z)) - u D (m D x y) - v D (A D z) +
      (D.weight (m D (m D y x) (B D z)) - u D (m D y x) - v D (B D z)) =
    D.weight (m D x z) - u D x - v D z
  change D.weight (m D (m D x y) (A D z)) +
      D.weight (m D (m D y x) (B D z)) =
    D.weight (m D x z) + u D y at hh
  linarith

theorem K_split (D : Contract V) (he : KernelMarginalLaw D) (x z : V) :
    K D x (A D z) + K D x (B D z) = K D x z := by
  simpa only [m_diagonal D] using he x x z

theorem K_A_adjoint (D : Contract V) (he : KernelMarginalLaw D) (x z : V) :
    K D (A D x) z = K D x (B D z) := by
  have hh := he (A D x) (B D x) z
  rw [m_A_B D, m_B_A D, K_left_zero D, zero_add] at hh
  exact hh.symm

theorem K_B_adjoint (D : Contract V) (he : KernelMarginalLaw D) (x z : V) :
    K D (B D x) z = K D x (A D z) := by
  have hh := he (B D x) (A D x) z
  rw [m_B_A D, m_A_B D, K_left_zero D, add_zero] at hh
  exact hh.symm

theorem K_AB_commute (D : Contract V) (he : KernelMarginalLaw D) (x z : V) :
    K D x (A D (B D z)) = K D x (B D (A D z)) := by
  have h1 := K_split D he (B D x) z
  rw [K_B_adjoint D he, K_B_adjoint D he, K_B_adjoint D he] at h1
  have h2 := K_split D he x (A D z)
  linarith

theorem K_cross (D : Contract V) (he : KernelMarginalLaw D) (x z : V) :
    K D x (B D (A D z)) + K D x (A D (B D z)) = K D x z := by
  have hh := he x D.chosenZero z
  change K D (A D x) (A D z) + K D (B D x) (B D z) = K D x z at hh
  rw [K_A_adjoint D he, K_B_adjoint D he] at hh
  exact hh

theorem K_squares (D : Contract V) (he : KernelMarginalLaw D) (x z : V) :
    K D x (A D (A D z)) + K D x (B D (B D z)) = 0 := by
  have h0 := K_split D he x z
  have h1 := K_split D he x (A D z)
  have h2 := K_split D he x (B D z)
  have h3 := K_cross D he x z
  linarith

/-- A pointwise real identity; no functional span is assumed or constructed. -/
theorem K_m (D : Contract V) (he : KernelMarginalLaw D) (x y z : V) :
    K D (m D x y) z = K D x (B D z) + K D y (A D z) := by
  have h1 := he x y (B D z)
  have h2 := he y x (A D z)
  have h3 := K_cross D he (m D x y) z
  have h4 := K_squares D he (m D y x) z
  linarith

theorem kernel_medial (D : Contract V) (he : KernelMarginalLaw D) (a b c d : V) :
    KernelEq D (m D (m D a b) (m D c d)) (m D (m D a c) (m D b d)) := by
  intro z
  simp only [K_m D he]
  rw [K_AB_commute D he b z, K_AB_commute D he c z]
  ring

theorem K_A_B_self (D : Contract V) (x : V) :
    K D (A D x) (B D x) = -u D (A D x) - v D (B D x) := by
  unfold K
  rw [m_A_B D, D.vacuum]
  ring

def q (D : Contract V) (x : V) : ℝ := 2 * K D x (A D (A D x))
def r (D : Contract V) (x : V) : ℝ := D.weight x - q D x

theorem q_nonnegative_formula (D : Contract V) (he : KernelMarginalLaw D) (x : V) :
    q D x = 2 * u D (A D x) + 2 * v D (B D x) := by
  have h1 := K_A_B_self D x
  rw [K_A_adjoint D he] at h1
  have h2 := K_squares D he x x
  unfold q
  linarith

theorem q_nonnegative (D : Contract V) (he : KernelMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x : V) : 0 ≤ q D x := by
  rw [q_nonnegative_formula D he]
  exact add_nonneg (mul_nonneg (by norm_num) (hnonnegative (A D (A D x))))
    (mul_nonneg (by norm_num) (hnonnegative (B D (B D x))))

theorem q_A (D : Contract V) (he : KernelMarginalLaw D) (x : V) :
    q D (A D x) = q D x / 2 := by
  have h1 := K_A_adjoint D he x (A D (A D (A D x)))
  have h2 := K_cross D he x (A D (A D x))
  have h3 := K_AB_commute D he x (A D (A D x))
  unfold q
  linarith

theorem q_weight_AB (D : Contract V) (hs : SparseMarginalLaw D) (x : V) :
    q D x = 2 * D.weight x - 4 * D.weight (A D (B D x)) := by
  have hq := q_nonnegative_formula D (sparse_implies_kernel D hs) x
  have hu := u_conserved D hs x D.chosenZero
  change u D (A D x) + u D (B D x) = u D x + u D D.chosenZero at hu
  rw [u_zero D] at hu
  have hb := u_add_v D hs (B D x)
  have hx := u_add_v D hs x
  change u D (B D x) + v D (B D x) = v D x at hb
  change q D x = 2 * D.weight x - 4 * u D (B D x)
  linarith

theorem weight_AA_recurrence (D : Contract V) (hs : SparseMarginalLaw D) (x : V) :
    D.weight (A D (A D x)) = D.weight (A D x) - D.weight x / 2 + q D x / 4 := by
  have hu := u_conserved D hs x D.chosenZero
  change D.weight (A D (A D x)) + D.weight (A D (B D x)) =
    D.weight (A D x) + u D D.chosenZero at hu
  rw [u_zero D] at hu
  have hq := q_weight_AB D hs x
  linarith

theorem r_AA (D : Contract V) (hs : SparseMarginalLaw D) (x : V) :
    r D (A D (A D x)) = r D (A D x) - r D x / 2 := by
  have hw := weight_AA_recurrence D hs x
  have hq0 := q_A D (sparse_implies_kernel D hs) x
  have hq1 := q_A D (sparse_implies_kernel D hs) (A D x)
  unfold r
  linarith

def fourthVacuum (D : Contract V) (x : V) : V := A D (A D (A D (A D x)))

theorem q_fourthVacuum (D : Contract V) (he : KernelMarginalLaw D) (x : V) :
    q D (fourthVacuum D x) = q D x / 16 := by
  unfold fourthVacuum
  rw [q_A D he, q_A D he, q_A D he, q_A D he]
  ring

theorem r_fourthVacuum (D : Contract V) (hs : SparseMarginalLaw D) (x : V) :
    r D (fourthVacuum D x) = -r D x / 4 := by
  have h0 := r_AA D hs x
  have h1 := r_AA D hs (A D x)
  have h2 := r_AA D hs (A D (A D x))
  unfold fourthVacuum
  linarith

theorem scaled_weight_iterate (D : Contract V) (hs : SparseMarginalLaw D)
    (k : ℕ) (x : V) :
    (16 : ℝ)^k * D.weight ((fourthVacuum D)^[k] x) =
      q D x + (-4 : ℝ)^k * r D x := by
  induction k generalizing x with
  | zero => simp [r]
  | succ k ih =>
      rw [Function.iterate_succ_apply, pow_succ, pow_succ]
      have hh := ih (fourthVacuum D x)
      rw [q_fourthVacuum D (sparse_implies_kernel D hs), r_fourthVacuum D hs] at hh
      nlinarith

theorem scaled_weight_iterate_nonnegative (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (k : ℕ) (x : V) :
    0 ≤ q D x + (-4 : ℝ)^k * r D x := by
  have hh := mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 16) k)
    (hnonnegative ((fourthVacuum D)^[k] x))
  rw [scaled_weight_iterate D hs] at hh
  exact hh

theorem r_nonnegative (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x : V) : 0 ≤ r D x := by
  apply RawSparseMarginalReconstruction.nonnegative_of_geometric_bounds (q D x) (r D x)
  intro n
  have hh := scaled_weight_iterate_nonnegative D hs hnonnegative (2*n) x
  simpa only [pow_mul, show (-4 : ℝ)^2 = 16 by norm_num] using hh

theorem r_eq_zero (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x : V) : r D x = 0 := by
  have h0 := r_nonnegative D hs hnonnegative x
  have h1 := r_nonnegative D hs hnonnegative (fourthVacuum D x)
  rw [r_fourthVacuum D hs] at h1
  linarith

theorem weight_eq_q (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x : V) : D.weight x = q D x := by
  have hh := r_eq_zero D hs hnonnegative x
  unfold r at hh
  linarith

/-- Vacuum half-weight is a conclusion of the actual sparse law and positivity. -/
theorem weight_A (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x : V) : D.weight (A D x) = D.weight x / 2 := by
  calc
    D.weight (A D x) = q D (A D x) := weight_eq_q D hs hnonnegative (A D x)
    _ = q D x / 2 := q_A D (sparse_implies_kernel D hs) x
    _ = D.weight x / 2 := congrArg (fun t : ℝ => t / 2) (weight_eq_q D hs hnonnegative x).symm

/-- Global positivity eliminates the signed residual before conservation is used. -/
theorem pair_conserved (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) : PairConserved D := by
  intro x y
  have hu := u_conserved D hs x y
  have hxy := weight_A D hs hnonnegative (m D x y)
  have hyx := weight_A D hs hnonnegative (m D y x)
  have hx := weight_A D hs hnonnegative x
  have hy := weight_A D hs hnonnegative y
  unfold u at hu
  rw [second_eq_reverse D]
  change D.weight (m D x y) + D.weight (m D y x) = D.weight x + D.weight y
  linarith

/-- The published conserved contract is constructed only after supplying conservation. -/
def toConservedContract (D : Contract V) (hc : PairConserved D) :
    RawSparseMarginalReconstruction.Contract V where
  chosenZero := D.chosenZero
  operation := D.operation
  weight := D.weight
  vacuum := D.vacuum
  square := D.square
  transparent := D.transparent
  conserved := hc

theorem observed_medial_of_sparse (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) : ObservedMedial D :=
  RawSparseMarginalReconstruction.observed_medial_of_sparse
    (toConservedContract D (pair_conserved D hs hnonnegative)) hs hnonnegative

/-- Conservation is retained explicitly in the reverse implication. -/
theorem sparse_of_conserved_and_observed_medial (D : Contract V)
    (hc : PairConserved D) (hm : ObservedMedial D) : SparseMarginalLaw D :=
  RawSparseMarginalReconstruction.sparse_of_observed_medial (toConservedContract D hc) hm

theorem sparse_iff_conserved_and_observed_medial (D : Contract V)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) :
    SparseMarginalLaw D ↔ PairConserved D ∧ ObservedMedial D :=
  ⟨fun hs => ⟨pair_conserved D hs hnonnegative,
      observed_medial_of_sparse D hs hnonnegative⟩,
    fun h => sparse_of_conserved_and_observed_medial D h.1 h.2⟩

/-- Reuse the established representation only through the derived conserved contract. -/
def observedData (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) : ObservedData V :=
  RawSparseMarginalReconstruction.observedData
    (toConservedContract D (pair_conserved D hs hnonnegative)) hs hnonnegative

abbrev Hilbert (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) := (observedData D hs hnonnegative).Hilbert

def feature (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x : V) : Hilbert D hs hnonnegative :=
  (observedData D hs hnonnegative).feature x

theorem norm_feature_sq (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x : V) :
    ‖feature D hs hnonnegative x‖ ^ 2 = D.weight x :=
  (observedData D hs hnonnegative).norm_feature_sq x

theorem feature_eq_iff_observationalEq (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x y : V) :
    feature D hs hnonnegative x = feature D hs hnonnegative y ↔
      ObservationalEq D.operation D.weight x y :=
  (observedData D hs hnonnegative).feature_eq_iff_observationalEq x y

end

end IDT.QMClosure.RawSparseConservationSelection
