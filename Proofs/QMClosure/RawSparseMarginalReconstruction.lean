import Proofs.QMClosure.RawObservableMedialWall
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Actual sparse readout reconstructs the observational quotient

The core starts with a pointed set, a pair operation, and a real weight. Its
supplied conditions are exact square-swap, transparency, total conservation,
and zero weight at the chosen zero. No vacuum balance or nonnegativity is a
field of this contract. No raw addition, complex scalar action, homogeneity,
split bijection, faithful weight, topology, or Hilbert representation is given.

The sparse equation is the actual selected-row equality for arbitrary supplied
raw triples, including the actual vacuum readout on its right side. Its
pointwise kernel consequences need no positivity. Global nonnegativity enters
explicitly in the all-iterate argument that eliminates the signed residual
and derives vacuum half-weight, weight descent, and contextual mediality.
The constructed complex Hilbert representation is downstream output, may be
degenerate, and identifies exactly the existing finite one-hole contexts.

No generated availability, complete physical context coverage, independent
parties, detector actualization, Born selection, IDT primitive derivation,
literal raw mediality, or full QM/GR closure is asserted.
-/

namespace IDT.QMClosure.RawSparseMarginalReconstruction

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 10000000
open OperationalContextQuotient
open RawNetworkMedialWall (Quad rows columns)
open RawObservableMedialWall (rowReadout)

universe u

/-- Neither nonnegativity nor vacuum half-weight is an input field. -/
structure Contract (V : Type u) where
  chosenZero : V
  operation : V × V → V × V
  weight : V → ℝ
  vacuum : weight chosenZero = 0
  square : ∀ p, operation (operation p) = p.swap
  transparent : ∀ x, operation (x, x) = (x, x)
  conserved : ∀ x y,
    weight (operation (x, y)).1 + weight (operation (x, y)).2 = weight x + weight y

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

theorem m_conserved (D : Contract V) (x y : V) :
    D.weight (m D x y) + D.weight (m D y x) = D.weight x + D.weight y := by
  simpa only [m, second_eq_reverse D] using D.conserved x y

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

theorem u_add_v (D : Contract V) (x : V) : u D x + v D x = D.weight x := by
  have hc := m_conserved D x D.chosenZero
  change u D x + v D x = D.weight x + D.weight D.chosenZero at hc
  simpa only [D.vacuum, add_zero] using hc

theorem u_conserved (D : Contract V) (hs : SparseMarginalLaw D) (x y : V) :
    u D (m D x y) + u D (m D y x) = u D x + u D y := by
  have hh := hs x y D.chosenZero
  rw [A_zero D, B_zero D] at hh
  exact hh

theorem v_conserved (D : Contract V) (hs : SparseMarginalLaw D) (x y : V) :
    v D (m D x y) + v D (m D y x) = v D x + v D y := by
  have hu := u_conserved D hs x y
  have hc := m_conserved D x y
  have h1 := u_add_v D (m D x y)
  have h2 := u_add_v D (m D y x)
  have hx := u_add_v D x
  have hy := u_add_v D y
  linarith

theorem v_vacuum_conserved (D : Contract V) (hs : SparseMarginalLaw D) (z : V) :
    v D (A D z) + v D (B D z) = v D z := by
  have hh := v_conserved D hs z D.chosenZero
  change v D (A D z) + v D (B D z) = v D z + v D D.chosenZero at hh
  simpa only [v_zero D, add_zero] using hh

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

theorem K_skew (D : Contract V) (x z : V) : K D z x = -K D x z := by
  have hc := m_conserved D x z
  have hx := u_add_v D x
  have hz := u_add_v D z
  unfold K
  linarith

theorem K_right_zero (D : Contract V) (x : V) : K D x D.chosenZero = 0 := by
  change u D x - u D x - v D D.chosenZero = 0
  rw [v_zero D]
  ring

theorem K_left_zero (D : Contract V) (x : V) : K D D.chosenZero x = 0 := by
  rw [K_skew D x D.chosenZero, K_right_zero D]
  simp

theorem K_diagonal (D : Contract V) (x : V) : K D x x = 0 := by
  have hx := u_add_v D x
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

/-- The complete first row uses one actual supplied zero, with no discarded slot. -/
def sparseInput (D : Contract V) (x y z : V) : Quad V := ((x, y), (z, D.chosenZero))

theorem sparse_marginal_iff_after_analyzer (D : Contract V) :
    SparseMarginalLaw D ↔ ∀ x y z,
      rowReadout D.weight (columns D.operation (rows D.operation (sparseInput D x y z))) =
        rowReadout D.weight (columns D.operation (sparseInput D x y z)) := by
  have pointwise (x y z : V) :
      rowReadout D.weight (columns D.operation (rows D.operation (sparseInput D x y z))) =
          rowReadout D.weight (columns D.operation (sparseInput D x y z)) ↔
        D.weight (m D (m D x y) (A D z)) + D.weight (m D (m D y x) (B D z)) =
          D.weight (m D x z) + D.weight (A D y) := by
    simp only [rowReadout, columns, rows, sparseInput, second_eq_reverse D]
    rfl
  exact ⟨fun hs x y z => (pointwise x y z).mpr (hs x y z),
    fun hs x y z => (pointwise x y z).mp (hs x y z)⟩

theorem sparse_marginal_iff_row_order (D : Contract V) :
    SparseMarginalLaw D ↔ ∀ x y z,
      rowReadout D.weight (columns D.operation (rows D.operation (sparseInput D x y z))) =
        rowReadout D.weight (rows D.operation (columns D.operation (sparseInput D x y z))) := by
  rw [sparse_marginal_iff_after_analyzer D]
  constructor
  · intro hs x y z
    exact (RawObservableMedialWall.row_order_eq_iff_after_analyzer
      D.operation D.weight D.conserved (sparseInput D x y z)).mpr (hs x y z)
  · intro hs x y z
    exact (RawObservableMedialWall.row_order_eq_iff_after_analyzer
      D.operation D.weight D.conserved (sparseInput D x y z)).mp (hs x y z)

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
  have hb := u_add_v D (B D x)
  have hx := u_add_v D x
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

theorem nonnegative_of_geometric_bounds (p t : ℝ)
    (hbound : ∀ n : ℕ, 0 ≤ p + (16 : ℝ)^n * t) : 0 ≤ t := by
  by_contra hn
  have ht : t < 0 := lt_of_not_ge hn
  have hneg : 0 < -t := neg_pos.mpr ht
  obtain ⟨n, hpow⟩ := pow_unbounded_of_one_lt (p / -t) (by norm_num : (1 : ℝ) < 16)
  have hh : p < (16 : ℝ)^n * -t := (div_lt_iff₀ hneg).mp hpow
  have hb := hbound n
  nlinarith

theorem r_nonnegative (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x : V) : 0 ≤ r D x := by
  apply nonnegative_of_geometric_bounds (q D x) (r D x)
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

theorem weight_B (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x : V) : D.weight (B D x) = D.weight x / 2 := by
  have hc := u_add_v D x
  have ha := weight_A D hs hnonnegative x
  change D.weight (A D x) + D.weight (B D x) = D.weight x at hc
  linarith

theorem weight_eq_two_K_AA (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x : V) :
    D.weight x = 2 * K D x (A D (A D x)) :=
  weight_eq_q D hs hnonnegative x

def L (D : Contract V) (x y : V) : ℝ := K D x (A D (A D y))

theorem L_symmetric (D : Contract V) (he : KernelMarginalLaw D) (x y : V) :
    L D y x = L D x y := by
  have h1 := K_B_adjoint D he (B D y) x
  have h2 := K_B_adjoint D he y (A D x)
  have h3 := K_skew D x (B D (B D y))
  have h4 := K_squares D he x y
  unfold L
  linarith

theorem kernelEq_weight_eq (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x)
    {x y : V} (hxy : KernelEq D x y) : D.weight x = D.weight y := by
  have he := sparse_implies_kernel D hs
  have h1 := hxy (A D (A D x))
  have h2 := hxy (A D (A D y))
  have h3 := L_symmetric D he x y
  have hx := weight_eq_two_K_AA D hs hnonnegative x
  have hy := weight_eq_two_K_AA D hs hnonnegative y
  unfold L at h3
  linarith

theorem kernelEq_refl (D : Contract V) (x : V) : KernelEq D x x := fun _ => rfl

theorem kernelEq_m_congr (D : Contract V) (he : KernelMarginalLaw D)
    {x x' y y' : V} (hx : KernelEq D x x') (hy : KernelEq D y y') :
    KernelEq D (m D x y) (m D x' y') := by
  intro z
  rw [K_m D he, K_m D he, hx (B D z), hy (A D z)]

theorem kernelEq_implies_observationalEq (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x)
    {x y : V} (hxy : KernelEq D x y) : ObservationalEq D.operation D.weight x y := by
  have he := sparse_implies_kernel D hs
  apply relation_le_observationalEq D.operation D.weight (KernelEq D)
    (fun _ _ hh => kernelEq_weight_eq D hs hnonnegative hh) _ _ hxy
  · intro s a b r hab
    cases s with
    | first => exact kernelEq_m_congr D he hab (kernelEq_refl D r)
    | second =>
        simpa only [select, second_eq_reverse D] using
          kernelEq_m_congr D he (kernelEq_refl D r) hab
  · intro s a b r hab
    cases s with
    | first => exact kernelEq_m_congr D he (kernelEq_refl D r) hab
    | second =>
        simpa only [select, second_eq_reverse D] using
          kernelEq_m_congr D he hab (kernelEq_refl D r)

/-- The reverse implication needs no sparse law. -/
theorem observationalEq_implies_kernelEq (D : Contract V) {x y : V}
    (hxy : ObservationalEq D.operation D.weight x y) : KernelEq D x y := by
  have hu := hxy (.left .first .hole D.chosenZero)
  change u D x = u D y at hu
  intro z
  have hm := hxy (.left .first .hole z)
  change D.weight (m D x z) = D.weight (m D y z) at hm
  unfold K
  rw [hm, hu]

theorem kernelEq_iff_observationalEq (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x y : V) :
    KernelEq D x y ↔ ObservationalEq D.operation D.weight x y :=
  ⟨kernelEq_implies_observationalEq D hs hnonnegative,
    observationalEq_implies_kernelEq D⟩

theorem observed_medial_of_sparse (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) : ObservedMedial D := by
  intro a b c d
  have he := sparse_implies_kernel D hs
  exact kernelEq_implies_observationalEq D hs hnonnegative (kernel_medial D he a b c d)

/-- Two sparse medial observations and exact conservation recover the sparse law. -/
theorem sparse_of_observed_medial (D : Contract V) (hm : ObservedMedial D) :
    SparseMarginalLaw D := by
  intro x y z
  have h1 := weight_eq (hm x y z D.chosenZero)
  change D.weight (m D (m D x y) (A D z)) =
    D.weight (m D (m D x z) (A D y)) at h1
  have h2 := weight_eq (hm y x D.chosenZero z)
  change D.weight (m D (m D y x) (B D z)) =
    D.weight (m D (A D y) (m D x z)) at h2
  have hc := m_conserved D (m D x z) (A D y)
  linarith

theorem sparse_marginal_iff_observed_medial (D : Contract V)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) :
    SparseMarginalLaw D ↔ ObservedMedial D :=
  ⟨fun hs => observed_medial_of_sparse D hs hnonnegative, sparse_of_observed_medial D⟩

/-- The existing representation construction retains explicit nonnegativity. -/
def observedData (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) : ObservedData V where
  chosenZero := D.chosenZero
  operation := D.operation
  weight := D.weight
  vacuum := D.vacuum
  nonnegative := hnonnegative
  conserved := D.conserved
  square p := by
    rw [D.square p]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  medial := observed_medial_of_sparse D hs hnonnegative

abbrev quotientData (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) := (observedData D hs hnonnegative).quotientData

abbrev Hilbert (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) := (observedData D hs hnonnegative).Hilbert

def feature (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x : V) : Hilbert D hs hnonnegative :=
  (observedData D hs hnonnegative).feature x

theorem norm_feature_sq (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x : V) :
    ‖feature D hs hnonnegative x‖ ^ 2 = D.weight x :=
  (observedData D hs hnonnegative).norm_feature_sq x

theorem feature_chosenZero (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) : feature D hs hnonnegative D.chosenZero = 0 :=
  (observedData D hs hnonnegative).feature_zero

theorem feature_eq_iff_observationalEq (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x y : V) :
    feature D hs hnonnegative x = feature D hs hnonnegative y ↔
      ObservationalEq D.operation D.weight x y :=
  (observedData D hs hnonnegative).feature_eq_iff_observationalEq x y

theorem feature_eq_iff_kernelEq (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x y : V) :
    feature D hs hnonnegative x = feature D hs hnonnegative y ↔ KernelEq D x y := by
  rw [feature_eq_iff_observationalEq D hs hnonnegative,
    kernelEq_iff_observationalEq D hs hnonnegative]

/-- A positive supplied witness excludes only the degenerate feature at that point. -/
theorem feature_ne_zero_of_positive_weight (D : Contract V) (hs : SparseMarginalLaw D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x : V) (hx : 0 < D.weight x) :
    feature D hs hnonnegative x ≠ 0 := by
  intro hz
  have hn := norm_feature_sq D hs hnonnegative x
  rw [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hn
  linarith

end
end IDT.QMClosure.RawSparseMarginalReconstruction
