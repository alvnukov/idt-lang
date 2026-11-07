import Proofs.QMClosure.RawSparseConservationSelection

/-!
# Six universal sparse test families select conservation

The six families below restrict the actual sparse equality to the inputs used
by the conservation argument. Each family is universally quantified over its
displayed parameters. They are not six finite examples, and no minimality or
physical availability claim is made.

Global weight nonnegativity eliminates the signed residual. Observed mediality
remains a separate premise when recovering the full sparse marginal law.
-/

namespace IDT.QMClosure.RawSparseConservationTests

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 10000000
open RawSparseConservationSelection

universe u
variable {V : Type u}

/-- The actual sparse readout equality at one raw input triple. -/
def SparseAt (D : Contract V) (x y z : V) : Prop :=
  D.weight (m D (m D x y) (A D z)) +
      D.weight (m D (m D y x) (B D z)) =
    D.weight (m D x z) + D.weight (A D y)

/-- Six universal families, with no conservation or positivity input field. -/
structure Tests (D : Contract V) : Prop where
  vacuum_diagonal : ∀ t, SparseAt D D.chosenZero t t
  vacuum_reference : ∀ x y, SparseAt D x y D.chosenZero
  diagonal : ∀ t z, SparseAt D t t z
  split_forward : ∀ t z, SparseAt D (A D t) (B D t) z
  split_reverse : ∀ t z, SparseAt D (B D t) (A D t) z
  vacuum_second : ∀ t z, SparseAt D t D.chosenZero z

theorem of_sparse (D : Contract V) (hs : SparseMarginalLaw D) : Tests D :=
  ⟨fun t => hs _ t t, fun x y => hs x y _, fun t z => hs t t z,
    fun t z => hs (A D t) (B D t) z,
    fun t z => hs (B D t) (A D t) z, fun t z => hs t _ z⟩

theorem u_conserved (D : Contract V) (ht : Tests D) (x y : V) :
    u D (m D x y) + u D (m D y x) = u D x + u D y := by
  have hh := ht.vacuum_reference x y
  unfold SparseAt at hh
  rw [A_zero D, B_zero D] at hh
  exact hh

theorem u_add_v (D : Contract V) (ht : Tests D) (x : V) :
    u D x + v D x = D.weight x := by
  have hh := ht.vacuum_diagonal x
  change D.weight (m D (B D x) (A D x)) +
      D.weight (m D (A D x) (B D x)) = v D x + u D x at hh
  rw [m_B_A D, m_A_B D, D.vacuum] at hh
  linarith

theorem v_vacuum_conserved (D : Contract V) (ht : Tests D) (z : V) :
    v D (A D z) + v D (B D z) = v D z := by
  have hu := u_conserved D ht z D.chosenZero
  change u D (A D z) + u D (B D z) = u D z + u D D.chosenZero at hu
  rw [u_zero D] at hu
  have ha := u_add_v D ht (A D z)
  have hb := u_add_v D ht (B D z)
  have hz := u_add_v D ht z
  change u D (A D z) + v D (A D z) = u D z at ha
  change u D (B D z) + v D (B D z) = v D z at hb
  linarith

/-- This helper uses only the supplied pointwise sparse test. -/
theorem kernel_at (D : Contract V) (ht : Tests D) {x y z : V}
    (h : SparseAt D x y z) :
    K D (m D x y) (A D z) + K D (m D y x) (B D z) = K D x z := by
  have hu := u_conserved D ht x y
  have hv := v_vacuum_conserved D ht z
  unfold K
  change D.weight (m D (m D x y) (A D z)) - u D (m D x y) - v D (A D z) +
      (D.weight (m D (m D y x) (B D z)) - u D (m D y x) - v D (B D z)) =
    D.weight (m D x z) - u D x - v D z
  change D.weight (m D (m D x y) (A D z)) +
      D.weight (m D (m D y x) (B D z)) =
    D.weight (m D x z) + u D y at h
  linarith

theorem K_split (D : Contract V) (ht : Tests D) (x z : V) :
    K D x (A D z) + K D x (B D z) = K D x z := by
  simpa only [m_diagonal D] using kernel_at D ht (ht.diagonal x z)

theorem K_A_adjoint (D : Contract V) (ht : Tests D) (x z : V) :
    K D (A D x) z = K D x (B D z) := by
  have hh := kernel_at D ht (ht.split_forward x z)
  rw [m_A_B D, m_B_A D, K_left_zero D, zero_add] at hh
  exact hh.symm

theorem K_B_adjoint (D : Contract V) (ht : Tests D) (x z : V) :
    K D (B D x) z = K D x (A D z) := by
  have hh := kernel_at D ht (ht.split_reverse x z)
  rw [m_B_A D, m_A_B D, K_left_zero D, add_zero] at hh
  exact hh.symm

theorem K_AB_commute (D : Contract V) (ht : Tests D) (x z : V) :
    K D x (A D (B D z)) = K D x (B D (A D z)) := by
  have h1 := K_split D ht (B D x) z
  rw [K_B_adjoint D ht, K_B_adjoint D ht, K_B_adjoint D ht] at h1
  have h2 := K_split D ht x (A D z)
  linarith

theorem K_cross (D : Contract V) (ht : Tests D) (x z : V) :
    K D x (B D (A D z)) + K D x (A D (B D z)) = K D x z := by
  have hh := kernel_at D ht (ht.vacuum_second x z)
  change K D (A D x) (A D z) + K D (B D x) (B D z) = K D x z at hh
  rw [K_A_adjoint D ht, K_B_adjoint D ht] at hh
  exact hh

theorem K_squares (D : Contract V) (ht : Tests D) (x z : V) :
    K D x (A D (A D z)) + K D x (B D (B D z)) = 0 := by
  have h0 := K_split D ht x z
  have h1 := K_split D ht x (A D z)
  have h2 := K_split D ht x (B D z)
  have h3 := K_cross D ht x z
  linarith

theorem q_nonnegative_formula (D : Contract V) (ht : Tests D) (x : V) :
    q D x = 2 * u D (A D x) + 2 * v D (B D x) := by
  have h1 := K_A_B_self D x
  rw [K_A_adjoint D ht] at h1
  have h2 := K_squares D ht x x
  unfold q
  linarith

theorem q_nonnegative (D : Contract V) (ht : Tests D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x : V) : 0 ≤ q D x := by
  rw [q_nonnegative_formula D ht]
  exact add_nonneg (mul_nonneg (by norm_num) (hnonnegative (A D (A D x))))
    (mul_nonneg (by norm_num) (hnonnegative (B D (B D x))))

theorem q_A (D : Contract V) (ht : Tests D) (x : V) :
    q D (A D x) = q D x / 2 := by
  have h1 := K_A_adjoint D ht x (A D (A D (A D x)))
  have h2 := K_cross D ht x (A D (A D x))
  have h3 := K_AB_commute D ht x (A D (A D x))
  unfold q
  linarith

theorem q_weight_AB (D : Contract V) (ht : Tests D) (x : V) :
    q D x = 2 * D.weight x - 4 * D.weight (A D (B D x)) := by
  have hq := q_nonnegative_formula D ht x
  have hu := u_conserved D ht x D.chosenZero
  change u D (A D x) + u D (B D x) = u D x + u D D.chosenZero at hu
  rw [u_zero D] at hu
  have hb := u_add_v D ht (B D x)
  have hx := u_add_v D ht x
  change u D (B D x) + v D (B D x) = v D x at hb
  change q D x = 2 * D.weight x - 4 * u D (B D x)
  linarith

theorem weight_AA_recurrence (D : Contract V) (ht : Tests D) (x : V) :
    D.weight (A D (A D x)) = D.weight (A D x) - D.weight x / 2 + q D x / 4 := by
  have hu := u_conserved D ht x D.chosenZero
  change D.weight (A D (A D x)) + D.weight (A D (B D x)) =
    D.weight (A D x) + u D D.chosenZero at hu
  rw [u_zero D] at hu
  have hq := q_weight_AB D ht x
  linarith

theorem r_AA (D : Contract V) (ht : Tests D) (x : V) :
    r D (A D (A D x)) = r D (A D x) - r D x / 2 := by
  have hw := weight_AA_recurrence D ht x
  have hq0 := q_A D ht x
  have hq1 := q_A D ht (A D x)
  unfold r
  linarith

theorem q_fourthVacuum (D : Contract V) (ht : Tests D) (x : V) :
    q D (fourthVacuum D x) = q D x / 16 := by
  unfold fourthVacuum
  rw [q_A D ht, q_A D ht, q_A D ht, q_A D ht]
  ring

theorem r_fourthVacuum (D : Contract V) (ht : Tests D) (x : V) :
    r D (fourthVacuum D x) = -r D x / 4 := by
  have h0 := r_AA D ht x
  have h1 := r_AA D ht (A D x)
  have h2 := r_AA D ht (A D (A D x))
  unfold fourthVacuum
  linarith

theorem scaled_weight_iterate (D : Contract V) (ht : Tests D)
    (k : ℕ) (x : V) :
    (16 : ℝ)^k * D.weight ((fourthVacuum D)^[k] x) =
      q D x + (-4 : ℝ)^k * r D x := by
  induction k generalizing x with
  | zero => simp [r]
  | succ k ih =>
      rw [Function.iterate_succ_apply, pow_succ, pow_succ]
      have hh := ih (fourthVacuum D x)
      rw [q_fourthVacuum D ht, r_fourthVacuum D ht] at hh
      nlinarith

theorem scaled_weight_iterate_nonnegative (D : Contract V) (ht : Tests D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (k : ℕ) (x : V) :
    0 ≤ q D x + (-4 : ℝ)^k * r D x := by
  have hh := mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 16) k)
    (hnonnegative ((fourthVacuum D)^[k] x))
  rw [scaled_weight_iterate D ht] at hh
  exact hh

theorem r_nonnegative (D : Contract V) (ht : Tests D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x : V) : 0 ≤ r D x := by
  apply RawSparseMarginalReconstruction.nonnegative_of_geometric_bounds (q D x) (r D x)
  intro n
  have hh := scaled_weight_iterate_nonnegative D ht hnonnegative (2*n) x
  simpa only [pow_mul, show (-4 : ℝ)^2 = 16 by norm_num] using hh

theorem r_eq_zero (D : Contract V) (ht : Tests D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x : V) : r D x = 0 := by
  have h0 := r_nonnegative D ht hnonnegative x
  have h1 := r_nonnegative D ht hnonnegative (fourthVacuum D x)
  rw [r_fourthVacuum D ht] at h1
  linarith

theorem weight_eq_q (D : Contract V) (ht : Tests D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x : V) : D.weight x = q D x := by
  have hh := r_eq_zero D ht hnonnegative x
  unfold r at hh
  linarith

/-- The six universal test families and positivity force vacuum half-weight. -/
theorem weight_A_of_tests (D : Contract V) (ht : Tests D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x : V) : D.weight (A D x) = D.weight x / 2 := by
  calc
    D.weight (A D x) = q D (A D x) := weight_eq_q D ht hnonnegative (A D x)
    _ = q D x / 2 := q_A D ht x
    _ = D.weight x / 2 := congrArg (fun t : ℝ => t / 2) (weight_eq_q D ht hnonnegative x).symm

/-- Global positivity eliminates the signed residual before conservation is used. -/
theorem pair_conserved_of_tests (D : Contract V) (ht : Tests D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) : PairConserved D := by
  intro x y
  have hu := u_conserved D ht x y
  have hxy := weight_A_of_tests D ht hnonnegative (m D x y)
  have hyx := weight_A_of_tests D ht hnonnegative (m D y x)
  have hx := weight_A_of_tests D ht hnonnegative x
  have hy := weight_A_of_tests D ht hnonnegative y
  unfold u at hu
  rw [second_eq_reverse D]
  change D.weight (m D x y) + D.weight (m D y x) = D.weight x + D.weight y
  linarith

/-- The complementary vacuum output has the same forced half-weight. -/
theorem weight_B_of_tests (D : Contract V) (ht : Tests D)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) (x : V) :
    D.weight (B D x) = D.weight x / 2 := by
  have hh := u_add_v D ht x
  have ha := weight_A_of_tests D ht hnonnegative x
  unfold u v at hh
  linarith

/-- The remaining full-law content is observed mediality under positivity. -/
theorem sparse_iff_tests_and_observed_medial (D : Contract V)
    (hnonnegative : ∀ x, 0 ≤ D.weight x) :
    SparseMarginalLaw D ↔ Tests D ∧ ObservedMedial D :=
  ⟨fun hs => ⟨of_sparse D hs, observed_medial_of_sparse D hs hnonnegative⟩,
    fun h => sparse_of_conserved_and_observed_medial D
      (pair_conserved_of_tests D h.1 hnonnegative) h.2⟩

end

end IDT.QMClosure.RawSparseConservationTests
