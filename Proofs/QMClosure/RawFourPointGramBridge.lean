import Proofs.QMClosure.RawSparseConservationTests
import Proofs.QMClosure.RawGramGeometry

/-!
# Four-point Gram positivity recovers the actual sparse marginal law

The raw carrier has only the square-swap operation, transparent diagonal, and
weight of the conservation-selection contract. A symmetric real kernel supplies
the diagonal weight, vacuum-map adjointness, and a three-point
mixer-null identity. Positivity is required for every four-point tuple, including
repetitions. It transfers the mixer null relation to every kernel row.

Kernel-row equivalence is stable under both outputs in both ports. Consequently
the derived medial identity holds in every finite one-hole observation. The
square-swap law and kernel-row identity give conservation directly. The existing
conservation-and-observed-medial theorem gives the actual sparse marginal law.

No raw medial equality or separation assumption is required. All kernel laws and
four-point positivity remain explicit premises of this conditional bridge.
-/

namespace IDT.QMClosure.RawFourPointGramBridge

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 10000000
open RawSparseConservationSelection
open OperationalContextQuotient

universe u
variable {V : Type u}

/-- Local kernel compatibility. Each field has at most two independent raw
preparations. Positivity of four-point tuples is a separate premise. -/
structure LocalKernel (D : Contract V) (G : V → V → ℝ) : Prop where
  symmetric : ∀ x y, G x y = G y x
  diagonal : ∀ x, G x x = D.weight x
  adjoint : ∀ x z, G (A D x) z = G x (B D z)
  mixer_null : ∀ x y,
    RawGramGeometry.quadratic G ![A D x, B D y, m D x y] ![1, 1, -1] = 0

/-- Equality of complete kernel rows, without raw-point separation. -/
def GramEq (G : V → V → ℝ) (x y : V) : Prop := ∀ z, G x z = G y z

theorem weight_nonnegative (D : Contract V) (G : V → V → ℝ)
    (hk : LocalKernel D G) (hfour : RawGramGeometry.GramNonnegative G 4) :
    ∀ x, 0 ≤ D.weight x := by
  intro x
  rw [← hk.diagonal x]
  exact RawGramGeometry.diagonal_nonnegative hfour x

theorem B_adjoint (D : Contract V) (G : V → V → ℝ)
    (hk : LocalKernel D G) (x z : V) : G (B D x) z = G x (A D z) := by
  calc
    G (B D x) z = G z (B D x) := hk.symmetric _ _
    _ = G (A D z) x := (hk.adjoint z x).symm
    _ = G x (A D z) := hk.symmetric _ _

/-- Four-point positivity transfers the three-point mixer-null identity to an
arbitrary fourth preparation. -/
theorem G_m (D : Contract V) (G : V → V → ℝ)
    (hk : LocalKernel D G) (hfour : RawGramGeometry.GramNonnegative G 4)
    (x y z : V) :
    G (m D x y) z = G x (B D z) + G y (A D z) := by
  have hh := RawGramGeometry.four_point_null_transfer hk.symmetric hfour
    (A D x) (B D y) (m D x y) z (hk.mixer_null x y)
  rw [hk.adjoint, B_adjoint D G hk] at hh
  linarith

theorem gramEq_weight (D : Contract V) (G : V → V → ℝ)
    (hk : LocalKernel D G) (x y : V) (hxy : GramEq G x y) :
    D.weight x = D.weight y := by
  calc
    D.weight x = G x x := (hk.diagonal x).symm
    _ = G y x := hxy x
    _ = G x y := hk.symmetric y x
    _ = G y y := hxy y
    _ = D.weight y := hk.diagonal y

theorem gramEq_m_left (D : Contract V) (G : V → V → ℝ)
    (hk : LocalKernel D G) (hfour : RawGramGeometry.GramNonnegative G 4)
    {x y : V} (hxy : GramEq G x y) (r : V) :
    GramEq G (m D x r) (m D y r) := by
  intro z
  rw [G_m D G hk hfour, G_m D G hk hfour, hxy (B D z)]

theorem gramEq_m_right (D : Contract V) (G : V → V → ℝ)
    (hk : LocalKernel D G) (hfour : RawGramGeometry.GramNonnegative G 4)
    {x y : V} (hxy : GramEq G x y) (r : V) :
    GramEq G (m D r x) (m D r y) := by
  intro z
  rw [G_m D G hk hfour, G_m D G hk hfour, hxy (A D z)]

/-- Row equivalence survives arbitrary finite one-hole observations, including
both retained outputs and arbitrary fixed references. -/
theorem gramEq_observationalEq (D : Contract V) (G : V → V → ℝ)
    (hk : LocalKernel D G) (hfour : RawGramGeometry.GramNonnegative G 4)
    {x y : V} (hxy : GramEq G x y) :
    ObservationalEq D.operation D.weight x y := by
  apply relation_le_observationalEq D.operation D.weight (GramEq G)
    (gramEq_weight D G hk) ?_ ?_ hxy
  · intro s a b r hab
    cases s with
    | first => exact gramEq_m_left D G hk hfour hab r
    | second =>
      simpa only [select, second_eq_reverse D] using
        gramEq_m_right D G hk hfour hab r
  · intro s a b r hab
    cases s with
    | first => exact gramEq_m_right D G hk hfour hab r
    | second =>
      simpa only [select, second_eq_reverse D] using
        gramEq_m_left D G hk hfour hab r

theorem gram_split (D : Contract V) (G : V → V → ℝ)
    (hk : LocalKernel D G) (hfour : RawGramGeometry.GramNonnegative G 4)
    (x z : V) : G (A D x) z + G (B D x) z = G x z := by
  have hh := G_m D G hk hfour x x z
  rw [m_diagonal D] at hh
  rw [hk.adjoint, B_adjoint D G hk]
  exact hh.symm

/-- The attenuation maps commute at the level of complete kernel rows. -/
theorem gram_attenuation_commute (D : Contract V) (G : V → V → ℝ)
    (hk : LocalKernel D G) (hfour : RawGramGeometry.GramNonnegative G 4)
    (x : V) : GramEq G (A D (B D x)) (B D (A D x)) := by
  intro z
  have h1 := gram_split D G hk hfour (B D x) z
  have h2 := gram_split D G hk hfour x (A D z)
  rw [← B_adjoint D G hk (A D x) z,
    ← B_adjoint D G hk (B D x) z, ← B_adjoint D G hk x z] at h2
  linarith

theorem G_attenuation_commute_right (D : Contract V) (G : V → V → ℝ)
    (hk : LocalKernel D G) (hfour : RawGramGeometry.GramNonnegative G 4)
    (x z : V) : G x (A D (B D z)) = G x (B D (A D z)) := by
  calc
    G x (A D (B D z)) = G (A D (B D z)) x := hk.symmetric _ _
    _ = G (B D (A D z)) x := gram_attenuation_commute D G hk hfour z x
    _ = G x (B D (A D z)) := hk.symmetric _ _

theorem gram_medial (D : Contract V) (G : V → V → ℝ)
    (hk : LocalKernel D G) (hfour : RawGramGeometry.GramNonnegative G 4)
    (a b c d : V) :
    GramEq G (m D (m D a b) (m D c d))
      (m D (m D a c) (m D b d)) := by
  intro z
  simp only [G_m D G hk hfour]
  rw [G_attenuation_commute_right D G hk hfour b z,
    G_attenuation_commute_right D G hk hfour c z]
  ring

theorem observed_medial (D : Contract V) (G : V → V → ℝ)
    (hk : LocalKernel D G) (hfour : RawGramGeometry.GramNonnegative G 4) :
    ObservedMedial D := by
  intro a b c d
  exact gramEq_observationalEq D G hk hfour (gram_medial D G hk hfour a b c d)

/-- Square-swap and the derived kernel mixer identity force conservation. -/
theorem pair_conserved (D : Contract V) (G : V → V → ℝ)
    (hk : LocalKernel D G) (hfour : RawGramGeometry.GramNonnegative G 4) :
    PairConserved D := by
  intro x y
  have hsq := D.square (x, y)
  rw [operation_eq D x y] at hsq
  have hy : m D (m D x y) (m D y x) = y := congrArg Prod.fst hsq
  have hx : m D (m D y x) (m D x y) = x := by
    simpa only [second_eq_reverse D] using congrArg Prod.snd hsq
  have hu := G_m D G hk hfour x y (m D x y)
  have hv := G_m D G hk hfour y x (m D y x)
  have hxx := G_m D G hk hfour (m D y x) (m D x y) x
  have hyy := G_m D G hk hfour (m D x y) (m D y x) y
  rw [hx] at hxx
  rw [hy] at hyy
  rw [hk.symmetric (m D y x) (B D x), B_adjoint D G hk x (m D y x),
    hk.symmetric (m D x y) (A D x), hk.adjoint x (m D x y)] at hxx
  rw [hk.symmetric (m D x y) (B D y), B_adjoint D G hk y (m D x y),
    hk.symmetric (m D y x) (A D y), hk.adjoint y (m D y x)] at hyy
  rw [hk.diagonal] at hu hv hxx hyy
  rw [second_eq_reverse D]
  change D.weight (m D x y) + D.weight (m D y x) = D.weight x + D.weight y
  linarith

/-- Local kernel compatibility and four-point positivity recover the actual raw
sparse marginal law, with no sparse test or conservation premise. -/
theorem sparse_of_fourPointPositive (D : Contract V) (G : V → V → ℝ)
    (hk : LocalKernel D G) (hfour : RawGramGeometry.GramNonnegative G 4) :
    SparseMarginalLaw D :=
  sparse_of_conserved_and_observed_medial D (pair_conserved D G hk hfour)
    (observed_medial D G hk hfour)

/-- Positivity, conservation, observed mediality, and the actual sparse law are
all conclusions. No positivity or conservation field is hidden in the contract. -/
theorem conclusions_of_fourPointPositive (D : Contract V) (G : V → V → ℝ)
    (hk : LocalKernel D G) (hfour : RawGramGeometry.GramNonnegative G 4) :
    (∀ x, 0 ≤ D.weight x) ∧ PairConserved D ∧ ObservedMedial D ∧
      SparseMarginalLaw D ∧ RawSparseConservationTests.Tests D := by
  have hn := weight_nonnegative D G hk hfour
  have hc := pair_conserved D G hk hfour
  have hm := observed_medial D G hk hfour
  have hs := sparse_of_conserved_and_observed_medial D hc hm
  exact ⟨hn, hc, hm, hs, RawSparseConservationTests.of_sparse D hs⟩

end

end IDT.QMClosure.RawFourPointGramBridge
