import Proofs.QMClosure.BoundedFibrePowerEnvelope

/-! An ordinary classical reference-fibre control on four nonnegative coordinates.
Two bounded normalized marginal fibres have nonzero, disjoint difference spans.
Each branch satisfies the published marginal-fibre power-envelope contract on
its own span. The positive branches sum to the identity on the ambient carrier.
The four coordinate readouts separate tables, and the fibre spans describe
ordinary reference variation. A full operational reconstruction or countermodel
requires additional data beyond this finite control. -/

namespace IDT.QMClosure.ClassicalSeparateFibreControl

open Set BoundedFibrePowerEnvelope

abbrev Row := ℝ × ℝ
abbrev State := Row × Row

/-- Elementary row-and-column coordinate readouts on the classical table. -/
def productReadout (row column : Bool) : State →ₗ[ℝ] ℝ where
  toFun v := if row then (if column then v.2.2 else v.2.1)
    else (if column then v.1.2 else v.1.1)
  map_add' := by intro v w; cases row <;> cases column <;> rfl
  map_smul' := by intro r v; cases row <;> cases column <;> rfl

theorem product_readouts_separate {v w : State}
    (h : ∀ row column, productReadout row column v = productReadout row column w) :
    v = w := by
  exact Prod.ext (Prod.ext (h false false) (h false true))
    (Prod.ext (h true false) (h true true))

/-- A table deviation invisible to every coordinate readout is zero. -/
theorem product_invisible_zero {v : State}
    (h : ∀ row column, productReadout row column v = 0) : v = 0 := by
  apply product_readouts_separate
  intro row column
  simpa using h row column

def cone : Set State :=
  {v | 0 ≤ v.1.1 ∧ 0 ≤ v.1.2 ∧ 0 ≤ v.2.1 ∧ 0 ≤ v.2.2}

def marginal : State →ₗ[ℝ] Row where
  toFun v := (v.1.1 + v.1.2, v.2.1 + v.2.2)
  map_add' := by intro v w; ext <;> dsimp <;> ring
  map_smul' := by intro r v; ext <;> dsimp <;> ring

noncomputable def diagonal (u v : ℝ) : State →L[ℝ] State :=
  ({ toFun := fun x => ((u * x.1.1, u * x.1.2), (v * x.2.1, v * x.2.2))
     map_add' := by intro x y; ext <;> dsimp <;> ring
     map_smul' := by intro r x; ext <;> dsimp <;> ring } :
    State →ₗ[ℝ] State).toContinuousLinearMap

def localDiagonal (u v : ℝ) : Row →ₗ[ℝ] Row where
  toFun x := (u * x.1, v * x.2)
  map_add' := by intro x y; ext <;> dsimp <;> ring
  map_smul' := by intro r x; ext <;> dsimp <;> ring

noncomputable def q : ℝ := 1 / 4
def c : ℝ := 1
noncomputable def a : ℝ := 3 / 4

theorem q_pos : 0 < q := by norm_num [q]

theorem a_gt_q : q < a := by norm_num [a, q]

theorem a_nonneg : 0 ≤ a := q_pos.le.trans a_gt_q.le

noncomputable def branchA : State →L[ℝ] State := diagonal q a
noncomputable def branchB : State →L[ℝ] State := diagonal a q
noncomputable def localA : Row →ₗ[ℝ] Row := localDiagonal q a
noncomputable def localB : Row →ₗ[ℝ] Row := localDiagonal a q

theorem cone_scale (r : ℝ) (hr : 0 ≤ r) (v : State) (hv : v ∈ cone) :
    r • v ∈ cone := by
  exact ⟨mul_nonneg hr hv.1, mul_nonneg hr hv.2.1,
    mul_nonneg hr hv.2.2.1, mul_nonneg hr hv.2.2.2⟩

theorem diagonal_positive {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    MapsTo (diagonal u v) cone cone := by
  intro x hx
  exact ⟨mul_nonneg hu hx.1, mul_nonneg hu hx.2.1,
    mul_nonneg hv hx.2.2.1, mul_nonneg hv hx.2.2.2⟩

theorem branchA_positive : MapsTo branchA cone cone := diagonal_positive q_pos.le a_nonneg
theorem branchB_positive : MapsTo branchB cone cone := diagonal_positive a_nonneg q_pos.le

theorem diagonal_natural (u v : ℝ) :
    marginal.comp (diagonal u v).toLinearMap = (localDiagonal u v).comp marginal := by
  ext <;> dsimp [marginal, diagonal, localDiagonal] <;> ring

theorem branchA_natural : marginal.comp branchA.toLinearMap = localA.comp marginal :=
  diagonal_natural q a

theorem branchB_natural : marginal.comp branchB.toLinearMap = localB.comp marginal :=
  diagonal_natural a q

theorem localA_endpoint : localA (1, 0) = q • (1, 0) := by
  ext <;> simp [localA, localDiagonal]

theorem localB_endpoint : localB (0, 1) = q • (0, 1) := by
  ext <;> simp [localB, localDiagonal]

theorem branches_complement : branchA + branchB = c • (1 : State →L[ℝ] State) := by
  ext <;> dsimp [branchA, branchB, diagonal, a, c, q] <;> ring

theorem branches_sum_identity : branchA + branchB = (1 : State →L[ℝ] State) := by
  simpa [c] using branches_complement

def K0 : Set State := marginalFibre cone marginal (1, 0)
def K1 : Set State := marginalFibre cone marginal (0, 1)
noncomputable def H0 : Submodule ℝ State := fibreSpan K0
noncomputable def H1 : Submodule ℝ State := fibreSpan K1

/-- The first fibre is a normalized segment with the second row zero. -/
theorem fibre0_constraints {v : State} (hv : v ∈ K0) :
    0 ≤ v.1.1 ∧ v.1.1 ≤ 1 ∧ 0 ≤ v.1.2 ∧ v.1.2 ≤ 1 ∧ v.2 = 0 := by
  have hs : v.1.1 + v.1.2 = 1 := congrArg Prod.fst hv.2
  have hz : v.2.1 + v.2.2 = 0 := congrArg Prod.snd hv.2
  rcases hv.1 with ⟨h00, h01, h10, h11⟩
  refine ⟨h00, by linarith, h01, by linarith, ?_⟩
  exact Prod.ext (show v.2.1 = 0 by linarith) (show v.2.2 = 0 by linarith)

/-- The second fibre is a normalized segment with the first row zero. -/
theorem fibre1_constraints {v : State} (hv : v ∈ K1) :
    0 ≤ v.2.1 ∧ v.2.1 ≤ 1 ∧ 0 ≤ v.2.2 ∧ v.2.2 ≤ 1 ∧ v.1 = 0 := by
  have hs : v.2.1 + v.2.2 = 1 := congrArg Prod.snd hv.2
  have hz : v.1.1 + v.1.2 = 0 := congrArg Prod.fst hv.2
  rcases hv.1 with ⟨h00, h01, h10, h11⟩
  refine ⟨h10, by linarith, h11, by linarith, ?_⟩
  exact Prod.ext (show v.1.1 = 0 by linarith) (show v.1.2 = 0 by linarith)

theorem K0_bounded : Bornology.IsBounded K0 := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1, fun v hv => ?_⟩
  rcases fibre0_constraints hv with ⟨h00, h00le, h01, h01le, hz⟩
  rw [Prod.norm_def, hz, norm_zero, Prod.norm_def]
  exact max_le (max_le (by simpa [Real.norm_eq_abs, abs_of_nonneg h00] using h00le)
    (by simpa [Real.norm_eq_abs, abs_of_nonneg h01] using h01le)) (by norm_num)

theorem K1_bounded : Bornology.IsBounded K1 := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1, fun v hv => ?_⟩
  rcases fibre1_constraints hv with ⟨h10, h10le, h11, h11le, hz⟩
  rw [Prod.norm_def, hz, norm_zero, Prod.norm_def]
  exact max_le (by norm_num)
    (max_le (by simpa [Real.norm_eq_abs, abs_of_nonneg h10] using h10le)
      (by simpa [Real.norm_eq_abs, abs_of_nonneg h11] using h11le))

def d0 : State := ((1, -1), (0, 0))
def d1 : State := ((0, 0), (1, -1))

theorem d0_mem : d0 ∈ H0 := by
  apply Submodule.subset_span
  refine ⟨((1, 0), (0, 0)), ?_, ((0, 1), (0, 0)), ?_, ?_⟩
  · norm_num [K0, marginalFibre, cone, marginal]
  · norm_num [K0, marginalFibre, cone, marginal]
  · ext <;> norm_num [d0]

theorem d1_mem : d1 ∈ H1 := by
  apply Submodule.subset_span
  refine ⟨((0, 0), (1, 0)), ?_, ((0, 0), (0, 1)), ?_, ?_⟩
  · norm_num [K1, marginalFibre, cone, marginal]
  · norm_num [K1, marginalFibre, cone, marginal]
  · ext <;> norm_num [d1]

theorem d0_nonzero : d0 ≠ 0 := by simp [d0]
theorem d1_nonzero : d1 ≠ 0 := by simp [d1]

theorem H0_second_row_zero {v : State} (hv : v ∈ H0) : v.2 = 0 := by
  have hle : H0 ≤ LinearMap.ker (LinearMap.snd ℝ Row Row) := by
    apply Submodule.span_le.mpr
    rintro z ⟨v, hv, w, hw, rfl⟩
    change v.2 - w.2 = 0
    rw [(fibre0_constraints hv).2.2.2.2, (fibre0_constraints hw).2.2.2.2, sub_self]
  exact hle hv

theorem H1_first_row_zero {v : State} (hv : v ∈ H1) : v.1 = 0 := by
  have hle : H1 ≤ LinearMap.ker (LinearMap.fst ℝ Row Row) := by
    apply Submodule.span_le.mpr
    rintro z ⟨v, hv, w, hw, rfl⟩
    change v.1 - w.1 = 0
    rw [(fibre1_constraints hv).2.2.2.2, (fibre1_constraints hw).2.2.2.2, sub_self]
  exact hle hv

/-- The two nonzero reference difference spans have zero intersection. -/
theorem fibre_spans_intersection : H0 ⊓ H1 = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  change v = 0
  exact Prod.ext (H1_first_row_zero hv.2) (H0_second_row_zero hv.1)

/-- The published marginal contract derives the first branch's envelope on H0. -/
theorem branchA_fibre_envelope :
    (∀ v ∈ H0, branchA v ∈ H0) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ∀ v ∈ H0,
        ‖(branchA ^ n) v‖ ≤ M * q ^ n * ‖v‖ := by
  exact bounded_marginal_fibre_power_envelope cone marginal (1, 0) branchA localA
    q q_pos cone_scale branchA_positive branchA_natural localA_endpoint K0_bounded

/-- The published marginal contract derives the second branch's envelope on H1. -/
theorem branchB_fibre_envelope :
    (∀ v ∈ H1, branchB v ∈ H1) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ∀ v ∈ H1,
        ‖(branchB ^ n) v‖ ≤ M * q ^ n * ‖v‖ := by
  exact bounded_marginal_fibre_power_envelope cone marginal (0, 1) branchB localB
    q q_pos cone_scale branchB_positive branchB_natural localB_endpoint K1_bounded

end IDT.QMClosure.ClassicalSeparateFibreControl
