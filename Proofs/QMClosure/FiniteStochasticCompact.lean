import Proofs.QMClosure.FiniteStochasticPeripheral
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice

/-!
# Compact finite stochastic probability models

For a fixed finite state type, row-stochastic kernels, probability initial
distributions and readouts in `[0,1]` form a compact parameter family. Every
fixed-depth prediction, and every finite prediction vector, is continuous.
Consequently a finite window separating every model has a positive uniform
gap. An all-depth strict threshold obstruction also has some finite uniform
window. These are existence statements, without an effective window or gap.

The endpoint bounds supply the compact parameter box used here. This argument
makes no assertion about other compactification methods for unbounded endpoints.
-/

namespace IDT.QMClosure.FiniteStochasticCompact

open Finset Set

variable (S : Type*) [Fintype S] [DecidableEq S]

/-- Kernel, initial distribution and readout coordinates, before constraints. -/
abbrev ParameterData := (Matrix S S ℝ) × (S → ℝ) × (S → ℝ)

/-- Fixed finite stochastic models with probability-valued endpoints. -/
def parameterFamily : Set (ParameterData S) :=
  {x | x.1 ∈ Matrix.rowStochastic ℝ S ∧
    (∀ i, 0 ≤ x.2.1 i) ∧ (∑ i, x.2.1 i) = 1 ∧
    (∀ i, 0 ≤ x.2.2 i) ∧ (∀ i, x.2.2 i ≤ 1)}

/-- Complex-valued notation for the real stochastic probability prediction. -/
noncomputable def modelPrediction (x : ParameterData S) (n : ℕ) : ℂ :=
  ∑ i, (x.2.1 i : ℂ) *
    ((FiniteStochasticPeripheral.complexify x.1) ^ n).mulVec
      (fun j => (x.2.2 j : ℂ)) i

variable {S}

/-- The real row-stochastic matrix carrier is closed. -/
theorem isClosed_rowStochastic :
    IsClosed (Matrix.rowStochastic ℝ S : Set (Matrix S S ℝ)) := by
  have hp : IsClosed {P : Matrix S S ℝ | ∀ i j, 0 ≤ P i j} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le continuous_const (continuous_apply_apply i j)
  have hs : IsClosed {P : Matrix S S ℝ | ∀ i, (∑ j, P i j) = 1} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_eq
      (continuous_finset_sum _ fun j _ => continuous_apply_apply i j) continuous_const
  change IsClosed {P : Matrix S S ℝ | P ∈ Matrix.rowStochastic ℝ S}
  simpa only [Matrix.mem_rowStochastic_iff_sum, Set.setOf_and] using hp.inter hs

/-- Real row-stochastic kernels on a fixed finite state type form a compact set. -/
theorem isCompact_rowStochastic :
    IsCompact (Matrix.rowStochastic ℝ S : Set (Matrix S S ℝ)) := by
  have hbox : IsCompact ((Set.Icc (0 : ℝ) 1).matrix : Set (Matrix S S ℝ)) :=
    isCompact_Icc.matrix
  apply hbox.of_isClosed_subset isClosed_rowStochastic
  intro P hP
  exact fun _ _ => ⟨hP.1 _ _, Matrix.le_one_of_mem_rowStochastic hP⟩

/-- The stochastic, normalization and endpoint inequalities are closed. -/
theorem isClosed_parameterFamily : IsClosed (parameterFamily S) := by
  have hp : IsClosed {x : ParameterData S | ∀ i j, 0 ≤ x.1 i j} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le continuous_const
        ((continuous_apply_apply i j).comp continuous_fst)
  have hs : IsClosed {x : ParameterData S | ∀ i, (∑ j, x.1 i j) = 1} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_eq
      (continuous_finset_sum _ fun j _ =>
        (continuous_apply_apply i j).comp continuous_fst) continuous_const
  have hm : IsClosed {x : ParameterData S | ∀ i, 0 ≤ x.2.1 i} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const
      ((continuous_apply i).comp (continuous_fst.comp continuous_snd))
  have ht : IsClosed {x : ParameterData S | (∑ i, x.2.1 i) = 1} :=
    isClosed_eq (continuous_finset_sum _ fun i _ =>
      (continuous_apply i).comp (continuous_fst.comp continuous_snd)) continuous_const
  have hr₀ : IsClosed {x : ParameterData S | ∀ i, 0 ≤ x.2.2 i} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const
      ((continuous_apply i).comp (continuous_snd.comp continuous_snd))
  have hr₁ : IsClosed {x : ParameterData S | ∀ i, x.2.2 i ≤ 1} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le
      ((continuous_apply i).comp (continuous_snd.comp continuous_snd)) continuous_const
  simpa only [parameterFamily, Matrix.mem_rowStochastic_iff_sum, Set.setOf_and]
    using (hp.inter hs).inter (hm.inter (ht.inter (hr₀.inter hr₁)))

/-- The family is a closed subset of a coordinatewise unit box. -/
theorem isCompact_parameterFamily : IsCompact (parameterFamily S) := by
  have hv : IsCompact (Set.Icc (fun _ : S => (0 : ℝ)) (fun _ => 1)) :=
    isCompact_Icc
  apply (isCompact_rowStochastic.prod (hv.prod hv)).of_isClosed_subset
    isClosed_parameterFamily
  intro x hx
  rcases hx with ⟨hP, hμ, hsum, hr₀, hr₁⟩
  refine ⟨hP, ⟨hμ, ?_⟩, ⟨hr₀, hr₁⟩⟩
  intro i
  calc
    x.2.1 i ≤ ∑ j, x.2.1 j :=
      single_le_sum (fun j _ => hμ j) (mem_univ i)
    _ = 1 := hsum

/-- Fixed-depth predictions depend continuously on every parameter. -/
theorem continuous_modelPrediction (n : ℕ) :
    Continuous (fun x : ParameterData S => modelPrediction S x n) := by
  have hP : Continuous (fun x : ParameterData S =>
      FiniteStochasticPeripheral.complexify x.1) := by
    apply continuous_matrix
    intro i j
    exact Complex.continuous_ofReal.comp
      ((continuous_apply_apply i j).comp continuous_fst)
  have hμ : Continuous (fun x : ParameterData S => fun i => (x.2.1 i : ℂ)) :=
    continuous_pi fun i => Complex.continuous_ofReal.comp
      ((continuous_apply i).comp (continuous_fst.comp continuous_snd))
  have hr : Continuous (fun x : ParameterData S => fun i => (x.2.2 i : ℂ)) :=
    continuous_pi fun i => Complex.continuous_ofReal.comp
      ((continuous_apply i).comp (continuous_snd.comp continuous_snd))
  exact hμ.dotProduct ((hP.pow n).matrix_mulVec hr)

/-- Any prescribed finite vector of preparation-depth predictions is continuous. -/
theorem continuous_finitePredictions (N : ℕ) :
    Continuous (fun x : ParameterData S => fun n : Fin N => modelPrediction S x n) :=
  continuous_pi fun n => continuous_modelPrediction n

/-- A separating nonempty finite window has a strictly positive uniform gap. -/
theorem exists_positive_window_gap (N : ℕ) (hN : 0 < N) (target : ℕ → ℂ)
    (hsep : ∀ x ∈ parameterFamily S,
      ∃ n : ℕ, n < N ∧ modelPrediction S x n ≠ target n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ parameterFamily S,
      ∃ n : ℕ, n < N ∧ δ ≤ ‖modelPrediction S x n - target n‖ := by
  have hne : (range N).Nonempty := nonempty_range_iff.mpr (Nat.ne_of_gt hN)
  let errorMax : ParameterData S → ℝ := fun x =>
    (range N).sup' hne (fun n => ‖modelPrediction S x n - target n‖)
  have hc : Continuous errorMax :=
    Continuous.finset_sup'_apply hne fun n _ =>
      ((continuous_modelPrediction n).sub continuous_const).norm
  have hp : ∀ x ∈ parameterFamily S, 0 < errorMax x := by
    intro x hx
    obtain ⟨n, hn, hdiff⟩ := hsep x hx
    exact (Finset.lt_sup'_iff hne).mpr
      ⟨n, mem_range.mpr hn, norm_pos_iff.mpr (sub_ne_zero.mpr hdiff)⟩
  obtain ⟨δ, hδ, hbound⟩ :=
    isCompact_parameterFamily.exists_forall_le' hc.continuousOn hp
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  obtain ⟨n, hn, hδn⟩ := (Finset.le_sup'_iff hne).mp (hbound x hx)
  exact ⟨n, mem_range.mp hn, hδn⟩

/-- A strict all-depth obstruction has some finite window uniform over the family. -/
theorem exists_finite_threshold_window (target : ℕ → ℂ) (ε : ℝ)
    (hsep : ∀ x ∈ parameterFamily S,
      ∃ n : ℕ, ε < ‖modelPrediction S x n - target n‖) :
    ∃ N : ℕ, ∀ x ∈ parameterFamily S,
      ∃ n : ℕ, n < N ∧ ε < ‖modelPrediction S x n - target n‖ := by
  let U : ℕ → Set (ParameterData S) :=
    fun n => {x | ε < ‖modelPrediction S x n - target n‖}
  have hU : ∀ n, IsOpen (U n) := fun n =>
    isOpen_lt continuous_const ((continuous_modelPrediction n).sub continuous_const).norm
  have hcover : parameterFamily S ⊆ ⋃ n, U n := by
    intro x hx
    obtain ⟨n, hn⟩ := hsep x hx
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨t, ht⟩ := isCompact_parameterFamily.elim_finite_subcover U hU hcover
  refine ⟨t.sup id + 1, ?_⟩
  intro x hx
  obtain ⟨n, hn, herror⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact ⟨n, Nat.lt_succ_of_le (Finset.le_sup (f := id) hn), herror⟩

end IDT.QMClosure.FiniteStochasticCompact
