import Proofs.QMClosure.FiniteRankReadoutFilter

/-!
# Four fixed raw probes and the global translate-rank separation

Four exact translated response values reconstruct each Gaussian-integer source.
The observable state is the image of this nonlinear statistic. Every source
operation therefore induces an operation on observable states, and every source
equivalence induces an observable equivalence.

The imported arithmetic readout has global real translate rank twenty. Thus the
number of coordinates of this injective nonlinear statistic and the dimension
of the global linear translate span measure different mathematical structures.
The statements concern exact raw responses on the integer coordinate carrier.
Normalized probabilities, noise stability, physical reconstruction algorithms,
and universal rank classification require their own hypotheses and artifacts.
-/

namespace IDT.QMClosure.FiniteReadoutTomographyWall

noncomputable section

open FiniteRankReadoutFilter

/-- The four fixed corners, selected independently of the source. -/
def corner : Fin 4 → GaussianPair :=
  ![(0, 0), (1, 0), (0, 1), (1, 1)]

/-- The four exact raw translated responses. -/
def probe (z : GaussianPair) : Fin 4 → ℝ :=
  fun j => readout (z + corner j)

private theorem corner_residue_injective :
    Function.Injective (fun j : Fin 4 => rho (corner j)) := by
  decide

/-- The distinct corner residues allow at most one extinguished probe. -/
theorem zero_residue_probe_unique (z : GaussianPair) (i j : Fin 4)
    (hi : rho (z + corner i) = 0) (hj : rho (z + corner j) = 0) :
    i = j := by
  apply corner_residue_injective
  apply add_left_cancel (a := rho z)
  simpa only [rho_add] using hi.trans hj.symm

/-- A retained residue has a strictly positive squared norm. -/
theorem normSq_pos_of_residue_ne_zero (z : GaussianPair) (hz : rho z ≠ 0) :
    0 < normSq z := by
  by_contra h
  have hn : normSq z ≤ 0 := le_of_not_gt h
  change (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 ≤ 0 at hn
  have hx : (z.1 : ℝ) = 0 := by
    nlinarith [sq_nonneg (z.1 : ℝ), sq_nonneg (z.2 : ℝ)]
  have hy : (z.2 : ℝ) = 0 := by
    nlinarith [sq_nonneg (z.1 : ℝ), sq_nonneg (z.2 : ℝ)]
  have hxInt : z.1 = 0 := by exact_mod_cast hx
  have hyInt : z.2 = 0 := by exact_mod_cast hy
  apply hz
  simp [rho, hxInt, hyInt]

/-- Equality with a positive retained response forces retention on both sides. -/
theorem normSq_eq_of_readout_eq_of_residue_ne_zero (z w : GaussianPair)
    (hz : rho z ≠ 0) (h : readout z = readout w) : normSq z = normSq w := by
  have hp : 0 < readout z := by
    simpa [readout, hz] using normSq_pos_of_residue_ne_zero z hz
  have hw : rho w ≠ 0 := by
    intro hw
    have hwzero : readout w = 0 := by simp [readout, hw]
    rw [h, hwzero] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  simpa [readout, hz, hw] using h

private theorem three_corner_norms_injective (z w : GaussianPair) (missing : Fin 4)
    (h : ∀ j : Fin 4, j ≠ missing →
      normSq (z + corner j) = normSq (w + corner j)) : z = w := by
  have hcoordinates : (z.1 : ℝ) = (w.1 : ℝ) ∧ (z.2 : ℝ) = (w.2 : ℝ) := by
    fin_cases missing
    · have h1 := h 1 (by decide)
      have h2 := h 2 (by decide)
      have h3 := h 3 (by decide)
      norm_num [corner, normSq, Prod.fst_add, Prod.snd_add, Matrix.cons_val_two, Matrix.cons_val_three] at h1 h2 h3
      constructor <;> nlinarith
    · have h0 := h 0 (by decide)
      have h2 := h 2 (by decide)
      have h3 := h 3 (by decide)
      norm_num [corner, normSq, Prod.fst_add, Prod.snd_add, Matrix.cons_val_two, Matrix.cons_val_three] at h0 h2 h3
      constructor <;> nlinarith
    · have h0 := h 0 (by decide)
      have h1 := h 1 (by decide)
      have h3 := h 3 (by decide)
      norm_num [corner, normSq, Prod.fst_add, Prod.snd_add, Matrix.cons_val_two, Matrix.cons_val_three] at h0 h1 h3
      constructor <;> nlinarith
    · have h0 := h 0 (by decide)
      have h1 := h 1 (by decide)
      have h2 := h 2 (by decide)
      norm_num [corner, normSq, Prod.fst_add, Prod.snd_add, Matrix.cons_val_two, Matrix.cons_val_three] at h0 h1 h2
      constructor <;> nlinarith
  apply Prod.ext
  · exact_mod_cast hcoordinates.1
  · exact_mod_cast hcoordinates.2

/-- Four fixed exact raw probes uniquely determine every source pair. -/
theorem probe_injective : Function.Injective probe := by
  intro z w h
  have hretained : ∃ missing : Fin 4, ∀ j : Fin 4, j ≠ missing →
      rho (z + corner j) ≠ 0 := by
    by_cases hz : ∃ i : Fin 4, rho (z + corner i) = 0
    · obtain ⟨i, hi⟩ := hz
      refine ⟨i, ?_⟩
      intro j hji hj
      exact hji (zero_residue_probe_unique z j i hj hi)
    · push Not at hz
      exact ⟨0, fun j _ => hz j⟩
  obtain ⟨missing, hmissing⟩ := hretained
  apply three_corner_norms_injective z w missing
  intro j hj
  exact normSq_eq_of_readout_eq_of_residue_ne_zero
    (z + corner j) (w + corner j) (hmissing j hj) (congrFun h j)

/-- Observable states are precisely realized raw response vectors. -/
abbrev ObservableState := Set.range probe

/-- Encode a source as its realized response vector. -/
def observe (z : GaussianPair) : ObservableState :=
  ⟨probe z, z, rfl⟩

/-- Exact reconstruction on the realized image, using classical choice. -/
def reconstruct (s : ObservableState) : GaussianPair :=
  Classical.choose s.property

theorem probe_reconstruct (s : ObservableState) : probe (reconstruct s) = s.val :=
  Classical.choose_spec s.property

@[simp] theorem reconstruct_observe (z : GaussianPair) : reconstruct (observe z) = z := by
  apply probe_injective
  exact probe_reconstruct (observe z)

@[simp] theorem observe_reconstruct (s : ObservableState) : observe (reconstruct s) = s := by
  apply Subtype.ext
  exact probe_reconstruct s

/-- Each realized response vector has exactly one source. -/
theorem unique_reconstruction (s : ObservableState) : ∃! z, probe z = s.val := by
  refine ⟨reconstruct s, probe_reconstruct s, ?_⟩
  intro z hz
  exact probe_injective (hz.trans (probe_reconstruct s).symm)

/-- The exact raw observable image is equivalent to the full source carrier. -/
def observableEquiv : GaussianPair ≃ ObservableState where
  toFun := observe
  invFun := reconstruct
  left_inv := reconstruct_observe
  right_inv := observe_reconstruct

/-- Any source operation induces an operation on the realized raw observable image. -/
def inducedUpdate (U : GaussianPair → GaussianPair) : ObservableState → ObservableState :=
  fun s => observe (U (reconstruct s))

/-- The induced update exactly factors the source update through observation. -/
@[simp] theorem inducedUpdate_observe (U : GaussianPair → GaussianPair) (z : GaussianPair) :
    inducedUpdate U (observe z) = observe (U z) := by
  simp [inducedUpdate]

theorem inducedUpdate_comp (U V : GaussianPair → GaussianPair) :
    inducedUpdate (U ∘ V) = inducedUpdate U ∘ inducedUpdate V := by
  funext s
  simp [inducedUpdate]

/-- Every source equivalence transports to an equivalence of exact observable states. -/
def inducedEquiv (e : GaussianPair ≃ GaussianPair) : ObservableState ≃ ObservableState where
  toFun := inducedUpdate e
  invFun := inducedUpdate e.symm
  left_inv := by
    intro s
    simp [inducedUpdate]
  right_inv := by
    intro s
    simp [inducedUpdate]

/-- Reversible source translation by an arbitrary integer pair. -/
def shiftEquiv (h : GaussianPair) : GaussianPair ≃ GaussianPair where
  toFun := fun z => z + h
  invFun := fun z => z - h
  left_inv := by intro z; simp
  right_inv := by intro z; simp

/-- Gaussian multiplication by the imaginary unit is reversible on the source carrier. -/
def unitPhaseEquiv : GaussianPair ≃ GaussianPair where
  toFun := gmul (0, 1)
  invFun := gmul (0, -1)
  left_inv := by
    rintro ⟨x, y⟩
    apply Prod.ext <;> simp [gmul]
  right_inv := by
    rintro ⟨x, y⟩
    apply Prod.ext <;> simp [gmul]

theorem induced_shift (h z : GaussianPair) :
    inducedEquiv (shiftEquiv h) (observe z) = observe (z + h) := by
  exact inducedUpdate_observe (shiftEquiv h) z

theorem induced_unit_phase (z : GaussianPair) :
    inducedEquiv unitPhaseEquiv (observe z) = observe (gmul (0, 1) z) := by
  exact inducedUpdate_observe unitPhaseEquiv z

/-- The unit phase moves this explicit source. -/
theorem unit_phase_moves_one : unitPhaseEquiv (1, 0) = (0, 1) := by
  norm_num [unitPhaseEquiv, gmul]

/-- The fixed shift moves this explicit source. -/
theorem shift_moves_zero : shiftEquiv (1, 0) (0, 0) = (1, 0) := by
  simp [shiftEquiv]

/-- This arithmetic control combines exact four-probe reconstruction and global rank twenty. -/
theorem four_probe_translate_rank_separation :
    Function.Injective probe ∧ Module.finrank ℝ (translateSpan readout) = 20 :=
  ⟨probe_injective, translateSpan_finrank_eq_twenty⟩

private theorem residue_zero_iff_divides (z : GaussianPair) :
    rho z = 0 ↔ (5 : ℤ) ∣ z.1 - 2 * z.2 := by
  have hcast : rho z = ((z.1 - 2 * z.2 : ℤ) : ZMod 5) := by
    simp [rho]
  rw [hcast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num

/-- Ordinary equal-half averaging of the two exact raw response vectors. -/
def meanProbe (z w : GaussianPair) : Fin 4 → ℝ :=
  fun j => (probe z j + probe w j) / 2

/-- First explicit pair has constant-one averaged responses. -/
theorem meanProbe_first_pair : meanProbe (0, 0) (-1, -1) = fun _ => 1 := by
  funext j
  fin_cases j <;>
    norm_num [meanProbe, probe, corner, readout, residue_zero_iff_divides, normSq]

/-- Second explicit pair has the same constant-one averaged responses. -/
theorem meanProbe_second_pair : meanProbe (-1, 0) (0, -1) = fun _ => 1 := by
  funext j
  fin_cases j <;>
    norm_num [meanProbe, probe, corner, readout, residue_zero_iff_divides, normSq]

theorem equal_meanProbes :
    meanProbe (0, 0) (-1, -1) = meanProbe (-1, 0) (0, -1) :=
  meanProbe_first_pair.trans meanProbe_second_pair.symm

/-- Translating both sources in the first pair gives this exact averaged vector. -/
theorem shifted_meanProbe_first_pair :
    meanProbe ((0, 0) + (1, 0)) ((-1, -1) + (1, 0)) = ![1, 3, 1, 1 / 2] := by
  funext j
  fin_cases j <;>
    norm_num [meanProbe, probe, corner, readout, residue_zero_iff_divides, normSq]

/-- Translating both sources in the second pair gives this exact averaged vector. -/
theorem shifted_meanProbe_second_pair :
    meanProbe ((-1, 0) + (1, 0)) ((0, -1) + (1, 0)) = ![1, 3, 1, 3] := by
  funext j
  fin_cases j <;>
    norm_num [meanProbe, probe, corner, readout, residue_zero_iff_divides, normSq]

/-- Equal averaged raw responses can separate under one fixed source translation. -/
theorem shifted_meanProbes_ne :
    meanProbe ((0, 0) + (1, 0)) ((-1, -1) + (1, 0)) ≠
      meanProbe ((-1, 0) + (1, 0)) ((0, -1) + (1, 0)) := by
  rw [shifted_meanProbe_first_pair, shifted_meanProbe_second_pair]
  intro h
  have h3 := congrFun h 3
  norm_num [Matrix.cons_val_three] at h3

/-- Four averaged raw responses admit no update reproducing this translation on every pair.
The averaging is a mathematical operation on vectors. Physical realization of these
averages requires an additional semantic interpretation. -/
theorem no_meanProbe_translation_update :
    ¬ ∃ F : (Fin 4 → ℝ) → (Fin 4 → ℝ),
      ∀ z w : GaussianPair,
        F (meanProbe z w) = meanProbe (z + (1, 0)) (w + (1, 0)) := by
  rintro ⟨F, hF⟩
  have h := congrArg F equal_meanProbes
  rw [hF (0, 0) (-1, -1), hF (-1, 0) (0, -1)] at h
  exact shifted_meanProbes_ne h

end

end IDT.QMClosure.FiniteReadoutTomographyWall
