import Proofs.QMClosure.NativeSignedAccounting
import Proofs.QMClosure.NativeSignedPhaseVariation
import Proofs.QMClosure.NativeProbabilityUniqueness

/-!
# Selection by bounded signed variation on literal native refinements

The five signed accounting fields do not assume nonnegativity. Eventwise
bounded total variation on the selected leaves of actual native trees forces
halving; the signed Gaussian theorem then selects the quadratic readout and
only afterwards supplies nonnegativity. Every other output wire is retained.
This is conditional mathematical selection, not physical actualization or QM
closure.
-/

namespace IDT.QMClosure.NativeSignedVariationSelection

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily NativeBinaryLeaves
open NativeBinaryRefinement NativeSignedAccounting
open scoped BigOperators
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def signedLeafProbability (L : SignedLaw) (s : ι) (c : Native ι) (i : ι) (n : ℕ) (w : Leaf n) : ℝ :=
  L.prob (sourceAt s n) (tree c i n) (leafPort i n w)

theorem child_probability_sum (L : SignedLaw) (s : ι) (c : Native ι) (i : ι)
    (n : ℕ) (w : Leaf n) :
    signedLeafProbability L s c i (n + 1) (w, false) +
      signedLeafProbability L s c i (n + 1) (w, true) = signedLeafProbability L s c i n w := by
  have h := NativeSignedAccounting.appendPairs_child_sum L (.inl (sourceAt s n)) (leafPort i n)
    (leafPort_injective i n) (padCircuit (Leaf n) (tree c i n))
    (Finset.univ : Finset (Leaf n)).toList (Finset.nodup_toList _) w (by simp)
  simpa [signedLeafProbability, tree, sourceAt, leafPort, L.vacuum,
    NativeSignedAccounting.vacuum_probability_zero] using h

theorem total_leaf_probability (L : SignedLaw) (s : ι) (c : Native ι) (i : ι) (n : ℕ) :
    (∑ w : Leaf n, signedLeafProbability L s c i n w) = L.prob s c i := by
  induction n with
  | zero => simp [Leaf, signedLeafProbability, sourceAt, tree, leafPort]; rfl
  | succ n ih =>
      change (∑ w : Leaf n × Bool, signedLeafProbability L s c i (n + 1) w) = _
      simp only [Fintype.sum_prod_type, Fintype.sum_bool]
      simpa [add_comm, child_probability_sum] using ih

theorem rootA_probability (L : SignedLaw) (s : ι) (c : Native ι) (i : ι) (n : ℕ) :
    (∑ w : Leaf n, signedLeafProbability L s c i (n + 1) (rootA n w)) =
      signedLeafProbability L s c i 1 (PUnit.unit, false) := by
  induction n with
  | zero => simp [Leaf, rootA]
  | succ n ih =>
      change (∑ w : Leaf n × Bool,
        signedLeafProbability L s c i (n + 2) (rootA (n + 1) w)) = _
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, rootA]
      simpa [add_comm, child_probability_sum] using ih


theorem leaf_probability_phase_eq (L : SignedLaw) (s : ι) (c : Native ι) (i : ι)
    (n : ℕ) (u v : Leaf n) (hphase : phase n u = phase n v) :
    signedLeafProbability L s c i n u = signedLeafProbability L s c i n v := by
  apply NativeSignedAccounting.equal_coordinate_probabilities
  rw [leaf_amplitude, leaf_amplitude, hphase]

/-- Representatives are chosen from actual finite output fibres; empty fibres get zero. -/
def signedPhaseProbability (L : SignedLaw) (s : ι) (c : Native ι) (i : ι) (n : ℕ) (j : Fin 4) : ℝ :=
  if h : ∃ w : Leaf n, phase n w = j then
    signedLeafProbability L s c i n (Classical.choose h)
  else 0


theorem signedPhaseProbability_at_leaf (L : SignedLaw) (s : ι) (c : Native ι) (i : ι)
    (n : ℕ) (w : Leaf n) :
    signedPhaseProbability L s c i n (phase n w) = signedLeafProbability L s c i n w := by
  have hex : ∃ v : Leaf n, phase n v = phase n w := ⟨w, rfl⟩
  unfold signedPhaseProbability
  rw [dif_pos hex]
  exact leaf_probability_phase_eq L s c i n _ w (Classical.choose_spec hex)

/-- Both counted sums concern the same root-first native refinement circuit. -/
theorem counted_native_masses (L : SignedLaw) (s : ι) (c : Native ι) (i : ι) (n : ℕ) :
    (∑ j, (NativeBinaryPhaseCounting.phaseCount (n + 1) j : ℝ) *
        signedPhaseProbability L s c i (n + 1) j) = L.prob s c i ∧
    (∑ j, (NativeBinaryPhaseCounting.phaseCount n j : ℝ) *
        signedPhaseProbability L s c i (n + 1) j) =
      signedLeafProbability L s c i 1 (PUnit.unit, false) := by
  constructor
  · rw [← sum_by_phase]
    simp only [signedPhaseProbability_at_leaf]
    exact total_leaf_probability L s c i (n + 1)
  · rw [← sum_by_phase]
    calc
      _ = ∑ w : Leaf n,
          signedPhaseProbability L s c i (n + 1) (phase (n + 1) (rootA n w)) := by
            simp only [rootA_phase]
      _ = ∑ w : Leaf n, signedLeafProbability L s c i (n + 1) (rootA n w) := by
            simp only [signedPhaseProbability_at_leaf]
      _ = _ := rootA_probability L s c i n

/-- Total variation only on the selected descendants; all output wires remain. -/
def selectedVariation (L : SignedLaw) (s : ι) (c : Native ι) (i : ι) (k : ℕ) : ℝ :=
  ∑ w : Leaf (4 * k + 1), |signedLeafProbability L s c i (4 * k + 1) w|

theorem selectedVariation_by_phase (L : SignedLaw) (s : ι) (c : Native ι) (i : ι)
    (k : ℕ) : selectedVariation L s c i k =
      ∑ j, (NativeBinaryPhaseCounting.phaseCount (4 * k + 1) j : ℝ) *
        |signedPhaseProbability L s c i (4 * k + 1) j| := by
  rw [← sum_by_phase]
  simp only [signedPhaseProbability_at_leaf, selectedVariation]

/-- The bound may depend on the initial event, but not on refinement depth or
the number of added vacuum wires. Separate finite bounds for each apparatus
width are insufficient; no finite experiment establishes this all-depth premise. -/
def EventwiseBoundedVariation (L : SignedLaw) : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) (i : ι),
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → selectedVariation L s c i k ≤ C

/-- Exact finite bound from one actual refinement depth; no positivity premise. -/
theorem native_finite_refinement_variation_bound (L : SignedLaw)
    (s : ι) (c : Native ι) (i : ι) (k : ℕ) (hk : 1 ≤ k) :
    2 * ((4 : ℝ)^k - 1) *
      |L.prob (.inl s) (split c i) (.inl i) - L.prob s c i / 2| ≤
      selectedVariation L s c i k := by
  obtain ⟨hp, hr⟩ := counted_native_masses L s c i (4 * k)
  have h := NativeSignedPhaseVariation.mass_deviation_mul_bound k hk
    (signedPhaseProbability L s c i (4 * k + 1)) (L.prob s c i)
    (signedLeafProbability L s c i 1 (PUnit.unit, false)) hp hr
  rw [selectedVariation_by_phase]
  simpa only [signedLeafProbability, sourceAt, leafPort, tree_one_eq_split,
    NativeSignedPhaseVariation.variation, NativeBinaryPhaseCounting.realCount] using h

theorem native_vacuum_split_halves_of_bounded_variation (L : SignedLaw)
    (hbounded : EventwiseBoundedVariation L) (s : ι) (c : Native ι) (i : ι) :
    L.prob (.inl s) (split c i) (.inl i) = L.prob s c i / 2 := by
  obtain ⟨C, hC⟩ := hbounded s c i
  have h := NativeSignedPhaseVariation.phase_count_mass_halving_of_bounded_variation
    (L.prob s c i) (signedLeafProbability L s c i 1 (PUnit.unit, false)) C (by
      intro k hk
      refine ⟨signedPhaseProbability L s c i (4 * k + 1), ?_, ?_, ?_⟩
      · exact (counted_native_masses L s c i (4 * k)).1
      · exact (counted_native_masses L s c i (4 * k)).2
      · simpa only [NativeSignedPhaseVariation.variation,
          NativeBinaryPhaseCounting.realCount, selectedVariation_by_phase] using hC k hk)
  simpa only [signedLeafProbability, sourceAt, leafPort, tree_one_eq_split] using h

def boundedVariation_toSignedHalvingLaw (L : SignedLaw)
    (hbounded : EventwiseBoundedVariation L) : SignedHalvingLaw where
  toSignedLaw := L
  split_halves := native_vacuum_split_halves_of_bounded_variation L hbounded

theorem probability_eq_normSq_of_bounded_variation (L : SignedLaw)
    (hbounded : EventwiseBoundedVariation L) (s : ι) (c : Native ι) (i : ι) :
    L.prob s c i = Complex.normSq (c.eval (source s) i) :=
  NativeProbabilityUniqueness.signedHalving_probability_eq_normSq
    (boundedVariation_toSignedHalvingLaw L hbounded) s c i

/-- Nonnegativity is obtained only after the signed selection theorem. -/
theorem nonnegative_of_bounded_variation (L : SignedLaw)
    (hbounded : EventwiseBoundedVariation L) (s : ι) (c : Native ι) (i : ι) :
    0 ≤ L.prob s c i := by
  rw [probability_eq_normSq_of_bounded_variation L hbounded]
  exact Complex.normSq_nonneg _

def boundedVariation_toLaw (L : SignedLaw) (hbounded : EventwiseBoundedVariation L) :
    Law where
  prob := L.prob
  nonnegative := nonnegative_of_bounded_variation L hbounded
  normalized := L.normalized
  prepared_eq := L.prepared_eq
  output_perm := L.output_perm
  spectator_pair := L.spectator_pair
  vacuum := L.vacuum

@[simp] theorem boundedVariation_toLaw_prob (L : SignedLaw)
    (hbounded : EventwiseBoundedVariation L) (s : ι) (c : Native ι) (i : ι) :
    (boundedVariation_toLaw L hbounded).prob s c i = L.prob s c i := rfl

theorem boundedVariation_toLaw_entire_prob (L : SignedLaw)
    (hbounded : EventwiseBoundedVariation L) :
    @Law.prob (boundedVariation_toLaw L hbounded) = @SignedLaw.prob L := rfl

/-- The original positive contract implies this alternative bounded contract. -/
theorem ofLaw_eventwiseBoundedVariation (L : Law) :
    EventwiseBoundedVariation (ofLaw L).toSignedLaw := by
  intro ι _ _ s c i
  refine ⟨L.prob s c i, ?_⟩
  intro k _
  have he : selectedVariation (ofLaw L).toSignedLaw s c i k =
      ∑ w : Leaf (4 * k + 1),
        signedLeafProbability (ofLaw L).toSignedLaw s c i (4 * k + 1) w := by
    apply Finset.sum_congr rfl
    intro w _
    exact abs_of_nonneg (L.nonnegative _ _ _)
  rw [he, total_leaf_probability]
  exact le_refl _

end
end IDT.QMClosure.NativeSignedVariationSelection
