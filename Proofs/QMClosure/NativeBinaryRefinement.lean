import Proofs.QMClosure.NativeVacuumProbabilityFamily
import Proofs.QMClosure.NativeBinaryPhaseCounting
import Proofs.QMClosure.NativeBinaryLeaves

/-!
# Literal binary refinement of one selected native output

Every level appends fresh zero-input wires and actual disjoint pair gates.
All wires remain in the output. Probability conservation is derived from the
supplied family contract, and equal-phase probabilities from equality of the
complete prepared state under a swap. No probability on an abstract refinement
tree is supplied as an additional primitive.
-/

namespace IDT.QMClosure.NativeBinaryRefinement

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
open MixerGeneratedProcessWall NativeVacuumProbabilityFamily NativeBinaryLeaves
open scoped BigOperators

variable {ι τ : Type} [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]

def branchPair (f : τ → ι) (t : τ) : Native (ι ⊕ τ) :=
  .pair (.inl (f t)) (.inr t) (by simp)

/-- The list fixes a literal circuit order; no parallel-gate primitive is used. -/
def appendPairs (f : τ → ι) (c : Native (ι ⊕ τ)) : List τ → Native (ι ⊕ τ)
  | [] => c
  | t :: ts => appendPairs f (.seq c (branchPair f t)) ts

omit [Fintype ι] [Fintype τ] in
theorem appendPairs_eval_untouched (f : τ → ι) (c : Native (ι ⊕ τ))
    (ts : List τ) (w : ι ⊕ τ)
    (h : ∀ t ∈ ts, w ≠ .inl (f t) ∧ w ≠ .inr t) (x : ι ⊕ τ → ℂ) :
    (appendPairs f c ts).eval x w = c.eval x w := by
  induction ts generalizing c with
  | nil => rfl
  | cons t ts ih =>
      rw [appendPairs, ih _ (fun u hu => h u (List.mem_cons_of_mem t hu))]
      have ht := h t (by simp)
      simp [branchPair, Circuit.eval, pairGate, pairReplace, ht.1, ht.2]

theorem appendPairs_probability_untouched (L : Law) (s : ι ⊕ τ)
    (f : τ → ι) (c : Native (ι ⊕ τ)) (ts : List τ) (w : ι ⊕ τ)
    (h : ∀ t ∈ ts, w ≠ .inl (f t) ∧ w ≠ .inr t) :
    L.prob s (appendPairs f c ts) w = L.prob s c w := by
  induction ts generalizing c with
  | nil => rfl
  | cons t ts ih =>
      rw [appendPairs, ih _ (fun u hu => h u (List.mem_cons_of_mem t hu))]
      have ht := h t (by simp)
      exact L.spectator_pair s c (.inl (f t)) (.inr t) w (by simp) ht.1 ht.2

theorem appendPairs_child_sum (L : Law) (s : ι ⊕ τ) (f : τ → ι)
    (hf : Function.Injective f) (c : Native (ι ⊕ τ)) (ts : List τ)
    (hn : ts.Nodup) (t : τ) (ht : t ∈ ts) :
    L.prob s (appendPairs f c ts) (.inl (f t)) +
      L.prob s (appendPairs f c ts) (.inr t) =
      L.prob s c (.inl (f t)) + L.prob s c (.inr t) := by
  induction ts generalizing c with
  | nil => simp at ht
  | cons u us ih =>
      have hnu : u ∉ us := (List.nodup_cons.mp hn).1
      have hns : us.Nodup := (List.nodup_cons.mp hn).2
      by_cases hut : u = t
      · subst u
        have hleft : ∀ v ∈ us, (Sum.inl (f t) : ι ⊕ τ) ≠ .inl (f v) ∧
            (Sum.inl (f t) : ι ⊕ τ) ≠ .inr v := by
          intro v hv
          constructor
          · intro he
            have htv : t = v := hf (Sum.inl.inj he)
            exact hnu (htv.symm ▸ hv)
          · simp
        have hright : ∀ v ∈ us, (Sum.inr t : ι ⊕ τ) ≠ .inl (f v) ∧
            (Sum.inr t : ι ⊕ τ) ≠ .inr v := by
          intro v hv
          constructor
          · simp
          · intro he
            exact hnu ((Sum.inr.inj he).symm ▸ hv)
        simp only [appendPairs,
          appendPairs_probability_untouched L s f _ us _ hleft,
          appendPairs_probability_untouched L s f _ us _ hright]
        exact pair_probability_sum L s c _ _ (by simp)
      · have htu : t ≠ u := Ne.symm hut
        have hmem : t ∈ us := (List.mem_cons.mp ht).resolve_left htu
        rw [appendPairs, ih _ hns hmem]
        have hftu : f t ≠ f u := fun he => htu (hf he)
        simp only [branchPair]
        rw [L.spectator_pair s c (.inl (f u)) (.inr u) (.inl (f t))
          (by simp) (by simpa using hftu) (by simp),
          L.spectator_pair s c (.inl (f u)) (.inr u) (.inr t)
          (by simp) (by simp) (by simpa using htu)]

omit [Fintype ι] [Fintype τ] in
theorem appendPairs_child_amplitudes (f : τ → ι) (hf : Function.Injective f)
    (c : Native (ι ⊕ τ)) (ts : List τ) (hn : ts.Nodup) (t : τ) (ht : t ∈ ts)
    (x : ι ⊕ τ → ℂ) :
    (appendPairs f c ts).eval x (.inl (f t)) =
        NativeAttenuationCircuit.a * c.eval x (.inl (f t)) +
          NativeAttenuationCircuit.b * c.eval x (.inr t) ∧
    (appendPairs f c ts).eval x (.inr t) =
        NativeAttenuationCircuit.b * c.eval x (.inl (f t)) +
          NativeAttenuationCircuit.a * c.eval x (.inr t) := by
  induction ts generalizing c with
  | nil => simp at ht
  | cons u us ih =>
      have hnu : u ∉ us := (List.nodup_cons.mp hn).1
      have hns : us.Nodup := (List.nodup_cons.mp hn).2
      by_cases hut : u = t
      · subst u
        have hleft : ∀ v ∈ us, (Sum.inl (f t) : ι ⊕ τ) ≠ .inl (f v) ∧
            (Sum.inl (f t) : ι ⊕ τ) ≠ .inr v := by
          intro v hv
          constructor
          · intro he
            exact hnu ((hf (Sum.inl.inj he)).symm ▸ hv)
          · simp
        have hright : ∀ v ∈ us, (Sum.inr t : ι ⊕ τ) ≠ .inl (f v) ∧
            (Sum.inr t : ι ⊕ τ) ≠ .inr v := by
          intro v hv
          constructor
          · simp
          · intro he
            exact hnu ((Sum.inr.inj he).symm ▸ hv)
        simp only [appendPairs,
          appendPairs_eval_untouched f _ us _ hleft x,
          appendPairs_eval_untouched f _ us _ hright x]
        constructor <;> simp [branchPair, Circuit.eval, pairGate, pairReplace,
          NativeAttenuationCircuit.mixer_fst, NativeAttenuationCircuit.mixer_snd]
      · have htu : t ≠ u := Ne.symm hut
        have hmem : t ∈ us := (List.mem_cons.mp ht).resolve_left htu
        have hftu : f t ≠ f u := fun he => htu (hf he)
        have h := ih (.seq c (branchPair f u)) hns hmem
        simpa [appendPairs, branchPair, Circuit.eval, pairGate, pairReplace,
          hftu, htu] using h

def Wire (ι : Type) : ℕ → Type
  | 0 => ι
  | n + 1 => Wire ι n ⊕ Leaf n

instance wireFintype (n : ℕ) : Fintype (Wire ι n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype ι)
  | succ n ih => letI := ih; exact inferInstanceAs (Fintype (Wire ι n ⊕ Leaf n))

instance wireDecidableEq (n : ℕ) : DecidableEq (Wire ι n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq ι)
  | succ n ih => letI := ih; exact inferInstanceAs (DecidableEq (Wire ι n ⊕ Leaf n))

def sourceAt (s : ι) : (n : ℕ) → Wire ι n
  | 0 => s
  | n + 1 => .inl (sourceAt s n)

def leafPort (i : ι) : (n : ℕ) → Leaf n → Wire ι n
  | 0, _ => i
  | n + 1, (w, false) => .inl (leafPort i n w)
  | _ + 1, (w, true) => .inr w

omit [Fintype ι] [DecidableEq ι] in
theorem leafPort_injective (i : ι) (n : ℕ) : Function.Injective (leafPort i n) := by
  induction n with
  | zero => intro x y _; exact @Subsingleton.elim PUnit _ x y
  | succ n ih =>
      rintro ⟨x, bx⟩ ⟨y, byy⟩ h
      cases bx <;> cases byy
      · exact Prod.ext (ih (Sum.inl.inj h)) rfl
      · cases h
      · cases h
      · exact Prod.ext (Sum.inr.inj h) rfl

def tree (c : Native ι) (i : ι) : (n : ℕ) → Native (Wire ι n)
  | 0 => c
  | n + 1 => appendPairs (leafPort i n) (padCircuit (Leaf n) (tree c i n))
      (Finset.univ : Finset (Leaf n)).toList

def leafProbability (L : Law) (s : ι) (c : Native ι) (i : ι) (n : ℕ) (w : Leaf n) : ℝ :=
  L.prob (sourceAt s n) (tree c i n) (leafPort i n w)

theorem child_probability_sum (L : Law) (s : ι) (c : Native ι) (i : ι)
    (n : ℕ) (w : Leaf n) :
    leafProbability L s c i (n + 1) (w, false) +
      leafProbability L s c i (n + 1) (w, true) = leafProbability L s c i n w := by
  have h := appendPairs_child_sum L (.inl (sourceAt s n)) (leafPort i n)
    (leafPort_injective i n) (padCircuit (Leaf n) (tree c i n))
    (Finset.univ : Finset (Leaf n)).toList (Finset.nodup_toList _) w (by simp)
  simpa [leafProbability, tree, sourceAt, leafPort, L.vacuum,
    vacuum_probability_zero] using h

theorem total_leaf_probability (L : Law) (s : ι) (c : Native ι) (i : ι) (n : ℕ) :
    (∑ w : Leaf n, leafProbability L s c i n w) = L.prob s c i := by
  induction n with
  | zero => simp [Leaf, leafProbability, sourceAt, tree, leafPort]; rfl
  | succ n ih =>
      change (∑ w : Leaf n × Bool, leafProbability L s c i (n + 1) w) = _
      simp only [Fintype.sum_prod_type, Fintype.sum_bool]
      simpa [add_comm, child_probability_sum] using ih

theorem rootA_probability (L : Law) (s : ι) (c : Native ι) (i : ι) (n : ℕ) :
    (∑ w : Leaf n, leafProbability L s c i (n + 1) (rootA n w)) =
      leafProbability L s c i 1 (PUnit.unit, false) := by
  induction n with
  | zero => simp [Leaf, rootA]
  | succ n ih =>
      change (∑ w : Leaf n × Bool,
        leafProbability L s c i (n + 2) (rootA (n + 1) w)) = _
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, rootA]
      simpa [add_comm, child_probability_sum] using ih

omit [Fintype ι] [DecidableEq ι] in
theorem tree_one_eq_split (c : Native ι) (i : ι) : tree c i 1 = split c i := by
  simp [tree, Leaf, appendPairs, branchPair, leafPort, split]
  rfl

def phaseFactor : Fin 4 → ℂ := ![1, -Complex.I, -1, Complex.I]

theorem b_phaseFactor (j : Fin 4) :
    NativeAttenuationCircuit.b * phaseFactor j =
      NativeAttenuationCircuit.a * phaseFactor (phaseNext j) := by
  fin_cases j <;> apply Complex.ext <;>
    norm_num [NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
      phaseFactor, phaseNext, Matrix.cons_val_two, Matrix.cons_val_three,
      Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im]

theorem child_amplitudes (s : ι) (c : Native ι) (i : ι) (n : ℕ) (w : Leaf n) :
    (tree c i (n + 1)).eval (source (sourceAt s (n + 1)))
        (leafPort i (n + 1) (w, false)) =
      NativeAttenuationCircuit.a *
        (tree c i n).eval (source (sourceAt s n)) (leafPort i n w) ∧
    (tree c i (n + 1)).eval (source (sourceAt s (n + 1)))
        (leafPort i (n + 1) (w, true)) =
      NativeAttenuationCircuit.b *
        (tree c i n).eval (source (sourceAt s n)) (leafPort i n w) := by
  have h := appendPairs_child_amplitudes (leafPort i n) (leafPort_injective i n)
    (padCircuit (Leaf n) (tree c i n)) (Finset.univ : Finset (Leaf n)).toList
    (Finset.nodup_toList _) w (by simp) (source (Sum.inl (sourceAt s n)))
  simpa [tree, sourceAt, leafPort, pad_prepared, padState] using h

/-- Actual selected leaf amplitudes of the literal finite circuit. -/
theorem leaf_amplitude (s : ι) (c : Native ι) (i : ι) (n : ℕ) (w : Leaf n) :
    (tree c i n).eval (source (sourceAt s n)) (leafPort i n w) =
      NativeAttenuationCircuit.a ^ n * phaseFactor (phase n w) * c.eval (source s) i := by
  induction n with
  | zero => simp [tree, sourceAt, leafPort, phase, phaseFactor]; rfl
  | succ n ih =>
      rcases w with ⟨w, b⟩
      cases b
      · rw [(child_amplitudes s c i n w).1, ih]
        simp only [phase, pow_succ]
        ring
      · rw [(child_amplitudes s c i n w).2, ih]
        simp only [phase]
        calc
          _ = NativeAttenuationCircuit.a ^ n *
              (NativeAttenuationCircuit.b * phaseFactor (phase n w)) *
              c.eval (source s) i := by ring
          _ = _ := by rw [b_phaseFactor, pow_succ]; ring

theorem leaf_probability_phase_eq (L : Law) (s : ι) (c : Native ι) (i : ι)
    (n : ℕ) (u v : Leaf n) (hphase : phase n u = phase n v) :
    leafProbability L s c i n u = leafProbability L s c i n v := by
  apply equal_coordinate_probabilities
  rw [leaf_amplitude, leaf_amplitude, hphase]

/-- Representatives are chosen from actual finite output fibres; empty fibres get zero. -/
def phaseProbability (L : Law) (s : ι) (c : Native ι) (i : ι) (n : ℕ) (j : Fin 4) : ℝ :=
  if h : ∃ w : Leaf n, phase n w = j then
    leafProbability L s c i n (Classical.choose h)
  else 0

theorem phaseProbability_nonnegative (L : Law) (s : ι) (c : Native ι) (i : ι)
    (n : ℕ) (j : Fin 4) : 0 ≤ phaseProbability L s c i n j := by
  unfold phaseProbability
  split_ifs
  · exact L.nonnegative _ _ _
  · exact le_refl 0

theorem phaseProbability_at_leaf (L : Law) (s : ι) (c : Native ι) (i : ι)
    (n : ℕ) (w : Leaf n) :
    phaseProbability L s c i n (phase n w) = leafProbability L s c i n w := by
  have hex : ∃ v : Leaf n, phase n v = phase n w := ⟨w, rfl⟩
  unfold phaseProbability
  rw [dif_pos hex]
  exact leaf_probability_phase_eq L s c i n _ w (Classical.choose_spec hex)

/-- Both counted sums concern the same root-first native refinement circuit. -/
theorem counted_native_masses (L : Law) (s : ι) (c : Native ι) (i : ι) (n : ℕ) :
    (∑ j, (NativeBinaryPhaseCounting.phaseCount (n + 1) j : ℝ) *
        phaseProbability L s c i (n + 1) j) = L.prob s c i ∧
    (∑ j, (NativeBinaryPhaseCounting.phaseCount n j : ℝ) *
        phaseProbability L s c i (n + 1) j) =
      leafProbability L s c i 1 (PUnit.unit, false) := by
  constructor
  · rw [← sum_by_phase]
    simp only [phaseProbability_at_leaf]
    exact total_leaf_probability L s c i (n + 1)
  · rw [← sum_by_phase]
    calc
      _ = ∑ w : Leaf n,
          phaseProbability L s c i (n + 1) (phase (n + 1) (rootA n w)) := by
            simp only [rootA_phase]
      _ = ∑ w : Leaf n, leafProbability L s c i (n + 1) (rootA n w) := by
            simp only [phaseProbability_at_leaf]
      _ = _ := rootA_probability L s c i n

/-- The proof of this bound uses only the refinement at depth `4*k+1`.
The stated family contract remains global; finite physical testing is not asserted. -/
theorem native_finite_refinement_bound (L : Law) (s : ι) (c : Native ι) (i : ι)
    (k : ℕ) (hk : 1 ≤ k) :
    |L.prob (.inl s) (split c i) (.inl i) - L.prob s c i / 2| ≤
      L.prob s c i / (2 * ((4 : ℝ)^k - 1)) := by
  obtain ⟨hp, hr⟩ := counted_native_masses L s c i (4 * k)
  have h := NativeBinaryPhaseCounting.mass_deviation_bound k hk
    (phaseProbability L s c i (4 * k + 1))
    (phaseProbability_nonnegative L s c i (4 * k + 1))
    (L.prob s c i) (leafProbability L s c i 1 (PUnit.unit, false)) hp hr
  simpa only [leafProbability, sourceAt, leafPort, tree_one_eq_split] using h

/-- The all-depth conclusion uses the same fixed literal split probability. -/
theorem native_vacuum_split_halves (L : Law) (s : ι) (c : Native ι) (i : ι) :
    L.prob (.inl s) (split c i) (.inl i) = L.prob s c i / 2 := by
  have h := NativeBinaryPhaseCounting.phase_count_mass_halving (L.prob s c i)
    (leafProbability L s c i 1 (PUnit.unit, false)) (by
      intro k _
      refine ⟨phaseProbability L s c i (4 * k + 1),
        phaseProbability_nonnegative L s c i (4 * k + 1), ?_⟩
      exact counted_native_masses L s c i (4 * k))
  simpa only [leafProbability, sourceAt, leafPort, tree_one_eq_split] using h

theorem native_vacuum_split_fresh_halves (L : Law) (s : ι) (c : Native ι) (i : ι) :
    L.prob (.inl s) (split c i) (.inr PUnit.unit) = L.prob s c i / 2 := by
  have hsum := split_probability_sum L s c i
  rw [native_vacuum_split_halves] at hsum
  linarith

end

end IDT.QMClosure.NativeBinaryRefinement
