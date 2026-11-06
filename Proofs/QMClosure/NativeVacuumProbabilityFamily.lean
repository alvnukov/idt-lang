import Proofs.QMClosure.NativeAttenuationCircuit

/-!
# Probability families compatible with literal native vacuum embeddings

This is an explicit conditional contract, indexed by finite wire types and a
marked source basis port. The only comparison between different wire types is
constructorwise embedding into a sum with fresh zero-input wires. There is no
additional relabel-invariance, scalar-amplitude sufficiency, mixture law,
probability continuity, or physical availability assertion.
-/

namespace IDT.QMClosure.NativeVacuumProbabilityFamily

noncomputable section
open MixerGeneratedProcessWall NativeMixerEventConeExclusion
open scoped BigOperators

abbrev Native (ι : Type) := Circuit (ι := ι) mixer

def source {ι : Type} [DecidableEq ι] (s : ι) : ι → ℂ := single s 1

def padState {ι κ : Type} (v : ι → ℂ) : ι ⊕ κ → ℂ :=
  Sum.elim v (fun _ => 0)

/-- Every constructor is preserved; the new wires are untouched. -/
def padCircuit {ι : Type} (κ : Type) : Native ι → Native (ι ⊕ κ)
  | .identity => .identity
  | .pair i j hij => .pair (.inl i) (.inl j) (fun h => hij (Sum.inl.inj h))
  | .permute e => .permute (Equiv.sumCongr e (Equiv.refl κ))
  | .seq c d => .seq (padCircuit κ c) (padCircuit κ d)

theorem padCircuit_eval {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (c : Native ι) (v : ι → ℂ) :
    (padCircuit κ c).eval (padState v) = padState (c.eval v) := by
  induction c generalizing v with
  | identity => rfl
  | pair i j hij =>
      ext w
      cases w <;> simp [padCircuit, padState, Circuit.eval, pairGate, pairReplace]
  | permute e =>
      ext w
      cases w <;> simp [padCircuit, padState, Circuit.eval]
  | seq c d hc hd =>
      change (padCircuit κ d).eval ((padCircuit κ c).eval (padState v)) = _
      rw [hc, hd]
      rfl

theorem pad_source {ι κ : Type} [DecidableEq ι] [DecidableEq κ] (s : ι) :
    source (Sum.inl s : ι ⊕ κ) = padState (source s) := by
  ext w
  cases w <;> simp [source, single, padState]

theorem pad_prepared {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (s : ι) (c : Native ι) :
    (padCircuit κ c).eval (source (.inl s)) = padState (c.eval (source s)) := by
  rw [pad_source, padCircuit_eval]

/-- All probability assumptions used by native binary refinement. -/
structure Law where
  prob : {ι : Type} → [Fintype ι] → [DecidableEq ι] → ι → Native ι → ι → ℝ
  nonnegative : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) i,
    0 ≤ prob s c i
  normalized : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι),
    ∑ i, prob s c i = 1
  prepared_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c d : Native ι), c.eval (source s) = d.eval (source s) → prob s c = prob s d
  output_perm : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (e : Equiv.Perm ι) i,
    prob s (.seq c (.permute e)) i = prob s c (e i)
  spectator_pair : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (i j k : ι) (hij : i ≠ j),
    k ≠ i → k ≠ j → prob s (.seq c (.pair i j hij)) k = prob s c k
  vacuum : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (s : ι) (c : Native ι) i,
    prob (.inl s) (padCircuit κ c) (.inl i) = prob s c i

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- New output ports have probability zero before any new gates are applied. -/
theorem vacuum_probability_zero (L : Law) (s : ι) (c : Native ι) (j : κ) :
    L.prob (.inl s) (padCircuit κ c) (.inr j) = 0 := by
  have hn := L.normalized (.inl s) (padCircuit κ c)
  rw [Fintype.sum_sum_type] at hn
  have ho : (∑ i : ι, L.prob (.inl s) (padCircuit κ c) (.inl i)) = 1 := by
    simpa only [L.vacuum] using L.normalized s c
  have hz : (∑ k : κ, L.prob (.inl s) (padCircuit κ c) (.inr k)) = 0 := by
    linarith
  have hj := Finset.single_le_sum
    (fun k (_ : k ∈ (Finset.univ : Finset κ)) =>
      L.nonnegative (.inl s) (padCircuit κ c) (.inr k))
    (Finset.mem_univ j)
  exact le_antisymm (by simpa [hz] using hj)
    (L.nonnegative (.inl s) (padCircuit κ c) (.inr j))

private theorem sum_two (f : ι → ℝ) (i j : ι) (hij : i ≠ j) :
    ∑ k, f k = f i + f j + ∑ k ∈ (Finset.univ.erase i).erase j, f k := by
  have hi := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  have hj := Finset.sum_erase_add (Finset.univ.erase i) f
    (show j ∈ Finset.univ.erase i by simp [Ne.symm hij])
  rw [← hi, ← hj]
  simp only [add_comm, add_left_comm]

/-- Pair probability conservation follows from normalization and spectator locality. -/
theorem pair_probability_sum (L : Law) (s : ι) (c : Native ι)
    (i j : ι) (hij : i ≠ j) :
    L.prob s (.seq c (.pair i j hij)) i + L.prob s (.seq c (.pair i j hij)) j =
      L.prob s c i + L.prob s c j := by
  have hsum : (∑ k, L.prob s (.seq c (.pair i j hij)) k) = ∑ k, L.prob s c k := by
    rw [L.normalized, L.normalized]
  rw [sum_two _ i j hij, sum_two _ i j hij] at hsum
  have hrest :
      (∑ k ∈ (Finset.univ.erase i).erase j, L.prob s (.seq c (.pair i j hij)) k) =
      ∑ k ∈ (Finset.univ.erase i).erase j, L.prob s c k := by
    apply Finset.sum_congr rfl
    intro k hk
    exact L.spectator_pair s c i j k hij
      (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1 (Finset.mem_erase.mp hk).1
  rw [hrest] at hsum
  linarith

/-- A swap of equal coordinates fixes the complete prepared state. -/
theorem equal_coordinate_probabilities (L : Law) (s : ι) (c : Native ι) (i j : ι)
    (hcoord : c.eval (source s) i = c.eval (source s) j) :
    L.prob s c i = L.prob s c j := by
  have he : (Circuit.seq c (.permute (Equiv.swap i j))).eval (source s) =
      c.eval (source s) := by
    ext k
    change c.eval (source s) (Equiv.swap i j k) = c.eval (source s) k
    by_cases hki : k = i
    · subst k
      simpa only [Equiv.swap_apply_left] using hcoord.symm
    by_cases hkj : k = j
    · subst k
      simpa only [Equiv.swap_apply_right] using hcoord
    · simp only [Equiv.swap_apply_def, if_neg hki, if_neg hkj]
  have hs := congrFun (L.prepared_eq s (.seq c (.permute (Equiv.swap i j))) c he) i
  have hp := L.output_perm s c (Equiv.swap i j) i
  rw [Equiv.swap_apply_left] at hp
  exact hs.symm.trans hp

/-- The literal continuation whose retained probability is to be selected. -/
def split (c : Native ι) (i : ι) : Native (ι ⊕ PUnit) :=
  .seq (padCircuit PUnit c) (.pair (.inl i) (.inr PUnit.unit) (by simp))

theorem split_probability_sum (L : Law) (s : ι) (c : Native ι) (i : ι) :
    L.prob (.inl s) (split c i) (.inl i) +
      L.prob (.inl s) (split c i) (.inr PUnit.unit) = L.prob s c i := by
  rw [split, pair_probability_sum, L.vacuum, vacuum_probability_zero, add_zero]

theorem split_retained_amplitude (s : ι) (c : Native ι) (i : ι) :
    (split c i).eval (source (.inl s)) (.inl i) =
      NativeAttenuationCircuit.a * c.eval (source s) i := by
  simp [split, Circuit.eval, pad_prepared, pairGate, pairReplace, padState,
    NativeAttenuationCircuit.mixer_fst]

theorem split_fresh_amplitude (s : ι) (c : Native ι) (i : ι) :
    (split c i).eval (source (.inl s)) (.inr PUnit.unit) =
      NativeAttenuationCircuit.b * c.eval (source s) i := by
  simp [split, Circuit.eval, pad_prepared, pairGate, pairReplace, padState,
    NativeAttenuationCircuit.mixer_snd]

theorem zero_amplitude_probability_zero (L : Law) (s : ι) (c : Native ι) (i : ι)
    (hz : c.eval (source s) i = 0) : L.prob s c i = 0 := by
  have he : (padCircuit PUnit c).eval (source (.inl s)) (.inl i) =
      (padCircuit PUnit c).eval (source (.inl s)) (.inr PUnit.unit) := by
    rw [pad_prepared]
    simp [padState, hz]
  have hp := equal_coordinate_probabilities L (.inl s) (padCircuit PUnit c)
    (.inl i) (.inr PUnit.unit) he
  rw [L.vacuum, vacuum_probability_zero] at hp
  exact hp

/-- Basis calibration is a consequence, not an independent field of the law. -/
theorem basis_calibration (L : Law) (s : ι) (c : Native ι) (j : ι)
    (hc : c.eval (source s) = source j) (i : ι) :
    L.prob s c i = if i = j then 1 else 0 := by
  have hz : ∀ k, k ≠ j → L.prob s c k = 0 := by
    intro k hk
    apply zero_amplitude_probability_zero L s c k
    rw [hc]
    simp [source, single, hk]
  have he : (∑ k, L.prob s c k) = L.prob s c j := by
    apply Finset.sum_eq_single j
    · intro k _ hk
      exact hz k hk
    · simp
  have hn := L.normalized s c
  rw [he] at hn
  by_cases hij : i = j
  · subst i
    simpa using hn
  · simp [hij, hz i hij]

/-- A mathematical consistency witness, never a premise of probability selection.
This definition does not assert that the physical probability law is quadratic. -/
def canonicalLaw : Law where
  prob s c i := Complex.normSq (c.eval (source s) i)
  nonnegative _ _ _ := Complex.normSq_nonneg _
  normalized s c := by
    have h := c.preserves_readout Complex.normSq mixer_conserves (source s)
    simpa [totalReadout, source, single] using h
  prepared_eq _ _ _ h := by
    funext i
    rw [h]
  output_perm _ _ _ _ := rfl
  spectator_pair s c i j k hij hki hkj := by
    change Complex.normSq (pairReplace mixer i j (c.eval (source s)) k) = _
    simp [pairReplace, hki, hkj]
  vacuum s c i := by
    rw [pad_prepared]
    rfl

end

end IDT.QMClosure.NativeVacuumProbabilityFamily
