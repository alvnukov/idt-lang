import Proofs.QMClosure.NativeZeroPortSplitting

/-!
# Actual coherent two-block dilation and branch probability accounting

All copying below means native vacuum splitting, not a copying primitive.
The wire types are literal sums, the source stays in the left summand, and
each block operation is built constructor by constructor from the original
circuit. The only cross-type probability premise is `Law.vacuum`.

The two branch probabilities are derived from native zero-partner halving,
complete prepared-state equality, and spectator locality. No classical random
mixture law or arbitrary coarse-effect equivalence is supplied.
-/

namespace IDT.QMClosure.NativeCoherentBranchDilation

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

open MixerGeneratedProcessWall NativeVacuumProbabilityFamily NativeBinaryRefinement
open NativeZeroPortSplitting
open scoped BigOperators

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-! ## Literal block circuits, on arbitrary states in the other block -/

def rightCircuit {ι : Type} (κ : Type) : Native ι → Native (κ ⊕ ι)
  | .identity => .identity
  | .pair i j hij => .pair (.inr i) (.inr j) (fun h => hij (Sum.inr.inj h))
  | .permute e => .permute (Equiv.sumCongr (Equiv.refl κ) e)
  | .seq c d => .seq (rightCircuit κ c) (rightCircuit κ d)

omit [Fintype ι] [Fintype κ] in
theorem padCircuit_eval_general (c : Native ι) (x : ι ⊕ κ → ℂ) :
    (padCircuit κ c).eval x =
      Sum.elim (c.eval (fun i => x (.inl i))) (fun j => x (.inr j)) := by
  induction c generalizing x with
  | identity => ext w; cases w <;> rfl
  | pair i j hij =>
      ext w
      cases w <;> simp [padCircuit, Circuit.eval, pairGate, pairReplace]
  | permute e => ext w; cases w <;> rfl
  | seq c d hc hd =>
      change (padCircuit κ d).eval ((padCircuit κ c).eval x) = _
      rw [hc, hd]
      rfl

omit [Fintype ι] [Fintype κ] in
theorem rightCircuit_eval (c : Native ι) (x : κ ⊕ ι → ℂ) :
    (rightCircuit κ c).eval x =
      Sum.elim (fun j => x (.inl j)) (c.eval (fun i => x (.inr i))) := by
  induction c generalizing x with
  | identity => ext w; cases w <;> rfl
  | pair i j hij =>
      ext w
      cases w <;> simp [rightCircuit, Circuit.eval, pairGate, pairReplace]
  | permute e => ext w; cases w <;> rfl
  | seq c d hc hd =>
      change (rightCircuit κ d).eval ((rightCircuit κ c).eval x) = _
      rw [hc, hd]
      rfl

omit [Fintype ι] in
theorem eval_scale (c : Native ι) (z : ℂ) (x : ι → ℂ) :
    c.eval (fun i => z * x i) = fun i => z * c.eval x i := by
  induction c generalizing x with
  | identity => rfl
  | pair i j hij =>
      funext k
      by_cases hki : k = i
      · simp [Circuit.eval, pairGate, pairReplace, hki,
          NativeAttenuationCircuit.mixer_fst]
        ring
      · by_cases hkj : k = j
        · simp [Circuit.eval, pairGate, pairReplace, hkj, Ne.symm hij,
            NativeAttenuationCircuit.mixer_snd]
          ring
        · simp [Circuit.eval, pairGate, pairReplace, hki, hkj]
  | permute e => rfl
  | seq c d hc hd =>
      change d.eval (c.eval (fun i => z * x i)) = _
      rw [hc, hd]
      rfl

theorem probability_seq_assoc (L : Law) (s : ι) (p c d : Native ι) (i : ι) :
    L.prob s (.seq p (.seq c d)) i = L.prob s (.seq (.seq p c) d) i :=
  congrFun (L.prepared_eq s _ _ (by rfl)) i

theorem padCircuit_probability_right (L : Law) (s : ι ⊕ κ)
    (p : Native (ι ⊕ κ)) (c : Native ι) (j : κ) :
    L.prob s (.seq p (padCircuit κ c)) (.inr j) = L.prob s p (.inr j) := by
  induction c generalizing p with
  | identity => exact congrFun (L.prepared_eq s _ _ (by rfl)) (.inr j)
  | pair i k hik =>
      exact L.spectator_pair s p (.inl i) (.inl k) (.inr j)
        (fun h => hik (Sum.inl.inj h)) (by simp) (by simp)
  | permute e =>
      simpa [padCircuit] using
        L.output_perm s p (Equiv.sumCongr e (Equiv.refl κ)) (.inr j)
  | seq c d hc hd =>
      rw [padCircuit, probability_seq_assoc, hd, hc]

theorem rightCircuit_probability_left (L : Law) (s : κ ⊕ ι)
    (p : Native (κ ⊕ ι)) (c : Native ι) (j : κ) :
    L.prob s (.seq p (rightCircuit κ c)) (.inl j) = L.prob s p (.inl j) := by
  induction c generalizing p with
  | identity => exact congrFun (L.prepared_eq s _ _ (by rfl)) (.inl j)
  | pair i k hik =>
      exact L.spectator_pair s p (.inr i) (.inr k) (.inl j)
        (fun h => hik (Sum.inr.inj h)) (by simp) (by simp)
  | permute e =>
      simpa [rightCircuit] using
        L.output_perm s p (Equiv.sumCongr (Equiv.refl κ) e) (.inl j)
  | seq c d hc hd =>
      rw [rightCircuit, probability_seq_assoc, hd, hc]

def blocks (c d : Native ι) : Native (ι ⊕ ι) :=
  .seq (padCircuit ι c) (rightCircuit ι d)

omit [Fintype ι] in
theorem blocks_eval (c d : Native ι) (x : ι ⊕ ι → ℂ) :
    (blocks c d).eval x =
      Sum.elim (c.eval (fun i => x (.inl i))) (d.eval (fun i => x (.inr i))) := by
  change (rightCircuit ι d).eval ((padCircuit ι c).eval x) = _
  rw [padCircuit_eval_general, rightCircuit_eval]
  rfl

omit [Fintype ι] in
theorem blocks_reverse_order (c d : Native ι) (x : ι ⊕ ι → ℂ) :
    (blocks c d).eval x =
      (padCircuit ι c).eval ((rightCircuit ι d).eval x) := by
  rw [blocks_eval, rightCircuit_eval, padCircuit_eval_general]
  rfl

theorem blocks_probability_left (L : Law) (s : ι ⊕ ι)
    (p : Native (ι ⊕ ι)) (c d : Native ι) (i : ι) :
    L.prob s (.seq p (blocks c d)) (.inl i) =
      L.prob s (.seq p (padCircuit ι c)) (.inl i) := by
  rw [blocks, probability_seq_assoc, rightCircuit_probability_left]

theorem blocks_probability_right (L : Law) (s : ι ⊕ ι)
    (p : Native (ι ⊕ ι)) (c d : Native ι) (i : ι) :
    L.prob s (.seq p (blocks c d)) (.inr i) =
      L.prob s (.seq p (rightCircuit ι d)) (.inr i) := by
  have he : (Circuit.seq p (blocks c d)).eval (source s) =
      (Circuit.seq (.seq p (rightCircuit ι d)) (padCircuit ι c)).eval (source s) :=
    blocks_reverse_order c d (p.eval (source s))
  rw [congrFun (L.prepared_eq s _ _ he) (.inr i)]
  exact padCircuit_probability_right L s _ c i

/-! ## Each original wire is split against its own fresh vacuum wire -/

theorem appendPairs_child_halves (L : Law) (s : ι ⊕ κ) (f : κ → ι)
    (hf : Function.Injective f) (c : Native (ι ⊕ κ)) (ts : List κ)
    (hn : ts.Nodup) (t : κ) (ht : t ∈ ts)
    (hz : c.eval (source s) (.inr t) = 0) :
    L.prob s (appendPairs f c ts) (.inl (f t)) = L.prob s c (.inl (f t)) / 2 ∧
    L.prob s (appendPairs f c ts) (.inr t) = L.prob s c (.inl (f t)) / 2 := by
  induction ts generalizing c with
  | nil => simp at ht
  | cons u us ih =>
      have hnu : u ∉ us := (List.nodup_cons.mp hn).1
      have hns : us.Nodup := (List.nodup_cons.mp hn).2
      by_cases hut : u = t
      · subst u
        have hleft : ∀ v ∈ us, (Sum.inl (f t) : ι ⊕ κ) ≠ .inl (f v) ∧
            (Sum.inl (f t) : ι ⊕ κ) ≠ .inr v := by
          intro v hv
          constructor
          · intro he
            exact hnu ((hf (Sum.inl.inj he)).symm ▸ hv)
          · simp
        have hright : ∀ v ∈ us, (Sum.inr t : ι ⊕ κ) ≠ .inl (f v) ∧
            (Sum.inr t : ι ⊕ κ) ≠ .inr v := by
          intro v hv
          constructor
          · simp
          · intro he
            exact hnu ((Sum.inr.inj he).symm ▸ hv)
        simp only [appendPairs,
          appendPairs_probability_untouched L s f _ us _ hleft,
          appendPairs_probability_untouched L s f _ us _ hright]
        exact internal_zero_partner_halves L s c (.inl (f t)) (.inr t) (by simp) hz
      · have htu : t ≠ u := Ne.symm hut
        have hmem : t ∈ us := (List.mem_cons.mp ht).resolve_left htu
        have hftu : f t ≠ f u := fun he => htu (hf he)
        have hzero : (Circuit.seq c (branchPair f u)).eval (source s) (.inr t) = 0 := by
          simpa [branchPair, Circuit.eval, pairGate, pairReplace, htu] using hz
        have h := ih (.seq c (branchPair f u)) hns hmem hzero
        have hp := L.spectator_pair s c (.inl (f u)) (.inr u) (.inl (f t))
          (by simp) (by simpa using hftu) (by simp)
        simpa only [appendPairs, branchPair, hp] using h

def duplicate (c : Native ι) : Native (ι ⊕ ι) :=
  appendPairs id (padCircuit ι c) (Finset.univ : Finset ι).toList

theorem duplicate_amplitudes (s : ι) (c : Native ι) (i : ι) :
    (duplicate c).eval (source (.inl s)) (.inl i) =
        NativeAttenuationCircuit.a * c.eval (source s) i ∧
    (duplicate c).eval (source (.inl s)) (.inr i) =
        NativeAttenuationCircuit.b * c.eval (source s) i := by
  have h := appendPairs_child_amplitudes (id : ι → ι) (fun _ _ h => h)
    (padCircuit ι c) (Finset.univ : Finset ι).toList (Finset.nodup_toList _) i (by simp)
    (source (Sum.inl s))
  simpa [duplicate, pad_prepared, padState] using h

theorem duplicate_prepared (s : ι) (c : Native ι) :
    (duplicate c).eval (source (.inl s)) =
      Sum.elim (fun i => NativeAttenuationCircuit.a * c.eval (source s) i)
        (fun i => NativeAttenuationCircuit.b * c.eval (source s) i) := by
  funext w
  cases w with
  | inl i => exact (duplicate_amplitudes s c i).1
  | inr i => exact (duplicate_amplitudes s c i).2

theorem duplicate_probabilities (L : Law) (s : ι) (c : Native ι) (i : ι) :
    L.prob (.inl s) (duplicate c) (.inl i) = L.prob s c i / 2 ∧
    L.prob (.inl s) (duplicate c) (.inr i) = L.prob s c i / 2 := by
  have hz : (padCircuit ι c).eval (source (Sum.inl s)) (.inr i) = 0 := by
    rw [pad_prepared]
    rfl
  have h := appendPairs_child_halves L (.inl s) (id : ι → ι) (fun _ _ h => h)
    (padCircuit ι c) (Finset.univ : Finset ι).toList (Finset.nodup_toList _) i (by simp) hz
  simpa only [duplicate, id_eq, L.vacuum] using h

/-! ## Independent circuits in the two actual coherent branches -/

def dilation (c d : Native ι) : Native (ι ⊕ ι) :=
  .seq (duplicate (.identity : Native ι)) (blocks c d)

theorem dilation_prepared (s : ι) (c d : Native ι) :
    (dilation c d).eval (source (.inl s)) =
      Sum.elim (fun i => NativeAttenuationCircuit.a * c.eval (source s) i)
        (fun i => NativeAttenuationCircuit.b * d.eval (source s) i) := by
  change (blocks c d).eval ((duplicate (.identity : Native ι)).eval
    (source (Sum.inl s))) = _
  rw [duplicate_prepared, blocks_eval]
  change Sum.elim
    (c.eval (fun i => NativeAttenuationCircuit.a * source s i))
    (d.eval (fun i => NativeAttenuationCircuit.b * source s i)) = _
  rw [eval_scale, eval_scale]

theorem dilation_amplitude_left (s : ι) (c d : Native ι) (i : ι) :
    (dilation c d).eval (source (.inl s)) (.inl i) =
      NativeAttenuationCircuit.a * c.eval (source s) i := by
  rw [dilation_prepared]
  rfl

theorem dilation_amplitude_right (s : ι) (c d : Native ι) (i : ι) :
    (dilation c d).eval (source (.inl s)) (.inr i) =
      NativeAttenuationCircuit.b * d.eval (source s) i := by
  rw [dilation_prepared]
  rfl

theorem same_dilation_prepared (s : ι) (c : Native ι) :
    (dilation c c).eval (source (.inl s)) =
      (duplicate c).eval (source (.inl s)) := by
  rw [dilation_prepared, duplicate_prepared]

theorem dilation_probability_left (L : Law) (s : ι) (c d : Native ι) (i : ι) :
    L.prob (.inl s) (dilation c d) (.inl i) = L.prob s c i / 2 := by
  have hd := blocks_probability_left L (.inl s) (duplicate (.identity : Native ι)) c d i
  have hc := blocks_probability_left L (.inl s) (duplicate (.identity : Native ι)) c c i
  calc
    L.prob (.inl s) (dilation c d) (.inl i) =
        L.prob (.inl s) (dilation c c) (.inl i) := hd.trans hc.symm
    _ = L.prob (.inl s) (duplicate c) (.inl i) :=
      congrFun (L.prepared_eq (Sum.inl s : ι ⊕ ι) (dilation c c) (duplicate c)
        (same_dilation_prepared s c)) (Sum.inl i)
    _ = L.prob s c i / 2 := (duplicate_probabilities L s c i).1

theorem dilation_probability_right (L : Law) (s : ι) (c d : Native ι) (i : ι) :
    L.prob (.inl s) (dilation c d) (.inr i) = L.prob s d i / 2 := by
  have hc := blocks_probability_right L (.inl s) (duplicate (.identity : Native ι)) c d i
  have hd := blocks_probability_right L (.inl s) (duplicate (.identity : Native ι)) d d i
  calc
    L.prob (.inl s) (dilation c d) (.inr i) =
        L.prob (.inl s) (dilation d d) (.inr i) := hc.trans hd.symm
    _ = L.prob (.inl s) (duplicate d) (.inr i) :=
      congrFun (L.prepared_eq (Sum.inl s : ι ⊕ ι) (dilation d d) (duplicate d)
        (same_dilation_prepared s d)) (Sum.inr i)
    _ = L.prob s d i / 2 := (duplicate_probabilities L s d i).2

theorem dilation_probabilities (L : Law) (s : ι) (c d : Native ι) (i j : ι) :
    L.prob (.inl s) (dilation c d) (.inl i) = L.prob s c i / 2 ∧
    L.prob (.inl s) (dilation c d) (.inr j) = L.prob s d j / 2 :=
  ⟨dilation_probability_left L s c d i, dilation_probability_right L s c d j⟩

end

end IDT.QMClosure.NativeCoherentBranchDilation
