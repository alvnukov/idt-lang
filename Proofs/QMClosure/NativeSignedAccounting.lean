import Proofs.QMClosure.NativeBinaryRefinement

/-!
# Native accounting without a positivity premise

`SignedLaw` keeps the same marked-source and literal-circuit semantics as the
positive family, but permits arbitrary real values. `SignedHalvingLaw` adds
halving as an explicit intermediate contract; the five accounting fields alone
are not asserted to imply it.
-/

namespace IDT.QMClosure.NativeSignedAccounting

noncomputable section
open MixerGeneratedProcessWall NativeMixerEventConeExclusion
open NativeVacuumProbabilityFamily NativeBinaryRefinement
open scoped BigOperators

structure SignedLaw where
  prob : {ι : Type} → [Fintype ι] → [DecidableEq ι] → ι → Native ι → ι → ℝ
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

/-- The extra halving field is explicit and is not part of `SignedLaw`. -/
structure SignedHalvingLaw extends SignedLaw where
  split_halves : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (i : ι),
    prob (.inl s) (split c i) (.inl i) = prob s c i / 2

/-- Preserve the entire positive law, using its already proved halving theorem. -/
def ofLaw (L : Law) : SignedHalvingLaw where
  toSignedLaw := {
    prob := L.prob
    normalized := L.normalized
    prepared_eq := L.prepared_eq
    output_perm := L.output_perm
    spectator_pair := L.spectator_pair
    vacuum := L.vacuum }
  split_halves := NativeBinaryRefinement.native_vacuum_split_halves L

instance : Coe Law SignedHalvingLaw := ⟨ofLaw⟩

theorem ofLaw_prob (L : Law) :
    @SignedLaw.prob (ofLaw L).toSignedLaw = @Law.prob L := rfl

variable {ι κ τ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype τ] [DecidableEq τ]

/-- Equal prepared coordinates have equal signed values by output symmetry. -/
theorem equal_coordinate_probabilities (L : SignedLaw) (s : ι) (c : Native ι) (i j : ι)
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

/-- All fresh coordinates agree; normalization forces their common value to zero. -/
theorem vacuum_probability_zero (L : SignedLaw) (s : ι) (c : Native ι) (j : κ) :
    L.prob (.inl s) (padCircuit κ c) (.inr j) = 0 := by
  have hn := L.normalized (.inl s) (padCircuit κ c)
  rw [Fintype.sum_sum_type] at hn
  have ho : (∑ i : ι, L.prob (.inl s) (padCircuit κ c) (.inl i)) = 1 := by
    simpa only [L.vacuum] using L.normalized s c
  have hz : (∑ k : κ, L.prob (.inl s) (padCircuit κ c) (.inr k)) = 0 := by
    linarith
  have hall : ∀ k : κ, L.prob (.inl s) (padCircuit κ c) (.inr k) =
      L.prob (.inl s) (padCircuit κ c) (.inr j) := by
    intro k
    apply equal_coordinate_probabilities
    rw [pad_prepared]
    rfl
  simp_rw [hall] at hz
  have hz' : (Fintype.card κ : ℝ) *
      L.prob (.inl s) (padCircuit κ c) (.inr j) = 0 := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hz
  have hc : (Fintype.card κ : ℝ) ≠ 0 := by
    have hpos : 0 < Fintype.card κ := Fintype.card_pos_iff.mpr ⟨j⟩
    exact_mod_cast (Nat.ne_of_gt hpos)
  exact (mul_eq_zero.mp hz').resolve_left hc

private theorem sum_two (f : ι → ℝ) (i j : ι) (hij : i ≠ j) :
    ∑ k, f k = f i + f j + ∑ k ∈ (Finset.univ.erase i).erase j, f k := by
  have hi := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  have hj := Finset.sum_erase_add (Finset.univ.erase i) f
    (show j ∈ Finset.univ.erase i by simp [Ne.symm hij])
  rw [← hi, ← hj]
  simp only [add_comm, add_left_comm]

theorem pair_probability_sum (L : SignedLaw) (s : ι) (c : Native ι)
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

theorem split_probability_sum (L : SignedLaw) (s : ι) (c : Native ι) (i : ι) :
    L.prob (.inl s) (split c i) (.inl i) +
      L.prob (.inl s) (split c i) (.inr PUnit.unit) = L.prob s c i := by
  rw [split, pair_probability_sum, L.vacuum, vacuum_probability_zero, add_zero]

theorem split_fresh_halves (L : SignedHalvingLaw) (s : ι) (c : Native ι) (i : ι) :
    L.prob (.inl s) (split c i) (.inr PUnit.unit) = L.prob s c i / 2 := by
  have hsum := split_probability_sum L.toSignedLaw s c i
  rw [L.split_halves] at hsum
  linarith

theorem zero_amplitude_probability_zero (L : SignedLaw) (s : ι) (c : Native ι) (i : ι)
    (hz : c.eval (source s) i = 0) : L.prob s c i = 0 := by
  have he : (padCircuit PUnit c).eval (source (.inl s)) (.inl i) =
      (padCircuit PUnit c).eval (source (.inl s)) (.inr PUnit.unit) := by
    rw [pad_prepared]
    simp [padState, hz]
  have hp := equal_coordinate_probabilities L (.inl s) (padCircuit PUnit c)
    (.inl i) (.inr PUnit.unit) he
  rw [L.vacuum, vacuum_probability_zero] at hp
  exact hp

theorem basis_calibration (L : SignedLaw) (s : ι) (c : Native ι) (j : ι)
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

theorem appendPairs_probability_untouched (L : SignedLaw) (s : ι ⊕ τ)
    (f : τ → ι) (c : Native (ι ⊕ τ)) (ts : List τ) (w : ι ⊕ τ)
    (h : ∀ t ∈ ts, w ≠ .inl (f t) ∧ w ≠ .inr t) :
    L.prob s (appendPairs f c ts) w = L.prob s c w := by
  induction ts generalizing c with
  | nil => rfl
  | cons t ts ih =>
      rw [appendPairs, ih _ (fun u hu => h u (List.mem_cons_of_mem t hu))]
      have ht := h t (by simp)
      exact L.spectator_pair s c (.inl (f t)) (.inr t) w (by simp) ht.1 ht.2

theorem appendPairs_child_sum (L : SignedLaw) (s : ι ⊕ τ) (f : τ → ι)
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

end
end IDT.QMClosure.NativeSignedAccounting
