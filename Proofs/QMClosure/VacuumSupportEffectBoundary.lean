import Proofs.QMClosure.RawPowerLossReadoutControl

/-!
# Conditional vacuum-support identification and its full-function boundary

A least vacuum-certain effect is fixed by any order automorphism preserving
vacuum certainty. Identifying the actual residual detector with that least
effect is a separate hypothesis in the covariance corollary.

The supplied full function space contains every [0,1]-valued state test,
including the discontinuous indicator of exact vacuum. In that space the
power-response residual is the least vacuum-certain effect exactly at exponent
one. The concrete native split induces a vacuum-preserving pullback order
automorphism at every exponent, while changing residuals above exponent one.

The effect domain, complex arrays, response family, and evaluation are supplied
mathematical data. Physical detector availability, an ideal-support
identification for an actual detector, and a physical probability
interpretation remain separate obligations.
-/

namespace IDT.QMClosure.VacuumSupportEffectBoundary

noncomputable section
open scoped BigOperators

/-- A preserved subset's least element is fixed by an order automorphism. -/
theorem least_fixed {E : Type*} [PartialOrder E] (C : Set E)
    (A : E ≃o E) (n : E) (hn : IsLeast C n)
    (preserves : ∀ e, e ∈ C ↔ A e ∈ C) : A n = n := by
  apply le_antisymm
  · have hi : A.symm n ∈ C := (preserves (A.symm n)).2 (by simpa using hn.1)
    simpa using A.monotone (hn.2 hi)
  · exact hn.2 ((preserves n).1 hn.1)

/-- Covariance yields residual invariance after ideal-support identification. -/
theorem identified_detector_invariant {S E : Type*} [PartialOrder E]
    (p : S → E → ℝ) (T : S → S) (A : E ≃o E) (v : S) (n : E)
    (covariance : ∀ s e, p (T s) e = p s (A e))
    (vacuum_fixed : T v = v)
    (identified : IsLeast {e | p v e = 1} n) (s : S) :
    p (T s) n = p s n := by
  have hc : ∀ e, e ∈ {e | p v e = 1} ↔ A e ∈ {e | p v e = 1} := by
    intro e
    change p v e = 1 ↔ p v (A e) = 1
    rw [← covariance v e, vacuum_fixed]
  rw [covariance, least_fixed _ A n identified hc]

/-- The full function space deliberately includes discontinuous state tests. -/
abbrev Effect (S : Type*) := S → Set.Icc (0 : ℝ) 1

def vacuumCertain {S : Type*} (v : S) : Set (Effect S) :=
  {e | (e v : ℝ) = 1}

/-- Evaluation against every state is supplied by this mathematical model. -/
def evaluate {S : Type*} (s : S) (e : Effect S) : ℝ := e s

/-- A state equivalence acts on all effects by pullback. -/
def pullback {S : Type*} (u : S ≃ S) : Effect S ≃o Effect S where
  toFun e := fun s => e (u s)
  invFun e := fun s => e (u.symm s)
  left_inv e := by funext s; simp
  right_inv e := by funext s; simp
  map_rel_iff' := by
    intro e f
    constructor
    · intro h s
      simpa using h (u.symm s)
    · intro h s
      exact h (u s)

theorem pullback_covariance {S : Type*} (u : S ≃ S) (s : S) (e : Effect S) :
    evaluate (u s) e = evaluate s (pullback u e) := rfl

theorem pullback_preserves_vacuum_certainty {S : Type*}
    (u : S ≃ S) (v : S) (hv : u v = v) (e : Effect S) :
    e ∈ vacuumCertain v ↔ pullback u e ∈ vacuumCertain v := by
  change (e v : ℝ) = 1 ↔ (e (u v) : ℝ) = 1
  rw [hv]

def vacuumIndicator {S : Type*} (v : S) : Effect S := by
  classical
  exact fun s => ⟨if s = v then 1 else 0, by split_ifs <;> norm_num⟩

theorem vacuumIndicator_least {S : Type*} (v : S) :
    IsLeast (vacuumCertain v) (vacuumIndicator v) := by
  classical
  constructor
  · simp [vacuumCertain, vacuumIndicator]
  · intro e he s
    change (if s = v then (1 : ℝ) else 0) ≤ (e s : ℝ)
    by_cases hs : s = v
    · subst s
      change (e v : ℝ) = 1 at he
      simpa using le_of_eq he.symm
    · simpa [hs] using (e s).property.1

theorem pullback_fixes_vacuumIndicator {S : Type*} (u : S ≃ S)
    (v : S) (hv : u v = v) :
    pullback u (vacuumIndicator v) = vacuumIndicator v :=
  least_fixed _ (pullback u) _ (vacuumIndicator_least v)
    (pullback_preserves_vacuum_certainty u v hv)

open RawPowerLossReadoutControl

variable {ι : Type} [Fintype ι]

/-- A bounded residual is an available effect only in this supplied full space. -/
def residualEffect (k : ℕ) (hk : 1 ≤ k) : Effect (ι → ℂ) :=
  fun x => ⟨residual k x, residual_nonneg k hk x,
    probability_le_one k hk x none⟩

theorem energy_zero_iff (x : ι → ℂ) : energy x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    exact Complex.normSq_eq_zero.mp (zero_energy_coordinate x h i)
  · rintro rfl
    simp [energy]

theorem residualEffect_vacuum_certain (k : ℕ) (hk : 1 ≤ k) :
    residualEffect (ι := ι) k hk ∈ vacuumCertain 0 := by
  change residual k (0 : ι → ℂ) = 1
  exact zero_energy_residual k hk 0 (by simp [energy])

/-- Exponent one is the exact-vacuum indicator on all finite arrays. -/
theorem residual_one_eq_indicator :
    residualEffect (ι := ι) 1 (by omega) = vacuumIndicator 0 := by
  classical
  funext x
  apply Subtype.ext
  simp only [residualEffect, vacuumIndicator]
  by_cases hx : x = 0
  · subst x
    simp only [ite_true]
    exact zero_energy_residual 1 (by omega) 0 (by simp [energy])
  · rw [if_neg hx]
    have he : energy x ≠ 0 := fun h => hx ((energy_zero_iff x).1 h)
    simp only [RawPowerLossReadoutControl.residual, port, weight, exposure, pow_one]
    rw [← Finset.sum_div]
    change 1 - energy x / energy x = 0
    rw [div_self he, sub_self]

theorem native_split_nonzero : before.eval basis ≠ 0 := by
  intro h
  have he := native_witness_energy_before
  rw [h] at he
  simp [energy] at he

/-- Above exponent one, the actual split has positive nonvacuum residual. -/
theorem native_split_indicator_strictly_below (k : ℕ) (hk : 1 < k) :
    (vacuumIndicator (0 : Fin 3 → ℂ) (before.eval basis) : ℝ) <
      (residualEffect k (by omega) (before.eval basis) : ℝ) := by
  have hn : residual k (before.eval basis) ≠ 0 := by
    intro h
    have hk1 := (native_split_residual_zero_iff k (by omega)).1 h
    omega
  have hp : 0 < residual k (before.eval basis) :=
    lt_of_le_of_ne (residual_nonneg k (by omega) _) (Ne.symm hn)
  simpa [vacuumIndicator, native_split_nonzero, residualEffect] using hp

/-- In the full effect space, leastness selects exponent one in this family. -/
theorem residualEffect_least_iff (k : ℕ) (hk : 1 ≤ k) :
    IsLeast (vacuumCertain (0 : Fin 3 → ℂ)) (residualEffect k hk) ↔ k = 1 := by
  constructor
  · intro h
    have hi := h.2 (vacuumIndicator_least (0 : Fin 3 → ℂ)).1
    have hb := hi (before.eval basis)
    have hb' : (residualEffect k hk (before.eval basis) : ℝ) ≤
        (vacuumIndicator (0 : Fin 3 → ℂ) (before.eval basis) : ℝ) := hb
    have hz : residual k (before.eval basis) ≤ 0 := by
      simpa [residualEffect, vacuumIndicator, native_split_nonzero] using hb'
    exact (native_split_residual_zero_iff k hk).1
      (le_antisymm hz (residual_nonneg k hk _))
  · rintro rfl
    rw [residual_one_eq_indicator]
    exact vacuumIndicator_least _

open MixerGeneratedProcessWall NativeMixerEventConeExclusion

/-- The actual split squares to the exchange of its two selected wires. -/
theorem native_split_square (x : Fin 3 → ℂ) :
    before.eval (before.eval x) = fun i => x (Equiv.swap 0 1 i) := by
  have hp : (before.eval (before.eval x) 0, before.eval (before.eval x) 1) =
      (x 1, x 0) := by
    change mixer (mixer (x 0, x 1)) = (x 1, x 0)
    exact mixer_square _
  funext i
  fin_cases i
  · simpa using congrArg Prod.fst hp
  · simpa using congrArg Prod.snd hp
  · rfl

theorem native_split_fourth (x : Fin 3 → ℂ) :
    before.eval (before.eval (before.eval (before.eval x))) = x := by
  rw [native_split_square, native_split_square]
  funext i
  simp

/-- The concrete native split has its third iterate as a two-sided inverse. -/
def nativeSplitEquiv : (Fin 3 → ℂ) ≃ (Fin 3 → ℂ) where
  toFun := before.eval
  invFun x := before.eval (before.eval (before.eval x))
  left_inv := native_split_fourth
  right_inv := native_split_fourth

theorem nativeSplitEquiv_vacuum : nativeSplitEquiv 0 = 0 :=
  map_zero before.eval

/-- Concrete reversibility and vacuum covariance coexist with residual change. -/
theorem native_pullback_changes_residual (k : ℕ) (hk : 1 < k) :
    pullback nativeSplitEquiv (residualEffect k (by omega)) ≠
      residualEffect k (by omega) := by
  intro heq
  have he := congrArg (fun e : Effect (Fin 3 → ℂ) => (e basis : ℝ)) heq
  change residual k (before.eval basis) = residual k basis at he
  have hk1 := (native_split_residual_invariant_iff k (by omega)).1 he
  omega

/-- A least effect exists, yet a different chosen residual need not be fixed. -/
theorem native_full_effect_countercontrol (k : ℕ) (hk : 1 < k) :
    IsLeast (vacuumCertain (0 : Fin 3 → ℂ)) (vacuumIndicator 0) ∧
    residualEffect k (by omega) ∈ vacuumCertain (0 : Fin 3 → ℂ) ∧
    (∀ e, e ∈ vacuumCertain (0 : Fin 3 → ℂ) ↔
      pullback nativeSplitEquiv e ∈ vacuumCertain (0 : Fin 3 → ℂ)) ∧
    (∀ s e, evaluate (nativeSplitEquiv s) e =
      evaluate s (pullback nativeSplitEquiv e)) ∧
    pullback nativeSplitEquiv (residualEffect k (by omega)) ≠
      residualEffect k (by omega) :=
  ⟨vacuumIndicator_least _, residualEffect_vacuum_certain k (by omega),
    pullback_preserves_vacuum_certainty nativeSplitEquiv _ nativeSplitEquiv_vacuum,
    pullback_covariance nativeSplitEquiv, native_pullback_changes_residual k hk⟩

end

end IDT.QMClosure.VacuumSupportEffectBoundary
