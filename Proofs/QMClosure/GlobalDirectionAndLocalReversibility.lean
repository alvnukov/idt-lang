import Mathlib

/-!
# Full-state descent, recurrence, and conditional reversal

The map and score below are fixed on the entire stated state space. A positive
full-state return and all-state nonincrease force equality on that orbit step.
The reversal result retains nonincrease and explicitly supplies both its
reversal relation and reversal-invariant score. No physical time-reversal law,
positivity, entropy, energy, cosmological interpretation, or QM/GR conclusion
is asserted.

Two involutions can compose to an aperiodic translation. The example's score
does not descend under both involutions. An arbitrary local map can also be
extended by a manually supplied integer clock: every chosen readout through
the local projection is preserved while the clock score strictly descends.
Observations of the whole extended state may detect the clock. This construction
selects no local dynamics or readout and supplies no physical arrow mechanism.

The separate existing `NativeMixerInfiniteOrder.lean` artifact proves
`native_word_infinite_order`: every positive power of one fixed native matrix
is nonidentity. That map-level result is not an assertion that all its orbits
are nonperiodic; its native proof is not duplicated here.
-/

namespace IDT.QMClosure.GlobalDirectionAndLocalReversibility

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

section Score

variable [PartialOrder β]

theorem score_iterate_le (T : α → α) (F : α → β)
    (hdesc : ∀ x, F (T x) ≤ F x) (n : ℕ) (x : α) : F (T^[n] x) ≤ F x := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      simpa only [Function.iterate_succ_apply'] using (hdesc (T^[n] x)).trans ih

/-- This premise is a return of the entire state, not merely of an observation. -/
theorem score_eq_of_positive_return (T : α → α) (F : α → β)
    (hdesc : ∀ x, F (T x) ≤ F x) (n : ℕ) (x : α)
    (hn : 0 < n) (hreturn : T^[n] x = x) : F (T x) = F x := by
  cases n with
  | zero => omega
  | succ n =>
      have hback := score_iterate_le T F hdesc n (T x)
      have hreturn' : T^[n] (T x) = x := by
        simpa only [Function.iterate_succ_apply] using hreturn
      rw [hreturn'] at hback
      exact le_antisymm (hdesc x) hback

theorem score_eq_of_pointwise_periodic (T : α → α) (F : α → β)
    (hdesc : ∀ x, F (T x) ≤ F x)
    (hperiodic : ∀ x, ∃ n : ℕ, 0 < n ∧ T^[n] x = x) (x : α) :
    F (T x) = F x := by
  obtain ⟨n, hn, hreturn⟩ := hperiodic x
  exact score_eq_of_positive_return T F hdesc n x hn hreturn

theorem finite_perm_score_invariant [Finite α] (e : Equiv.Perm α) (F : α → β)
    (hdesc : ∀ x, F (e x) ≤ F x) (x : α) : F (e x) = F x := by
  classical
  letI := Fintype.ofFinite α
  apply score_eq_of_positive_return (e : α → α) F hdesc (orderOf e) x (orderOf_pos e)
  change (e ^ orderOf e) x = x
  rw [pow_orderOf_eq_one]
  rfl

/-- Both reversal hypotheses and all-state descent are supplied conditions. -/
theorem score_eq_of_reversal (T R : α → α) (F : α → β)
    (hdesc : ∀ x, F (T x) ≤ F x)
    (hreverse : ∀ x, T (R (T x)) = R x)
    (hscore : ∀ x, F (R x) = F x) (x : α) : F (T x) = F x := by
  have hback := hdesc (R (T x))
  rw [hreverse x, hscore x, hscore (T x)] at hback
  exact le_antisymm (hdesc x) hback

end Score

/-! ## Two involutions whose composition has no positive return -/

def integerA (n : ℤ) : ℤ := -n
def integerB (n : ℤ) : ℤ := 1 - n

theorem integerA_involutive : Function.Involutive integerA := by
  intro n
  simp [integerA]

theorem integerB_involutive : Function.Involutive integerB := by
  intro n
  dsimp [integerB]
  omega

def integerTranslation : ℤ → ℤ := integerB ∘ integerA

theorem integerTranslation_apply (n : ℤ) : integerTranslation n = n + 1 := by
  dsimp [integerTranslation, integerA, integerB]
  omega

theorem integerTranslation_iterate (k : ℕ) (n : ℤ) :
    integerTranslation^[k] n = n + (k : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', integerTranslation_apply, ih]
      push_cast
      omega

theorem integerTranslation_no_positive_return (k : ℕ) (hk : 0 < k) (n : ℤ) :
    integerTranslation^[k] n ≠ n := by
  rw [integerTranslation_iterate]
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  omega

def integerScore (n : ℤ) : ℤ := -n

theorem integerTranslation_strict_descent (n : ℤ) :
    integerScore (integerTranslation n) < integerScore n := by
  rw [integerTranslation_apply]
  dsimp [integerScore]
  omega

theorem integerA_not_globally_descending :
    ¬ (∀ n : ℤ, integerScore (integerA n) ≤ integerScore n) := by
  intro h
  have h1 := h 1
  norm_num [integerA, integerScore] at h1

theorem integerB_not_globally_descending :
    ¬ (∀ n : ℤ, integerScore (integerB n) ≤ integerScore n) := by
  intro h
  have h1 := h 1
  norm_num [integerB, integerScore] at h1

/-! ## An arbitrary local map with a manually appended clock -/

def clockLift (f : α → α) (p : α × ℤ) : α × ℤ := (f p.1, p.2 + 1)

theorem clockLift_iterate (f : α → α) (k : ℕ) (p : α × ℤ) :
    (clockLift f)^[k] p = (f^[k] p.1, p.2 + (k : ℤ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      apply Prod.ext
      · change f (f^[k] p.1) = f^[k+1] p.1
        rw [Function.iterate_succ_apply']
      · change p.2 + (k : ℤ) + 1 = p.2 + ((k+1 : ℕ) : ℤ)
        push_cast
        ring

/-- Only this chosen readout ignores the appended coordinate. -/
def projectedReadout (r : α → γ) (p : α × ℤ) : γ := r p.1

theorem clockLift_readout_iterate (f : α → α) (r : α → γ) (k : ℕ) (p : α × ℤ) :
    projectedReadout r ((clockLift f)^[k] p) = r (f^[k] p.1) := by
  rw [clockLift_iterate]
  rfl

def clockScore (p : α × ℤ) : ℤ := -p.2

theorem clockLift_strict_descent (f : α → α) (p : α × ℤ) :
    clockScore (clockLift f p) < clockScore p := by
  dsimp [clockScore, clockLift]
  omega

theorem clockLift_no_positive_return (f : α → α) (k : ℕ) (hk : 0 < k) (p : α × ℤ) :
    (clockLift f)^[k] p ≠ p := by
  intro h
  have hs : p.2 + (k : ℤ) = p.2 := by
    simpa only [clockLift_iterate] using congrArg Prod.snd h
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  omega

theorem clockLift_bijective (f : α → α) (hf : Function.Bijective f) :
    Function.Bijective (clockLift f) := by
  constructor
  · intro p q h
    have hx : f p.1 = f q.1 := congrArg Prod.fst h
    have hn : p.2 + 1 = q.2 + 1 := congrArg Prod.snd h
    exact Prod.ext (hf.1 hx) (by omega)
  · rintro ⟨y, n⟩
    obtain ⟨x, hx⟩ := hf.2 y
    refine ⟨(x, n-1), ?_⟩
    apply Prod.ext
    · exact hx
    · change n - 1 + 1 = n
      omega

/-! ## A compact projected four-cycle with full-state descent -/

abbrev FourLocal := Bool × Bool

def fourCycle (p : FourLocal) : FourLocal := (p.2, !p.1)

theorem fourCycle_return (p : FourLocal) : fourCycle^[4] p = p := by
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> rfl

theorem local_return_with_full_descent (p : FourLocal × ℤ) :
    ((clockLift fourCycle)^[4] p).1 = p.1 ∧
      (clockLift fourCycle)^[4] p ≠ p ∧
      clockScore (clockLift fourCycle p) < clockScore p := by
  refine ⟨?_, clockLift_no_positive_return fourCycle 4 (by decide) p,
    clockLift_strict_descent fourCycle p⟩
  simp only [clockLift_iterate, fourCycle_return]

end IDT.QMClosure.GlobalDirectionAndLocalReversibility
