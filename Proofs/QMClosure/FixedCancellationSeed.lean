import Proofs.QMClosure.CoherentReferencePositivity

namespace IDT.QMClosure.FixedCancellationSeed

open CoherentReference

/-!
# Integer reference tests from one supplied cancellation seed

The pair-kernel representation, tensor rule, admission of this particular seed,
arbitrarily many copies, and all correlated events are supplied assumptions.
This file does not derive detector probabilities, the complex carrier or QM.
-/

def seedAmplitude : Fin 3 → ℚ := ![1, 1, -1]

def seed : Kernel (Fin 3) := reference seedAmplitude

def wordAmplitude (k : ℕ) (w : Fin k → Fin 3) : ℚ :=
  ∏ l, seedAmplitude (w l)

theorem seed_normalized : eventWeight seed Finset.univ = 1 := by
  rw [seed, reference_event_is_square]
  norm_num [seedAmplitude, Fin.sum_univ_succ]

theorem seed_power_is_reference (k : ℕ) :
    tensorPower seed k = reference (wordAmplitude k) := by
  funext u v
  simp [tensorPower, seed, reference, wordAmplitude, Finset.prod_mul_distrib]

theorem seed_all_copy_events_nonnegative (k : ℕ)
    (event : Finset (Fin k → Fin 3)) :
    0 ≤ eventWeight (tensorPower seed k) event := by
  rw [seed_power_is_reference]
  exact reference_event_nonnegative _ event

/-- Unary labels suffice: n distinct words of each sign in n+1 copies.
This deliberately avoids claiming an optimal copy count. -/
def signedWord {n : ℕ} (negative : Bool) (j : Fin n) : Fin (n + 1) → Fin 3 :=
  Fin.cases (if negative then 2 else 0) (fun l => if l = j then 1 else 0)

theorem signedWord_injective (n : ℕ) (negative : Bool) :
    Function.Injective (signedWord (n := n) negative) := by
  intro i j h
  have hi := congrFun h i.succ
  simpa [signedWord] using hi

theorem signedWord_amplitude {n : ℕ} (negative : Bool) (j : Fin n) :
    wordAmplitude (n + 1) (signedWord negative j) = if negative then -1 else 1 := by
  simp only [wordAmplitude, Fin.prod_univ_succ, signedWord, Fin.cases_zero,
    Fin.cases_succ]
  have tail : (∏ l : Fin n, seedAmplitude (if l = j then 1 else 0)) = 1 := by
    apply Finset.prod_eq_one
    intro l _
    split_ifs <;> norm_num [seedAmplitude]
  rw [tail]
  cases negative
  · norm_num [seedAmplitude]
  · change (-1 : ℚ) * 1 = -1
    ring

def coefficientWords (n : ℕ) (z : ℤ) : Finset (Fin (n + 1) → Fin 3) :=
  (Finset.univ.filter (fun j : Fin n => j.val < z.natAbs)).image
    (signedWord (decide (z < 0)))

theorem coefficientWords_sum (n : ℕ) (z : ℤ) (bound : z.natAbs ≤ n) :
    (∑ w ∈ coefficientWords n z, wordAmplitude (n + 1) w) = (z : ℚ) := by
  classical
  rw [coefficientWords, Finset.sum_image]
  · simp_rw [signedWord_amplitude]
    rw [Finset.sum_const, nsmul_eq_mul, Fin.card_filter_val_lt, Nat.min_eq_right bound]
    by_cases hz : z < 0
    · simp only [hz, decide_true, ↓reduceIte]
      have h : (z.natAbs : ℤ) = -z := by omega
      have hq : (z.natAbs : ℚ) = -(z : ℚ) := by
        simpa only [Int.cast_natCast, Int.cast_neg] using congrArg (fun a : ℤ => (a : ℚ)) h
      rw [hq]
      ring
    · simp only [hz, decide_false, Bool.false_eq]
      have h : (z.natAbs : ℤ) = z := by omega
      have hq : (z.natAbs : ℚ) = (z : ℚ) := by
        simpa only [Int.cast_natCast] using congrArg (fun a : ℤ => (a : ℚ)) h
      simpa using hq
  · intro i _ j _ h
    exact signedWord_injective n _ h

section Finite

variable {α β : Type*} [Fintype α]

/-- A genuine event: every candidate index chooses a subset of reference words.
The same reference word may be reused at different candidate indices. -/
def correlatedEvent (fibers : α → Finset β) : Finset (α × β) :=
  (Finset.univ.sigma fibers).map
    ⟨fun p => (p.1, p.2), by
      intro a b h
      cases a
      cases b
      cases h
      rfl⟩

theorem correlated_event_weight (K : Kernel α) (a : β → ℚ)
    (fibers : α → Finset β) :
    eventWeight (tensor K (reference a)) (correlatedEvent fibers) =
      quadratic K (fun i => ∑ w ∈ fibers i, a w) := by
  classical
  simp only [eventWeight, correlatedEvent, Finset.sum_map, Finset.sum_sigma,
    tensor, reference, quadratic]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ x ∈ fibers i, ∑ y ∈ fibers j, K i j * (a x * a y)) = _
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem integer_vector_is_seed_event (K : Kernel α) (v : α → ℤ) :
    ∃ k, ∃ event : Finset (α × (Fin k → Fin 3)),
      eventWeight (tensor K (tensorPower seed k)) event =
        quadratic K (fun i => (v i : ℚ)) := by
  classical
  let n := ∑ i, (v i).natAbs
  refine ⟨n + 1, correlatedEvent (fun i => coefficientWords n (v i)), ?_⟩
  rw [seed_power_is_reference, correlated_event_weight]
  congr 1
  funext i
  apply coefficientWords_sum
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (v j).natAbs) (Finset.mem_univ i)

theorem seed_tests_force_integer_quadratic_nonnegative (K : Kernel α)
    (positive : ∀ k (event : Finset (α × (Fin k → Fin 3))),
      0 ≤ eventWeight (tensor K (tensorPower seed k)) event) :
    ∀ v : α → ℤ, 0 ≤ quadratic K (fun i => (v i : ℚ)) := by
  intro v
  obtain ⟨k, event, he⟩ := integer_vector_is_seed_event K v
  rw [← he]
  exact positive k event

theorem quadratic_scale (K : Kernel α) (v : α → ℚ) (c : ℚ) :
    quadratic K (fun i => c * v i) = c ^ 2 * quadratic K v := by
  simp only [quadratic, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A common positive denominator, without approximation or continuity. -/
theorem rational_vector_has_integer_scale (q : α → ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ v : α → ℤ, ∀ i, (v i : ℚ) = (d : ℚ) * q i := by
  classical
  let d := ∏ i, (q i).den
  refine ⟨d, Finset.prod_pos (fun i _ => (q i).den_pos),
    (fun i => (q i).num * (∏ j ∈ Finset.univ.erase i, (q j).den : ℕ)), ?_⟩
  intro i
  have hnum : q i * ((q i).den : ℚ) = ((q i).num : ℚ) := by
    exact (eq_div_iff (by exact_mod_cast (q i).den_ne_zero)).mp
      (Rat.num_div_den (q i)).symm
  dsimp [d]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (q j).den) (Finset.mem_univ i)]
  push_cast
  linear_combination -(∏ j ∈ Finset.univ.erase i, ((q j).den : ℚ)) * hnum

theorem seed_tests_force_quadratic_nonnegative (K : Kernel α)
    (positive : ∀ k (event : Finset (α × (Fin k → Fin 3))),
      0 ≤ eventWeight (tensor K (tensorPower seed k)) event) :
    QuadraticNonnegative K := by
  intro q
  obtain ⟨d, hd, v, hv⟩ := rational_vector_has_integer_scale q
  have h := seed_tests_force_integer_quadratic_nonnegative K positive v
  have heq : (fun i => (v i : ℚ)) = (fun i => (d : ℚ) * q i) := funext hv
  rw [heq, quadratic_scale] at h
  have hp : (0 : ℚ) < (d : ℚ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hd)
  exact nonneg_of_mul_nonneg_right h hp

/-- Rational tests have exact event certificates up to a positive square scale. -/
theorem rational_vector_is_scaled_seed_event (K : Kernel α) (q : α → ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ k, ∃ event : Finset (α × (Fin k → Fin 3)),
      eventWeight (tensor K (tensorPower seed k)) event =
        (d : ℚ) ^ 2 * quadratic K q := by
  obtain ⟨d, hd, v, hv⟩ := rational_vector_has_integer_scale q
  obtain ⟨k, event, he⟩ := integer_vector_is_seed_event K v
  refine ⟨d, hd, k, event, ?_⟩
  rw [he]
  have heq : (fun i => (v i : ℚ)) = (fun i => (d : ℚ) * q i) := funext hv
  rw [heq, quadratic_scale]

theorem negative_quadratic_yields_negative_seed_event (K : Kernel α)
    (q : α → ℚ) (negative : quadratic K q < 0) :
    ∃ k, ∃ event : Finset (α × (Fin k → Fin 3)),
      eventWeight (tensor K (tensorPower seed k)) event < 0 := by
  obtain ⟨d, hd, k, event, he⟩ := rational_vector_is_scaled_seed_event K q
  refine ⟨k, event, ?_⟩
  rw [he]
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos (by exact_mod_cast hd)) negative

theorem candidate_rejected_by_fixed_seed :
    ∃ k, ∃ event : Finset (Bool × (Fin k → Fin 3)),
      eventWeight (tensor candidate (tensorPower seed k)) event = -1 / 2 := by
  obtain ⟨k, event, he⟩ :=
    integer_vector_is_seed_event candidate (fun b : Bool => if b then -2 else 1)
  refine ⟨k, event, ?_⟩
  rw [he]
  have hv : (fun b : Bool => ((if b then -2 else 1 : ℤ) : ℚ)) = signedReference := by
    funext b
    cases b <;> norm_num [signedReference]
  rw [hv]
  exact candidate_has_a_negative_signed_direction

end Finite

end IDT.QMClosure.FixedCancellationSeed
