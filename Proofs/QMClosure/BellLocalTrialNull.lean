import Mathlib
import Proofs.QMClosure.ContextFirstBellCountermodel

namespace IDT.QMClosure.BellLocalTrialNull

/-!
# Conditional local-CHSH fixed-trial risk bound

Local response tables are an additional candidate restriction, not a consequence
of the context-first primitive base. Setting weights, their conditional product
structure, and any experimental bias calibration are hypotheses. The probability
tree allows arbitrary dependence on earlier wins/losses; it assumes neither
identical trial distributions nor independence between trials.

The result concerns a fixed trial count and a fixed win threshold. It does not
justify optional stopping, certify physical setting independence, verify a data
adapter or its Python arithmetic, or prove QM or reject the primitive base.
-/

def localWin (a0 a1 b0 b1 a b : Bool) : Prop :=
  (if a && b then (-1 : ℤ) else 1) *
    boolOutcomeSign (if a then a1 else a0) *
    boolOutcomeSign (if b then b1 else b0) = 1

instance (a0 a1 b0 b1 a b : Bool) : Decidable (localWin a0 a1 b0 b1 a b) :=
  inferInstanceAs (Decidable (_ = (1 : ℤ)))

def localWinCount (a0 a1 b0 b1 : Bool) : ℕ :=
  (if localWin a0 a1 b0 b1 false false then 1 else 0) +
  (if localWin a0 a1 b0 b1 false true then 1 else 0) +
  (if localWin a0 a1 b0 b1 true false then 1 else 0) +
  (if localWin a0 a1 b0 b1 true true then 1 else 0)

theorem local_response_table_wins_at_most_three (a0 a1 b0 b1 : Bool) :
    localWinCount a0 a1 b0 b1 ≤ 3 := by
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;>
    norm_num [localWinCount, localWin, boolOutcomeSign]

def localWinMass (a0 a1 b0 b1 : Bool) (w : Bool → Bool → ℝ) : ℝ :=
  (if localWin a0 a1 b0 b1 false false then w false false else 0) +
  (if localWin a0 a1 b0 b1 false true then w false true else 0) +
  (if localWin a0 a1 b0 b1 true false then w true false else 0) +
  (if localWin a0 a1 b0 b1 true true then w true true else 0)

theorem local_win_mass_probability_bounds (a0 a1 b0 b1 : Bool)
    (w : Bool → Bool → ℝ) (hw : ∀ a b, 0 ≤ w a b)
    (hnorm : w false false + w false true + w true false + w true true = 1) :
    0 ≤ localWinMass a0 a1 b0 b1 w ∧ localWinMass a0 a1 b0 b1 w ≤ 1 := by
  have h00 := hw false false
  have h01 := hw false true
  have h10 := hw true false
  have h11 := hw true true
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;>
    norm_num [localWinMass, localWin, boolOutcomeSign] <;> constructor <;> linarith

/-- The cap alone suffices for this upper bound; a probability interpretation
additionally requires nonnegative normalized setting weights. -/
theorem local_win_mass_le_three_mul (a0 a1 b0 b1 : Bool)
    (w : Bool → Bool → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hw : ∀ a b, w a b ≤ u) :
    localWinMass a0 a1 b0 b1 w ≤ 3 * u := by
  have h00 := hw false false
  have h01 := hw false true
  have h10 := hw true false
  have h11 := hw true true
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;>
    norm_num [localWinMass, localWin, boolOutcomeSign] <;> linarith

/-- A finite hidden-variable mixture preserves the local per-trial cap. -/
theorem finite_local_mixture_win_le {ι : Type*} (s : Finset ι)
    (μ : ι → ℝ) (a0 a1 b0 b1 : ι → Bool)
    (w : ι → Bool → Bool → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hμ : ∀ i ∈ s, 0 ≤ μ i) (hnorm : ∑ i ∈ s, μ i = 1)
    (hw : ∀ i ∈ s, ∀ a b, w i a b ≤ u) :
    ∑ i ∈ s, μ i * localWinMass (a0 i) (a1 i) (b0 i) (b1 i) (w i) ≤
      3 * u := by
  calc
    _ ≤ ∑ i ∈ s, μ i * (3 * u) := Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left
        (local_win_mass_le_three_mul _ _ _ _ _ _ hu (hw i hi)) (hμ i hi)
    _ = 3 * u := by rw [← Finset.sum_mul, hnorm, one_mul]

noncomputable def biasAdjustedBound (τ : ℝ) : ℝ := 3 * (1 / 2 + τ) ^ 2

theorem bias_adjusted_bound_source_formula (τ : ℝ) :
    biasAdjustedBound τ = 3 / 4 + 3 * (τ + τ ^ 2) := by
  unfold biasAdjustedBound
  ring

/-- Product structure is an explicit hypothesis, not a physical derivation. -/
theorem product_setting_cell_le (pa pb : Bool → ℝ) (τ : ℝ)
    (hτ : 0 ≤ 1 / 2 + τ)
    (ha : ∀ a, 0 ≤ pa a ∧ pa a ≤ 1 / 2 + τ)
    (hb : ∀ b, 0 ≤ pb b ∧ pb b ≤ 1 / 2 + τ) (a b : Bool) :
    pa a * pb b ≤ (1 / 2 + τ) ^ 2 := by
  simpa [pow_two] using mul_le_mul (ha a).2 (hb b).2 (hb b).1 hτ

theorem local_product_settings_bias_bound (a0 a1 b0 b1 : Bool)
    (pa pb : Bool → ℝ) (τ : ℝ) (hτ : 0 ≤ 1 / 2 + τ)
    (ha : ∀ a, 0 ≤ pa a ∧ pa a ≤ 1 / 2 + τ)
    (hb : ∀ b, 0 ≤ pb b ∧ pb b ≤ 1 / 2 + τ) :
    localWinMass a0 a1 b0 b1 (fun a b => pa a * pb b) ≤
      biasAdjustedBound τ := by
  exact local_win_mass_le_three_mul _ _ _ _ _ _ (sq_nonneg _)
    (product_setting_cell_le pa pb τ hτ ha hb)

/-- Real binomial-tail recurrence, including impossible thresholds.
The exact rational Python implementation is not formally verified here. -/
def binomialTail (q : ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => q * binomialTail q n k + (1 - q) * binomialTail q n (k + 1)

theorem binomial_tail_zero (q : ℝ) (n : ℕ) : binomialTail q n 0 = 1 := by
  cases n <;> rfl

theorem binomial_tail_bounds (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (n k : ℕ) : 0 ≤ binomialTail q n k ∧ binomialTail q n k ≤ 1 := by
  induction n generalizing k with
  | zero => cases k <;> norm_num [binomialTail]
  | succ n ih =>
    cases k with
    | zero => norm_num [binomialTail]
    | succ k =>
      have h₀ := ih k
      have h₁ := ih (k + 1)
      constructor
      · exact add_nonneg (mul_nonneg hq0 h₀.1) (mul_nonneg (by linarith) h₁.1)
      · dsimp [binomialTail]
        nlinarith [mul_nonneg hq0 (sub_nonneg.mpr h₀.2),
          mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr h₁.2)]

theorem binomial_tail_threshold_antitone (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (n k : ℕ) : binomialTail q n (k + 1) ≤ binomialTail q n k := by
  induction n generalizing k with
  | zero => cases k <;> norm_num [binomialTail]
  | succ n ih =>
    cases k with
    | zero => simpa [binomial_tail_zero] using (binomial_tail_bounds q hq0 hq1 (n + 1) 1).2
    | succ k =>
      dsimp [binomialTail]
      exact add_le_add (mul_le_mul_of_nonneg_left (ih k) hq0)
        (mul_le_mul_of_nonneg_left (ih (k + 1)) (by linarith))

/-- Every history has its own probability and its own two continuation trees. -/
inductive TrialTree : ℕ → Type where
  | leaf : TrialTree 0
  | node {n : ℕ} (p : ℝ) (win lose : TrialTree n) : TrialTree (n + 1)

def TrialTree.Valid (q : ℝ) : {n : ℕ} → TrialTree n → Prop
  | _, .leaf => True
  | _, .node p win lose => 0 ≤ p ∧ p ≤ q ∧ win.Valid q ∧ lose.Valid q

def TrialTree.tail : {n : ℕ} → TrialTree n → ℕ → ℝ
  | _, .leaf, 0 => 1
  | _, .leaf, _ + 1 => 0
  | _, .node _ _ _, 0 => 1
  | _, .node p win lose, k + 1 => p * win.tail k + (1 - p) * lose.tail (k + 1)

theorem valid_tree_tail_probability_bounds (q : ℝ) (hq1 : q ≤ 1)
    {n : ℕ} (tree : TrialTree n) (valid : tree.Valid q) (k : ℕ) :
    0 ≤ tree.tail k ∧ tree.tail k ≤ 1 := by
  induction tree generalizing k with
  | leaf => cases k <;> norm_num [TrialTree.tail]
  | node p win lose ihwin ihlose =>
    rcases valid with ⟨hp0, hpq, hwin, hlose⟩
    cases k with
    | zero => norm_num [TrialTree.tail]
    | succ k =>
      have hw := ihwin hwin k
      have hl := ihlose hlose (k + 1)
      have hp1 : 0 ≤ 1 - p := by linarith
      constructor
      · exact add_nonneg (mul_nonneg hp0 hw.1) (mul_nonneg hp1 hl.1)
      · dsimp [TrialTree.tail]
        nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hw.2),
          mul_nonneg hp1 (sub_nonneg.mpr hl.2)]

/-- Universal fixed-N domination, allowing arbitrary history-dependent memory. -/
theorem valid_tree_tail_le_binomial (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {n : ℕ} (tree : TrialTree n) (valid : tree.Valid q) (k : ℕ) :
    tree.tail k ≤ binomialTail q n k := by
  induction tree generalizing k with
  | leaf => cases k <;> simp [TrialTree.tail, binomialTail]
  | @node n p win lose ihwin ihlose =>
    rcases valid with ⟨hp0, hpq, hwin, hlose⟩
    cases k with
    | zero => simp [TrialTree.tail, binomialTail]
    | succ k =>
      have hp1 : 0 ≤ 1 - p := by linarith
      have hw := ihwin hwin k
      have hl := ihlose hlose (k + 1)
      have hm := binomial_tail_threshold_antitone q hq0 hq1 n k
      dsimp [TrialTree.tail, binomialTail]
      calc
        _ ≤ p * binomialTail q n k + (1 - p) * binomialTail q n (k + 1) :=
          add_le_add (mul_le_mul_of_nonneg_left hw hp0) (mul_le_mul_of_nonneg_left hl hp1)
        _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hm)]

/-- A pre-fixed threshold with tail at most alpha controls false rejection. -/
theorem fixed_trial_threshold_risk_control (q α : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {n : ℕ} (tree : TrialTree n) (valid : tree.Valid q) (critical : ℕ)
    (hcritical : binomialTail q n critical ≤ α) : tree.tail critical ≤ α :=
  le_trans (valid_tree_tail_le_binomial q hq0 hq1 tree valid critical) hcritical

end IDT.QMClosure.BellLocalTrialNull
