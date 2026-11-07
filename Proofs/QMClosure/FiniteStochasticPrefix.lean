import Proofs.QMClosure.NativeFiniteStochasticReadoutWall
import Proofs.QMClosure.NativeVacuumProbabilityFamily

/-!
# Exact finite prefixes by a supplied stochastic clock

For each supplied probability table and horizon N, this construction chooses
N+1 states, one fixed transition matrix, one initial distribution and one fixed
readout. The whole table is encoded in that readout. The terminal state absorbs,
so the extension after N is constant. This is one model per horizon, not one
finite model for all horizons. It supplies no probability origin, detector law,
independent prediction, asymptotic approximation, physical preparation mechanism,
or QM closure. In particular it does not contradict the uniform stochastic wall.
-/

namespace IDT.QMClosure.FiniteStochasticPrefix

noncomputable section

open Finset Function

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- A deterministic map regarded as a real row-stochastic matrix. -/
def deterministicMatrix (step : S → S) : Matrix S S ℝ :=
  fun i j => if j = step i then 1 else 0

theorem deterministicMatrix_rowStochastic (step : S → S) :
    deterministicMatrix step ∈ Matrix.rowStochastic ℝ S := by
  apply Matrix.mem_rowStochastic_iff_sum.mpr
  constructor
  · intro i j
    simp only [deterministicMatrix]
    split_ifs <;> norm_num
  · intro i
    simp [deterministicMatrix]

theorem deterministicMatrix_mulVec (step : S → S) (r : S → ℂ) (i : S) :
    (FiniteStochasticPeripheral.complexify (deterministicMatrix step)).mulVec r i =
      r (step i) := by
  simp [FiniteStochasticPeripheral.complexify, deterministicMatrix,
    Matrix.mulVec, dotProduct, apply_ite]

/-- Powers use the same transition matrix at every depth. -/
theorem deterministicMatrix_pow_mulVec (step : S → S) (r : S → ℂ)
    (n : ℕ) (i : S) :
    ((FiniteStochasticPeripheral.complexify (deterministicMatrix step)) ^ n).mulVec r i =
      r ((step^[n]) i) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, deterministicMatrix_mulVec, ih,
        iterate_succ_apply]

/-- An N+1-state clock which remains at N after reaching it. -/
def clockStep (N : ℕ) (i : Fin (N + 1)) : Fin (N + 1) :=
  ⟨min (i.val + 1) N, by omega⟩

def clockMatrix (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  deterministicMatrix (clockStep N)

def initial (N : ℕ) (i : Fin (N + 1)) : ℝ :=
  if i = 0 then 1 else 0

/-- This readout explicitly stores the supplied table; it does not derive it. -/
def readout (N : ℕ) (g : ℕ → ℝ) (i : Fin (N + 1)) : ℝ := g i.val

theorem clock_card (N : ℕ) : Fintype.card (Fin (N + 1)) = N + 1 := by simp

theorem clockMatrix_rowStochastic (N : ℕ) :
    clockMatrix N ∈ Matrix.rowStochastic ℝ (Fin (N + 1)) :=
  deterministicMatrix_rowStochastic _

theorem initial_nonnegative (N : ℕ) (i : Fin (N + 1)) : 0 ≤ initial N i := by
  simp only [initial]
  split_ifs <;> norm_num

theorem initial_normalized (N : ℕ) : ∑ i, initial N i = 1 := by
  simp [initial]

theorem readout_bounds (N : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k ≤ N, 0 ≤ g k ∧ g k ≤ 1) (i : Fin (N + 1)) :
    0 ≤ readout N g i ∧ readout N g i ≤ 1 :=
  hg i.val (by omega)

theorem clockStep_iterate_val (N n : ℕ) (i : Fin (N + 1)) :
    ((clockStep N)^[n] i).val = min (i.val + n) N := by
  induction n with
  | zero => simp; omega
  | succ n ih =>
      rw [iterate_succ_apply']
      change min (((clockStep N)^[n] i).val + 1) N = _
      rw [ih]
      omega

/-- Exact prediction in the same matrix semantics as the uniform stochastic wall. -/
theorem prediction_eq_terminal_extension (N : ℕ) (g : ℕ → ℝ) (n : ℕ) :
    NativeFiniteStochasticReadoutWall.prediction (clockMatrix N)
      (fun i => (initial N i : ℂ)) (fun i => (readout N g i : ℂ)) n =
        (g (min n N) : ℂ) := by
  simp only [NativeFiniteStochasticReadoutWall.prediction, clockMatrix,
    deterministicMatrix_pow_mulVec]
  simp [initial, readout, clockStep_iterate_val, apply_ite]

theorem prediction_eq_prefix (N : ℕ) (g : ℕ → ℝ) (n : ℕ) (hn : n ≤ N) :
    NativeFiniteStochasticReadoutWall.prediction (clockMatrix N)
      (fun i => (initial N i : ℂ)) (fun i => (readout N g i : ℂ)) n = (g n : ℂ) := by
  rw [prediction_eq_terminal_extension, Nat.min_eq_left hn]

/-- The native supplied squared-norm semantics has probability-table bounds.
The canonical law here is only an explicit mathematical consistency witness. -/
theorem native_selectedWeight_bounds (n : ℕ) :
    0 ≤ NativeThreeWireProbabilityDenominator.selectedWeight n ∧
      NativeThreeWireProbabilityDenominator.selectedWeight n ≤ 1 := by
  let L := NativeVacuumProbabilityFamily.canonicalLaw
  have heq : L.prob (0 : Fin 3)
      (NativeThreeWireProbabilityDenominator.repeatedWord n) 0 =
      NativeThreeWireProbabilityDenominator.selectedWeight n := by
    change Complex.normSq
      ((NativeThreeWireProbabilityDenominator.repeatedWord n).eval
        (NativeVacuumProbabilityFamily.source (0 : Fin 3)) 0) = _
    rw [show NativeVacuumProbabilityFamily.source (0 : Fin 3) =
      NativeThreeWireProbabilityDenominator.source from
        NativeThreeWireProbabilityDenominator.source_eq_single.symm]
    exact NativeThreeWireProbabilityDenominator.repeatedWord_selectedWeight n
  rw [← heq]
  constructor
  · exact L.nonnegative _ _ _
  · calc
      _ ≤ ∑ i, L.prob (0 : Fin 3)
          (NativeThreeWireProbabilityDenominator.repeatedWord n) i :=
        single_le_sum (fun i _ => L.nonnegative _ _ i) (mem_univ 0)
      _ = 1 := L.normalized _ _

/-- The readout table is the supplied native sequence restricted to N+1 states. -/
theorem native_readout_bounds (N : ℕ) (i : Fin (N + 1)) :
    0 ≤ readout N NativeThreeWireProbabilityDenominator.selectedWeight i ∧
      readout N NativeThreeWireProbabilityDenominator.selectedWeight i ≤ 1 :=
  native_selectedWeight_bounds i.val

/-- Every fixed finite native prefix is exactly reproduced by this explicit model. -/
theorem native_prediction_eq_prefix (N n : ℕ) (hn : n ≤ N) :
    NativeFiniteStochasticReadoutWall.prediction (clockMatrix N)
      (fun i => (initial N i : ℂ))
      (fun i => (readout N NativeThreeWireProbabilityDenominator.selectedWeight i : ℂ)) n =
        (NativeThreeWireProbabilityDenominator.selectedWeight n : ℂ) :=
  prediction_eq_prefix N _ n hn

end

end IDT.QMClosure.FiniteStochasticPrefix
