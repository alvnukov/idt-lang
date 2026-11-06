import Proofs.QMClosure.NativeBinaryPhaseCounting

/-!
# Binary leaves and exact modulo-four phase cardinalities

Leaves are explicit finite binary words, extended by one Boolean at each depth.
This module identifies their phase-fibre cardinalities with the checked phase
count recurrence and groups arbitrary real weights by phase. It has no circuit
or probability-law assumptions; the native refinement adapter remains separate.
-/

namespace IDT.QMClosure.NativeBinaryLeaves

noncomputable section
open scoped BigOperators
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def Leaf : ℕ → Type
  | 0 => PUnit
  | n + 1 => Leaf n × Bool

instance leafFintype (n : ℕ) : Fintype (Leaf n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => letI := ih; exact inferInstanceAs (Fintype (Leaf n × Bool))

instance leafDecidableEq (n : ℕ) : DecidableEq (Leaf n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ n ih => letI := ih; exact inferInstanceAs (DecidableEq (Leaf n × Bool))

def phaseNext : Fin 4 → Fin 4 := ![1, 2, 3, 0]

def phase : (n : ℕ) → Leaf n → Fin 4
  | 0, _ => 0
  | n + 1, (w, false) => phase n w
  | n + 1, (w, true) => phaseNext (phase n w)

/-- The embedding of the subtree whose first split took the retained A branch. -/
def rootA : (n : ℕ) → Leaf n → Leaf (n + 1)
  | 0, _ => (PUnit.unit, false)
  | n + 1, (w, b) => (rootA n w, b)

theorem rootA_phase (n : ℕ) (w : Leaf n) :
    phase (n + 1) (rootA n w) = phase n w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases w with ⟨w, b⟩
    cases b <;> simp [phase, rootA, ih]

theorem phaseNext_eq_iff (j r : Fin 4) :
    phaseNext j = r ↔ j = NativeBinaryPhaseCounting.phasePred r := by
  fin_cases j <;> fin_cases r <;> decide

/-- The actual finite cardinality of a phase fibre, expressed as an indicator sum. -/
def leafCount (n : ℕ) (j : Fin 4) : ℕ :=
  ∑ w : Leaf n, if phase n w = j then 1 else 0

theorem leafCount_zero : leafCount 0 = ![1, 0, 0, 0] := by
  funext j
  fin_cases j <;> simp [leafCount, Leaf, phase]

theorem leafCount_succ (n : ℕ) (j : Fin 4) :
    leafCount (n + 1) j = leafCount n j +
      leafCount n (NativeBinaryPhaseCounting.phasePred j) := by
  unfold leafCount
  change (∑ w : Leaf n × Bool, if phase (n + 1) w = j then 1 else 0) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, phase,
    phaseNext_eq_iff, Finset.sum_add_distrib]
  exact add_comm _ _

/-- The count recurrence is now identified with explicit binary-leaf fibres. -/
theorem leafCount_eq (n : ℕ) : leafCount n = NativeBinaryPhaseCounting.phaseCount n :=
  NativeBinaryPhaseCounting.phaseCount_unique leafCount leafCount_zero leafCount_succ n

theorem sum_by_phase (n : ℕ) (q : Fin 4 → ℝ) :
    (∑ w : Leaf n, q (phase n w)) =
      ∑ j, (NativeBinaryPhaseCounting.phaseCount n j : ℝ) * q j := by
  rw [← leafCount_eq]
  symm
  calc
    (∑ j, (leafCount n j : ℝ) * q j) =
        ∑ j, ∑ w : Leaf n, if phase n w = j then q j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [leafCount, Nat.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro w _
      split_ifs <;> norm_num
    _ = ∑ w : Leaf n, ∑ j : Fin 4, if phase n w = j then q j else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by simp

end
end IDT.QMClosure.NativeBinaryLeaves
