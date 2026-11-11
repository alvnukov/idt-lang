import Proofs.QMClosure.OriginalMaskLocalKernel

/-!
# Complete finite dependency circuits on original mask bits

Nodes have fixed finite parent lists, arbitrary total real-valued gate
functions, and a rank that strictly decreases along every dependency. Parent
indices may be repeated and may be shared among arbitrarily many nodes.

Unrolling preserves every solution of the circuit equations. The induction
counts distinct original ancestors by a union bound, so sharing is allowed.
Reported output is explicitly a finite sum of terminal values. This external
additive collector is outside the bounded-fanin/depth mechanism. Each summand
has its own complete dependency graph. The number of terminal values and the
fanout of every node are unrestricted.

Every operation that changes a terminal value must occur within this graph.
Application to a physical apparatus additionally supplies the original-bit,
complete-dependency, all-mask-calibration, and additive-reporting contracts.
-/

noncomputable section

namespace IDT.QMClosure.OriginalMaskCircuitAncestry

open scoped BigOperators
open NativeInitialHistoryPresentation
open OriginalOccurrenceKernel
open OriginalMaskLocalKernel

/-- A depth-indexed expression used solely for finite DAG unrolling. -/
inductive Expression (U : Type) (r : ℕ) : ℕ → Type
  | input {d : ℕ} (t : U) : Expression U r d
  | constant {d : ℕ} (c : ℝ) : Expression U r d
  | gate {d : ℕ} (arity : ℕ) (fanin : arity ≤ r)
      (function : (Fin arity → ℝ) → ℝ)
      (parent : Fin arity → Expression U r d) : Expression U r (d + 1)

def Expression.eval {U : Type} [DecidableEq U] {r d : ℕ} :
    Expression U r d → Finset U → ℝ
  | .input t, S => if t ∈ S then 1 else 0
  | .constant c, _ => c
  | .gate _ _ f parent, S => f (fun j => (parent j).eval S)

def Expression.support {U : Type} [DecidableEq U] {r d : ℕ} :
    Expression U r d → Finset U
  | .input t => {t}
  | .constant _ => ∅
  | .gate _ _ _ parent => Finset.univ.biUnion (fun j => (parent j).support)

theorem one_le_power (r : ℕ) (hr : 1 ≤ r) (d : ℕ) : 1 ≤ r ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [pow_succ]
      exact (show 1 * 1 ≤ r ^ d * r from Nat.mul_le_mul ih hr)

/-- Only fanin and depth enter the ancestry cardinal bound. -/
theorem Expression.support_card_le {U : Type} [DecidableEq U] {r d : ℕ}
    (x : Expression U r d) (hr : 1 ≤ r) : x.support.card ≤ r ^ d := by
  classical
  induction d with
  | zero => cases x <;> simp [Expression.support]
  | succ d ih =>
      cases x with
      | input t =>
          simpa [Expression.support] using one_le_power r hr (d + 1)
      | constant c => simp [Expression.support]
      | gate k hk f parent =>
          calc
            _ ≤ ∑ j : Fin k, (parent j).support.card := Finset.card_biUnion_le
            _ ≤ ∑ j : Fin k, r ^ d := by
              apply Finset.sum_le_sum
              intro j hj
              exact ih (parent j)
            _ = k * r ^ d := by simp
            _ ≤ r * r ^ d := Nat.mul_le_mul_right (r ^ d) hk
            _ = r ^ (d + 1) := by rw [pow_succ, Nat.mul_comm]

/-- The generated support is sufficient for evaluating each unrolled value. -/
theorem Expression.eval_eq_of_inter_eq {U : Type} [DecidableEq U] {r d : ℕ}
    (x : Expression U r d) (S T : Finset U)
    (h : S ∩ x.support = T ∩ x.support) : x.eval S = x.eval T := by
  classical
  induction x generalizing S T with
  | input t =>
      have hmem : (t ∈ S) = (t ∈ T) := by
        simpa [Expression.support] using congrArg (fun A => t ∈ A) h
      simp only [Expression.eval]
      simp only [hmem]
  | constant c => rfl
  | gate k hk f parent ih =>
      apply congrArg f
      funext j
      apply ih j
      apply inter_eq_of_subset _ h
      intro t ht
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, ht⟩

theorem Expression.eval_eq_restricted {U : Type} [DecidableEq U] {r d : ℕ}
    (x : Expression U r d) (S : Finset U) : x.eval S = x.eval (S ∩ x.support) := by
  apply x.eval_eq_of_inter_eq
  simp [Finset.inter_assoc]

/-- Parent indices refer to the same global node set, permitting shared DAGs. -/
inductive Operation (U : Type) (N : ℕ)
  | input (t : U)
  | constant (c : ℝ)
  | gate (arity : ℕ) (function : (Fin arity → ℝ) → ℝ)
      (parent : Fin arity → Fin N)

/-- A finite ranked dependency DAG with an additive terminal report. -/
structure Circuit (U : Type) (r D : ℕ) where
  nodeCount : ℕ
  operation : Fin nodeCount → Operation U nodeCount
  rank : Fin nodeCount → ℕ
  rank_le : ∀ i, rank i ≤ D
  arity_le : ∀ i, match operation i with
    | .gate k _ _ => k ≤ r
    | _ => True
  parent_rank : ∀ i, match operation i with
    | .gate _ _ parent => ∀ j, rank (parent j) < rank i
    | _ => True
  outputCount : ℕ
  terminal : Fin outputCount → Fin nodeCount

/-- A larger fanin ceiling keeps every node, gate, rank, and terminal fixed. -/
def Circuit.weakenFanin {U : Type} {r s D : ℕ} (C : Circuit U r D)
    (hrs : r ≤ s) : Circuit U s D where
  nodeCount := C.nodeCount
  operation := C.operation
  rank := C.rank
  rank_le := C.rank_le
  arity_le i := by
    cases hop : C.operation i with
    | input t => trivial
    | constant c => trivial
    | gate k f parent =>
        have hk : k ≤ r := by simpa [hop] using C.arity_le i
        exact hk.trans hrs
  parent_rank := C.parent_rank
  outputCount := C.outputCount
  terminal := C.terminal

/-- Truncation at zero has an arbitrary fixed value for an unfinished gate.
Rank descent proves that this fallback cannot affect a completed evaluation. -/
def Circuit.unroll {U : Type} {r D : ℕ} (C : Circuit U r D) :
    (d : ℕ) → Fin C.nodeCount → Expression U r d
  | 0, i => match C.operation i with
    | .input t => .input t
    | .constant c => .constant c
    | .gate _ f _ => .constant (f (fun _ => 0))
  | d + 1, i => match h : C.operation i with
    | .input t => .input t
    | .constant c => .constant c
    | .gate k f parent => .gate k (by simpa [h] using C.arity_le i) f
        (fun j => C.unroll d (parent j))

/-- Evaluating one unrolling layer commutes with the fixed node operation. -/
theorem Circuit.eval_unroll_succ {U : Type} [DecidableEq U] {r D : ℕ}
    (C : Circuit U r D) (d : ℕ) (i : Fin C.nodeCount) (S : Finset U) :
    (C.unroll (d + 1) i).eval S = match C.operation i with
      | .input t => if t ∈ S then 1 else 0
      | .constant c => c
      | .gate _ f parent => f (fun j => (C.unroll d (parent j)).eval S) := by
  conv_lhs => unfold Circuit.unroll
  split <;> simp_all only [Expression.eval]

/-- Once the rank is covered, one more unrolling layer preserves the value.
At rank zero, any gate has an empty parent type by strict rank descent. -/
theorem Circuit.unroll_stable {U : Type} [DecidableEq U] {r D : ℕ}
    (C : Circuit U r D) (d : ℕ) (i : Fin C.nodeCount)
    (h : C.rank i ≤ d) (S : Finset U) :
    (C.unroll (d + 1) i).eval S = (C.unroll d i).eval S := by
  induction d generalizing i with
  | zero =>
      rw [C.eval_unroll_succ]
      cases hop : C.operation i with
      | input t => simp [Circuit.unroll, hop, Expression.eval]
      | constant c => simp [Circuit.unroll, hop, Expression.eval]
      | gate k f parent =>
          simp only [hop, Circuit.unroll, Expression.eval]
          apply congrArg f
          funext j
          have hp : ∀ j, C.rank (parent j) < C.rank i := by
            simpa [hop] using C.parent_rank i
          have hj := hp j
          omega
  | succ d ih =>
      rw [C.eval_unroll_succ, C.eval_unroll_succ]
      cases hop : C.operation i with
      | input t => rfl
      | constant c => rfl
      | gate k f parent =>
          apply congrArg f
          funext j
          apply ih (parent j)
          have hp : ∀ j, C.rank (parent j) < C.rank i := by
            simpa [hop] using C.parent_rank i
          have hj := hp j
          omega

def Circuit.value {U : Type} [DecidableEq U] {r D : ℕ}
    (C : Circuit U r D) (i : Fin C.nodeCount) (S : Finset U) : ℝ :=
  (C.unroll D i).eval S

/-- Unrolled values satisfy the actual DAG equations, including shared parents. -/
theorem Circuit.value_equation {U : Type} [DecidableEq U] {r D : ℕ}
    (C : Circuit U r D) (i : Fin C.nodeCount) (S : Finset U) :
    C.value i S = match C.operation i with
      | .input t => if t ∈ S then 1 else 0
      | .constant c => c
      | .gate _ f parent => f (fun j => C.value (parent j) S) := by
  calc
    _ = (C.unroll (D + 1) i).eval S :=
      (C.unroll_stable D i (C.rank_le i) S).symm
    _ = _ := C.eval_unroll_succ D i S

/-- Every assignment satisfying the DAG equations equals its finite unrolling.
This explicitly justifies value preservation when shared DAGs are unrolled. -/
theorem Circuit.value_unique {U : Type} [DecidableEq U] {r D : ℕ}
    (C : Circuit U r D) (S : Finset U) (v : Fin C.nodeCount → ℝ)
    (hv : ∀ i, v i = match C.operation i with
      | .input t => if t ∈ S then 1 else 0
      | .constant c => c
      | .gate _ f parent => f (fun j => v (parent j))) :
    ∀ i, v i = C.value i S := by
  have main : ∀ d, ∀ i, C.rank i = d → v i = C.value i S := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro i hi
        rw [hv i, C.value_equation i S]
        cases hop : C.operation i with
        | input t => rfl
        | constant c => rfl
        | gate k f parent =>
            apply congrArg f
            funext j
            have hp : ∀ j, C.rank (parent j) < C.rank i := by
              simpa [hop] using C.parent_rank i
            exact ih (C.rank (parent j)) (by simpa [hi] using hp j) (parent j) rfl
  intro i
  exact main (C.rank i) i rfl

/-- The report contains exactly the supplied finite sum of terminal values. -/
def Circuit.reported {U : Type} [DecidableEq U] {r D : ℕ}
    (C : Circuit U r D) (S : Finset U) : ℝ :=
  ∑ e : Fin C.outputCount, C.value (C.terminal e) S

/-- Fanin weakening preserves the unique solution of the same DAG equations. -/
theorem Circuit.weakenFanin_value {U : Type} [DecidableEq U] {r s D : ℕ}
    (C : Circuit U r D) (hrs : r ≤ s) (i : Fin C.nodeCount) (S : Finset U) :
    (C.weakenFanin hrs).value i S = C.value i S := by
  exact C.value_unique S (fun j => (C.weakenFanin hrs).value j S)
    (fun j => by
      have h := (C.weakenFanin hrs).value_equation j S
      cases hop : C.operation j <;> simpa [Circuit.weakenFanin, hop] using h) i

theorem Circuit.weakenFanin_reported {U : Type} [DecidableEq U] {r s D : ℕ}
    (C : Circuit U r D) (hrs : r ≤ s) (S : Finset U) :
    (C.weakenFanin hrs).reported S = C.reported S := by
  classical
  change (∑ e : Fin C.outputCount, (C.weakenFanin hrs).value (C.terminal e) S) =
    ∑ e : Fin C.outputCount, C.value (C.terminal e) S
  apply Finset.sum_congr rfl
  intro e he
  exact C.weakenFanin_value hrs (C.terminal e) S

/-- Every terminal support is generated by original-bit ancestry. -/
def Circuit.toLocalApparatus {U : Type} [Fintype U] [DecidableEq U] {r D : ℕ}
    (C : Circuit U r D) (hr : 1 ≤ r) : LocalApparatus U (r ^ D) where
  Output := Fin C.outputCount
  finiteOutput := inferInstance
  support e := (C.unroll D (C.terminal e)).support
  support_le e := (C.unroll D (C.terminal e)).support_card_le hr
  localValue e M := C.value (C.terminal e) M

theorem Circuit.localApparatus_value {U : Type} [Fintype U] [DecidableEq U] {r D : ℕ}
    (C : Circuit U r D) (hr : 1 ≤ r) (S : Finset U) :
    (C.toLocalApparatus hr).value S = C.reported S := by
  classical
  unfold LocalApparatus.value Circuit.toLocalApparatus Circuit.reported Circuit.value
  apply Finset.sum_congr rfl
  intro e he
  exact ((C.unroll D (C.terminal e)).eval_eq_restricted S).symm

/-- Uniform fanin/depth and every-mask agreement are supplied for the family. -/
def CompleteCircuitFamily (W : Presentation → ℝ) (r D : ℕ) : Prop :=
  ∀ n m : ℕ, ∃ C : Circuit (Occurrence n m) r D,
    ∀ S, W (maskEval S) = C.reported S

theorem completeCircuitFamily_mono {W : Presentation → ℝ} {r s D : ℕ}
    (hrs : r ≤ s) (H : CompleteCircuitFamily W r D) : CompleteCircuitFamily W s D := by
  intro n m
  obtain ⟨C, hC⟩ := H n m
  refine ⟨C.weakenFanin hrs, ?_⟩
  intro S
  rw [C.weakenFanin_reported hrs]
  exact hC S

theorem allMaskLocalFamily_of_completeCircuitFamily {W : Presentation → ℝ} {r D : ℕ}
    (hr : 1 ≤ r) (H : CompleteCircuitFamily W r D) : AllMaskLocalFamily W (r ^ D) := by
  intro n m
  obtain ⟨C, hC⟩ := H n m
  refine ⟨C.toLocalApparatus hr, ?_⟩
  intro S
  rw [C.localApparatus_value hr]
  exact hC S

theorem compatible_of_completeCircuitFamily {W : Presentation → ℝ} {r D : ℕ}
    (hr : 1 ≤ r) (H : CompleteCircuitFamily W r D) :
    CompatibleOriginalKernel W (r ^ D) (countKernel W) :=
  compatible_of_allMaskLocalFamily (allMaskLocalFamily_of_completeCircuitFamily hr H)

/-- Every finite fanin ceiling, including zero, has the max(1,r) ancestry bound. -/
theorem allMaskLocalFamily_of_completeCircuitFamily_max {W : Presentation → ℝ} {r D : ℕ}
    (H : CompleteCircuitFamily W r D) : AllMaskLocalFamily W ((max 1 r) ^ D) :=
  allMaskLocalFamily_of_completeCircuitFamily (Nat.le_max_left 1 r)
    (completeCircuitFamily_mono (Nat.le_max_right 1 r) H)

end IDT.QMClosure.OriginalMaskCircuitAncestry
