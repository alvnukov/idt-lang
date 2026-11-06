import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace IDT.QMClosure.NonadditiveClassicalSwapRoot

/-!
# A deterministic finite root without coherent additivity

Four classical states carry a supplied maximum merge and rational weight.
The two-port routing below is transparent on equal inputs, squares to exchange,
is reversible, and conserves the sum of the two weights. Nevertheless it does
not preserve coordinatewise merge, and merge has no inverse for state 1.
Thus these operational laws alone do not imply the additive hypothesis of
`TransparentSwapRoot`. This is a finite counterexample to dropping that
hypothesis, not a counterexample to its additive reconstruction theorem.

No event algebra, probabilities, detector actualization, physical realization,
or minimality of the four-state carrier is established here. In particular,
the group-based `PositiveQuadratic` contract is not applied to this monoid.
-/

abbrev State := Fin 4
abbrev Ports := State × State

/-- Maximum in the ordering of the four state labels. -/
def merge (x y : State) : State := if x.val ≤ y.val then y else x

def mergePorts (p q : Ports) : Ports :=
  (merge p.1 q.1, merge p.2 q.2)

def weight (x : State) : ℚ :=
  match x.val with
  | 0 => 0
  | 3 => 2
  | _ => 1

/-- The supplied routing table, with rows and columns indexed by the two inputs. -/
def route (p : Ports) : Ports :=
  match p.1.val, p.2.val with
  | 0, 0 => (0, 0)
  | 0, 1 => (0, 2)
  | 0, 2 => (1, 0)
  | 0, 3 => (1, 2)
  | 1, 0 => (2, 0)
  | 1, 1 => (1, 1)
  | 1, 2 => (3, 0)
  | 1, 3 => (2, 3)
  | 2, 0 => (0, 1)
  | 2, 1 => (0, 3)
  | 2, 2 => (2, 2)
  | 2, 3 => (3, 1)
  | 3, 0 => (2, 1)
  | 3, 1 => (3, 2)
  | 3, 2 => (1, 3)
  | _, _ => (3, 3)

theorem merge_associative :
    ∀ x y z : State, merge (merge x y) z = merge x (merge y z) := by decide

theorem merge_commutative : ∀ x y : State, merge x y = merge y x := by decide

theorem merge_zero_left : ∀ x : State, merge 0 x = x := by decide

theorem merge_zero_right : ∀ x : State, merge x 0 = x := by decide

theorem merge_idempotent : ∀ x : State, merge x x = x := by decide

theorem one_has_no_merge_inverse : ∀ x : State, merge 1 x ≠ 0 := by decide

theorem transparent : ∀ x : State, route (x, x) = (x, x) := by decide

theorem square : ∀ p : Ports, route (route p) = (p.2, p.1) := by
  rintro ⟨x, y⟩
  fin_cases x <;> fin_cases y <;> decide

/-- This implication uses only the exact square law, with no additive structure. -/
theorem fourth_of_square {α : Type*} (F : α × α → α × α)
    (h : ∀ p, F (F p) = (p.2, p.1)) (p : α × α) :
    F (F (F (F p))) = p := by
  rw [h, h]

theorem fourth (p : Ports) : route (route (route (route p))) = p :=
  fourth_of_square route square p

theorem bijective : Function.Bijective route := by
  constructor
  · intro p q h
    have hh := congrArg route h
    rw [square, square] at hh
    exact Prod.ext (congrArg Prod.snd hh) (congrArg Prod.fst hh)
  · intro p
    exact ⟨route (route (route p)), fourth p⟩

theorem vacuum_weight : weight 0 = 0 := by decide

theorem weight_nonnegative : ∀ x : State, 0 ≤ weight x := by decide

theorem weight_zero_iff : ∀ x : State, weight x = 0 ↔ x = 0 := by decide

theorem weight_positive_iff : ∀ x : State, 0 < weight x ↔ x ≠ 0 := by decide

theorem weight_one : weight 1 = 1 := by decide

theorem weight_conservation : ∀ x y : State,
    weight (route (x, y)).1 + weight (route (x, y)).2 = weight x + weight y := by
  intro x y
  fin_cases x <;> fin_cases y <;> norm_num [route, weight]

/-- The two sides of the explicit merge-additivity failure. -/
theorem merge_failure_values :
    route (mergePorts (0, 1) (0, 2)) = (1, 0) ∧
      mergePorts (route (0, 1)) (route (0, 2)) = (1, 2) := by decide

theorem route_not_merge_additive :
    ¬ ∀ p q, route (mergePorts p q) = mergePorts (route p) (route q) := by
  intro h
  have impossible := h (0, 1) (0, 2)
  exact (by decide : route (mergePorts (0, 1) (0, 2)) ≠
    mergePorts (route (0, 1)) (route (0, 2))) impossible

/-- A numerical scaling failure, without invoking a group-based quadratic contract. -/
theorem doubled_weight_not_quadratic :
    weight (merge 1 1) = 1 ∧ weight (merge 1 1) ≠ 4 * weight 1 := by
  norm_num [merge, weight]

/-- Machine-visible scope of the supplied finite control. -/
inductive BoundaryRole where
  | suppliedFiniteClassicalCarrierAndRouting
  | suppliedMaximumMergeAndRationalWeight
  | finiteCounterexampleToDroppingMixerAdditivity
  | noMergeInverseForOne
  | notAnApplicationOfGroupBasedPositiveQuadratic
  | doesNotDeriveEventsOrProbabilities
  | doesNotEstablishPhysicalRealizationOrMinimality
  | doesNotDeriveFullQMOrUpgradeManifestStatus
  deriving DecidableEq, Repr

def boundaryRoles : List BoundaryRole := [
  .suppliedFiniteClassicalCarrierAndRouting,
  .suppliedMaximumMergeAndRationalWeight,
  .finiteCounterexampleToDroppingMixerAdditivity,
  .noMergeInverseForOne,
  .notAnApplicationOfGroupBasedPositiveQuadratic,
  .doesNotDeriveEventsOrProbabilities,
  .doesNotEstablishPhysicalRealizationOrMinimality,
  .doesNotDeriveFullQMOrUpgradeManifestStatus]

end IDT.QMClosure.NonadditiveClassicalSwapRoot
