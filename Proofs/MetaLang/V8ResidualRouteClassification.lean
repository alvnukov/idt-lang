import Proofs.MetaLang.V8FormalProofScopeBoundary

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 residual route classification.

Residual material must not stay as untyped legacy backlog. Each residual item
is either a Lean-migration candidate or an IDT v8 residual input. This module
records that routing discipline without doing research or changing CI.
-/

inductive ResidualRoute where
  | migrateToLean
  | encodeAsIdtV8Residual
deriving DecidableEq, Repr

structure RoutedResidualKind where
  kind : ResidualMaterialKind
  route : ResidualRoute
  count : Nat
deriving Repr

def currentResidualRouteClassification : List RoutedResidualKind :=
  [
    {
      kind := ResidualMaterialKind.finiteGate,
      route := ResidualRoute.encodeAsIdtV8Residual,
      count := 247
    },
    {
      kind := ResidualMaterialKind.qmExperiment,
      route := ResidualRoute.encodeAsIdtV8Residual,
      count := 35
    },
    {
      kind := ResidualMaterialKind.theoremCard,
      route := ResidualRoute.migrateToLean,
      count := 23
    },
    {
      kind := ResidualMaterialKind.qmCoreProofObligation,
      route := ResidualRoute.migrateToLean,
      count := 11
    }
  ]

def RoutedResidualKind.isRouted (item : RoutedResidualKind) : Prop :=
  item.route = ResidualRoute.migrateToLean
    ∨ item.route = ResidualRoute.encodeAsIdtV8Residual

def RoutedResidualKind.hasCount (item : RoutedResidualKind) : Prop :=
  item.count > 0

def RoutedResidualKind.isLeanCandidate (item : RoutedResidualKind) : Prop :=
  item.route = ResidualRoute.migrateToLean

def RoutedResidualKind.isIdtV8Residual (item : RoutedResidualKind) : Prop :=
  item.route = ResidualRoute.encodeAsIdtV8Residual

def allResidualKindsRouted (items : List RoutedResidualKind) : Prop :=
  ∀ item, item ∈ items → item.isRouted ∧ item.hasCount

theorem current_residual_route_classification_all_routed :
    allResidualKindsRouted currentResidualRouteClassification := by
  intro item itemPresent
  simp [currentResidualRouteClassification] at itemPresent
  rcases itemPresent with rfl | rfl | rfl | rfl
  all_goals
    constructor
    · first | left; rfl | right; rfl
    · unfold RoutedResidualKind.hasCount
      decide

theorem theorem_cards_are_lean_migration_candidates :
    ∃ item, item ∈ currentResidualRouteClassification
      ∧ item.kind = ResidualMaterialKind.theoremCard
      ∧ item.isLeanCandidate := by
  exact ⟨{
      kind := ResidualMaterialKind.theoremCard,
      route := ResidualRoute.migrateToLean,
      count := 23
    },
    by simp [currentResidualRouteClassification],
    And.intro rfl rfl⟩

theorem finite_gates_are_idt_v8_residual_inputs :
    ∃ item, item ∈ currentResidualRouteClassification
      ∧ item.kind = ResidualMaterialKind.finiteGate
      ∧ item.isIdtV8Residual := by
  exact ⟨{
      kind := ResidualMaterialKind.finiteGate,
      route := ResidualRoute.encodeAsIdtV8Residual,
      count := 247
    },
    by simp [currentResidualRouteClassification],
    And.intro rfl rfl⟩

end V8
end MetaLang
end IDT
