import Proofs.QMClosure.OrientedRelationalProcessCountermodel
import Proofs.QMClosure.NativeAttenuationBoundary

namespace IDT.QMClosure.RelationalPassivityWall

/-!
# Readout-blind relational causality does not imply uniform response gain

The relational dagger and discard are the existing process operations. Every
function graph preserves discard, and every bijection graph is dagger-unitary.
The rational shear meets both tests but fails constant total-response gain for
every normalized real-valued scalar response. This excludes an inference from
these readout-blind tests alone; it does not exclude a causal probability theory
with an additional law coupling discard, processes, and numerical response.
No physical accessibility, probability interpretation, or primitive origin is
asserted for the shear.
-/

def relGraph {A B : Type} (f : A → B) : RelProcess A B :=
  fun x y => f x = y

theorem graph_preserves_discard {A B : Type} (f : A → B) :
    relSequential (relGraph f) relDiscard = relDiscard := by
  funext x u
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨f x, rfl, trivial⟩

theorem graph_dagger_left_identity {A B : Type} (f : A → B)
    (hinj : Function.Injective f) :
    relSequential (relGraph f) (relDagger (relGraph f)) = relIdentity := by
  funext x y
  apply propext
  constructor
  · rintro ⟨b, hxb, hyb⟩
    exact hinj (hxb.trans hyb.symm)
  · intro hxy
    change x = y at hxy
    subst y
    exact ⟨f x, rfl, rfl⟩

theorem graph_dagger_right_identity {A B : Type} (f : A → B)
    (hsurj : Function.Surjective f) :
    relSequential (relDagger (relGraph f)) (relGraph f) = relIdentity := by
  funext x y
  apply propext
  constructor
  · rintro ⟨a, hax, hay⟩
    exact hax.symm.trans hay
  · intro hxy
    change x = y at hxy
    subst y
    obtain ⟨a, ha⟩ := hsurj x
    exact ⟨a, ha, ha⟩

theorem bijection_graph_dagger_unitary {A B : Type} (f : A → B)
    (hbij : Function.Bijective f) :
    relSequential (relGraph f) (relDagger (relGraph f)) = relIdentity ∧
      relSequential (relDagger (relGraph f)) (relGraph f) = relIdentity :=
  ⟨graph_dagger_left_identity f hbij.1, graph_dagger_right_identity f hbij.2⟩

theorem inverse_graph_equals_dagger {A B : Type} (f : A → B) (g : B → A)
    (hleft : Function.LeftInverse g f) (hright : Function.RightInverse g f) :
    relGraph g = relDagger (relGraph f) := by
  funext b a
  apply propext
  constructor
  · intro h
    change g b = a at h
    change f a = b
    rw [← h]
    exact hright b
  · intro h
    change f a = b at h
    change g b = a
    rw [← h]
    exact hleft a

open NativeAttenuationBoundary.ScalarTwoPort

theorem shear_bijective : Function.Bijective shear :=
  ⟨Function.LeftInverse.injective unshear_shear,
    Function.RightInverse.surjective shear_unshear⟩

theorem unshear_graph_equals_dagger :
    relGraph unshear = relDagger (relGraph shear) :=
  inverse_graph_equals_dagger shear unshear unshear_shear shear_unshear

/-- The normalization tests at (1,0) and (0,1) already force incompatible gains. -/
theorem no_uniform_real_gain (g : ℚ → ℝ) (hzero : g 0 = 0) (hone : g 1 = 1) :
    ¬ ∃ c : ℝ, ∀ x y : ℚ,
      g (x + y) + g y = c * (g x + g y) := by
  rintro ⟨c, hgain⟩
  have hunit := hgain 1 0
  have hsplit := hgain 0 1
  norm_num [hzero, hone] at hunit hsplit
  linarith

theorem causal_dagger_unitary_shear_response_wall :
    relSequential (relGraph shear) relDiscard = relDiscard ∧
    relSequential (relGraph shear) (relDagger (relGraph shear)) = relIdentity ∧
    relSequential (relDagger (relGraph shear)) (relGraph shear) = relIdentity ∧
    (∀ g : ℚ → ℝ, g 0 = 0 → g 1 = 1 →
      ¬ ∃ c : ℝ, ∀ x y : ℚ,
        g (x + y) + g y = c * (g x + g y)) := by
  exact ⟨graph_preserves_discard shear,
    graph_dagger_left_identity shear shear_bijective.1,
    graph_dagger_right_identity shear shear_bijective.2,
    no_uniform_real_gain⟩

/-- All constant preparations followed by discard give the same inhabited scalar. -/
theorem preparation_discard_independent {A : Type} (a b : A) :
    relSequential (relGraph (fun _ : Unit => a)) relDiscard =
      relSequential (relGraph (fun _ : Unit => b)) relDiscard := by
  rw [graph_preserves_discard, graph_preserves_discard]

theorem preparation_discard_inhabited {A : Type} (a : A) :
    relSequential (relGraph (fun _ : Unit => a)) relDiscard () () :=
  ⟨a, rfl, trivial⟩

theorem scalar_valuation_cannot_distinguish_preparation {A V : Type}
    (valuation : RelProcess Unit Unit → V) (a b : A) :
    valuation (relSequential (relGraph (fun _ : Unit => a)) relDiscard) =
      valuation (relSequential (relGraph (fun _ : Unit => b)) relDiscard) := by
  rw [preparation_discard_independent a b]

/-- Data-only scope ledger, not hypotheses asserting a physical theory. -/
inductive OpenObligation where
  | deriveProcessResponseCoupling
  | derivePhysicalAccessibility
  | deriveClosedEnvironmentAccounting
  | deriveResponseSensitivePassivity
  deriving DecidableEq, Repr

def openObligations : List OpenObligation :=
  [.deriveProcessResponseCoupling, .derivePhysicalAccessibility,
    .deriveClosedEnvironmentAccounting, .deriveResponseSensitivePassivity]

end IDT.QMClosure.RelationalPassivityWall
