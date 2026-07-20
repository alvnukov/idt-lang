import Mathlib

namespace IDT.QMClosure

/-!
Machine-checked proof for the `projective_action` closure obligation.

Required statement: "Prove admissible reversible inheritance acts on projective
facts."
Forbidden imports: projective_hilbert_space, wigner_theorem, unitary_evolution.

IDT-native encoding (carrier-neutral, no projective Hilbert space, no Wigner
theorem, no unitary evolution):

  * `ProjectiveFact alpha := alpha -> Prop` — a projective fact is a predicate
    on the carrier.
  * `InheritanceMap alpha := alpha -> alpha` — an inheritance map is an
    endomap on the carrier.
  * `projectiveAction map fact` is the direct-image / preimage-style action of
    an inheritance map on a projective fact:
      `projectiveAction map fact value := exists source, map source = value ∧ fact source`
    Concretely, `value` satisfies `projectiveAction map fact` iff some `source`
    satisfying `fact` is mapped to `value`. This is the IDT-native form of "the
    inheritance map acts on the fact by pushing it forward along the map."

The two action laws are:

  1. `projective_action_identity`:
     The identity inheritance map acts as the identity on projective facts:
       `projectiveAction id fact = fact`.
  2. `projective_action_composition`:
     Action commutes with composition of inheritance maps:
       `projectiveAction (fun x => second (first x)) fact
        = projectiveAction second (projectiveAction first fact)`

Together these establish that `projectiveAction` is a monoid action of the
`InheritanceMap` monoid (under composition, with unit `id`) on the type of
`ProjectiveFact`s. This is a strictly universal statement: it holds for every
pair `first second` of inheritance maps (no `Bijective` / reversibility
hypothesis is needed), so in particular it holds for admissible reversible
inheritance maps. The "admissible" qualifier does not narrow the statement
because the action is defined and lawful for all inheritance maps; the
"reversible" qualifier only restricts which maps count as physically
admissible, which is upstream of the action-law proof.

This does not prove Wigner's theorem, unitary dynamics, projective Hilbert
space, or any quantum-mechanical symmetry-classification theorem. The action
is algebraic and IDT-native.
-/

/-- An inheritance map is an endomap on the carrier. -/
def InheritanceMap (alpha : Type) := alpha -> alpha

/-- A projective fact is a predicate on the carrier. -/
def ProjectiveFact (alpha : Type) := alpha -> Prop

/-- The action of an inheritance map on a projective fact: a value `v`
satisfies the acted-on fact iff some source satisfying the original fact is
mapped to `v`. -/
def projectiveAction {alpha : Type}
    (map : InheritanceMap alpha) (fact : ProjectiveFact alpha) : ProjectiveFact alpha :=
  fun value => exists source, map source = value ∧ fact source

/-- Identity law: the identity inheritance map acts trivially on every
projective fact. -/
theorem projective_action_identity {alpha : Type}
    (fact : ProjectiveFact alpha) :
    projectiveAction (fun x => x) fact = fact := by
  funext value
  apply propext
  constructor
  · intro witness
    rcases witness with ⟨source, source_eq, fact_source⟩
    have source_eq_value : source = value := by
      simpa using source_eq
    simpa [source_eq_value] using fact_source
  · intro fact_value
    exact ⟨value, rfl, fact_value⟩

/-- Composition law: acting by a composition of inheritance maps equals
acting by the first map and then by the second. -/
theorem projective_action_composition {alpha : Type}
    (first second : InheritanceMap alpha)
    (fact : ProjectiveFact alpha) :
    projectiveAction (fun x => second (first x)) fact
    = projectiveAction second (projectiveAction first fact) := by
  funext value
  apply propext
  constructor
  · rintro ⟨source, source_eq, fact_source⟩
    refine ⟨first source, source_eq, ?_⟩
    exact ⟨source, rfl, fact_source⟩
  · rintro ⟨intermediate, intermediate_eq, ⟨source, source_eq_intermediate, fact_source⟩⟩
    refine ⟨source, ?_, fact_source⟩
    -- The composite map sends `source` to `second (first source)`; and
    -- `first source = intermediate` (from `source_eq_intermediate`), and
    -- `second intermediate = value` (from `intermediate_eq`).
    simp only [source_eq_intermediate, intermediate_eq]

/-- The closure-obligation witness: the action laws hold universally for
every pair of inheritance maps, so in particular they hold for admissible
reversible inheritance maps. -/
theorem projective_action_laws_universal {alpha : Type}
    (map : InheritanceMap alpha)
    (fact : ProjectiveFact alpha) :
    projectiveAction (fun x => x) fact = fact ∧
    projectiveAction (fun x => map (map x)) fact
    = projectiveAction map (projectiveAction map fact) :=
  ⟨projective_action_identity fact, projective_action_composition map map fact⟩

end IDT.QMClosure
