namespace IDT.QMClosure

/-!
Mechanical draft artifacts for reversible-inheritance obligations.

The encoding is intentionally carrier-neutral: distinguishability and overlap
are arbitrary relations/functions, and an inheritance map is accepted only when
the relevant preservation property is supplied explicitly.

These lemmas do not prove Wigner's theorem, unitary dynamics, continuity, or
generator closure. They only check the algebra of preservation predicates.
-/

def Distinguishability (alpha : Type) := alpha -> alpha -> Prop
def Overlap (alpha : Type) := alpha -> alpha -> Nat
def InheritanceMap (alpha : Type) := alpha -> alpha
def ProjectiveFact (alpha : Type) := alpha -> Prop

def PreservesDistinguishability {alpha : Type}
    (relation : Distinguishability alpha)
    (map : InheritanceMap alpha) : Prop :=
  forall left right, relation left right -> relation (map left) (map right)

def PreservesOverlap {alpha : Type}
    (overlap : Overlap alpha)
    (map : InheritanceMap alpha) : Prop :=
  forall left right, overlap (map left) (map right) = overlap left right

def projectiveAction {alpha : Type}
    (map : InheritanceMap alpha)
    (fact : ProjectiveFact alpha) : ProjectiveFact alpha :=
  fun value => exists source, map source = value /\ fact source

theorem identity_preserves_distinguishability {alpha : Type}
    (relation : Distinguishability alpha) :
    PreservesDistinguishability relation id := by
  intro left right witness
  exact witness

theorem compose_preserves_distinguishability {alpha : Type}
    (relation : Distinguishability alpha)
    (first second : InheritanceMap alpha)
    (first_preserves : PreservesDistinguishability relation first)
    (second_preserves : PreservesDistinguishability relation second) :
    PreservesDistinguishability relation (second ∘ first) := by
  intro left right witness
  exact second_preserves (first left) (first right) (first_preserves left right witness)

theorem identity_preserves_overlap {alpha : Type}
    (overlap : Overlap alpha) :
    PreservesOverlap overlap id := by
  intro left right
  rfl

theorem compose_preserves_overlap {alpha : Type}
    (overlap : Overlap alpha)
    (first second : InheritanceMap alpha)
    (first_preserves : PreservesOverlap overlap first)
    (second_preserves : PreservesOverlap overlap second) :
    PreservesOverlap overlap (second ∘ first) := by
  intro left right
  calc
    overlap (second (first left)) (second (first right)) =
        overlap (first left) (first right) := second_preserves (first left) (first right)
    _ = overlap left right := first_preserves left right

theorem projective_action_identity {alpha : Type}
    (fact : ProjectiveFact alpha) :
    projectiveAction id fact = fact := by
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

end IDT.QMClosure
