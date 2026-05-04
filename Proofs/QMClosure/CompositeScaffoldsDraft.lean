namespace IDT.QMClosure

/-!
Mechanical draft artifacts for composite/local-tomography obligations.

This file encodes readouts as predicates on states. Local tomography is defined
as separation by a declared family of product readouts. The main theorem is
therefore a scaffold: if product readouts separate states, then local
tomography holds by definition.

The file does not prove that IDT product contexts are exhaustive, does not
derive entanglement closure, and does not assume Hilbert tensor products.
-/

def Readout (state : Type) := state -> Prop

def AgreeOnReadouts {state : Type} (readouts : List (Readout state)) (left right : state) : Prop :=
  forall readout, readout ∈ readouts -> (readout left <-> readout right)

def SeparatesStates {state : Type} (readouts : List (Readout state)) : Prop :=
  forall left right, AgreeOnReadouts readouts left right -> left = right

def LocalTomography {state : Type} (productReadouts : List (Readout state)) : Prop :=
  forall left right, AgreeOnReadouts productReadouts left right -> left = right

theorem product_readout_separation_implies_local_tomography {state : Type}
    (productReadouts : List (Readout state))
    (separates : SeparatesStates productReadouts) :
    LocalTomography productReadouts := by
  intro left right agreement
  exact separates left right agreement

theorem state_equality_implies_readout_agreement {state : Type}
    (readouts : List (Readout state))
    (left right : state)
    (same_state : left = right) :
    AgreeOnReadouts readouts left right := by
  intro readout _readout_member
  constructor
  · intro readout_left
    simpa [same_state] using readout_left
  · intro readout_right
    simpa [same_state] using readout_right

end IDT.QMClosure
