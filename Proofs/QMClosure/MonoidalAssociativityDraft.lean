namespace IDT.QMClosure

/-!
Mechanical draft artifact for the `monoidal_associativity` closure obligation.

This file proves only a scaffold theorem: if finite context products are
encoded as list append, the product operation is associative. It is not a proof
of the full IDT composite theorem, because it does not yet prove that every
admissible context product reduces to this encoding without importing tensor
products or Hilbert-space structure.
-/

abbrev FiniteContextProduct (alpha : Type) := List alpha

def contextProduct {alpha : Type} (left right : FiniteContextProduct alpha) :
    FiniteContextProduct alpha :=
  left ++ right

theorem finite_context_product_assoc {alpha : Type}
    (a b c : FiniteContextProduct alpha) :
    contextProduct (contextProduct a b) c = contextProduct a (contextProduct b c) := by
  simp [contextProduct, List.append_assoc]

end IDT.QMClosure
