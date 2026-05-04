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

structure FiniteProductEncoding (context token : Type) where
  encode : context -> List token
  product : context -> context -> context
  product_encodes : forall left right, encode (product left right) = encode left ++ encode right

def operationallyEquivalentByEncoding {context token : Type}
    (bridge : FiniteProductEncoding context token)
    (left right : context) : Prop :=
  bridge.encode left = bridge.encode right

theorem encoded_context_product_assoc_up_to_operational_equivalence {context token : Type}
    (bridge : FiniteProductEncoding context token)
    (a b c : context) :
    operationallyEquivalentByEncoding bridge
      (bridge.product (bridge.product a b) c)
      (bridge.product a (bridge.product b c)) := by
  unfold operationallyEquivalentByEncoding
  rw [
    bridge.product_encodes,
    bridge.product_encodes,
    bridge.product_encodes,
    bridge.product_encodes,
  ]
  exact List.append_assoc (bridge.encode a) (bridge.encode b) (bridge.encode c)

inductive ContextProductExpr (atom : Type) where
  | atomContext : atom -> ContextProductExpr atom
  | productContext : ContextProductExpr atom -> ContextProductExpr atom -> ContextProductExpr atom

namespace ContextProductExpr

def flatten {atom : Type} : ContextProductExpr atom -> List atom
  | atomContext value => [value]
  | productContext left right => flatten left ++ flatten right

def equivalentByFlatten {atom : Type}
    (left right : ContextProductExpr atom) : Prop :=
  flatten left = flatten right

theorem product_context_flattens_to_append {atom : Type}
    (left right : ContextProductExpr atom) :
    flatten (productContext left right) = flatten left ++ flatten right := by
  rfl

theorem product_context_expr_assoc_up_to_flatten {atom : Type}
    (a b c : ContextProductExpr atom) :
    equivalentByFlatten
      (productContext (productContext a b) c)
      (productContext a (productContext b c)) := by
  unfold equivalentByFlatten
  simp [flatten, List.append_assoc]

end ContextProductExpr

end IDT.QMClosure
