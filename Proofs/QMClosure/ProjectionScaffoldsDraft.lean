namespace IDT.QMClosure

/-!
Mechanical draft artifacts for projection/idempotence obligations.

The encoding is intentionally minimal: a finite projection is represented by an
idempotent endomap, and conservative gluing is represented by composition of
commuting idempotent endomaps.

This does not assume Hilbert projectors. It also does not prove that IDT
projective facts must reduce to these endomaps.
-/

def Endomap (alpha : Type) := alpha -> alpha

def Idempotent {alpha : Type} (map : Endomap alpha) : Prop :=
  forall value, map (map value) = map value

def Commute {alpha : Type} (left right : Endomap alpha) : Prop :=
  forall value, left (right value) = right (left value)

def FixedBy {alpha : Type} (map : Endomap alpha) (value : alpha) : Prop :=
  map value = value

def composeEndomap {alpha : Type} (left right : Endomap alpha) : Endomap alpha :=
  fun value => left (right value)

theorem identity_projection_idempotent {alpha : Type} :
    Idempotent (id : Endomap alpha) := by
  intro value
  rfl

theorem commuting_idempotent_composition_idempotent {alpha : Type}
    (left right : Endomap alpha)
    (left_idempotent : Idempotent left)
    (right_idempotent : Idempotent right)
    (commutes : Commute left right) :
    Idempotent (composeEndomap left right) := by
  intro value
  have right_left_right_eq_left_right : right (left (right value)) = left (right value) := by
    have commute_at_right := commutes (right value)
    have left_right_right_eq_left_right : left (right (right value)) = left (right value) := by
      rw [right_idempotent value]
    exact Eq.symm ((Eq.symm left_right_right_eq_left_right).trans commute_at_right)
  calc
    composeEndomap left right (composeEndomap left right value)
        = left (right (left (right value))) := rfl
    _ = left (left (right value)) := by rw [right_left_right_eq_left_right]
    _ = left (right value) := left_idempotent (right value)
    _ = composeEndomap left right value := rfl

theorem commuting_projections_have_consistent_composition {alpha : Type}
    (left right : Endomap alpha)
    (commutes : Commute left right) :
    composeEndomap left right = composeEndomap right left := by
  funext value
  exact commutes value

theorem commuting_idempotent_composition_fixed_by_left {alpha : Type}
    (left right : Endomap alpha)
    (left_idempotent : Idempotent left)
    (value : alpha) :
    FixedBy left (composeEndomap left right value) := by
  unfold FixedBy composeEndomap
  exact left_idempotent (right value)

theorem commuting_idempotent_composition_fixed_by_right {alpha : Type}
    (left right : Endomap alpha)
    (right_idempotent : Idempotent right)
    (commutes : Commute left right)
    (value : alpha) :
    FixedBy right (composeEndomap left right value) := by
  unfold FixedBy composeEndomap
  have commute_at_right := commutes (right value)
  have left_right_right_eq_left_right : left (right (right value)) = left (right value) := by
    rw [right_idempotent value]
  exact (Eq.symm commute_at_right).trans left_right_right_eq_left_right

theorem jointly_fixed_value_survives_composition {alpha : Type}
    (left right : Endomap alpha)
    (value : alpha)
    (left_fixed : FixedBy left value)
    (right_fixed : FixedBy right value) :
    composeEndomap left right value = value := by
  unfold composeEndomap FixedBy at *
  rw [right_fixed, left_fixed]

end IDT.QMClosure
