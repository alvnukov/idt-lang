import Mathlib.Algebra.Group.Hom.End
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Group.Commute.Defs

/-!
# Additive inverses from transparent surjective mixing

This conditional algebraic result uses an additive commutative monoid,
transparent additive branches, coverage of their composite and exact first-axis
recovery. The inverse witness is a finite expression in addition and branch
application. Supplied preimage and recovery functions give an explicit inverse
function. Existential coverage and recovery give an existence theorem and a
chosen additive group with the original monoid operations.
-/

namespace IDT.QMClosure.TransparentSurjectiveMixingGroup

section Monoid

variable {V : Type*} [AddCommMonoid V]

/-- Every first-axis target has an exact symmetric two-port preimage. -/
def FirstAxisReachable (a b : AddMonoid.End V) : Prop :=
  ∀ p, ∃ x y, a x + b y = p ∧ b x + a y = 0

/-- The complete symmetric additive two-port map. -/
def twoPort (a b : AddMonoid.End V) : (V × V) → (V × V) :=
  fun p => (a p.1 + b p.2, b p.1 + a p.2)

/-- Positive branch word used as the additive inverse witness. -/
def inverseWord (a b : AddMonoid.End V) (x y : V) : V :=
  a (b (b x)) + a (a y) + a (a y) + a (b (a y)) + b x

/-- The positive word cancels the composite image of a recovered target. -/
theorem add_inverseWord
    (a b : AddMonoid.End V) (transparent : a + b = 1)
    (p t x y : V) (target : a (b t) = p)
    (first : a x + b y = t) (second : b x + a y = 0) :
    p + inverseWord a b x y = 0 := by
  have split (z : V) : a z + b z = z := by
    change (a + b) z = (1 : AddMonoid.End V) z
    rw [transparent]
  have hp : a (b (a x)) + a (b (b y)) = p := by
    have h := congrArg (fun z => a (b z)) first
    simp only [map_add] at h
    exact h.trans target
  have hx : a (b (a x)) + a (b (b x)) = a (b x) := by
    have h := congrArg (fun z => a (b z)) (split x)
    simpa only [map_add] using h
  have hz : a (b x) + a (a y) = 0 := by
    have h := congrArg a second
    simpa only [map_add, map_zero] using h
  have hy : a (b (a y)) + a (b (b y)) = a (b y) := by
    have h := congrArg (fun z => a (b z)) (split y)
    simpa only [map_add] using h
  have hy' : a (a y) + a (b y) = a y := by
    have h := congrArg a (split y)
    simpa only [map_add] using h
  have hfirst :
      (a (b (a x)) + a (b (b x))) + a (a y) = 0 := by
    rw [hx]
    exact hz
  have hsecond :
      a (b (b y)) + (a (a y) + a (b (a y))) + b x = 0 := by
    calc
      a (b (b y)) + (a (a y) + a (b (a y))) + b x =
          (a (a y) + (a (b (a y)) + a (b (b y)))) + b x := by
        simp only [add_comm, add_left_comm]
      _ = a y + b x := by rw [hy, hy']
      _ = 0 := by simpa only [add_comm] using second
  calc
    p + inverseWord a b x y =
        ((a (b (a x)) + a (b (b x))) + a (a y)) +
          (a (b (b y)) + (a (a y) + a (b (a y))) + b x) := by
      rw [← hp]
      dsimp only [inverseWord]
      simp only [add_comm, add_left_comm]
    _ = 0 := by rw [hfirst, hsecond, add_zero]

/-- Explicit inverse recipe from supplied branch right-preimages and recovery. -/
def negRecipe (a b : AddMonoid.End V) (ra rb : V → V)
    (R : V → V × V) (p : V) : V :=
  inverseWord a b (R (rb (ra p))).1 (R (rb (ra p))).2

/-- Supplied right-preimages and recovery certify the explicit recipe. -/
theorem add_negRecipe
    (a b : AddMonoid.End V) (transparent : a + b = 1)
    (ra rb : V → V) (R : V → V × V)
    (rightA : ∀ p, a (ra p) = p) (rightB : ∀ p, b (rb p) = p)
    (recover : ∀ t,
      a (R t).1 + b (R t).2 = t ∧ b (R t).1 + a (R t).2 = 0)
    (p : V) : p + negRecipe a b ra rb R p = 0 := by
  apply add_inverseWord a b transparent p (rb (ra p))
    (R (rb (ra p))).1 (R (rb (ra p))).2
  · rw [rightB, rightA]
  · exact (recover (rb (ra p))).1
  · exact (recover (rb (ra p))).2

/-- Coverage of the composite suffices for inverse existence. -/
theorem additive_inverses_of_axis_recovery
    (a b : AddMonoid.End V) (transparent : a + b = 1)
    (ontoAB : Function.Surjective (fun t => a (b t)))
    (axis : FirstAxisReachable a b) :
    ∀ p : V, ∃ q : V, p + q = 0 := by
  intro p
  obtain ⟨t, ht⟩ := ontoAB p
  obtain ⟨x, y, hfirst, hsecond⟩ := axis t
  exact ⟨inverseWord a b x y,
    add_inverseWord a b transparent p t x y ht hfirst hsecond⟩

/-- Separate branch coverage supplies the composite coverage. -/
theorem additive_inverses_of_branch_surjective
    (a b : AddMonoid.End V) (transparent : a + b = 1)
    (ontoA : Function.Surjective a) (ontoB : Function.Surjective b)
    (axis : FirstAxisReachable a b) :
    ∀ p : V, ∃ q : V, p + q = 0 := by
  apply additive_inverses_of_axis_recovery a b transparent
  · intro p
    obtain ⟨u, hu⟩ := ontoA p
    obtain ⟨t, ht⟩ := ontoB u
    exact ⟨t, (congrArg a ht).trans hu⟩
  · exact axis

/-- Full symmetric two-port coverage is equivalent to first-axis recovery. -/
theorem symmetric_surjective_iff_first_axis (a b : AddMonoid.End V) :
    Function.Surjective (twoPort a b) ↔ FirstAxisReachable a b := by
  constructor
  · intro onto p
    obtain ⟨⟨x, y⟩, hxy⟩ := onto (p, 0)
    exact ⟨x, y, congrArg Prod.fst hxy, congrArg Prod.snd hxy⟩
  · intro axis
    rintro ⟨p, q⟩
    obtain ⟨x, y, hp, hz⟩ := axis p
    obtain ⟨u, v, hq, hz'⟩ := axis q
    refine ⟨(x + v, y + u), Prod.ext ?_ ?_⟩
    · change a (x + v) + b (y + u) = p
      calc
        a (x + v) + b (y + u) = (a x + b y) + (b u + a v) := by
          simp only [map_add, add_comm, add_left_comm]
        _ = p := by rw [hp, hz', add_zero]
    · change b (x + v) + a (y + u) = q
      calc
        b (x + v) + a (y + u) = (b x + a y) + (a u + b v) := by
          simp only [map_add, add_comm, add_left_comm]
        _ = q := by rw [hz, hq, zero_add]

/-- Full two-port coverage is an alternative recovery interface. -/
theorem additive_inverses_of_twoPort_surjective
    (a b : AddMonoid.End V) (transparent : a + b = 1)
    (ontoA : Function.Surjective a) (ontoB : Function.Surjective b)
    (onto : Function.Surjective (twoPort a b)) :
    ∀ p : V, ∃ q : V, p + q = 0 :=
  additive_inverses_of_branch_surjective a b transparent ontoA ontoB
    ((symmetric_surjective_iff_first_axis a b).mp onto)

/-- Package a supplied inverse function using the standard group constructor.
The structure update retains every field of the original additive monoid. -/
abbrev groupFromNeg (neg : V → V) (hinv : ∀ p, p + neg p = 0) :
    AddCommGroup V :=
  letI : Neg V := ⟨neg⟩
  let group : AddGroup V := AddGroup.ofRightAxioms add_assoc add_zero hinv
  { (inferInstance : AddCommMonoid V) with
    neg := neg
    zsmul := zsmulRec
    neg_add_cancel := group.neg_add_cancel }

/-- The explicit recipe supplies a group directly from preimage/recovery data. -/
abbrev groupFromRecoveryData
    (a b : AddMonoid.End V) (transparent : a + b = 1)
    (ra rb : V → V) (R : V → V × V)
    (rightA : ∀ p, a (ra p) = p) (rightB : ∀ p, b (rb p) = p)
    (recover : ∀ t,
      a (R t).1 + b (R t).2 = t ∧ b (R t).1 + a (R t).2 = 0) :
    AddCommGroup V :=
  groupFromNeg (negRecipe a b ra rb R)
    (add_negRecipe a b transparent ra rb R rightA rightB recover)

/-- Existential inverse witnesses supply a chosen inverse function. -/
noncomputable abbrev groupFromInverses
    (hinv : ∀ p : V, ∃ q : V, p + q = 0) : AddCommGroup V :=
  groupFromNeg (fun p => Classical.choose (hinv p))
    (fun p => Classical.choose_spec (hinv p))

/-- The chosen group retains the original full additive-monoid structure. -/
theorem groupFromInverses_toAddCommMonoid
    (hinv : ∀ p : V, ∃ q : V, p + q = 0) :
    (groupFromInverses hinv).toAddCommMonoid = (inferInstance : AddCommMonoid V) := rfl

/-- The algebraic gate exposes the branch coverage needed by pairing. -/
structure Gate (V : Type*) [AddCommMonoid V] where
  a : AddMonoid.End V
  b : AddMonoid.End V
  transparent : a + b = 1
  ontoA : Function.Surjective a
  ontoB : Function.Surjective b
  axis : FirstAxisReachable a b

namespace Gate

variable (G : Gate V)

include G

/-- Every original preparation has an additive inverse. -/
theorem additive_inverses : ∀ p : V, ∃ q : V, p + q = 0 :=
  additive_inverses_of_branch_surjective G.a G.b G.transparent G.ontoA G.ontoB G.axis

/-- The gate-derived group retains the supplied additive monoid. -/
noncomputable abbrev additiveGroup : AddCommGroup V :=
  groupFromInverses G.additive_inverses

theorem additiveGroup_toAddCommMonoid :
    G.additiveGroup.toAddCommMonoid = (inferInstance : AddCommMonoid V) := rfl

end Gate
end Monoid

section Group

variable {V : Type*} [AddCommGroup V]

/-- Once inverses are available, transparent branches commute. -/
theorem commute_of_transparent (a b : AddMonoid.End V)
    (transparent : a + b = 1) : Commute a b := by
  have split (z : V) : a z + b z = z := by
    change (a + b) z = (1 : AddMonoid.End V) z
    rw [transparent]
  change a * b = b * a
  apply DFunLike.ext
  intro x
  change a (b x) = b (a x)
  have ha : a (a x) + a (b x) = a x := by
    have h := congrArg a (split x)
    simpa only [map_add] using h
  exact add_left_cancel (ha.trans (split (a x)).symm)

end Group

end IDT.QMClosure.TransparentSurjectiveMixingGroup
