import Proofs.QMClosure.ThreeSourceDistributiveSwapRoot
import Mathlib.Data.ZMod.Basic

namespace IDT.QMClosure.OneSidedDistributiveSwapControl

/-!
A finite mathematical control separates either single distributivity law from
the conjunction. Both ports have explicit inverses, transparency and the
swap-square identity hold, and right distributivity fails. Reversing the
operation gives the other one-sided control. No physical realization or
scalar readout is asserted.
-/

abbrev Carrier := (ZMod 5 × ZMod 5) × ZMod 5

def omega (v w : ZMod 5 × ZMod 5) : ZMod 5 := v.1 * w.2 - v.2 * w.1

def m (x y : Carrier) : Carrier :=
  ((-x.1.1 + 2 * y.1.1, -x.1.2 + 2 * y.1.2),
    2 * x.2 - y.2 - omega x.1 y.1)

theorem idempotent (x : Carrier) : m x x = x := by
  apply Prod.ext
  · apply Prod.ext <;> simp only [m] <;> grind
  · simp only [m, omega]
    grind

theorem bookend (x y : Carrier) : m (m x y) (m y x) = y := by
  apply Prod.ext
  · apply Prod.ext <;> simp only [m] <;> grind
  · simp only [m, omega]
    grind

theorem left_distributive (x y z : Carrier) :
    m x (m y z) = m (m x y) (m x z) := by
  apply Prod.ext
  · apply Prod.ext <;> simp only [m] <;> grind
  · simp only [m, omega]
    grind

def leftInverseTerm (x target : Carrier) : Carrier :=
  let w := (3 * (target.1.1 + x.1.1), 3 * (target.1.2 + x.1.2))
  (w, 2 * x.2 - target.2 - omega x.1 w)

def rightInverseTerm (y target : Carrier) : Carrier :=
  let v := (2 * y.1.1 - target.1.1, 2 * y.1.2 - target.1.2)
  (v, 3 * (target.2 + y.2 + omega v y.1))

theorem leftInverseTerm_apply (x target : Carrier) :
    m x (leftInverseTerm x target) = target := by
  apply Prod.ext
  · apply Prod.ext <;> simp only [m, leftInverseTerm] <;> grind
  · simp only [m, leftInverseTerm, omega]
    grind

theorem leftInverseTerm_reverse (x y : Carrier) :
    leftInverseTerm x (m x y) = y := by
  apply Prod.ext
  · apply Prod.ext <;> simp only [m, leftInverseTerm] <;> grind
  · simp only [m, leftInverseTerm, omega]
    grind

theorem rightInverseTerm_apply (y target : Carrier) :
    m (rightInverseTerm y target) y = target := by
  apply Prod.ext
  · apply Prod.ext <;> simp only [m, rightInverseTerm] <;> grind
  · simp only [m, rightInverseTerm, omega]
    grind

theorem rightInverseTerm_reverse (x y : Carrier) :
    rightInverseTerm y (m x y) = x := by
  apply Prod.ext
  · apply Prod.ext <;> simp only [m, rightInverseTerm] <;> grind
  · simp only [m, rightInverseTerm, omega]
    grind

theorem left_bijective (x : Carrier) : Function.Bijective (m x) := by
  constructor
  · intro y z heq
    calc
      y = leftInverseTerm x (m x y) := (leftInverseTerm_reverse x y).symm
      _ = leftInverseTerm x (m x z) := congrArg (leftInverseTerm x) heq
      _ = z := leftInverseTerm_reverse x z
  · intro target
    exact ⟨leftInverseTerm x target, leftInverseTerm_apply x target⟩

theorem right_bijective (y : Carrier) : Function.Bijective (fun x => m x y) := by
  constructor
  · intro x z heq
    calc
      x = rightInverseTerm y (m x y) := (rightInverseTerm_reverse x y).symm
      _ = rightInverseTerm y (m z y) := congrArg (rightInverseTerm y) heq
      _ = z := rightInverseTerm_reverse z y
  · intro target
    exact ⟨rightInverseTerm y target, rightInverseTerm_apply y target⟩

def witnessX : Carrier := ((1, 0), 0)
def witnessY : Carrier := ((0, 1), 0)
def witnessZ : Carrier := ((0, 0), 0)

theorem right_distributive_witness :
    m (m witnessX witnessY) witnessZ = ((1, 3), 3) ∧
      m (m witnessX witnessZ) (m witnessY witnessZ) = ((1, 3), 4) := by
  decide

theorem not_right_distributive :
    ¬ (∀ x y z, m (m x y) z = m (m x z) (m y z)) := by
  intro h
  have hh := congrArg (fun x : Carrier => x.2) (h witnessX witnessY witnessZ)
  have hw := right_distributive_witness
  rw [hw.1, hw.2] at hh
  exact (by decide : (3 : ZMod 5) ≠ 4) hh

theorem not_medial : ¬ MedialSwapRoot.Laws m := by
  intro h
  exact not_right_distributive
    (ThreeSourceDistributiveSwapRoot.ofMedialSwapRootLaws h).right_distributive

def operation (p : Carrier × Carrier) : Carrier × Carrier :=
  (m p.1 p.2, m p.2 p.1)

theorem transparent (x : Carrier) : operation (x, x) = (x, x) :=
  Prod.ext (idempotent x) (idempotent x)

theorem square (p : Carrier × Carrier) : operation (operation p) = p.swap :=
  Prod.ext (bookend p.1 p.2) (bookend p.2 p.1)

theorem not_restrictedExchange :
    ¬ ThreeSourceDistributiveSwapRoot.RestrictedExchange operation := by
  intro h
  exact not_right_distributive
    ((ThreeSourceDistributiveSwapRoot.restrictedExchange_iff_laws
      operation transparent square).mp h).right_distributive

def opposite (x y : Carrier) : Carrier := m y x

theorem opposite_idempotent (x : Carrier) : opposite x x = x := idempotent x

theorem opposite_bookend (x y : Carrier) :
    opposite (opposite x y) (opposite y x) = y := bookend x y

theorem opposite_right_distributive (x y z : Carrier) :
    opposite (opposite x y) z = opposite (opposite x z) (opposite y z) :=
  left_distributive z y x

theorem opposite_not_left_distributive :
    ¬ (∀ x y z, opposite x (opposite y z) =
      opposite (opposite x y) (opposite x z)) := by
  intro h
  apply not_right_distributive
  intro x y z
  exact h z y x

theorem opposite_left_bijective (x : Carrier) :
    Function.Bijective (opposite x) := right_bijective x

theorem opposite_right_bijective (y : Carrier) :
    Function.Bijective (fun x => opposite x y) := left_bijective y

end IDT.QMClosure.OneSidedDistributiveSwapControl
