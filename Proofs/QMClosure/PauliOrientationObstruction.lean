import Mathlib.Tactic

namespace IDT.QMClosure.PauliOrientationObstruction

/-!
Finite rational coordinate gates and supplied product readouts.
The normalization convention is `rho = (sum_w coefficient w * w) / 2^n`.
No Hilbert representation or physical realizability of these gates is assumed.
-/

inductive Pauli where
  | I | X | Y | Z
  deriving DecidableEq, Fintype

open Pauli
abbrev Word2 := Pauli × Pauli
abbrev Word3 := Pauli × Pauli × Pauli
abbrev State2 := Word2 → ℚ
abbrev State3 := Word3 → ℚ

def sign (b : Bool) : ℚ := if b then -1 else 1

/-- The four independent signs of the involutory two-coordinate table. -/
structure Signs where
  a : Bool
  b : Bool
  c : Bool
  d : Bool
  deriving DecidableEq, Fintype

/-- Pullback of the signed permutation. Each listed pair has the same sign
in both directions, so this is also its forward coefficient action. -/
def gateTable (s : Signs) : Word2 → Word2 × ℚ
  | (I,I) => ((I,I), 1)
  | (I,X) => ((I,X), 1)
  | (Z,I) => ((Z,I), 1)
  | (Z,X) => ((Z,X), 1)
  | (I,Y) => ((Z,Y), 1)
  | (Z,Y) => ((I,Y), 1)
  | (I,Z) => ((Z,Z), 1)
  | (Z,Z) => ((I,Z), 1)
  | (X,I) => ((X,X), sign s.a)
  | (X,X) => ((X,I), sign s.a)
  | (Y,I) => ((Y,X), sign s.b)
  | (Y,X) => ((Y,I), sign s.b)
  | (X,Z) => ((Y,Y), sign s.c)
  | (Y,Y) => ((X,Z), sign s.c)
  | (X,Y) => ((Y,Z), sign s.d)
  | (Y,Z) => ((X,Y), sign s.d)

def gate2 (s : Signs) (r : State2) (w : Word2) : ℚ :=
  (gateTable s w).2 * r (gateTable s w).1

theorem gate2_involutory (s : Signs) (r : State2) :
    gate2 s (gate2 s r) = r := by
  funext w
  rcases w with ⟨p,q⟩
  rcases s with ⟨a,b,c,d⟩
  cases p <;> cases q <;>
    simp [gate2, gateTable, sign] <;> split <;> norm_num

theorem gate2_add (s : Signs) (r t : State2) :
    gate2 s (fun w => r w + t w) = fun w => gate2 s r w + gate2 s t w := by
  funext w
  simp only [gate2, mul_add]

theorem gate2_smul (s : Signs) (k : ℚ) (r : State2) :
    gate2 s (fun w => k * r w) = fun w => k * gate2 s r w := by
  funext w
  simp only [gate2]
  ring

def hTable : Pauli → Pauli × ℚ
  | I => (I, 1) | X => (Z, 1) | Y => (Y, -1) | Z => (X, 1)

/-- Coefficient pullback for X ↦ Y, Y ↦ -X, Z ↦ Z. -/
def sTable : Pauli → Pauli × ℚ
  | I => (I, 1) | X => (Y, -1) | Y => (X, 1) | Z => (Z, 1)

def hFirst (r : State2) (w : Word2) : ℚ :=
  (hTable w.1).2 * r ((hTable w.1).1, w.2)

def sFirst (r : State2) (w : Word2) : ℚ :=
  (sTable w.1).2 * r ((sTable w.1).1, w.2)

def zeroTwo : State2 := fun w =>
  if (w.1 = I ∨ w.1 = Z) ∧ (w.2 = I ∨ w.2 = Z) then 1 else 0

/-- Chronological H_A, G, S_A, G. -/
def circuitOne (s : Signs) : State2 :=
  gate2 s (sFirst (gate2 s (hFirst zeroTwo)))

/-- Chronological H_A, S_A, G, H_A, G. -/
def circuitTwo (s : Signs) : State2 :=
  gate2 s (hFirst (gate2 s (sFirst (hFirst zeroTwo))))

def expectedOne (s : Signs) : State2
  | (I,I) => 1 | (I,Z) => 1
  | (Y,I) => sign s.a * sign s.b
  | (Y,Z) => -(sign s.c * sign s.d)
  | _ => 0

def expectedTwo (s : Signs) : State2
  | (I,I) => 1 | (Y,I) => -1
  | (I,Y) => sign s.d | (Y,Y) => sign s.c
  | _ => 0

theorem circuit_one_coefficients (s : Signs) : circuitOne s = expectedOne s := by
  rcases s with ⟨a,b,c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

theorem circuit_two_coefficients (s : Signs) : circuitTwo s = expectedTwo s := by
  rcases s with ⟨a,b,c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

/-- A local binary product effect. Identity coefficient is one. -/
def localEffect (axis : Pauli) (minus : Bool) (p : Pauli) : ℚ :=
  if p = I then 1 else if p = axis then sign minus else 0

def productReadout2 (r : State2) (axisA axisB : Pauli) (minusA minusB : Bool) : ℚ :=
  (∑ p : Pauli, ∑ q : Pauli,
    r (p,q) * localEffect axisA minusA p * localEffect axisB minusB q) / 4

/-- Only two explicitly supplied families of binary product tests are needed. -/
def TestedPositive (s : Signs) : Prop :=
  (∀ u v : Bool, 0 ≤ productReadout2 (circuitOne s) Y Z u v) ∧
  (∀ u v : Bool, 0 ≤ productReadout2 (circuitTwo s) Y Y u v)

instance (s : Signs) : Decidable (TestedPositive s) := inferInstanceAs
  (Decidable ((∀ u v : Bool, 0 ≤ productReadout2 (circuitOne s) Y Z u v) ∧
  (∀ u v : Bool, 0 ≤ productReadout2 (circuitTwo s) Y Y u v)))

/-- Classification is conditional on the stated finite table and product tests. -/
theorem tested_positive_iff_sign_constraints (s : Signs) :
    TestedPositive s ↔ s.a = s.b ∧ s.d = !s.c := by
  rcases s with ⟨a,b,c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

theorem tested_positive_forces_product_signs (s : Signs) :
    TestedPositive s →
      sign s.a * sign s.b = -(sign s.c * sign s.d) ∧
      sign s.d = -sign s.c := by
  rcases s with ⟨a,b,c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

def ordinary : Signs := ⟨false,false,true,false⟩
def ordinaryZ : Signs := ⟨true,true,false,true⟩
def mirror : Signs := ⟨false,false,false,true⟩
def mirrorZ : Signs := ⟨true,true,true,false⟩

theorem tested_positive_iff_four_choices (s : Signs) :
    TestedPositive s ↔ s = ordinary ∨ s = ordinaryZ ∨ s = mirror ∨ s = mirrorZ := by
  rw [tested_positive_iff_sign_constraints]
  rcases s with ⟨a,b,c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

/-- Three-wire states use explicit ordered wire coordinates. -/
def getWire (w : Word3) : Fin 3 → Pauli
  | 0 => w.1 | 1 => w.2.1 | 2 => w.2.2

def replacePair (w : Word3) (i j : Fin 3) (p : Word2) : Word3 :=
  let f := Function.update (Function.update (getWire w) i p.1) j p.2
  (f 0, f 1, f 2)

/-- Lift the same ordered-pair table to selected wires. -/
def gate3 (s : Signs) (i j : Fin 3) (r : State3) (w : Word3) : ℚ :=
  let t := gateTable s (getWire w i, getWire w j)
  t.2 * r (replacePair w i j t.1)

def hSecond (r : State3) (w : Word3) : ℚ :=
  (hTable w.2.1).2 * r (w.1, (hTable w.2.1).1, w.2.2)

def zeroThree : State3 := fun w =>
  if (w.1 = I ∨ w.1 = Z) ∧ (w.2.1 = I ∨ w.2.1 = Z) ∧
      (w.2.2 = I ∨ w.2.2 = Z) then 1 else 0

/-- H_2, G_{2→1}, G_{1→3}, G_{2→1}, G_{1→3}, G_{2→3}.
Wire numbers in the implementation are zero-based. -/
def mirrorTriangle : State3 :=
  gate3 mirror 1 2 (gate3 mirror 0 2 (gate3 mirror 1 0
    (gate3 mirror 0 2 (gate3 mirror 1 0 (hSecond zeroThree)))))

/-- Coefficients of (I+Z_1)(I+X_2+Z_3-X_2 Z_3). -/
def expectedTriangle (w : Word3) : ℚ :=
  if w.1 = I ∨ w.1 = Z then
    match w.2 with
    | (I,I) => 1 | (X,I) => 1 | (I,Z) => 1 | (X,Z) => -1 | _ => 0
  else 0

theorem mirror_triangle_coefficients : mirrorTriangle = expectedTriangle := by
  funext w
  rcases w with ⟨p,q,r⟩
  cases p <;> cases q <;> cases r <;> decide +kernel

/-- Product event X_2=-1, Z_3=-1, with wire 1 ignored.
Ignoring a wire selects its identity coefficient. -/
def negativeTriangleReadout (r : State3) : ℚ :=
  (∑ p : Pauli, ∑ q : Pauli,
    r (I,p,q) * localEffect X true p * localEffect Z true q) / 4

theorem mirror_triangle_negative : negativeTriangleReadout mirrorTriangle = -1/2 := by
  rw [mirror_triangle_coefficients]
  decide +kernel

/-- Reachability by exactly the supplied local and ordered-pair operations. -/
inductive Generated : State3 → Prop
  | initial : Generated zeroThree
  | hSecond {r} : Generated r → Generated (hSecond r)
  | pair {r} (i j : Fin 3) : i ≠ j → Generated r → Generated (gate3 mirror i j r)

theorem mirror_triangle_generated : Generated mirrorTriangle := by
  apply Generated.pair 1 2 (by decide +kernel)
  apply Generated.pair 0 2 (by decide +kernel)
  apply Generated.pair 1 0 (by decide +kernel)
  apply Generated.pair 0 2 (by decide +kernel)
  apply Generated.pair 1 0 (by decide +kernel)
  exact Generated.hSecond Generated.initial

theorem generated_product_nonnegativity_impossible :
    ¬ (∀ r : State3, Generated r → 0 ≤ negativeTriangleReadout r) := by
  intro h
  have hp := h mirrorTriangle mirror_triangle_generated
  rw [mirror_triangle_negative] at hp
  norm_num at hp

end IDT.QMClosure.PauliOrientationObstruction
