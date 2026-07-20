import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
V7 Positive Comparison Geometry — Concrete Proof with Mathlib.
-/

namespace IDT
namespace QMClosure

structure CompForm2 where
  a : Real
  b : Real
  c : Real

structure Dir2 where
  x : Real
  y : Real

def quadForm (G : CompForm2) (v : Dir2) : Real :=
  G.a * v.x * v.x + 2 * G.b * v.x * v.y + G.c * v.y * v.y

def toMatrix (G : CompForm2) : Matrix (Fin 2) (Fin 2) Real :=
  !![G.a, G.b;
     G.b, G.c]

def FacticizationStability (G : CompForm2) : Prop :=
  ∀ (v : Dir2), quadForm G v ≥ 0

-- Identity form is PSD
example : FacticizationStability ⟨1, 0, 1⟩ := by
  intro v
  simp [quadForm]
  have h1 : 0 ≤ v.x ^ 2 := sq_nonneg v.x
  have h2 : 0 ≤ v.y ^ 2 := sq_nonneg v.y
  have h3 : v.x * v.x = v.x ^ 2 := by ring
  have h4 : v.y * v.y = v.y ^ 2 := by ring
  rw [h3, h4]
  linarith

-- [[1,2],[2,1]] is NOT PSD (F rejects it)
example : ¬ FacticizationStability ⟨1, 2, 1⟩ := by
  intro h
  have := h ⟨1, -1⟩
  simp [quadForm] at this
  linarith

def status : String := "concrete_with_mathlib"

end QMClosure
end IDT
