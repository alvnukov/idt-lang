import Mathlib.Tactic

/-!
V7 Positive Comparison Geometry — Concrete Proofs.
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

def FacticizationStability (G : CompForm2) : Prop :=
  ∀ (v : Dir2), quadForm G v ≥ 0

-- Identity form is PSD: x² + y² ≥ 0
example : FacticizationStability ⟨1, 0, 1⟩ := by
  intro v
  change 1 * v.x * v.x + 2 * 0 * v.x * v.y + 1 * v.y * v.y ≥ 0
  have h1 : v.x * v.x ≥ 0 := mul_self_nonneg v.x
  have h2 : v.y * v.y ≥ 0 := mul_self_nonneg v.y
  linarith

-- [[1,2],[2,1]] is NOT PSD: x² + 4xy + y² can be negative
example : ¬ FacticizationStability ⟨1, 2, 1⟩ := by
  intro h
  have := h ⟨1, -1⟩
  change 1 * 1 * 1 + 2 * 2 * 1 * (-1) + 1 * (-1) * (-1) ≥ 0 at this
  linarith

-- [[2,1,1,2]] is PSD: 2x² + 2xy + 2y² ≥ 0
example : FacticizationStability ⟨2, 1, 2⟩ := by
  intro v
  change 2 * v.x * v.x + 2 * 1 * v.x * v.y + 2 * v.y * v.y ≥ 0
  have h1 : v.x * v.x ≥ 0 := mul_self_nonneg v.x
  have h2 : v.y * v.y ≥ 0 := mul_self_nonneg v.y
  have h3 : (v.x + v.y) * (v.x + v.y) ≥ 0 := mul_self_nonneg (v.x + v.y)
  linarith

-- [[1,3,1]] is NOT PSD: x² + 6xy + y² can be negative
example : ¬ FacticizationStability ⟨1, 3, 1⟩ := by
  intro h
  have := h ⟨1, -1⟩
  change 1 * 1 * 1 + 2 * 3 * 1 * (-1) + 1 * (-1) * (-1) ≥ 0 at this
  linarith

-- [[1,0.5,1]] is PSD: x² + xy + y² ≥ 0
-- This is (x+y/2)² + 3y²/4 ≥ 0
example : FacticizationStability ⟨1, 1/2, 1⟩ := by
  intro v
  change 1 * v.x * v.x + 2 * (1/2) * v.x * v.y + 1 * v.y * v.y ≥ 0
  have h1 : v.x * v.x ≥ 0 := mul_self_nonneg v.x
  have h2 : v.y * v.y ≥ 0 := mul_self_nonneg v.y
  have h3 : (v.x + v.y) * (v.x + v.y) ≥ 0 := mul_self_nonneg (v.x + v.y)
  linarith

def status : String := "concrete_proofs_with_mathlib"

/-!
CONCLUSION:
- Identity form is PSD (proved)
- [[1,2],[2,1]] rejected by F (proved)
- [[2,1,1,2]] is PSD (proved)
- [[1,3,1]] rejected by F (proved)
- [[1,0.5,1]] is PSD (proved)
-/

end QMClosure
end IDT
