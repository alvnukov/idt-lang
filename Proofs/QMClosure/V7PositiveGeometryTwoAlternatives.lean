/-!
V7 Positive Comparison Geometry for 2 Alternatives.
-/

namespace IDT
namespace QMClosure

def Real := Rat

structure CompForm2 where
  a : Real
  b : Real
  c : Real

structure Dir2 where
  x : Real
  y : Real

def quadForm (G : CompForm2) (v : Dir2) : Real :=
  G.a * v.x * v.x + 2 * G.b * v.x * v.y + G.c * v.y * v.y

-- F: facticization nonnegativity axiom
axiom facticizationNonneg :
  ∀ (G : CompForm2) (v : Dir2), quadForm G v ≥ 0

-- Theorem: G is PSD
theorem positiveGeometry2 :
  ∀ (G : CompForm2) (v : Dir2), quadForm G v ≥ 0 :=
  facticizationNonneg

def status : String := "proved_axiomatically"

/-!
HONEST BOUNDARY:
- This proves: IF facticizationNonneg holds, THEN G is PSD
- facticizationNonneg IS the axiom F
- This does NOT prove: F follows from B0
- The concrete example (identity form is PSD) requires Mathlib
-/

end QMClosure
end IDT
