import Proofs.QMClosure.RawNetworkMedialWall

/-!
# Homogeneous maps on scalar product arrays

Joint homogeneity makes a row map and a column map commute on arrays that
factor as `productArray a b`. The two maps may be different. This statement
does not assert interchange on arbitrary arrays or supply a physical tensor
product or independently available subsystems. No additivity of either map,
square-swap, continuity, norm conservation, or probability law is assumed.
-/

namespace IDT.QMClosure.HomogeneousProductInterchange

open RawNetworkMedialWall (Quad rows columns)

variable {K : Type*} [CommMonoid K]

/-- A two-by-two array given by products of two scalar pairs. -/
def productArray (a b : K × K) : Quad K :=
  ((a.1 * b.1, a.1 * b.2), (a.2 * b.1, a.2 * b.2))

/-- Scaling both input coordinates scales both output coordinates. -/
def JointHomogeneous (F : K × K → K × K) : Prop :=
  ∀ (t : K) (p : K × K),
    F (t * p.1, t * p.2) = (t * (F p).1, t * (F p).2)

/-- A homogeneous row map changes only the second factor. -/
theorem rows_productArray (G : K × K → K × K)
    (hG : JointHomogeneous G) (a b : K × K) :
    rows G (productArray a b) = productArray a (G b) := by
  change (G (a.1 * b.1, a.1 * b.2), G (a.2 * b.1, a.2 * b.2)) = _
  rw [hG a.1 b, hG a.2 b]
  rfl

/-- Commutative scalar multiplication lets a homogeneous column map change
only the first factor. -/
theorem columns_productArray (F : K × K → K × K)
    (hF : JointHomogeneous F) (a b : K × K) :
    columns F (productArray a b) = productArray (F a) b := by
  have h1 : F (a.1 * b.1, a.2 * b.1) =
      ((F a).1 * b.1, (F a).2 * b.1) := by
    simpa only [mul_comm] using hF b.1 a
  have h2 : F (a.1 * b.2, a.2 * b.2) =
      ((F a).1 * b.2, (F a).2 * b.2) := by
    simpa only [mul_comm] using hF b.2 a
  change (((F (a.1 * b.1, a.2 * b.1)).1,
      (F (a.1 * b.2, a.2 * b.2)).1),
    ((F (a.1 * b.1, a.2 * b.1)).2,
      (F (a.1 * b.2, a.2 * b.2)).2)) = _
  rw [h1, h2]
  rfl

theorem columns_rows_productArray (F G : K × K → K × K)
    (hF : JointHomogeneous F) (hG : JointHomogeneous G) (a b : K × K) :
    columns F (rows G (productArray a b)) = productArray (F a) (G b) := by
  rw [rows_productArray G hG, columns_productArray F hF]

theorem rows_columns_productArray (F G : K × K → K × K)
    (hF : JointHomogeneous F) (hG : JointHomogeneous G) (a b : K × K) :
    rows G (columns F (productArray a b)) = productArray (F a) (G b) := by
  rw [columns_productArray F hF, rows_productArray G hG]

/-- Interchange is restricted to scalar product arrays. -/
theorem interchange_productArray (F G : K × K → K × K)
    (hF : JointHomogeneous F) (hG : JointHomogeneous G) (a b : K × K) :
    columns F (rows G (productArray a b)) =
      rows G (columns F (productArray a b)) := by
  rw [columns_rows_productArray F G hF hG, rows_columns_productArray F G hF hG]

end IDT.QMClosure.HomogeneousProductInterchange
