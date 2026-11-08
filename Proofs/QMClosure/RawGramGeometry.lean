import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Finite Gram geometry without a vector-space structure

These lemmas concern a symmetric real kernel on an arbitrary carrier. The
triangle equivalence explicitly assumes closure under all real kernel scalings.
No global addition, topology, or Hilbert representation is supplied.
-/

namespace IDT.QMClosure.RawGramGeometry

open scoped BigOperators

noncomputable section

variable {V : Type*}

def quadratic (G : V → V → ℝ) {n : ℕ} (p : Fin n → V) (c : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * G (p i) (p j)

def GramNonnegative (G : V → V → ℝ) (n : ℕ) : Prop :=
  ∀ (p : Fin n → V) (c : Fin n → ℝ), 0 ≤ quadratic G p c

def Triangle (d : V → V → ℝ) : Prop :=
  ∀ x y z, d x z ≤ d x y + d y z

variable {G : V → V → ℝ}

theorem quadratic_three (hsym : ∀ x y, G x y = G y x)
    (p : Fin 3 → V) (c : Fin 3 → ℝ) :
    quadratic G p c = c 0 ^ 2 * G (p 0) (p 0) + c 1 ^ 2 * G (p 1) (p 1) +
      c 2 ^ 2 * G (p 2) (p 2) + 2 * c 0 * c 1 * G (p 0) (p 1) +
      2 * c 0 * c 2 * G (p 0) (p 2) + 2 * c 1 * c 2 * G (p 1) (p 2) := by
  simp [quadratic, Fin.sum_univ_succ]
  rw [hsym (p 1) (p 0), hsym (p 2) (p 0), hsym (p 2) (p 1)]
  ring

theorem quadratic_four (hsym : ∀ x y, G x y = G y x)
    (p : Fin 4 → V) (c : Fin 4 → ℝ) :
    quadratic G p c = c 0 ^ 2 * G (p 0) (p 0) + c 1 ^ 2 * G (p 1) (p 1) +
      c 2 ^ 2 * G (p 2) (p 2) + c 3 ^ 2 * G (p 3) (p 3) +
      2 * c 0 * c 1 * G (p 0) (p 1) + 2 * c 0 * c 2 * G (p 0) (p 2) +
      2 * c 0 * c 3 * G (p 0) (p 3) + 2 * c 1 * c 2 * G (p 1) (p 2) +
      2 * c 1 * c 3 * G (p 1) (p 3) + 2 * c 2 * c 3 * G (p 2) (p 3) := by
  simp [quadratic, Fin.sum_univ_succ]
  rw [hsym (p 1) (p 0), hsym (p 2) (p 0), hsym (p 3) (p 0),
    hsym (p 2) (p 1), hsym (p 3) (p 1), hsym (p 3) (p 2)]
  ring

theorem diagonal_nonnegative (h : GramNonnegative G 4) (x : V) : 0 ≤ G x x := by
  simpa [quadratic, Fin.sum_univ_succ] using h ![x, x, x, x] ![1, 0, 0, 0]

theorem null_plane_quadratic (hsym : ∀ x y, G x y = G y x)
    (x y u z : V) (s t : ℝ) :
    quadratic G ![x, y, u, z] ![s, s, -s, t] =
      s ^ 2 * quadratic G ![x, y, u] ![1, 1, -1] +
        2 * s * t * (G x z + G y z - G u z) + t ^ 2 * G z z := by
  rw [quadratic_four hsym, quadratic_three hsym]
  simp
  ring

theorem four_point_null_transfer (hsym : ∀ x y, G x y = G y x)
    (h : GramNonnegative G 4) (x y u z : V)
    (hnull : quadratic G ![x, y, u] ![1, 1, -1] = 0) :
    G x z + G y z - G u z = 0 := by
  have hp (s : ℝ) :
      0 ≤ (0 : ℝ) * (s * s) + (2 * (G x z + G y z - G u z)) * s + G z z := by
    have hh := h ![x, y, u, z] ![s, s, -s, 1]
    rw [null_plane_quadratic hsym, hnull] at hh
    nlinarith
  have hd := discrim_le_zero hp
  dsimp [discrim] at hd
  nlinarith [sq_nonneg (G x z + G y z - G u z)]

theorem null_plane_nonnegative_iff (hsym : ∀ x y, G x y = G y x)
    (x y u z : V) (hnull : quadratic G ![x, y, u] ![1, 1, -1] = 0)
    (hdiag : 0 ≤ G z z) :
    (∀ s t : ℝ, 0 ≤ quadratic G ![x, y, u, z] ![s, s, -s, t]) ↔
      G x z + G y z - G u z = 0 := by
  constructor
  · intro h
    have hp (s : ℝ) :
        0 ≤ (0 : ℝ) * (s * s) + (2 * (G x z + G y z - G u z)) * s + G z z := by
      have hh := h s 1
      rw [null_plane_quadratic hsym, hnull] at hh
      nlinarith
    have hd := discrim_le_zero hp
    dsimp [discrim] at hd
    nlinarith [sq_nonneg (G x z + G y z - G u z)]
  · intro hcross s t
    rw [null_plane_quadratic hsym, hnull, hcross]
    simpa using mul_nonneg (sq_nonneg t) hdiag

theorem triangle_iff_three_point (hsym : ∀ x y, G x y = G y x)
    (scale : ℝ → V → V)
    (hscale : ∀ r x y, G (scale r x) y = r * G x y)
    (d : V → V → ℝ) (dnonneg : ∀ x y, 0 ≤ d x y)
    (dsquare : ∀ x y, (d x y) ^ 2 = G x x + G y y - 2 * G x y) :
    Triangle d ↔ GramNonnegative G 3 := by
  have hright (r : ℝ) (x y : V) : G x (scale r y) = r * G x y := by
    rw [hsym, hscale, hsym y x]
  have hboth (r s : ℝ) (x y : V) :
      G (scale r x) (scale s y) = r * s * G x y := by
    rw [hscale, hright]
    ring
  constructor
  · intro htri p c
    let x := scale (c 0) (p 0)
    let y := scale (c 1) (p 1)
    let z := scale (-c 2 / 2) (p 2)
    have hid : quadratic G p c =
        2 * (d x z) ^ 2 + 2 * (d y z) ^ 2 - (d x y) ^ 2 := by
      rw [quadratic_three hsym, dsquare, dsquare, dsquare]
      dsimp [x, y, z]
      simp only [hboth]
      ring
    have hxy : d x y ≤ d x z + d y z := by
      have hz : d z y = d y z := by
        have he := dsquare z y
        rw [hsym z y] at he
        nlinarith [dsquare y z, dnonneg z y, dnonneg y z]
      simpa [hz] using htri x z y
    rw [hid]
    nlinarith [dnonneg x y, dnonneg x z, dnonneg y z,
      sq_nonneg (d x z - d y z)]
  · intro hgram x y z
    have hp (r : ℝ) :
        0 ≤ (d x y) ^ 2 * (r * r) +
          ((d x y) ^ 2 + (d y z) ^ 2 - (d x z) ^ 2) * r + (d y z) ^ 2 := by
      have hh := hgram ![x, y, z] ![r, -r - 1, 1]
      rw [quadratic_three hsym] at hh
      simp at hh
      rw [dsquare, dsquare, dsquare]
      convert hh using 1
      ring
    have hd := discrim_le_zero hp
    dsimp [discrim] at hd
    have hab : 0 ≤ d x y * d y z := mul_nonneg (dnonneg x y) (dnonneg y z)
    have hs : ((d x y) ^ 2 + (d y z) ^ 2 - (d x z) ^ 2) ^ 2 ≤
        (2 * d x y * d y z) ^ 2 := by nlinarith
    have hl : -(2 * d x y * d y z) ≤
        (d x y) ^ 2 + (d y z) ^ 2 - (d x z) ^ 2 := by
      have := (sq_le_sq₀ (by positivity : 0 ≤
        |(d x y) ^ 2 + (d y z) ^ 2 - (d x z) ^ 2|)
        (by nlinarith : 0 ≤ 2 * d x y * d y z)).mp (by simpa using hs)
      exact (abs_le.mp this).1
    nlinarith [dnonneg x y, dnonneg y z, dnonneg x z]

end

end IDT.QMClosure.RawGramGeometry
