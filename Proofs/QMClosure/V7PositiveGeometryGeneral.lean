import Mathlib.Tactic

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

-- FORWARD: F → PSD conditions
theorem a_nonneg (G : CompForm2) (h : FacticizationStability G) : G.a ≥ 0 := by
  have := h ⟨1, 0⟩; simp only [quadForm] at this; linarith

theorem c_nonneg (G : CompForm2) (h : FacticizationStability G) : G.c ≥ 0 := by
  have := h ⟨0, 1⟩; simp only [quadForm] at this; linarith

theorem sum_nonneg (G : CompForm2) (h : FacticizationStability G) : G.a + 2 * G.b + G.c ≥ 0 := by
  have := h ⟨1, 1⟩; simp only [quadForm] at this; linarith

theorem diff_nonneg (G : CompForm2) (h : FacticizationStability G) : G.a - 2 * G.b + G.c ≥ 0 := by
  have := h ⟨1, -1⟩; simp only [quadForm] at this; linarith

/-! KEY THEOREM: F → ac ≥ b² (determinant nonnegativity for 2×2 PSD)

Proof strategy (no division required):

Case a > 0: direction v = (-b, a) gives
  quadForm = a·b² - 2ab² + a²c = a(ac - b²) ≥ 0
  Since a > 0: ac - b² ≥ 0, i.e. ac ≥ b².

Case a = 0, c > 0: direction v = (c, -b) gives
  quadForm = ac² - 2b²c + b²c = c(ac - b²) = -b²·c ≥ 0
  Since c > 0 and -b²·c ≥ 0: b² ≤ 0, so b = 0. Then ac = 0 ≥ 0 = b².

Case a = 0, c = 0: from F(1,1) = 2b ≥ 0 and F(1,-1) = -2b ≥ 0, b = 0.
  Then ac = 0 ≥ 0 = b². -/
theorem det_nonneg (G : CompForm2) (h : FacticizationStability G) : G.a * G.c ≥ G.b * G.b := by
  have ha_nonneg := a_nonneg G h
  have hc_nonneg := c_nonneg G h
  by_cases ha_pos : G.a > 0
  · -- Case a > 0: direction (-b, a) gives a(ac - b²) ≥ 0, so ac ≥ b²
    have hv := h ⟨-G.b, G.a⟩
    simp only [quadForm] at hv
    -- hv: a*b² - 2a*b² + a²*c ≥ 0, i.e. a²c - a*b² ≥ 0, i.e. a(ac - b²) ≥ 0
    nlinarith [ha_pos, hv, sq_nonneg G.b]
  · -- a ≤ 0, but a ≥ 0, so a = 0
    have ha_zero : G.a = 0 := by linarith
    by_cases hc_pos : G.c > 0
    · -- Case a = 0, c > 0: direction (c, -b) gives -b²*c ≥ 0
      -- Since c > 0: b² ≤ 0, so b = 0
      have hv := h ⟨G.c, -G.b⟩
      simp only [quadForm] at hv
      -- Substitute a = 0 into hv
      rw [ha_zero] at hv
      simp at hv
      -- hv: -b²*c ≥ 0, i.e. b²*c ≤ 0
      -- Since c > 0: b² ≤ 0, so b = 0
      have hb_zero : G.b = 0 := by
        have : G.b * G.b * G.c ≤ 0 := by nlinarith [hv, hc_pos]
        have : G.b * G.b ≤ 0 := by
          by_contra hpos
          have : G.b * G.b > 0 := by linarith
          have : G.b * G.b * G.c > 0 := by nlinarith
          linarith
        nlinarith [sq_nonneg G.b]
      rw [ha_zero, hb_zero]
      simp
    · -- a = 0 and c ≤ 0, but c ≥ 0, so c = 0
      have hc_zero : G.c = 0 := by linarith
      -- From F(1,1) and F(1,-1): 2b ≥ 0 and -2b ≥ 0, so b = 0
      have h1 := h ⟨1, 1⟩
      have h2 := h ⟨1, -1⟩
      simp only [quadForm] at h1 h2
      rw [ha_zero, hc_zero] at h1 h2
      simp at h1 h2
      -- h1: 2*b ≥ 0, h2: -2*b ≥ 0
      have hb_zero : G.b = 0 := by linarith
      rw [ha_zero, hb_zero, hc_zero]

-- FULL CHARACTERIZATION
theorem psd_conditions (G : CompForm2) (h : FacticizationStability G) :
    G.a ≥ 0 ∧ G.c ≥ 0 ∧ G.a * G.c ≥ G.b * G.b :=
  ⟨a_nonneg G h, c_nonneg G h, det_nonneg G h⟩

def status : String := "general_proof_complete"

end QMClosure
end IDT
