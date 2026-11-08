import Mathlib.Tactic

/-! # Scalar estimates for the real-parameter phase witness -/

namespace IDT.QMClosure.RawPlanePhaseParameterBounds

noncomputable section

set_option maxHeartbeats 1000000

def L (l : ℝ) : ℝ := 36 + l ^ 2
def M (l : ℝ) : ℝ := 18 + l ^ 2
def epsilon (l : ℝ) : ℝ := l / L l
def Uplus (l : ℝ) : ℝ := L l + M l * (epsilon l ^ 2 + epsilon l)
def Uminus (l : ℝ) : ℝ := L l + M l * (epsilon l ^ 2 - epsilon l)
def p (l : ℝ) : ℝ := 3 * l * epsilon l * (epsilon l + 1) / Uplus l
def m (l : ℝ) : ℝ := 3 * l * epsilon l * (1 - epsilon l) / Uminus l

def scalarQ (l : ℝ) : ℝ := epsilon l ^ 2 + 4 *
  ((-m l + (1 + epsilon l) * m l ^ 2) / (1 + m l ^ 2) -
    (p l + (epsilon l - 1) * p l ^ 2) / (1 + p l ^ 2))

theorem L_positive (l : ℝ) : 0 < L l := by unfold L; positivity

theorem epsilon_mul_L (l : ℝ) : epsilon l * L l = l := by
  exact div_mul_cancel₀ l (L_positive l).ne'

theorem l_mul_epsilon (l : ℝ) : l * epsilon l = epsilon l ^ 2 * L l := by
  calc
    l * epsilon l = (epsilon l * L l) * epsilon l := by rw [epsilon_mul_L]
    _ = _ := by ring

theorem epsilon_bounds (l : ℝ) : -(1 / 12 : ℝ) ≤ epsilon l ∧ epsilon l ≤ 1 / 12 := by
  have hpos := L_positive l
  constructor
  · apply (le_div_iff₀ hpos).2
    unfold L
    nlinarith [sq_nonneg (l + 6)]
  · apply (div_le_iff₀ hpos).2
    unfold L
    nlinarith [sq_nonneg (l - 6)]

theorem epsilon_sq_le (l : ℝ) : epsilon l ^ 2 ≤ 1 / 144 := by
  rcases epsilon_bounds l with ⟨hlo, hhi⟩
  nlinarith [sq_nonneg (epsilon l - 1 / 12),
    mul_nonneg (by linarith : 0 ≤ epsilon l + 1 / 12)
      (by linarith : 0 ≤ 1 / 12 - epsilon l)]

theorem U_bounds (l : ℝ) :
    L l / 2 ≤ Uplus l ∧ Uplus l ≤ 2 * L l ∧
    L l / 2 ≤ Uminus l ∧ Uminus l ≤ 2 * L l := by
  rcases epsilon_bounds l with ⟨hlo, hhi⟩
  have he := epsilon_sq_le l
  have hm : 0 ≤ M l := by unfold M; positivity
  have hml : M l ≤ L l := by unfold M L; linarith
  have hp : -(1 / 2 : ℝ) ≤ epsilon l ^ 2 + epsilon l ∧
      epsilon l ^ 2 + epsilon l ≤ 1 := by constructor <;> nlinarith [sq_nonneg (epsilon l)]
  have hn : -(1 / 2 : ℝ) ≤ epsilon l ^ 2 - epsilon l ∧
      epsilon l ^ 2 - epsilon l ≤ 1 := by constructor <;> nlinarith [sq_nonneg (epsilon l)]
  unfold Uplus Uminus
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hp.1 hm]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hp.2 hm]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hn.1 hm]
  · nlinarith [mul_le_mul_of_nonneg_left hn.2 hm]

theorem Uplus_positive (l : ℝ) : 0 < Uplus l := by
  have := (U_bounds l).1
  have := L_positive l
  linarith

theorem Uminus_positive (l : ℝ) : 0 < Uminus l := by
  have := (U_bounds l).2.2.1
  have := L_positive l
  linarith

theorem p_mul_U (l : ℝ) : p l * Uplus l =
    3 * (epsilon l ^ 2 * L l) * (epsilon l + 1) := by
  rw [p, div_mul_cancel₀ _ (Uplus_positive l).ne']
  calc
    3 * l * epsilon l * (epsilon l + 1) =
        3 * (l * epsilon l) * (epsilon l + 1) := by ring
    _ = _ := by rw [l_mul_epsilon]

theorem m_mul_U (l : ℝ) : m l * Uminus l =
    3 * (epsilon l ^ 2 * L l) * (1 - epsilon l) := by
  rw [m, div_mul_cancel₀ _ (Uminus_positive l).ne']
  calc
    3 * l * epsilon l * (1 - epsilon l) =
        3 * (l * epsilon l) * (1 - epsilon l) := by ring
    _ = _ := by rw [l_mul_epsilon]

theorem pm_positive (l : ℝ) (hl : l ≠ 0) : 0 < p l ∧ 0 < m l := by
  have he : epsilon l ≠ 0 := div_ne_zero hl (L_positive l).ne'
  have hes : 0 < epsilon l ^ 2 * L l := mul_pos (sq_pos_of_ne_zero he) (L_positive l)
  rcases epsilon_bounds l with ⟨hlo, hhi⟩
  have hp := p_mul_U l
  have hm := m_mul_U l
  have hpp : 0 < 3 * (epsilon l ^ 2 * L l) * (epsilon l + 1) :=
    mul_pos (by positivity) (by linarith)
  have hmp : 0 < 3 * (epsilon l ^ 2 * L l) * (1 - epsilon l) :=
    mul_pos (by positivity) (by linarith)
  constructor
  · nlinarith [Uplus_positive l]
  · nlinarith [Uminus_positive l]

theorem pm_upper (l : ℝ) (hl : l ≠ 0) :
    p l ≤ 12 * epsilon l ^ 2 ∧ m l ≤ 12 * epsilon l ^ 2 := by
  rcases pm_positive l hl with ⟨hp, hm⟩
  rcases epsilon_bounds l with ⟨helo, hehi⟩
  rcases U_bounds l with ⟨hpl, hpu, hml, hmu⟩
  have heL : 0 ≤ epsilon l ^ 2 * L l := le_of_lt
    (mul_pos (sq_pos_of_ne_zero (div_ne_zero hl (L_positive l).ne')) (L_positive l))
  have hpn := mul_le_mul_of_nonneg_left (show epsilon l + 1 ≤ 2 by linarith)
    (show 0 ≤ 3 * (epsilon l ^ 2 * L l) by positivity)
  have hmn := mul_le_mul_of_nonneg_left (show 1 - epsilon l ≤ 2 by linarith)
    (show 0 ≤ 3 * (epsilon l ^ 2 * L l) by positivity)
  have hps := mul_le_mul_of_nonneg_left hpl (show 0 ≤ 12 * epsilon l ^ 2 by positivity)
  have hms := mul_le_mul_of_nonneg_left hml (show 0 ≤ 12 * epsilon l ^ 2 by positivity)
  constructor
  · apply (mul_le_mul_iff_left₀ (Uplus_positive l)).mp
    nlinarith [p_mul_U l]
  · apply (mul_le_mul_iff_left₀ (Uminus_positive l)).mp
    nlinarith [m_mul_U l]

theorem pm_sum_lower (l : ℝ) (hl : l ≠ 0) : 3 * epsilon l ^ 2 ≤ p l + m l := by
  rcases pm_positive l hl with ⟨hp, hm⟩
  have hpu := (U_bounds l).2.1
  have hmu := (U_bounds l).2.2.2
  have hpp := mul_le_mul_of_nonneg_left hpu hp.le
  have hmp := mul_le_mul_of_nonneg_left hmu hm.le
  have hpeq := p_mul_U l
  have hmeq := m_mul_U l
  have hs : 3 * epsilon l ^ 2 * (2 * L l) ≤ (p l + m l) * (2 * L l) := by
    nlinarith
  exact (mul_le_mul_iff_left₀ (by linarith [L_positive l] : 0 < 2 * L l)).mp hs

theorem fraction_lower (e u : ℝ) (he : e ≤ 1) (hu : 0 ≤ u) (hub : u ≤ 1 / 4) :
    u / 4 ≤ u * (1 - (1 + e) * u) / (1 + u ^ 2) := by
  apply (le_div_iff₀ (by positivity : 0 < 1 + u ^ 2)).2
  have hfactor : 1 / 2 ≤ 1 - (1 + e) * u := by
    nlinarith [mul_le_mul_of_nonneg_right he hu]
  have hus : u ^ 2 ≤ 1 := by nlinarith
  have hfirst := mul_le_mul_of_nonneg_left hfactor hu
  have hlast := mul_le_mul_of_nonneg_left hus (show 0 ≤ u / 4 by positivity)
  nlinarith

theorem scalarQ_upper (l : ℝ) (hl : l ≠ 0) : scalarQ l ≤ -2 * epsilon l ^ 2 := by
  rcases epsilon_bounds l with ⟨helo, hehi⟩
  rcases pm_positive l hl with ⟨hp, hm⟩
  rcases pm_upper l hl with ⟨hpu, hmu⟩
  have hes := epsilon_sq_le l
  have hmp : m l ≤ 1 / 4 := by nlinarith
  have hpp : p l ≤ 1 / 4 := by nlinarith
  have hfm := fraction_lower (epsilon l) (m l) (by linarith) hm.le hmp
  have hfp := fraction_lower (-epsilon l) (p l) (by linarith) hp.le hpp
  simp only [← sub_eq_add_neg] at hfp
  have heq : scalarQ l = epsilon l ^ 2 - 4 *
      (m l * (1 - (1 + epsilon l) * m l) / (1 + m l ^ 2) +
        p l * (1 - (1 - epsilon l) * p l) / (1 + p l ^ 2)) := by
    unfold scalarQ
    ring
  rw [heq]
  have hsum := pm_sum_lower l hl
  nlinarith

theorem scalarQ_negative (l : ℝ) (hl : l ≠ 0) : scalarQ l < 0 := by
  have he : epsilon l ≠ 0 := div_ne_zero hl (L_positive l).ne'
  have := scalarQ_upper l hl
  nlinarith [sq_pos_of_ne_zero he]

end
end IDT.QMClosure.RawPlanePhaseParameterBounds
