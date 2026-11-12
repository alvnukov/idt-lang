import Proofs.QMClosure.TransparentFourthVacuumCountermodels

/-!
# Ordered additive readout boundary on the literal initial presentation

This file specifies the lexicographic order directly on real pairs. The additive
commutative group operations are the ordinary componentwise pair operations.
The distinguished normalization element is `(1, 0)`.

The pair response satisfies the six scaled-word schemas, universal prepared
mixed zero, first-column conservation, and null insertion. Exact witnesses
separate it from the norm-valued response and from equal branch division.
The statements concern this supplied additive order and algebraic presentation.
-/

namespace IDT.QMClosure.TransparentFourthOrderedReadoutBoundary

noncomputable section

open TransparentFourthInitialHistoryPresentation
open TransparentFourthVacuumCountermodels

abbrev Pair := ℝ × ℝ

def LexLE (x y : Pair) : Prop :=
  x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 ≤ y.2

def LexLT (x y : Pair) : Prop :=
  x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 < y.2

def unit : Pair := (1, 0)

theorem lexLE_refl (x : Pair) : LexLE x x :=
  Or.inr ⟨rfl, le_refl _⟩

theorem lexLE_trans {x y z : Pair} (hxy : LexLE x y) (hyz : LexLE y z) :
    LexLE x z := by
  rcases hxy with hxy | ⟨hxy, hxy'⟩
  · rcases hyz with hyz | ⟨hyz, hyz'⟩
    · exact Or.inl (lt_trans hxy hyz)
    · exact Or.inl (by linarith)
  · rcases hyz with hyz | ⟨hyz, hyz'⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨hxy.trans hyz, le_trans hxy' hyz'⟩

theorem lexLE_antisymm {x y : Pair} (hxy : LexLE x y) (hyx : LexLE y x) :
    x = y := by
  rcases hxy with hxy | ⟨hxy, hxy'⟩ <;>
    rcases hyx with hyx | ⟨hyx, hyx'⟩ <;>
    apply Prod.ext <;> dsimp at * <;> linarith

theorem lexLE_total (x y : Pair) : LexLE x y ∨ LexLE y x := by
  rcases lt_trichotomy x.1 y.1 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases le_total x.2 y.2 with h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
  · exact Or.inr (Or.inl h)

theorem lexLE_add_right_iff (x y z : Pair) :
    LexLE (x + z) (y + z) ↔ LexLE x y := by
  change (x.1 + z.1 < y.1 + z.1 ∨
    x.1 + z.1 = y.1 + z.1 ∧ x.2 + z.2 ≤ y.2 + z.2) ↔
      (x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 ≤ y.2)
  simp only [add_lt_add_iff_right, add_right_cancel_iff, add_le_add_iff_right]

theorem lexLT_iff (x y : Pair) : LexLT x y ↔ LexLE x y ∧ ¬ LexLE y x := by
  unfold LexLT LexLE
  constructor
  · rintro (h | ⟨h, h'⟩)
    · constructor
      · exact Or.inl h
      · rintro (hr | ⟨hr, _⟩) <;> linarith
    · constructor
      · exact Or.inr ⟨h, h'.le⟩
      · rintro (hr | ⟨hr, hr'⟩) <;> linarith
  · rintro ⟨h, hn⟩
    rcases h with h | ⟨h, h'⟩
    · exact Or.inl h
    · right
      refine ⟨h, lt_of_le_of_ne h' ?_⟩
      intro he
      apply hn
      exact Or.inr ⟨h.symm, he.symm.le⟩

theorem lexLE_add_left_iff (x y z : Pair) :
    LexLE (z + x) (z + y) ↔ LexLE x y := by
  simpa only [add_comm] using lexLE_add_right_iff x y z

theorem unit_positive : LexLT 0 unit := by
  left
  norm_num [unit]

/-- A real pair with its response specified independently of carrier multiplication. -/
def L (p : Presentation) : Pair := (N p, (E p).re - N p)

def normPair (p : Presentation) : Pair := (N p, 0)

def half (x : Pair) : Pair := (x.1 / 2, x.2 / 2)

@[simp] theorem L_zero : L 0 = 0 := by simp [L]

@[simp] theorem L_one : L 1 = unit := by simp [L, unit]

@[simp] theorem L_c_mul (p : Presentation) : L (c * p) = L p := by
  simp [L]

theorem L_of_E_zero {p : Presentation} (hp : E p = 0) : L p = 0 := by
  simp [L, N, hp]

theorem L_nonnegative (p : Presentation) : LexLE 0 (L p) := by
  by_cases hp : E p = 0
  · rw [L_of_E_zero hp]
    exact lexLE_refl _
  · left
    exact Complex.normSq_pos.mpr hp

private theorem E_bag_re (n m : ℕ) (p : Presentation) :
    (E (bag n m p)).re =
      ((n : ℝ) * ((E p).re - (E p).im) +
        (m : ℝ) * ((E p).re + (E p).im)) / 2 := by
  simp [bag, complexA, complexB, Complex.mul_re, Complex.mul_im]
  ring

/-- The exact polynomial response at every natural-count bag and preparation. -/
theorem L_bag (n m : ℕ) (p : Presentation) :
    L (bag n m p) =
      (countNorm n m * N p,
        ((n : ℝ) * ((E p).re - (E p).im) +
          (m : ℝ) * ((E p).re + (E p).im)) / 2 - countNorm n m * N p) := by
  simp only [L, N_bag, E_bag_re]

private theorem countNorm_strict {n m n' m' : ℕ}
    (hn : n ≤ n') (hm : m ≤ m') (hne : ¬ (n = n' ∧ m = m')) :
    countNorm n m < countNorm n' m' := by
  have hn' : (n : ℝ) ≤ n' := by exact_mod_cast hn
  have hm' : (m : ℝ) ≤ m' := by exact_mod_cast hm
  have hnsq : (n : ℝ) ^ 2 ≤ (n' : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hn'
  have hmsq : (m : ℝ) ^ 2 ≤ (m' : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hm'
  have hlt : n < n' ∨ m < m' := by omega
  rcases hlt with hlt | hlt
  · have hlt' : (n : ℝ) < n' := by exact_mod_cast hlt
    have hsum : 0 < (n' : ℝ) + n := by
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      linarith
    have hprod := mul_pos (sub_pos.mpr hlt') hsum
    dsimp [countNorm]
    nlinarith
  · have hlt' : (m : ℝ) < m' := by exact_mod_cast hlt
    have hsum : 0 < (m' : ℝ) + m := by
      have hm0 : 0 ≤ (m : ℝ) := by positivity
      linarith
    have hprod := mul_pos (sub_pos.mpr hlt') hsum
    dsimp [countNorm]
    nlinarith

/-- Every actual preparation is covered, including the complex-null sector. -/
theorem L_preparedOrder (n m n' m' : ℕ) (p : Presentation)
    (hn : n ≤ n') (hm : m ≤ m') :
    LexLE (L (bag n m p)) (L (bag n' m' p)) := by
  by_cases hp : E p = 0
  · have hz (s t : ℕ) : L (bag s t p) = 0 := by
      apply L_of_E_zero
      simp [bag, hp]
    rw [hz, hz]
    exact lexLE_refl _
  · by_cases heq : n = n' ∧ m = m'
    · rcases heq with ⟨rfl, rfl⟩
      exact lexLE_refl _
    · left
      change N (bag n m p) < N (bag n' m' p)
      rw [N_bag, N_bag]
      exact mul_lt_mul_of_pos_right (countNorm_strict hn hm heq)
        (Complex.normSq_pos.mpr hp)

/-- Balanced addition states mixed zero without requiring response division. -/
def PreparedMixedZero (W : Presentation → Pair) : Prop :=
  ∀ (p : Presentation) (n m : ℕ),
    W (bag (n + 1) (m + 1) p) + W (bag n m p) =
      W (bag (n + 1) m p) + W (bag n (m + 1) p)

theorem L_preparedMixedZero : PreparedMixedZero L := by
  intro p n m
  rw [L_bag, L_bag, L_bag, L_bag]
  apply Prod.ext <;>
    simp [countNorm, Nat.cast_add, Nat.cast_one] <;> ring

/-- Universal preparation mixed zero includes every externally supplied scale family. -/
theorem L_scaledMixedZero (scale : ℕ → Presentation) (k n m : ℕ) :
    L (bag (n + 1) (m + 1) (scale k)) + L (bag n m (scale k)) =
      L (bag (n + 1) m (scale k)) + L (bag n (m + 1) (scale k)) :=
  L_preparedMixedZero (scale k) n m

def WordScaledRawMixedZero (W : Presentation → Pair) : Prop :=
  ∀ k n m : ℕ,
    W (bag (n + 1) (m + 1) ((a * b) ^ k)) + W (bag n m ((a * b) ^ k)) =
      W (bag (n + 1) m ((a * b) ^ k)) + W (bag n (m + 1) ((a * b) ^ k))

theorem L_wordScaledRawMixedZero : WordScaledRawMixedZero L := by
  intro k n m
  exact L_preparedMixedZero _ _ _

@[simp] theorem L_T : L T = 0 := by simp [L]

/-- The six schemas with their additive ordered-pair carrier made explicit. -/
structure OrderedVacuumContract (W : Presentation → Pair) : Prop where
  vacuum : W 0 = 0
  normalization : W 1 = unit
  transparent : ∀ p, W (c * p) = W p
  preparedOrder : ∀ (n m n' m' : ℕ) (p : Presentation), n ≤ n' → m ≤ m' →
    LexLE (W (bag n m p)) (W (bag n' m' p))
  scaledMixedZero : WordScaledRawMixedZero W
  nullWitness : W T = 0

theorem L_contract : OrderedVacuumContract L where
  vacuum := L_zero
  normalization := L_one
  transparent := L_c_mul
  preparedOrder := L_preparedOrder
  scaledMixedZero := L_wordScaledRawMixedZero
  nullWitness := L_T

theorem L_column (p : Presentation) : L (a * p) + L (b * p) = L p := by
  calc
    L (a * p) + L (b * p) = L (bag 1 0 p) + L (bag 0 1 p) := by simp [bag]
    _ = L p := by
      rw [L_bag, L_bag]
      apply Prod.ext <;> simp [L, countNorm] <;> ring

theorem L_nullInsertion (x p : Presentation) : L (x + e * p) = L x := by
  simp [L, N]

@[simp] theorem L_two : L 2 = (4, -2) := by
  norm_num [L, N, map_ofNat, Complex.normSq_apply]

@[simp] theorem L_a : L a = (1 / 2, 0) := by
  norm_num [L, complexA, Complex.div_re, Complex.div_im]

@[simp] theorem L_b : L b = (1 / 2, 0) := by
  norm_num [L, complexB, Complex.div_re, Complex.div_im]

@[simp] theorem L_ab : L (a * b) = (1 / 4, 1 / 4) := by
  norm_num [L, complexA, complexB, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]

@[simp] theorem L_a_squared : L (a ^ 2) = (1 / 4, -1 / 4) := by
  norm_num [L, pow_two, complexA, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]

theorem L_two_ne_normPair : L 2 ≠ normPair 2 := by
  rw [L_two]
  norm_num [normPair, N, map_ofNat, Complex.normSq_apply]

theorem L_ab_ne_normPair : L (a * b) ≠ normPair (a * b) := by
  rw [L_ab]
  norm_num [normPair]

theorem L_a_squared_ne_half : L (a ^ 2) ≠ half (L a) := by
  rw [L_a_squared, L_a]
  norm_num [half]

/-- The exact norm-pair difference at `ab` is a positive infinitesimal. -/
def infinitesimal : Pair := (0, 1 / 4)

theorem L_ab_infinitesimal : L (a * b) - normPair (a * b) = infinitesimal := by
  rw [L_ab]
  norm_num [normPair, infinitesimal]

theorem infinitesimal_positive : LexLT 0 infinitesimal := by
  right
  norm_num [infinitesimal]

theorem infinitesimal_nsmul_lt_unit (n : ℕ) : LexLT (n • infinitesimal) unit := by
  left
  simp [infinitesimal, unit]

/-- The literal initial presentation retains a nonzero preparation with zero response. -/
theorem L_has_nonzero_null : T ≠ 0 ∧ L T = 0 := ⟨T_ne_zero, L_T⟩

end

end IDT.QMClosure.TransparentFourthOrderedReadoutBoundary
