import Mathlib.Order.Monotone.Basic

/-!
# An order obstruction for a transparent square root of swap

On any preorder, a monotone two-port operation whose square swaps its inputs and
which fixes every raw diagonal forces every comparable pair to be comparable in
the reverse direction. For a partial order, every comparable pair is equal.
The result does not assert that the whole carrier is a subsingleton.
-/

namespace IDT.QMClosure.TransparentSwapRootOrderWall

variable {P : Type*}

/-- A square root of swap commutes with swap, without any order assumption. -/
theorem operation_commutes_swap (F : P × P → P × P)
    (square : ∀ p, F (F p) = p.swap) (p : P × P) :
    F p.swap = (F p).swap := by
  calc
    F p.swap = F (F (F p)) := congrArg F (square p).symm
    _ = (F p).swap := square (F p)

/-- Monotonicity, square-swap and a fixed diagonal eliminate strict comparability
in a preorder. Antisymmetry is not assumed. -/
theorem reverse_le [Preorder P] (F : P × P → P × P)
    (monotone : Monotone F) (square : ∀ p, F (F p) = p.swap)
    (diagonal : ∀ a, F (a, a) = (a, a)) {a b : P} (hab : a ≤ b) : b ≤ a := by
  let u := (F (a, b)).1
  let v := (F (a, b)).2
  have hlow : (a, a) ≤ F (a, b) := by
    simpa only [diagonal a] using monotone (show (a, a) ≤ (a, b) from ⟨le_rfl, hab⟩)
  have hupp : F (a, b) ≤ (b, b) := by
    simpa only [diagonal b] using monotone (show (a, b) ≤ (b, b) from ⟨hab, le_rfl⟩)
  have hau : a ≤ u := hlow.1
  have hub : u ≤ b := hupp.1
  have hvb : v ≤ b := hupp.2
  have common_lower : ∀ w, w ≤ u → w ≤ v → w ≤ a := by
    intro w hwu hwv
    have h := monotone (show (w, w) ≤ F (a, b) from ⟨hwu, hwv⟩)
    rw [diagonal w, square (a, b)] at h
    exact h.2
  let r := F (a, u)
  have hr_uv : r ≤ F (a, b) :=
    monotone (show (a, u) ≤ (a, b) from ⟨le_rfl, hub⟩)
  have hr_uu : r ≤ (u, u) := by
    simpa only [diagonal u] using
      monotone (show (a, u) ≤ (u, u) from ⟨hau, le_rfl⟩)
  have hr₂a : r.2 ≤ a := common_lower r.2 hr_uu.2 hr_uv.2
  have hr_ua : r ≤ (u, a) := ⟨hr_uv.1, hr₂a⟩
  have hreturn : (u, a) ≤ r.swap := by
    have h := monotone hr_ua
    change F (F (a, u)) ≤ F ((a, u).swap) at h
    rw [square (a, u), operation_commutes_swap F square (a, u)] at h
    exact h
  have hua : u ≤ a := le_trans hreturn.1 hr₂a
  have hcontract : F (a, b) ≤ (a, b) := ⟨hua, hvb⟩
  have hreturn_ab : (b, a) ≤ F (a, b) := by
    simpa only [square (a, b)] using monotone hcontract
  exact le_trans hreturn_ab.1 hua

/-- A partially ordered carrier may retain incomparable distinct elements. -/
theorem eq_of_le [PartialOrder P] (F : P × P → P × P)
    (monotone : Monotone F) (square : ∀ p, F (F p) = p.swap)
    (diagonal : ∀ a, F (a, a) = (a, a)) {a b : P} (hab : a ≤ b) : a = b :=
  le_antisymm hab (reverse_le F monotone square diagonal hab)

end IDT.QMClosure.TransparentSwapRootOrderWall
