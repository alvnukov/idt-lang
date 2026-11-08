import Proofs.QMClosure.RationalFiniteDistribution
import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite conserved signatures and strictly positive covariant noise

These are finite-carrier obstructions under exact square-swap and covariance
laws. They supply no physical detector origin, raw-response identification, or
quantum reconstruction.
-/

namespace IDT.QMClosure.FiniteCovariantNoiseWall

noncomputable section

open Finset

variable {V : Type*}

/-- A square root of exchange is injective. -/
theorem square_swap_injective (F : V × V → V × V)
    (hsquare : ∀ p, F (F p) = p.swap) : Function.Injective F := by
  intro p q hpq
  have h := congrArg F hpq
  rw [hsquare, hsquare] at h
  exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)

/-- A square root of exchange is surjective, with its cube as inverse. -/
theorem square_swap_surjective (F : V × V → V × V)
    (hsquare : ∀ p, F (F p) = p.swap) : Function.Surjective F := by
  intro p
  refine ⟨F (F (F p)), ?_⟩
  rw [hsquare, hsquare]
  rfl

/-- A mixed input cannot be routed to itself or its exchange. -/
theorem mixed_output_not_routing (F : V × V → V × V)
    (hsquare : ∀ p, F (F p) = p.swap) {a b : V} (hab : a ≠ b) :
    F (a, b) ≠ (a, b) ∧ F (a, b) ≠ (b, a) := by
  have hfix : F (a, b) ≠ (a, b) := by
    intro hh
    have h := hsquare (a, b)
    rw [hh, hh] at h
    exact hab (congrArg Prod.fst h)
  refine ⟨hfix, ?_⟩
  intro hh
  have heq : F (a, b) = F (F (a, b)) := by rw [hsquare]; exact hh
  exact hfix ((square_swap_injective F hsquare heq).symm)

/-- A finite ordered additive signature cannot be both injective and conserved. -/
theorem no_injective_ordered_conserved [Finite V] [Nontrivial V]
    {A : Type*} [AddCommMonoid A] [LinearOrder A] [IsOrderedCancelAddMonoid A]
    (F : V × V → V × V) (hsquare : ∀ p, F (F p) = p.swap)
    (c : V → A) (hconserve : ∀ x y, c (F (x, y)).1 + c (F (x, y)).2 = c x + c y) :
    ¬ Function.Injective c := by
  classical
  letI := Fintype.ofFinite V
  intro hc
  obtain ⟨a, _, ha⟩ := exists_min_image univ c univ_nonempty
  have hrest : (univ.erase a).Nonempty := by
    obtain ⟨b, hb⟩ := exists_ne a
    exact ⟨b, by simp [hb]⟩
  obtain ⟨b, hb, hmin⟩ := exists_min_image (univ.erase a) c hrest
  have hba : b ≠ a := (mem_erase.mp hb).1
  have hab : a ≠ b := Ne.symm hba
  have hcab : c a < c b := lt_of_le_of_ne (ha b (mem_univ b)) (fun h => hab (hc h))
  have hsum := hconserve a b
  have hroute : F (a, b) = (a, b) ∨ F (a, b) = (b, a) := by
    by_cases hu : (F (a, b)).1 = a
    · left
      have hv : (F (a, b)).2 = b := hc (add_left_cancel (hu ▸ hsum))
      exact Prod.ext hu hv
    by_cases hv : (F (a, b)).2 = a
    · right
      have hu' : (F (a, b)).1 = b := hc (add_right_cancel (by simpa only [hv, add_comm] using hsum))
      exact Prod.ext hu' hv
    have hbu : c b ≤ c (F (a, b)).1 := hmin _ (by simp [hu])
    have hbv : c b ≤ c (F (a, b)).2 := hmin _ (by simp [hv])
    have hlt : c a + c b < c (F (a, b)).1 + c (F (a, b)).2 :=
      lt_of_lt_of_le (show c a + c b < c b + c b from add_lt_add_left hcab _) (add_le_add hbu hbv)
    exact False.elim ((ne_of_lt hlt) hsum.symm)
  exact hroute.elim (mixed_output_not_routing F hsquare hab).1
    (mixed_output_not_routing F hsquare hab).2

/-- Every arbitrarily indexed conserved real family has a common collision. -/
theorem conserved_family_has_twins [Finite V] [Nontrivial V]
    {I : Type*} (h : I → V → ℝ) (F : V × V → V × V)
    (hsquare : ∀ p, F (F p) = p.swap)
    (hconserve : ∀ i x y, h i (F (x, y)).1 + h i (F (x, y)).2 = h i x + h i y) :
    ∃ x y, x ≠ y ∧ ∀ i, h i x = h i y := by
  classical
  letI := Fintype.ofFinite V
  by_contra hnot
  push Not at hnot
  let P := {p : V × V // p.1 ≠ p.2}
  have hsep : ∀ p : P, ∃ i, h i p.val.1 ≠ h i p.val.2 :=
    fun p => hnot p.val.1 p.val.2 p.property
  choose index hindex using hsep
  let e := Fintype.equivFin P
  let c : V → Lex (Fin (Fintype.card P) → ℝ) :=
    fun x => toLex (fun j => h (index (e.symm j)) x)
  have hinj : Function.Injective c := by
    intro x y hxy
    by_contra hne
    let p : P := ⟨(x, y), hne⟩
    have heq := congrFun (congrArg ofLex hxy) (e p)
    exact hindex p (by simpa [c, p] using heq)
  have hc : ∀ x y, c (F (x, y)).1 + c (F (x, y)).2 = c x + c y := by
    intro x y
    apply ofLex.injective
    funext j
    exact hconserve (index (e.symm j)) x y
  exact no_injective_ordered_conserved (A := Lex (Fin (Fintype.card P) → ℝ)) F hsquare c hc hinj

/-- Strictly positive conserved product signatures also have common twins. -/
theorem positive_product_family_has_twins [Finite V] [Nontrivial V]
    {I : Type*} (w : I → V → ℝ) (hw : ∀ i x, 0 < w i x)
    (F : V × V → V × V) (hsquare : ∀ p, F (F p) = p.swap)
    (hconserve : ∀ i x y, w i (F (x, y)).1 * w i (F (x, y)).2 = w i x * w i y) :
    ∃ x y, x ≠ y ∧ ∀ i, w i x = w i y := by
  obtain ⟨x, y, hxy, hlogs⟩ := conserved_family_has_twins (fun i x => Real.log (w i x)) F hsquare
    (fun i x y => by
      rw [← Real.log_mul (ne_of_gt (hw i _)) (ne_of_gt (hw i _)),
        hconserve, Real.log_mul (ne_of_gt (hw i x)) (ne_of_gt (hw i y))])
  exact ⟨x, y, hxy, fun i => Real.log_injOn_pos (hw i x) (hw i y) (hlogs i)⟩

/-- Normalization makes full product covariance descend to row equivalence. -/
theorem covariance_respects_equal_rows [Fintype V]
    (K : V → V → ℝ) (hnorm : ∀ x, ∑ a, K x a = 1)
    (F : V × V → V × V) (hsurj : Function.Surjective F)
    (hcov : ∀ x y a b, K (F (x, y)).1 (F (a, b)).1 * K (F (x, y)).2 (F (a, b)).2 =
      K x a * K y b)
    {x x' y y' : V} (hx : K x = K x') (hy : K y = K y') :
    K (F (x, y)).1 = K (F (x', y')).1 ∧ K (F (x, y)).2 = K (F (x', y')).2 := by
  have hp : ∀ a b, K (F (x, y)).1 a * K (F (x, y)).2 b =
      K (F (x', y')).1 a * K (F (x', y')).2 b := by
    intro a b
    obtain ⟨⟨u, v⟩, huv⟩ := hsurj (a, b)
    have hh := (hcov x y u v).trans ((congrArg₂ (· * ·) (congrFun hx u) (congrFun hy v)).trans (hcov x' y' u v).symm)
    simpa only [huv] using hh
  constructor
  · funext a
    have hh := congrArg (fun f : V → ℝ => ∑ b, f b) (funext (hp a))
    simpa only [← mul_sum, hnorm, mul_one] using hh
  · funext b
    have hh := congrArg (fun f : V → ℝ => ∑ a, f a) (funext (fun a => hp a b))
    simpa only [← sum_mul, hnorm, one_mul] using hh

private def rowSetoid (K : V → V → ℝ) : Setoid V := Setoid.ker K

private def rowValue (K : V → V → ℝ) : Quotient (rowSetoid K) → V → ℝ :=
  Quotient.lift K (fun _ _ h => h)

private def rowOperation (K : V → V → ℝ) (F : V × V → V × V)
    (hrespect : ∀ {x x' y y'}, K x = K x' → K y = K y' →
      K (F (x, y)).1 = K (F (x', y')).1 ∧ K (F (x, y)).2 = K (F (x', y')).2) :
    Quotient (rowSetoid K) × Quotient (rowSetoid K) →
      Quotient (rowSetoid K) × Quotient (rowSetoid K) :=
  fun p => Quotient.liftOn₂ p.1 p.2
    (fun x y => (Quotient.mk (rowSetoid K) (F (x, y)).1,
      Quotient.mk (rowSetoid K) (F (x, y)).2))
    (fun _ _ _ _ hx hy => Prod.ext (Quotient.sound (hrespect hx hy).1)
      (Quotient.sound (hrespect hx hy).2))

/-- On a finite carrier, exact full covariance forces every positive normalized
row to coincide. The covariance is for every input and output pair. -/
theorem strictly_positive_covariant_kernel_constant_rows [Finite V]
    (K : V → V → ℝ) (hpos : ∀ x a, 0 < K x a)
    [Fintype V] (hnorm : ∀ x, ∑ a, K x a = 1)
    (F : V × V → V × V) (hsquare : ∀ p, F (F p) = p.swap)
    (hdiag : ∀ x, F (x, x) = (x, x))
    (hcov : ∀ x y a b, K (F (x, y)).1 (F (a, b)).1 * K (F (x, y)).2 (F (a, b)).2 =
      K x a * K y b) : ∀ x y a, K x a = K y a := by
  let Q := Quotient (rowSetoid K)
  have hrespect : ∀ {x x' y y'}, K x = K x' → K y = K y' →
      K (F (x, y)).1 = K (F (x', y')).1 ∧ K (F (x, y)).2 = K (F (x', y')).2 :=
    fun hx hy => covariance_respects_equal_rows K hnorm F (square_swap_surjective F hsquare) hcov hx hy
  let G := rowOperation K F hrespect
  have hGsquare : ∀ p, G (G p) = p.swap := by
    rintro ⟨x, y⟩
    induction x using Quotient.inductionOn with | _ x =>
      induction y using Quotient.inductionOn with | _ y =>
        change (Quotient.mk _ (F (F (x, y))).1, Quotient.mk _ (F (F (x, y))).2) = _
        rw [hsquare]
        rfl
  have hprod : ∀ a x y, rowValue K (G (x, y)).1 a * rowValue K (G (x, y)).2 a =
      rowValue K x a * rowValue K y a := by
    intro a x y
    induction x using Quotient.inductionOn with | _ x =>
      induction y using Quotient.inductionOn with | _ y =>
        have hh := hcov x y a a
        simpa only [hdiag] using hh
  have hpositive : ∀ a x, 0 < rowValue K x a := by
    intro a x
    induction x using Quotient.inductionOn with | _ x => exact hpos x a
  have hsub : Subsingleton Q := by
    by_contra hh
    letI : Nontrivial Q := not_subsingleton_iff_nontrivial.mp hh
    obtain ⟨x, y, hxy, heq⟩ := positive_product_family_has_twins
      (fun a x => rowValue K x a) hpositive G hGsquare hprod
    apply hxy
    induction x using Quotient.inductionOn with | _ x =>
      induction y using Quotient.inductionOn with | _ y =>
        exact Quotient.sound (funext heq)
  intro x y a
  have heq : (Quotient.mk (rowSetoid K) x : Q) = Quotient.mk (rowSetoid K) y := hsub.elim _ _
  exact congrFun (Quotient.exact heq) a

/-- The deterministic identity kernel has zeros whenever the carrier is
nontrivial. It records why strict positivity matters. -/
def identityKernel (x a : V) : ℝ := by
  classical
  exact if a = x then 1 else 0

theorem identity_kernel_normalized [Fintype V] (x : V) :
    ∑ a, identityKernel x a = 1 := by
  classical
  simp [identityKernel]

theorem identity_kernel_injective : Function.Injective (identityKernel (V := V)) := by
  classical
  intro x y hxy
  by_contra hne
  have hh := congrFun hxy x
  simp [identityKernel, hne] at hh

/-- Every injective deterministic gate covaries with identity noise. -/
theorem identity_kernel_covariant (F : V × V → V × V) (hinj : Function.Injective F)
    (x y a b : V) :
    identityKernel (F (x, y)).1 (F (a, b)).1 *
      identityKernel (F (x, y)).2 (F (a, b)).2 = identityKernel x a * identityKernel y b := by
  classical
  have hprod : ∀ u v c d : V, identityKernel u c * identityKernel v d =
      if (c, d) = (u, v) then 1 else 0 := by
    intro u v c d
    by_cases hc : c = u <;> by_cases hd : d = v <;>
      simp [identityKernel, hc, hd]
  rw [hprod, hprod]
  simp only [Prod.eta, hinj.eq_iff]

theorem identity_kernel_has_zero [Nontrivial V] : ∃ x a : V, identityKernel x a = 0 := by
  classical
  obtain ⟨x, a, hxa⟩ := exists_pair_ne V
  exact ⟨x, a, by simp [identityKernel, hxa.symm]⟩

end
end IDT.QMClosure.FiniteCovariantNoiseWall
