/-
Authors: OpenAI Codex, delegated agent /root/cyclic_four_congruence_draft
Lean kernel-checked mathematical source.
Parent-approved design: /tmp/idt-initial-normal-form/v1/CONTRACTS.md.
This module gives algebraic consequences of the exact normal form. Its two
quotient classifications introduce no physical choice of a quotient.
-/
import Proofs.QMClosure.TransparentFourthInitialNormalForm

namespace IDT.QMClosure.TransparentFourthNormalFormConsequences

noncomputable section

open TransparentFourthInitialHistoryPresentation
open TransparentFourthInitialNormalForm

private theorem raw_e : rawSemantics e = (0, 1) := normalForm_e

private theorem gaussian_coordinate_mem (p : P) : (rawSemantics p).1 ∈ gaussianDyadic := by
  rcases raw_mem_normalSemiring p with hzero | ⟨hg, hd, hpos⟩
  · rw [hzero.1]
    exact gaussianDyadic.zero_mem
  · exact hg

private theorem dyadic_coordinate_mem (p : P) : (rawSemantics p).2 ∈ realDyadic := by
  rcases raw_mem_normalSemiring p with hzero | ⟨hg, hd, hpos⟩
  · rw [hzero.2]
    exact realDyadic.zero_mem
  · exact hd

theorem second_coordinate_nonnegative (p : P) : 0 ≤ (rawSemantics p).2 := by
  rcases raw_mem_normalSemiring p with hzero | ⟨hg, hd, hpos⟩
  · simpa only [hzero.2] using (le_refl (0 : ℝ))
  · exact hpos.le

theorem second_coordinate_zero_iff (p : P) : (rawSemantics p).2 = 0 ↔ p = 0 := by
  constructor
  · intro hz
    rcases raw_mem_normalSemiring p with hzero | ⟨hg, hd, hpos⟩
    · apply rawSemantics_injective
      simpa using Prod.ext hzero.1 hzero.2
    · exact (ne_of_gt hpos hz).elim
  · rintro rfl
    simp

theorem additive_left_cancel_iff (p x y : P) : p + x = p + y ↔ x = y := by
  constructor
  · intro h
    have hc := congrArg rawSemantics h
    rw [map_add, map_add] at hc
    exact rawSemantics_injective (add_left_cancel hc)
  · rintro rfl
    rfl

theorem e_ne_one : e ≠ (1 : P) := by
  intro h
  have hc := congrArg (fun p => (rawSemantics p).1) h
  simp [raw_e] at hc

/-- The three idempotents are zero, the vertical sector element, and one. -/
theorem idempotents (p : P) : p * p = p ↔ p = 0 ∨ p = e ∨ p = 1 := by
  classical
  constructor
  · intro hp
    by_cases hz : p = 0
    · exact Or.inl hz
    have hc := congrArg rawSemantics hp
    rw [map_mul] at hc
    have hcomplex := congrArg Prod.fst hc
    have hreal := congrArg Prod.snd hc
    change (rawSemantics p).1 * (rawSemantics p).1 = (rawSemantics p).1 at hcomplex
    change (rawSemantics p).2 * (rawSemantics p).2 = (rawSemantics p).2 at hreal
    have hzm : (rawSemantics p).1 * ((rawSemantics p).1 - 1) = 0 := by
      linear_combination hcomplex
    have hqm : (rawSemantics p).2 * ((rawSemantics p).2 - 1) = 0 := by
      linear_combination hreal
    have hq : (rawSemantics p).2 = 1 := by
      rcases mul_eq_zero.mp hqm with hq0 | hq1
      · exact (hz ((second_coordinate_zero_iff p).mp hq0)).elim
      · exact sub_eq_zero.mp hq1
    rcases mul_eq_zero.mp hzm with h0 | h1
    · right
      left
      apply rawSemantics_injective
      rw [raw_e]
      exact Prod.ext h0 hq
    · right
      right
      apply rawSemantics_injective
      simpa using Prod.ext (sub_eq_zero.mp h1) hq
  · rintro (rfl | rfl | rfl)
    · simp
    · exact e_idempotent
    · simp

theorem no_sector_complement : ¬ ∃ f : P, e + f = 1 := by
  rintro ⟨f, hf⟩
  have hc := congrArg rawSemantics hf
  rw [map_add, raw_e, map_one] at hc
  have hs := congrArg Prod.snd hc
  have hz : (rawSemantics f).2 = 0 := by
    change 1 + (rawSemantics f).2 = 1 at hs
    linarith
  have hf0 := (second_coordinate_zero_iff f).mp hz
  apply e_ne_one
  simpa [hf0] using hf

/-- An explicit failure of multiplicative cancellation. -/
theorem multiplicative_cancellation_counterexample :
    e * 1 = e * e ∧ (1 : P) ≠ e := by
  exact ⟨by rw [mul_one, e_idempotent], Ne.symm e_ne_one⟩

/-- The nonnegative part of the real dyadic ring. -/
def positiveDyadic : Subsemiring ℝ where
  carrier := {q | q ∈ realDyadic ∧ 0 ≤ q}
  zero_mem' := ⟨realDyadic.zero_mem, le_refl 0⟩
  one_mem' := ⟨realDyadic.one_mem, zero_le_one⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨realDyadic.add_mem hx.1 hy.1, add_nonneg hx.2 hy.2⟩
  mul_mem' := by
    intro x y hx hy
    exact ⟨realDyadic.mul_mem hx.1 hy.1, mul_nonneg hx.2 hy.2⟩

def gaussianProjection : P →+* gaussianDyadic :=
  ((RingHom.fst ℂ ℝ).comp rawSemantics).codRestrict
    gaussianDyadic gaussian_coordinate_mem

def dyadicProjection : P →+* positiveDyadic :=
  ((RingHom.snd ℂ ℝ).comp rawSemantics).codRestrict positiveDyadic
    (fun p => ⟨dyadic_coordinate_mem p, second_coordinate_nonnegative p⟩)

@[simp] theorem gaussianProjection_val (p : P) :
    (gaussianProjection p).val = (rawSemantics p).1 := rfl

@[simp] theorem dyadicProjection_val (p : P) :
    (dyadicProjection p).val = (rawSemantics p).2 := rfl

/-- Lift a pair already satisfying the established normal-form carrier. -/
def liftPair (z : ℂ) (q : ℝ) (h : (z, q) ∈ normalSemiring) : P :=
  normalFormEquiv.symm ⟨(z, q), h⟩

@[simp] theorem raw_liftPair (z : ℂ) (q : ℝ) (h : (z, q) ∈ normalSemiring) :
    rawSemantics (liftPair z q h) = (z, q) := by
  exact congrArg Subtype.val (normalFormEquiv.apply_symm_apply ⟨(z, q), h⟩)

def vertical (q : ℝ) (hq : q ∈ realDyadic) (hpos : 0 < q) : P :=
  liftPair 0 q (Or.inr ⟨gaussianDyadic.zero_mem, hq, hpos⟩)

@[simp] theorem raw_vertical (q : ℝ) (hq : q ∈ realDyadic) (hpos : 0 < q) :
    rawSemantics (vertical q hq hpos) = (0, q) := raw_liftPair _ _ _

theorem gaussianProjection_surjective : Function.Surjective gaussianProjection := by
  intro z
  refine ⟨liftPair z.val 1 (Or.inr ⟨z.property, realDyadic.one_mem, zero_lt_one⟩), ?_⟩
  apply Subtype.ext
  simp

theorem dyadicProjection_surjective : Function.Surjective dyadicProjection := by
  classical
  intro q
  by_cases hq0 : q.val = 0
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    simpa using hq0.symm
  · have hpos : 0 < q.val := lt_of_le_of_ne q.property.2 (Ne.symm hq0)
    refine ⟨vertical q.val q.property.1 hpos, ?_⟩
    apply Subtype.ext
    simp

private theorem vertical_killed (c : RingCon P) (he : c e 0)
    (q : ℝ) (hq : q ∈ realDyadic) (hpos : 0 < q) :
    c (vertical q hq hpos) 0 := by
  have hfix : e * vertical q hq hpos = vertical q hq hpos := by
    apply rawSemantics_injective
    rw [map_mul, raw_e, raw_vertical]
    ext <;> simp
  have hc := c.mul he (c.refl (vertical q hq hpos))
  simpa only [hfix, zero_mul] using hc

private theorem gaussian_fiber_related_of_lt (c : RingCon P) (he : c e 0)
    (p q : P) (hfirst : (rawSemantics p).1 = (rawSemantics q).1)
    (hsecond : (rawSemantics p).2 < (rawSemantics q).2) : c p q := by
  let delta := (rawSemantics q).2 - (rawSemantics p).2
  have hd : delta ∈ realDyadic :=
    realDyadic.sub_mem (dyadic_coordinate_mem q) (dyadic_coordinate_mem p)
  have hpos : 0 < delta := sub_pos.mpr hsecond
  have hq : q = p + vertical delta hd hpos := by
    apply rawSemantics_injective
    rw [map_add, raw_vertical]
    apply Prod.ext
    · simpa using hfirst.symm
    · dsimp [delta]
      ring
  rw [hq]
  simpa using c.add (c.refl p) (c.symm (vertical_killed c he delta hd hpos))

/-- The Gaussian kernel is the least semiring congruence identifying e with
zero. This interface is independent of any named destructive quotient. -/
theorem gaussian_kernel_le_iff (c : RingCon P) :
    RingCon.ker gaussianProjection ≤ c ↔ c e 0 := by
  classical
  constructor
  · intro h
    apply h
    change gaussianProjection e = gaussianProjection 0
    apply Subtype.ext
    simp [raw_e]
  · intro he p q hpq
    have hfirst : (rawSemantics p).1 = (rawSemantics q).1 :=
      congrArg Subtype.val hpq
    by_cases hsecond : (rawSemantics p).2 = (rawSemantics q).2
    · have hp : p = q := rawSemantics_injective (Prod.ext hfirst hsecond)
      simpa [hp] using c.refl q
    · rcases lt_or_gt_of_ne hsecond with hlt | hgt
      · exact gaussian_fiber_related_of_lt c he p q hfirst hlt
      · exact c.symm (gaussian_fiber_related_of_lt c he q p hfirst.symm hgt)

def gaussianKernelQuotientEquiv :
    (RingCon.ker gaussianProjection).Quotient ≃+* gaussianDyadic :=
  RingCon.quotientKerEquivOfSurjective gaussianProjection gaussianProjection_surjective

/-- The unit-sector quotient adds exactly one additional equation. -/
inductive ClassicalRelation : P → P → Prop
  | sector : ClassicalRelation e 1

def classicalCon : RingCon P := ringConGen ClassicalRelation

theorem classicalCon_e_one : classicalCon e 1 :=
  RingConGen.Rel.of e 1 ClassicalRelation.sector

theorem classicalCon_le_kernel : classicalCon ≤ RingCon.ker dyadicProjection := by
  apply RingCon.ringConGen_le
  intro p q h
  cases h
  change dyadicProjection e = dyadicProjection 1
  apply Subtype.ext
  simp [raw_e]

theorem classical_kernel_exact : classicalCon = RingCon.ker dyadicProjection := by
  apply le_antisymm classicalCon_le_kernel
  intro p q hpq
  have hsecond : (rawSemantics p).2 = (rawSemantics q).2 := by
    change dyadicProjection p = dyadicProjection q at hpq
    exact congrArg (fun x : positiveDyadic => x.val) hpq
  have hemul : e * p = e * q := by
    apply rawSemantics_injective
    rw [map_mul, map_mul, raw_e]
    apply Prod.ext
    · simp
    · simpa using hsecond
  have hp : classicalCon (e * p) p := by
    simpa using classicalCon.mul classicalCon_e_one (classicalCon.refl p)
  have hq : classicalCon (e * q) q := by
    simpa using classicalCon.mul classicalCon_e_one (classicalCon.refl q)
  apply classicalCon.trans (classicalCon.symm hp)
  rw [hemul]
  exact hq

theorem classical_fibers_iff (p q : P) :
    classicalCon p q ↔ (rawSemantics p).2 = (rawSemantics q).2 := by
  rw [classical_kernel_exact, RingCon.ker_apply]
  constructor
  · intro h
    exact congrArg (fun x : positiveDyadic => x.val) h
  · intro h
    exact Subtype.ext h

def classicalDyadicEquiv : classicalCon.Quotient ≃+* positiveDyadic :=
  (RingCon.congr classical_kernel_exact).trans
    (RingCon.quotientKerEquivOfSurjective dyadicProjection dyadicProjection_surjective)

end
end IDT.QMClosure.TransparentFourthNormalFormConsequences
