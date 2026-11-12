import Proofs.QMClosure.SurjectiveMixingQuadraticReadout
import Proofs.QMClosure.FiniteRejoinCarrierChoiceControls
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Data.Multiset.Filter

/-!
# Controls for surjective-mixing reconstruction

The complex control instantiates the new transparent gate with the accepted
unequal-gain branches whose positive powers never rejoin. The multiset control
has both branch coverages, surjective symmetric mixing and full nonnegative
conservation. Transparency fails and its count readout has linear scaling.

The controls use concrete algebraic carriers and imply no physical-origin,
scalar-field uniqueness, or full-QM conclusion.
-/

noncomputable section

namespace IDT.QMClosure.SurjectiveMixingQuadraticReadoutControls

namespace WithoutFiniteRejoin

open FiniteRejoinCarrierChoiceControls
open FiniteRejoinQuadraticReadoutControls

/-- The accepted unequal-gain complex branches satisfy the new gate. -/
def gate : TransparentSurjectiveMixingGroup.Gate ℂ where
  a := NoFiniteRejoin.A
  b := NoFiniteRejoin.B
  transparent := NoFiniteRejoin.transparent
  ontoA := by
    intro z
    refine ⟨CanonicalComplex.scalarEnd NoFiniteRejoin.alpha⁻¹ z, ?_⟩
    exact congrArg (fun f : AddMonoid.End ℂ => f z) NoFiniteRejoin.branch_invertible.1.2
  ontoB := by
    intro z
    refine ⟨CanonicalComplex.scalarEnd NoFiniteRejoin.beta⁻¹ z, ?_⟩
    exact congrArg (fun f : AddMonoid.End ℂ => f z) NoFiniteRejoin.branch_invertible.2.2
  axis := by
    intro p
    obtain ⟨⟨x, y⟩, h⟩ := NoFiniteRejoin.onto (p, 0)
    exact ⟨x, y, congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- The new theorem reconstructs this accepted no-rejoin control. -/
theorem reconstructed :
    ∃ C : ℂ →+ ℂ →+ ℝ,
      (∀ x y, C x y = C y x) ∧ (∀ x, Complex.normSq x = C x x) :=
  SurjectiveMixingQuadraticReadout.reconstruct gate Complex.normSq
    Complex.normSq_zero Complex.normSq_nonneg NoFiniteRejoin.norm_conservation

theorem positive_state : 0 < Complex.normSq (1 : ℂ) := by
  norm_num

/-- The two branches have unequal gains at the normalized state. -/
theorem unequal_gains :
    Complex.normSq (gate.a 1) = 4 / 5 ∧
    Complex.normSq (gate.b 1) = 1 / 5 ∧
    Complex.normSq (gate.a 1) ≠ Complex.normSq (gate.b 1) := by
  obtain ⟨ha, hb⟩ := NoFiniteRejoin.branch_gains 1
  have ha' : Complex.normSq (gate.a 1) = 4 / 5 := by
    simpa only [gate, Complex.normSq_one, mul_one] using ha
  have hb' : Complex.normSq (gate.b 1) = 1 / 5 := by
    simpa only [gate, Complex.normSq_one, mul_one] using hb
  exact ⟨ha', hb', by rw [ha', hb']; norm_num⟩

theorem no_positive_rejoin :
    ∀ n : ℕ, 0 < n → gate.a ^ n ≠ gate.b ^ n :=
  NoFiniteRejoin.no_finite_rejoin

/-- A single control supplies reconstruction, positive readout, unequal branch
responses and failure of every positive finite-rejoin equation. -/
theorem control_contract :
    (∃ C : ℂ →+ ℂ →+ ℝ,
      (∀ x y, C x y = C y x) ∧ (∀ x, Complex.normSq x = C x x)) ∧
    0 < Complex.normSq (1 : ℂ) ∧
    Complex.normSq (gate.a 1) = 4 / 5 ∧
    Complex.normSq (gate.b 1) = 1 / 5 ∧
    (∀ n : ℕ, 0 < n → gate.a ^ n ≠ gate.b ^ n) :=
  ⟨reconstructed, positive_state, unequal_gains.1, unequal_gains.2.1,
    no_positive_rejoin⟩

end WithoutFiniteRejoin

namespace WithoutTransparency

abbrev Label := List Bool
abbrev V := Multiset Label

/-- The empty label is retained by the first branch. -/
def routeA : Label → Option Label
  | [] => some []
  | false :: w => some w
  | true :: _ => none

/-- A true-prefixed label is routed through the second branch. -/
def routeB : Label → Option Label
  | [] => none
  | false :: _ => none
  | true :: w => some w

def A : AddMonoid.End V where
  toFun := Multiset.filterMap routeA
  map_zero' := Multiset.filterMap_zero routeA
  map_add' := Multiset.filterMap_add routeA

@[simp] theorem A_apply (s : V) : A s = Multiset.filterMap routeA s := rfl

def B : AddMonoid.End V where
  toFun := Multiset.filterMap routeB
  map_zero' := Multiset.filterMap_zero routeB
  map_add' := Multiset.filterMap_add routeB

@[simp] theorem B_apply (s : V) : B s = Multiset.filterMap routeB s := rfl

def prefixFalse (s : V) : V := s.map (List.cons false)
def prefixTrue (s : V) : V := s.map (List.cons true)

@[simp] theorem A_prefixFalse (s : V) : A (prefixFalse s) = s := by
  induction s using Multiset.induction_on with
  | empty => simp [prefixFalse]
  | cons w s ih =>
      simpa [prefixFalse, routeA] using congrArg (Multiset.cons w) ih

@[simp] theorem B_prefixFalse (s : V) : B (prefixFalse s) = 0 := by
  induction s using Multiset.induction_on with
  | empty => simp [prefixFalse]
  | cons w s ih => simpa [prefixFalse, routeB] using ih

@[simp] theorem A_prefixTrue (s : V) : A (prefixTrue s) = 0 := by
  induction s using Multiset.induction_on with
  | empty => simp [prefixTrue]
  | cons w s ih => simpa [prefixTrue, routeA] using ih

@[simp] theorem B_prefixTrue (s : V) : B (prefixTrue s) = s := by
  induction s using Multiset.induction_on with
  | empty => simp [prefixTrue]
  | cons w s ih =>
      simpa [prefixTrue, routeB] using congrArg (Multiset.cons w) ih

theorem ontoA : Function.Surjective A := fun s => ⟨prefixFalse s, A_prefixFalse s⟩
theorem ontoB : Function.Surjective B := fun s => ⟨prefixTrue s, B_prefixTrue s⟩

/-- Every two-output target has an explicit preimage in the first input. -/
theorem mixer_onto :
    Function.Surjective (TransparentSurjectiveMixingGroup.twoPort A B) := by
  rintro ⟨p, q⟩
  refine ⟨(prefixFalse p + prefixTrue q, 0), ?_⟩
  simp only [TransparentSurjectiveMixingGroup.twoPort, map_add, map_zero,
    A_prefixFalse, A_prefixTrue, B_prefixFalse, B_prefixTrue, add_zero, zero_add]

theorem first_axis : TransparentSurjectiveMixingGroup.FirstAxisReachable A B := by
  intro p
  refine ⟨prefixFalse p, 0, ?_, ?_⟩ <;>
    simp only [map_zero, A_prefixFalse, B_prefixFalse, add_zero]

/-- Each input label contributes exactly once to the total routed count. -/
theorem card_split (s : V) : (A s).card + (B s).card = s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons w s ih =>
      cases w with
      | nil =>
          simp [routeA, routeB] at *
          omega
      | cons bit w =>
          cases bit <;> simp [routeA, routeB] at * <;> omega

def W (s : V) : ℝ := s.card

@[simp] theorem vacuum : W 0 = 0 := by simp [W]
theorem nonnegative (s : V) : 0 ≤ W s := by
  dsimp only [W]
  exact_mod_cast Nat.zero_le s.card

@[simp] theorem weight_add (s t : V) : W (s + t) = W s + W t := by
  simp [W, Multiset.card_add]

theorem weight_split (s : V) : W (A s) + W (B s) = W s := by
  dsimp only [W]
  exact_mod_cast card_split s

/-- Full conservation holds for every pair of original-carrier inputs. -/
theorem conservation (x y : V) :
    W (A x + B y) + W (B x + A y) = W x + W y := by
  rw [weight_add, weight_add]
  have hx := weight_split x
  have hy := weight_split y
  linarith

/-- A nonzero state carrying one empty label. -/
def e : V := ([] : Label) ::ₘ 0

theorem normalized : W e = 1 := by simp [W, e]
theorem positive_state : 0 < W e := by rw [normalized]; norm_num

/-- A singleton preparation routed into the second branch. -/
def p : V := ([true] : Label) ::ₘ 0

/-- The original preparation and its branch sum have equal readout, while the
second-branch context distinguishes their readouts. -/
theorem contextual_transparency_failure :
    W (A p + B p) = W p ∧
    W (B (A p + B p)) = 0 ∧ W (B p) = 1 ∧
    W (B (A p + B p)) ≠ W (B p) := by
  have hpA : A p = 0 := by
    change Multiset.filterMap routeA (([true] : Label) ::ₘ 0) = 0
    rw [Multiset.filterMap_cons_none (f := routeA) [true] 0 rfl,
      Multiset.filterMap_zero]
  have hpB : B p = e := by
    change Multiset.filterMap routeB (([true] : Label) ::ₘ 0) = ([] : Label) ::ₘ 0
    rw [Multiset.filterMap_cons_some routeB [true] 0 rfl, Multiset.filterMap_zero]
  have heB : B e = 0 := by
    change Multiset.filterMap routeB (([] : Label) ::ₘ 0) = 0
    rw [Multiset.filterMap_cons_none (f := routeB) [] 0 rfl,
      Multiset.filterMap_zero]
  simp only [hpA, hpB, zero_add, heB, vacuum, normalized]
  norm_num [p, W]

/-- Transparency changes the label on this singleton state. -/
theorem transparency_failure : A + B ≠ 1 := by
  intro h
  have hv := congrArg (fun f : AddMonoid.End V => f (([false] : Label) ::ₘ 0)) h
  change A (([false] : Label) ::ₘ 0) + B (([false] : Label) ::ₘ 0) =
    ([false] : Label) ::ₘ 0 at hv
  have hA : A (([false] : Label) ::ₘ 0) = e := by
    change Multiset.filterMap routeA (([false] : Label) ::ₘ 0) = ([] : Label) ::ₘ 0
    rw [Multiset.filterMap_cons_some routeA [false] 0 rfl, Multiset.filterMap_zero]
  have hB : B (([false] : Label) ::ₘ 0) = 0 := by
    change Multiset.filterMap routeB (([false] : Label) ::ₘ 0) = 0
    rw [Multiset.filterMap_cons_none (f := routeB) [false] 0 rfl,
      Multiset.filterMap_zero]
  rw [hA, hB, add_zero] at hv
  have hlabel : ([] : Label) = [false] :=
    (Multiset.cons_inj_left (0 : V)).mp hv
  cases hlabel

/-- The positive singleton cannot have an additive inverse in this carrier. -/
theorem no_inverse : ¬ ∃ t : V, e + t = 0 := by
  rintro ⟨t, ht⟩
  have hcard := congrArg Multiset.card ht
  simp [e] at hcard

/-- The readout doubles under duplication of this state. -/
theorem linear_double : W (e + e) = 2 := by
  rw [weight_add, normalized]
  norm_num

theorem quadratic_double_failure : W (e + e) ≠ 4 * W e := by
  rw [linear_double, normalized]
  norm_num

/-- No real biadditive pairing has this count readout as its diagonal. -/
theorem no_biadditive_diagonal :
    ¬ ∃ C : V →+ V →+ ℝ, ∀ x, W x = C x x := by
  rintro ⟨C, hC⟩
  have hdouble : C (e + e) (e + e) = 4 * C e e := by
    simp only [map_add, AddMonoidHom.add_apply]
    ring
  rw [← hC (e + e), ← hC e] at hdouble
  exact quadratic_double_failure hdouble

/-- Complete omission control on a non-group additive commutative monoid. -/
theorem control_contract :
    Function.Surjective A ∧ Function.Surjective B ∧
    Function.Surjective (TransparentSurjectiveMixingGroup.twoPort A B) ∧
    TransparentSurjectiveMixingGroup.FirstAxisReachable A B ∧
    W 0 = 0 ∧ (∀ x, 0 ≤ W x) ∧
    (∀ x y, W (A x + B y) + W (B x + A y) = W x + W y) ∧
    0 < W e ∧ A + B ≠ 1 ∧ (¬ ∃ t : V, e + t = 0) ∧
    W (e + e) = 2 ∧ W (e + e) ≠ 4 * W e ∧
    (¬ ∃ C : V →+ V →+ ℝ, ∀ x, W x = C x x) :=
  ⟨ontoA, ontoB, mixer_onto, first_axis, vacuum, nonnegative, conservation,
    positive_state, transparency_failure, no_inverse, linear_double,
    quadratic_double_failure, no_biadditive_diagonal⟩

end WithoutTransparency

end IDT.QMClosure.SurjectiveMixingQuadraticReadoutControls
