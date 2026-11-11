/-
Authors: OpenAI Codex, delegated agent /root/cyclic_four_congruence_draft

Lean kernel-checked mathematical source.
Parent-approved analytic design: /tmp/idt-initial-normal-form/v1/CONTRACTS.md.
This module concerns a positive cyclic monoid algebra and one generated
semiring congruence. It has no dependence on a history presentation.
-/
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section

set_option maxHeartbeats 800000

namespace CyclicFourPositiveCongruence

abbrev C4 := Multiplicative (ZMod 4)
abbrev A := MonoidAlgebra ℕ C4
abbrev Target := GaussianInt × ℤ

/-- The distinguished positive singleton generator. -/
def r : A := MonoidAlgebra.single (Multiplicative.ofAdd (1 : ZMod 4)) 1

theorem r_four : r ^ 4 = 1 := by
  have hg : (Multiplicative.ofAdd (1 : ZMod 4) : C4) ^ 4 = 1 := by decide
  simpa only [r, MonoidAlgebra.single_pow, one_pow, MonoidAlgebra.one_def]
    using congrArg (fun g : C4 => MonoidAlgebra.single g (1 : ℕ)) hg

/-- Assemble four natural coefficients. The index order is 0, 1, 2, 3. -/
def ofFour (n0 n1 n2 n3 : ℕ) : A :=
  MonoidAlgebra.single (Multiplicative.ofAdd (0 : ZMod 4)) n0 +
  MonoidAlgebra.single (Multiplicative.ofAdd (1 : ZMod 4)) n1 +
  MonoidAlgebra.single (Multiplicative.ofAdd (2 : ZMod 4)) n2 +
  MonoidAlgebra.single (Multiplicative.ofAdd (3 : ZMod 4)) n3

/-- The coefficient function reindexed by the four finite residues. -/
def coefficientVector (u : A) (j : Fin 4) : ℕ :=
  u (Multiplicative.ofAdd (ZMod.finEquiv 4 j))

theorem four_expansion (u : A) :
    ofFour (coefficientVector u 0) (coefficientVector u 1)
      (coefficientVector u 2) (coefficientVector u 3) = u := by
  let v : Fin 4 →₀ ℕ := u
  change (Finsupp.single (0 : Fin 4) (v 0) +
    Finsupp.single 1 (v 1) +
    Finsupp.single 2 (v 2) +
    Finsupp.single 3 (v 3) : Fin 4 →₀ ℕ) = v
  ext g
  fin_cases g <;> simp

theorem four_surjective (u : A) :
    ∃ n0 n1 n2 n3 : ℕ, u = ofFour n0 n1 n2 n3 :=
  ⟨coefficientVector u 0, coefficientVector u 1,
    coefficientVector u 2, coefficientVector u 3, (four_expansion u).symm⟩

theorem ofFour_add (n0 n1 n2 n3 m0 m1 m2 m3 : ℕ) :
    ofFour n0 n1 n2 n3 + ofFour m0 m1 m2 m3 =
      ofFour (n0 + m0) (n1 + m1) (n2 + m2) (n3 + m3) := by
  apply MonoidAlgebra.ext
  intro g
  change Fin 4 at g
  fin_cases g <;>
    norm_num [ofFour, MonoidAlgebra.single_apply, Multiplicative.ofAdd,
      add_assoc, add_comm, add_left_comm]

theorem ofFour_nsmul (k n0 n1 n2 n3 : ℕ) :
    k • ofFour n0 n1 n2 n3 =
      ofFour (k * n0) (k * n1) (k * n2) (k * n3) := by
  apply MonoidAlgebra.ext
  intro g
  change Fin 4 at g
  fin_cases g <;>
    norm_num [ofFour, MonoidAlgebra.single_apply, MonoidAlgebra.smul_apply,
      Multiplicative.ofAdd, nsmul_eq_mul]

def s : A := 1 + r
def U : A := 1 + r ^ 2
def V : A := r + r ^ 3

theorem U_four : U = ofFour 1 0 1 0 := by
  have h2 : (Multiplicative.ofAdd (1 : ZMod 4) : C4) ^ 2 =
      Multiplicative.ofAdd (2 : ZMod 4) := by decide
  simp only [U, ofFour, r, MonoidAlgebra.single_pow, h2, MonoidAlgebra.one_def, one_pow]
  change (Finsupp.single (0 : Fin 4) 1 + Finsupp.single 2 1 : Fin 4 →₀ ℕ) =
    Finsupp.single 0 1 + Finsupp.single 1 0 + Finsupp.single 2 1 + Finsupp.single 3 0
  simp

theorem V_four : V = ofFour 0 1 0 1 := by
  have h3 : (Multiplicative.ofAdd (1 : ZMod 4) : C4) ^ 3 =
      Multiplicative.ofAdd (3 : ZMod 4) := by decide
  simp only [V, ofFour, r, MonoidAlgebra.single_pow, h3, one_pow]
  change (Finsupp.single (1 : Fin 4) 1 + Finsupp.single 3 1 : Fin 4 →₀ ℕ) =
    Finsupp.single 0 0 + Finsupp.single 1 1 + Finsupp.single 2 0 + Finsupp.single 3 1
  simp

/-- Expansion uses only the semiring laws and the fourth-power equation. -/
theorem s_mul_U_eq_s_mul_V : s * U = s * V := by
  have h12 : r * r ^ 2 = r ^ 3 := (pow_succ' r 2).symm
  have h13 : r * r ^ 3 = 1 := by
    rw [← pow_succ', r_four]
  change (1 + r) * (1 + r ^ 2) = (1 + r) * (r + r ^ 3)
  calc
    (1 + r) * (1 + r ^ 2) = (1 + r ^ 2) + (r + r ^ 3) := by
      rw [add_mul, one_mul, mul_add, mul_one, h12]
    _ = (r + r ^ 3) + (r ^ 2 + 1) := by ac_rfl
    _ = (1 + r) * (r + r ^ 3) := by
      rw [add_mul, one_mul, mul_add, ← pow_two, h13]

/-- The sole generating relation. -/
inductive GeneratingRelation : A → A → Prop
  | balance : GeneratingRelation U V

def congruence : RingCon A := ringConGen GeneratingRelation
abbrev B := congruence.Quotient

theorem congruence_U_V : congruence U V :=
  RingConGen.Rel.of U V GeneratingRelation.balance

/-- The four values of the cyclic monoid generator in the integer target. -/
def cyclicValue (g : C4) : Target :=
  let j := (Multiplicative.toAdd g).val
  (⟨if j = 0 then 1 else if j = 2 then -1 else 0,
    if j = 1 then 1 else if j = 3 then -1 else 0⟩, 1)

/-- A finite multiplication-table proof supplies the cyclic monoid map. -/
def cyclicValueHom : C4 →* Target where
  toFun := cyclicValue
  map_one' := by decide
  map_mul' x y := by
    change Fin 4 at x y
    fin_cases x <;> fin_cases y <;> decide

/-- Integer coordinate semantics, obtained from the monoid-algebra universal map. -/
noncomputable def phi : A →+* Target :=
  MonoidAlgebra.liftNCRingHom (Nat.castRingHom Target) cyclicValueHom
    (fun _ _ => mul_comm _ _)

@[simp] theorem phi_single (g : C4) (n : ℕ) :
    phi (MonoidAlgebra.single g n) = (n : Target) * cyclicValue g :=
  MonoidAlgebra.liftNCRingHom_single _ _ _ _ _

theorem phi_ofFour (n0 n1 n2 n3 : ℕ) :
    phi (ofFour n0 n1 n2 n3) =
      (⟨(n0 : ℤ) - n2, (n1 : ℤ) - n3⟩,
        (n0 : ℤ) + n1 + n2 + n3) := by
  have h0 : cyclicValue (Multiplicative.ofAdd (0 : ZMod 4)) = (⟨1, 0⟩, 1) := by decide
  have h1 : cyclicValue (Multiplicative.ofAdd (1 : ZMod 4)) = (⟨0, 1⟩, 1) := by decide
  have h2 : cyclicValue (Multiplicative.ofAdd (2 : ZMod 4)) = (⟨-1, 0⟩, 1) := by decide
  have h3 : cyclicValue (Multiplicative.ofAdd (3 : ZMod 4)) = (⟨0, -1⟩, 1) := by decide
  simp only [ofFour, map_add, phi_single, h0, h1, h2, h3]
  ext <;> simp <;> ring

theorem phi_r : phi r = (⟨0, 1⟩, 1) := by
  have h1 : cyclicValue (Multiplicative.ofAdd (1 : ZMod 4)) = (⟨0, 1⟩, 1) := by decide
  simpa only [r, phi_single, Nat.cast_one, one_mul] using h1

theorem phi_U_eq_phi_V : phi U = phi V := by
  rw [U_four, V_four, phi_ofFour, phi_ofFour]
  norm_num

theorem congruence_le_ker : congruence ≤ RingCon.ker phi := by
  apply RingCon.ringConGen_le
  intro x y h
  cases h
  exact phi_U_eq_phi_V

/-- Equal target coordinates with an ordered first coefficient have a shared
natural base. Only natural addition and natural scalar multiplication enter
this congruence derivation. -/
private theorem ordered_coefficients_related
    (n0 n1 n2 n3 m0 m1 m2 m3 : ℕ)
    (h0 : n0 ≤ m0)
    (hr : (n0 : ℤ) - n2 = (m0 : ℤ) - m2)
    (hi : (n1 : ℤ) - n3 = (m1 : ℤ) - m3)
    (hq : (n0 : ℤ) + n1 + n2 + n3 = (m0 : ℤ) + m1 + m2 + m3) :
    congruence (ofFour n0 n1 n2 n3) (ofFour m0 m1 m2 m3) := by
  let k := m0 - n0
  have h0k : m0 = n0 + k := by dsimp [k]; omega
  have h2k : m2 = n2 + k := by omega
  have h1k : n1 = m1 + k := by omega
  have h3k : n3 = m3 + k := by omega
  have hn : ofFour n0 n1 n2 n3 = ofFour n0 m1 n2 m3 + k • V := by
    rw [V_four, ofFour_nsmul, ofFour_add]
    simpa only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] using
      congrArg₂ (fun a b => ofFour n0 a n2 b) h1k h3k
  have hm : ofFour m0 m1 m2 m3 = ofFour n0 m1 n2 m3 + k • U := by
    rw [U_four, ofFour_nsmul, ofFour_add]
    simpa only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] using
      congrArg₂ (fun a b => ofFour a m1 b m3) h0k h2k
  rw [hn, hm]
  exact congruence.add (congruence.refl _)
    (congruence.nsmul k (congruence.symm congruence_U_V))

theorem coefficients_related_of_coordinates
    (n0 n1 n2 n3 m0 m1 m2 m3 : ℕ)
    (hr : (n0 : ℤ) - n2 = (m0 : ℤ) - m2)
    (hi : (n1 : ℤ) - n3 = (m1 : ℤ) - m3)
    (hq : (n0 : ℤ) + n1 + n2 + n3 = (m0 : ℤ) + m1 + m2 + m3) :
    congruence (ofFour n0 n1 n2 n3) (ofFour m0 m1 m2 m3) := by
  by_cases h0 : n0 ≤ m0
  · exact ordered_coefficients_related n0 n1 n2 n3 m0 m1 m2 m3 h0 hr hi hq
  · have hm0 : m0 ≤ n0 := by omega
    exact congruence.symm
      (ordered_coefficients_related m0 m1 m2 m3 n0 n1 n2 n3 hm0
        hr.symm hi.symm hq.symm)

/-- Exact kernel of the generated positive congruence. -/
theorem phi_eq_iff (u v : A) : phi u = phi v ↔ congruence u v := by
  constructor
  · intro h
    obtain ⟨n0, n1, n2, n3, rfl⟩ := four_surjective u
    obtain ⟨m0, m1, m2, m3, rfl⟩ := four_surjective v
    rw [phi_ofFour, phi_ofFour] at h
    have hr := congrArg (fun z : Target => z.1.re) h
    have hi := congrArg (fun z : Target => z.1.im) h
    have hq := congrArg (fun z : Target => z.2) h
    exact coefficients_related_of_coordinates n0 n1 n2 n3 m0 m1 m2 m3 hr hi hq
  · intro h
    exact congruence_le_ker h

theorem congruence_eq_ker : congruence = RingCon.ker phi :=
  RingCon.ext fun u v => (phi_eq_iff u v).symm

/-- The cyclic quotient is identified with its bundled integer range. -/
noncomputable def quotientEquivRange : B ≃+* phi.rangeS :=
  (RingCon.congr congruence_eq_ker).trans (RingCon.quotientKerEquivRangeS phi)

noncomputable def quotientEmbedding : B →+* Target :=
  phi.rangeS.subtype.comp quotientEquivRange.toRingHom

theorem quotientEmbedding_injective : Function.Injective quotientEmbedding := by
  intro x y h
  apply quotientEquivRange.injective
  exact Subtype.ext h

/-- Exact integer cone condition, including its parity constraint. -/
def ConeCondition (z : GaussianInt) (Q : ℤ) : Prop :=
  |z.re| + |z.im| ≤ Q ∧ Q % 2 = (z.re + z.im) % 2

private theorem signed_parts (x : ℤ) :
    (x.toNat : ℤ) - (-x).toNat = x ∧
      (x.toNat : ℤ) + (-x).toNat = |x| := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    constructor <;> omega
  · rw [abs_of_neg (lt_of_not_ge hx)]
    constructor <;> omega

private theorem abs_parity (x : ℤ) : |x| % 2 = x % 2 := by
  obtain ⟨hd, hs⟩ := signed_parts x
  omega

/-- Every nonnegative coefficient vector lies in the exact integer cone. -/
theorem coefficients_cone (n0 n1 n2 n3 : ℕ) :
    |(n0 : ℤ) - n2| + |(n1 : ℤ) - n3| ≤ (n0 : ℤ) + n1 + n2 + n3 ∧
      ((n0 : ℤ) + n1 + n2 + n3) % 2 =
        ((n0 : ℤ) - n2 + ((n1 : ℤ) - n3)) % 2 := by
  constructor
  · by_cases hr : 0 ≤ (n0 : ℤ) - n2
    · rw [abs_of_nonneg hr]
      by_cases hi : 0 ≤ (n1 : ℤ) - n3
      · rw [abs_of_nonneg hi]
        omega
      · rw [abs_of_neg (lt_of_not_ge hi)]
        omega
    · rw [abs_of_neg (lt_of_not_ge hr)]
      by_cases hi : 0 ≤ (n1 : ℤ) - n3
      · rw [abs_of_nonneg hi]
        omega
      · rw [abs_of_neg (lt_of_not_ge hi)]
        omega
  · omega

/-- Constructive coefficient existence for the cone. The nonnegative excess is
split into an equal pair added to the real-coordinate coefficients. -/
theorem exists_coefficients_of_cone (x y Q : ℤ)
    (hbound : |x| + |y| ≤ Q)
    (hparity : Q % 2 = (x + y) % 2) :
    ∃ n0 n1 n2 n3 : ℕ,
      (n0 : ℤ) - n2 = x ∧ (n1 : ℤ) - n3 = y ∧
        (n0 : ℤ) + n1 + n2 + n3 = Q := by
  let h : ℤ := (Q - |x| - |y|) / 2
  have hxparity := abs_parity x
  have hyparity := abs_parity y
  have hh : 0 ≤ h := by dsimp [h]; omega
  have htotal : Q = |x| + |y| + 2 * h := by dsimp [h]; omega
  have hhcast : (h.toNat : ℤ) = h := by omega
  obtain ⟨hxd, hxs⟩ := signed_parts x
  obtain ⟨hyd, hys⟩ := signed_parts y
  refine ⟨x.toNat + h.toNat, y.toNat, (-x).toNat + h.toNat, (-y).toNat, ?_⟩
  simp only [Nat.cast_add]
  constructor
  · omega
  constructor
  · exact hyd
  · omega

/-- Exact membership criterion for the bundled range subsemiring. -/
theorem mem_rangeS_iff (z : GaussianInt) (Q : ℤ) :
    (z, Q) ∈ phi.rangeS ↔ ConeCondition z Q := by
  change (∃ u : A, phi u = (z, Q)) ↔ _
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨n0, n1, n2, n3, rfl⟩ := four_surjective u
    rw [phi_ofFour] at hu
    have hr := congrArg (fun t : Target => t.1.re) hu
    have hi := congrArg (fun t : Target => t.1.im) hu
    have hq := congrArg (fun t : Target => t.2) hu
    have hc := coefficients_cone n0 n1 n2 n3
    change (n0 : ℤ) - n2 = z.re at hr
    change (n1 : ℤ) - n3 = z.im at hi
    change (n0 : ℤ) + n1 + n2 + n3 = Q at hq
    rw [hr, hi, hq] at hc
    exact hc
  · intro hz
    obtain ⟨n0, n1, n2, n3, hr, hi, hq⟩ :=
      exists_coefficients_of_cone z.re z.im Q hz.1 hz.2
    refine ⟨ofFour n0 n1 n2 n3, ?_⟩
    rw [phi_ofFour]
    apply Prod.ext
    · exact Zsqrtd.ext hr hi
    · exact hq

end CyclicFourPositiveCongruence
