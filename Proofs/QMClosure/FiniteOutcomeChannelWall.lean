import Proofs.QMClosure.FiniteOutcomeAffinityRigidity
import Mathlib.Data.ZMod.Basic

/-!
# Fixed finite-outcome common-channel obstruction

The common channel is an actual nonnegative finite stochastic matrix. Its
affinity data-processing inequality and product factorization derive the
additive comparison premise used by the reconstruction, with no supplied
Hilbert geometry, Gram positivity, or raw preparation algebra.

All overlaps must be strictly positive when interpreted through negative log.
The omission control records a nonconstant Dirac family with zero overlaps.
This exact full-carrier obstruction makes no finite-experiment or physical
detector-origin claim.
-/

namespace IDT.QMClosure.FiniteOutcomeChannelWall

noncomputable section

open scoped BigOperators
open FiniteOutcomeAffinityRigidity

universe u v w

/-- One state-independent finite stochastic transition matrix. -/
structure Channel (A : Type v) (B : Type w) [Fintype A] [Fintype B] where
  transition : A → B → ℝ
  nonnegative : ∀ a b, 0 ≤ transition a b
  normalized : ∀ a, ∑ b, transition a b = 1

namespace Channel

variable {A : Type v} {B : Type w} [Fintype A] [Fintype B]

def outputLaw (T : Channel A B) (p : A → ℝ) (b : B) : ℝ :=
  ∑ a, p a * T.transition a b

theorem outputLaw_nonnegative (T : Channel A B) (p : A → ℝ)
    (hp : ∀ a, 0 ≤ p a) (b : B) : 0 ≤ T.outputLaw p b := by
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (hp a) (T.nonnegative a b))

/-- Classical affinity is nondecreasing through the same stochastic channel. -/
theorem affinity_data_processing (T : Channel A B) (p q : A → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) :
    affinity p q ≤ affinity (T.outputLaw p) (T.outputLaw q) := by
  classical
  have hpoint (b : B) :
      (∑ a, Real.sqrt (p a * q a) * T.transition a b) ≤
        Real.sqrt (T.outputLaw p b * T.outputLaw q b) := by
    have hcs := Real.sum_sqrt_mul_sqrt_le Finset.univ
      (fun a => mul_nonneg (hp a) (T.nonnegative a b))
      (fun a => mul_nonneg (hq a) (T.nonnegative a b))
    rw [Real.sqrt_mul (T.outputLaw_nonnegative p hp b)]
    apply le_trans ?_ hcs
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro a _
    rw [Real.sqrt_mul (hp a), Real.sqrt_mul (hq a), Real.sqrt_mul (hp a)]
    calc
      _ = Real.sqrt (p a) * Real.sqrt (q a) * Real.sqrt (T.transition a b) ^ 2 := by
        rw [Real.sq_sqrt (T.nonnegative a b)]
      _ = _ := by ring
  calc
    affinity p q = ∑ b, ∑ a, Real.sqrt (p a * q a) * T.transition a b := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, T.normalized, mul_one]
      rfl
    _ ≤ affinity (T.outputLaw p) (T.outputLaw q) := Finset.sum_le_sum (fun b _ => hpoint b)

end Channel

/-- Independent two-port preparation law. Independence is an explicit premise. -/
def productLaw {Ω : Type v} (p q : Ω → ℝ) (ω : Ω × Ω) : ℝ := p ω.1 * q ω.2

theorem affinity_product {Ω : Type v} [Fintype Ω]
    (p₁ p₂ q₁ q₂ : Ω → ℝ)
    (hp₁ : ∀ ω, 0 ≤ p₁ ω) (_hp₂ : ∀ ω, 0 ≤ p₂ ω)
    (hq₁ : ∀ ω, 0 ≤ q₁ ω) (_hq₂ : ∀ ω, 0 ≤ q₂ ω) :
    affinity (productLaw p₁ p₂) (productLaw q₁ q₂) =
      affinity p₁ q₁ * affinity p₂ q₂ := by
  classical
  simp only [affinity, Fintype.sum_prod_type, productLaw]
  simp_rw [show ∀ a b, (p₁ a * p₂ b) * (q₁ a * q₂ b) =
      (p₁ a * q₁ a) * (p₂ b * q₂ b) by intros; ring]
  simp_rw [Real.sqrt_mul (mul_nonneg (hp₁ _) (hq₁ _)), ← Finset.mul_sum]
  rw [Finset.sum_mul]

theorem affinity_self {Ω : Type v} [Fintype Ω] (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hn : ∑ ω, p ω = 1) : affinity p p = 1 := by
  simp only [affinity, Real.sqrt_mul_self (hp _)]
  exact hn

theorem affinity_le_one {Ω : Type v} [Fintype Ω] (p q : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω)
    (hnp : ∑ ω, p ω = 1) (hnq : ∑ ω, q ω = 1) : affinity p q ≤ 1 := by
  have h := Real.sum_sqrt_mul_sqrt_le Finset.univ hp hq
  rw [hnp, hnq] at h
  simpa only [Real.sqrt_one, mul_one, affinity, Real.sqrt_mul (hp _)] using h

/-- Covariance means equality of actual output laws under a single common channel. -/
def CommonChannelCovariance {V : Type u} {Ω : Type v} [Fintype Ω]
    (K : V → Ω → ℝ) (F : V × V → V × V) (T : Channel (Ω × Ω) (Ω × Ω)) : Prop :=
  ∀ p, productLaw (K (F p).1) (K (F p).2) = T.outputLaw (productLaw (K p.1) (K p.2))

variable {V : Type u} {Ω : Type v} [Fintype Ω]

/-- Product affinity and stochastic data processing give additive-log nonexpansion. -/
theorem comparison_nonexpanding_of_common_channel
    (K : V → Ω → ℝ) (hK : ∀ x ω, 0 ≤ K x ω)
    (hpositive : ∀ x y, 0 < affinity (K x) (K y))
    (F : V × V → V × V) (T : Channel (Ω × Ω) (Ω × Ω))
    (hcov : CommonChannelCovariance K F T) :
    RawProcessComparisonBridge.PairComparisonNonexpanding
      (fun x y => -Real.log (affinity (K x) (K y))) F := by
  intro p q
  have hdpi := T.affinity_data_processing
    (productLaw (K p.1) (K p.2)) (productLaw (K q.1) (K q.2))
    (fun ω => mul_nonneg (hK p.1 ω.1) (hK p.2 ω.2))
    (fun ω => mul_nonneg (hK q.1 ω.1) (hK q.2 ω.2))
  rw [← hcov p, ← hcov q,
    affinity_product _ _ _ _ (hK p.1) (hK p.2) (hK q.1) (hK q.2),
    affinity_product _ _ _ _ (hK (F p).1) (hK (F p).2) (hK (F q).1) (hK (F q).2)] at hdpi
  have hlog := Real.log_le_log (mul_pos (hpositive p.1 q.1) (hpositive p.2 q.2)) hdpi
  rw [Real.log_mul (ne_of_gt (hpositive p.1 q.1)) (ne_of_gt (hpositive p.2 q.2)),
    Real.log_mul (ne_of_gt (hpositive (F p).1 (F q).1))
      (ne_of_gt (hpositive (F p).2 (F q).2))] at hlog
  dsimp [RawProcessComparisonBridge.pairComparison]
  linarith

/-- The reconstruction contract is derived from actual finite stochastic covariance. -/
def reconstructionOfCommonChannel
    (chosenZero : V) (K : V → Ω → ℝ) (hK : ∀ x ω, 0 ≤ K x ω)
    (hnorm : ∀ x, ∑ ω, K x ω = 1)
    (hpositive : ∀ x y, 0 < affinity (K x) (K y))
    (F : V × V → V × V) (hsquare : ∀ p, F (F p) = p.swap)
    (hdiag : ∀ x, F (x, x) = (x, x))
    (T : Channel (Ω × Ω) (Ω × Ω)) (hcov : CommonChannelCovariance K F T) :
    PairComparisonReconstruction.Contract V where
  chosenZero := chosenZero
  operation := F
  comparison x y := -Real.log (affinity (K x) (K y))
  square := hsquare
  transparent := hdiag
  symmetric x y := by simp only [affinity, mul_comm]
  nonnegative x y := neg_nonneg.mpr (Real.log_nonpos (hpositive x y).le
    (affinity_le_one _ _ (hK x) (hK y) (hnorm x) (hnorm y)))
  diagonal x := by rw [affinity_self (K x) (hK x) (hnorm x), Real.log_one, neg_zero]
  nonexpanding := comparison_nonexpanding_of_common_channel K hK hpositive F T hcov

/-- Universal fixed-finite-outcome rigidity for the actual common stochastic process. -/
theorem all_laws_equal_of_common_channel
    (chosenZero : V) (K : V → Ω → ℝ) (hK : ∀ x ω, 0 ≤ K x ω)
    (hnorm : ∀ x, ∑ ω, K x ω = 1)
    (hpositive : ∀ x y, 0 < affinity (K x) (K y))
    (F : V × V → V × V) (hsquare : ∀ p, F (F p) = p.swap)
    (hdiag : ∀ x, F (x, x) = (x, x))
    (T : Channel (Ω × Ω) (Ω × Ω)) (hcov : CommonChannelCovariance K F T)
    (x y : V) : K x = K y := by
  exact all_laws_equal
    (reconstructionOfCommonChannel chosenZero K hK hnorm hpositive F hsquare hdiag T hcov)
    K hK hnorm hpositive (fun _ _ => rfl) x y

namespace ZeroOverlapControl

/-- Dirac laws retain zero overlaps, so they lie outside the positive-overlap theorem. -/
def dirac {A : Type*} [DecidableEq A] (x : A) : A → ℝ :=
  fun a => if a = x then 1 else 0

theorem dirac_nonnegative {A : Type*} [DecidableEq A] (x a : A) : 0 ≤ dirac x a := by
  unfold dirac
  split_ifs <;> norm_num

theorem dirac_normalized {A : Type*} [Fintype A] [DecidableEq A] (x : A) :
    (∑ a, dirac x a) = 1 := by simp [dirac]

theorem dirac_affinity {A : Type*} [Fintype A] [DecidableEq A] (x y : A) :
    affinity (dirac x) (dirac y) = if x = y then 1 else 0 := by
  classical
  by_cases h : x = y
  · subst y
    simpa using affinity_self _ (dirac_nonnegative x) (dirac_normalized x)
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : a = x
    · subst a
      simp [dirac, h]
    · simp [dirac, ha]

def deterministicChannel {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) : Channel A B where
  transition a b := dirac (f a) b
  nonnegative := fun a b => dirac_nonnegative (f a) b
  normalized := fun a => dirac_normalized (f a)

theorem deterministic_dirac {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (f : A → B) (x : A) :
    (deterministicChannel f).outputLaw (dirac x) = dirac (f x) := by
  funext b
  change (∑ a, (if a = x then 1 else 0) * dirac (f a) b) = _
  simp only [ite_mul, one_mul, zero_mul]
  simp

theorem product_dirac {A : Type*} [DecidableEq A] (x y : A) :
    productLaw (dirac x) (dirac y) = dirac (x, y) := by
  funext a
  rcases a with ⟨a, b⟩
  by_cases ha : a = x <;> by_cases hb : b = y <;>
    simp [productLaw, dirac, ha, hb, Prod.mk.injEq]

def operation (p : ZMod 5 × ZMod 5) : ZMod 5 × ZMod 5 :=
  (4 * p.1 + 2 * p.2, 2 * p.1 + 4 * p.2)

theorem operation_square (p : ZMod 5 × ZMod 5) : operation (operation p) = p.swap := by
  have h20 : (20 : ZMod 5) = 0 := by decide
  have h16 : (16 : ZMod 5) = 1 := by decide
  apply Prod.ext <;> dsimp [operation] <;> ring_nf <;> simp [h20, h16]

theorem operation_diagonal (x : ZMod 5) : operation (x, x) = (x, x) := by
  have h6 : (6 : ZMod 5) = 1 := by decide
  apply Prod.ext <;> dsimp [operation] <;> ring_nf <;> simp [h6]

def channel : Channel (ZMod 5 × ZMod 5) (ZMod 5 × ZMod 5) :=
  deterministicChannel operation

theorem common_channel_covariance : CommonChannelCovariance
    (fun x : ZMod 5 => dirac x) operation channel := by
  intro p
  rw [product_dirac, product_dirac]
  exact (deterministic_dirac operation p).symm

/-- Every totalized-log comparison is zero, despite distinct laws. -/
theorem logarithmic_comparison_zero (x y : ZMod 5) :
    -Real.log (affinity (dirac x) (dirac y)) = 0 := by
  rw [dirac_affinity]
  split_ifs <;> simp

theorem distinct_laws : dirac (0 : ZMod 5) ≠ dirac 1 := by
  intro h
  have hh := congrFun h 0
  simp [dirac, show (0 : ZMod 5) ≠ 1 by decide] at hh

theorem zero_overlap : affinity (dirac (0 : ZMod 5)) (dirac 1) = 0 := by
  rw [dirac_affinity, if_neg (by decide : (0 : ZMod 5) ≠ 1)]

end ZeroOverlapControl

end

end IDT.QMClosure.FiniteOutcomeChannelWall
