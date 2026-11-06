import Proofs.QMClosure.QuadraticRecordRefinement
import Proofs.QMClosure.OperationalQuadraticReconstruction
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Topology.Instances.Rat

namespace IDT.QMClosure.PositiveQuadraticPolarization

open QuadraticRecordRefinement

noncomputable section

/-!
Universal real-valued algebra on an additive commutative group. Positivity and
the parallelogram identity are supplied. No scalar multiplication by real or
rational numbers, divisibility, topology, or continuity is required on the
carrier. Density below concerns only a real coefficient polynomial, not Q.
-/

variable {U : Type*} [AddCommGroup U]

/-- Real polarization, defined without halving an element of the carrier. -/
def polarization (Q : U → ℝ) (u v : U) : ℝ := (Q (u + v) - Q u - Q v) / 2

variable {Q : U → ℝ} (h : PositiveQuadratic Q)

theorem symmetric (u v : U) : polarization Q u v = polarization Q v u := by
  simp only [polarization, add_comm u v]
  ring

include h

theorem zero_left (v : U) : polarization Q 0 v = 0 := by
  simp [polarization, h.zero]

theorem zero_right (u : U) : polarization Q u 0 = 0 := by
  rw [symmetric, zero_left h]

theorem add_left (u v w : U) :
    polarization Q (u + v) w = polarization Q u w + polarization Q v w := by
  have ht := OperationalQuadraticReconstruction.third_order_zero_of_parallelogram
    Q h.even h.parallelogram u v w
  dsimp [polarization]
  linarith

theorem add_right (u v w : U) :
    polarization Q u (v + w) = polarization Q u v + polarization Q u w := by
  rw [symmetric u (v + w), add_left h, symmetric v u, symmetric w u]

theorem diagonal (u : U) : polarization Q u u = Q u := by
  dsimp [polarization]
  rw [h.double]
  ring

/-- Polarization as an additive map in the first coordinate. -/
def leftAddHom (v : U) : U →+ ℝ where
  toFun := fun u => polarization Q u v
  map_zero' := zero_left h v
  map_add' := fun u w => add_left h u w v

theorem zsmul_left (m : ℤ) (u v : U) :
    polarization Q (m • u) v = (m : ℝ) * polarization Q u v := by
  exact (map_zsmul (leftAddHom h v) m u).trans (by simp [zsmul_eq_mul, leftAddHom])

theorem zsmul_right (n : ℤ) (u v : U) :
    polarization Q u (n • v) = (n : ℝ) * polarization Q u v := by
  rw [symmetric, zsmul_left h, symmetric v u]

theorem quadratic_zsmul (m : ℤ) (u : U) : Q (m • u) = (m : ℝ)^2 * Q u := by
  rw [← diagonal h, zsmul_left h, zsmul_right h, diagonal h]
  ring

omit h in
theorem sum_expansion (u v : U) :
    Q (u + v) = Q u + 2 * polarization Q u v + Q v := by
  dsimp [polarization]
  ring

/-- Exact integer-coordinate law; no scalar structure on U is assumed. -/
theorem integer_coordinate_law (m n : ℤ) (u v : U) :
    Q (m • u + n • v) = (m : ℝ)^2 * Q u +
      2 * (m : ℝ) * (n : ℝ) * polarization Q u v + (n : ℝ)^2 * Q v := by
  rw [sum_expansion (Q := Q) (m • u) (n • v), quadratic_zsmul h, quadratic_zsmul h,
    zsmul_left h, zsmul_right h]
  ring

omit h

/-- Integer tests characterize positivity of a real binary quadratic form.
Rational density is used only in the coefficient plane, never on U. -/
theorem integer_binary_nonnegative_iff (α β γ : ℝ) :
    (∀ m n : ℤ, 0 ≤ α * (m : ℝ)^2 + 2 * β * (m : ℝ) * (n : ℝ) + γ * (n : ℝ)^2) ↔
      0 ≤ α ∧ 0 ≤ γ ∧ β^2 ≤ α * γ := by
  constructor
  · intro hp
    have ha : 0 ≤ α := by simpa using hp 1 0
    have hc : 0 ≤ γ := by simpa using hp 0 1
    have hrat (q : ℚ) : 0 ≤ α * (q : ℝ)^2 + 2 * β * (q : ℝ) + γ := by
      have hd : 0 < (q.den : ℝ) := by exact_mod_cast q.pos
      apply nonneg_of_mul_nonneg_right _ (sq_pos_of_pos hd)
      convert hp q.num q.den using 1
      rw [Rat.cast_def]
      push_cast
      field_simp
    have hall (x : ℝ) : 0 ≤ α * (x * x) + (2 * β) * x + γ := by
      apply Rat.denseRange_cast.induction_on
        (p := fun x : ℝ => 0 ≤ α * (x * x) + (2 * β) * x + γ) x
      · exact isClosed_le continuous_const (by fun_prop)
      · intro q
        simpa only [pow_two, mul_assoc] using hrat q
    have hd := discrim_le_zero hall
    dsimp [discrim] at hd
    exact ⟨ha, hc, by nlinarith⟩
  · rintro ⟨ha, hc, hd⟩ m n
    by_cases hz : α = 0
    · have hb : β = 0 := by nlinarith [sq_nonneg β]
      simp only [hz, hb, zero_mul, mul_zero, zero_add]
      exact mul_nonneg hc (sq_nonneg _)
    · have ha' : 0 < α := lt_of_le_of_ne ha (Ne.symm hz)
      have hdet := mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg (n : ℝ))
      have hs := sq_nonneg (α * (m : ℝ) + β * (n : ℝ))
      apply nonneg_of_mul_nonneg_left _ ha'
      nlinarith

include h

/-- Cauchy–Schwarz from positivity on every integer combination. -/
theorem cauchy_schwarz (u v : U) : (polarization Q u v)^2 ≤ Q u * Q v := by
  have hp : ∀ m n : ℤ, 0 ≤ Q u * (m : ℝ)^2 +
      2 * polarization Q u v * (m : ℝ) * (n : ℝ) + Q v * (n : ℝ)^2 := by
    intro m n
    have hn := h.nonnegative (m • u + n • v)
    rw [integer_coordinate_law h] at hn
    convert hn using 1
    ring
  exact ((integer_binary_nonnegative_iff _ _ _).mp hp).2.2

/-- Null separation is exactly invisibility to every coherent reference. -/
theorem null_iff_all_reference_tests (x y : U) :
    Q (x - y) = 0 ↔ ∀ z, Q (x + z) = Q (y + z) := by
  constructor
  · intro hn z
    have ht := h.null_translate (y + z) (x - y) hn
    have he : y + z + (x - y) = x + z := by abel
    rwa [he] at ht
  · intro ht
    have hz := ht (-y)
    simpa [sub_eq_add_neg, h.zero] using hz

omit h

/-- A positive quadratic readout dominated by Q cannot see a Q-null direction. -/
theorem dominated_null_invisibility {R : U → ℝ} (hR : PositiveQuadratic R)
    (dominated : ∀ u, R u ≤ Q u) (v : U) (hv : Q v = 0) (u : U) :
    R (u + v) = R u := by
  have hr : R v = 0 := le_antisymm (by simpa [hv] using dominated v) (hR.nonnegative v)
  exact hR.null_translate u v hr

/-- Machine-visible scope: these are supplied or excluded, never claim upgrades. -/
inductive BoundaryRole where
  | suppliedRealCodomainAndOrder
  | suppliedPositivityAndParallelogram
  | noCarrierScalarDivisibilityOrTopologyPremise
  | universalAlgebraicTheoremOnly
  | doesNotActualizeProbability
  | doesNotDerivePhysicsOrFullQM
  | doesNotUpgradeAnyManifestStatus
  deriving DecidableEq, Repr

def boundaryRoles : List BoundaryRole := [
  .suppliedRealCodomainAndOrder,
  .suppliedPositivityAndParallelogram,
  .noCarrierScalarDivisibilityOrTopologyPremise,
  .universalAlgebraicTheoremOnly,
  .doesNotActualizeProbability,
  .doesNotDerivePhysicsOrFullQM,
  .doesNotUpgradeAnyManifestStatus]

end

end IDT.QMClosure.PositiveQuadraticPolarization
