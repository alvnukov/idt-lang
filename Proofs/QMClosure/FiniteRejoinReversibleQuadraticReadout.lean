import Proofs.QMClosure.FiniteRejoinColumnBalance
import Proofs.QMClosure.OperationalQuadraticReconstruction
import Proofs.QMClosure.PositiveQuadraticPolarization

/-!
# Reversible finite rejoin and a quadratic readout

This source formalizes the analytic argument for the supplied full-domain
contract. A transparent additive branch pair has an equal positive-power
rejoin, its complete symmetric two-port map is surjective, and a nonnegative
vacuum-zero real readout is conserved on every pair of carrier inputs.

The additive inverses and the positive quadratic readout are conclusions.
The argument is conditional on these operational hypotheses. It supplies no
physical origin, physical accessibility claim, QM closure, or literal fourth
rejoin on the full original carrier. No continuity, scalar multiplication,
serial readout multiplication, or extra readout monotonicity is supplied.
-/

noncomputable section

namespace IDT.QMClosure.FiniteRejoinReversibleQuadraticReadout

open QuadraticRecordRefinement
open IDT.TransparentPositivePowerRejoin

section EndEvaluation

variable {V : Type*} [AddCommMonoid V]

private theorem end_mul_apply (f g : AddMonoid.End V) (x : V) :
    (f * g) x = f (g x) := rfl

private theorem end_add_apply (f g : AddMonoid.End V) (x : V) :
    (f + g) x = f x + g x := rfl

private theorem end_one_apply (x : V) : (1 : AddMonoid.End V) x = x := rfl

private theorem inverse_apply {f g : AddMonoid.End V}
    (h : f * g = 1) (x : V) : f (g x) = x := by
  change (f * g) x = (1 : AddMonoid.End V) x
  rw [h]

end EndEvaluation

section Monoid

variable {V : Type*} [AddCommMonoid V]

/-- The complete symmetric additive two-port map. -/
def twoPort (a b : AddMonoid.End V) : (V × V) → (V × V) :=
  fun p => (a p.1 + b p.2, b p.1 + a p.2)

/-- Two invertible branches and surjectivity of the complete two-port map
supply an additive inverse for every element of the original monoid. -/
theorem additive_inverses_of_twoPort_surjective
    (a b u v : AddMonoid.End V) (hua : u * a = 1) (hvb : v * b = 1)
    (onto : Function.Surjective (twoPort a b)) :
    ∀ p : V, ∃ q : V, p + q = 0 := by
  intro p
  obtain ⟨⟨x, y⟩, hxy⟩ := onto (p, 0)
  have hp : a x + b y = p := congrArg Prod.fst hxy
  have hz : b x + a y = 0 := congrArg Prod.snd hxy
  have hxt : x + v (a y) = 0 := by
    have h := congrArg v hz
    simpa only [map_add, inverse_apply hvb, map_zero] using h
  have hys : y + u (b x) = 0 := by
    have h := congrArg u hz
    have h' : u (b x) + y = 0 := by
      simpa only [map_add, inverse_apply hua, map_zero] using h
    simpa only [add_comm] using h'
  refine ⟨a (v (a y)) + b (u (b x)), ?_⟩
  calc
    p + (a (v (a y)) + b (u (b x))) =
        a (x + v (a y)) + b (y + u (b x)) := by
      rw [← hp, map_add, map_add]
      simp only [add_assoc, add_comm, add_left_comm]
    _ = 0 := by rw [hxt, hys, map_zero, map_zero, add_zero]

/-- This group has exactly the given addition, zero and natural-number action.
Its inverse is chosen from the proved monoid inverse-existence statement. -/
abbrev groupFromInverses (hinv : ∀ p : V, ∃ q : V, p + q = 0) :
    AddCommGroup V :=
  letI : Neg V := ⟨fun p => Classical.choose (hinv p)⟩
  { (inferInstance : AddCommMonoid V) with
    neg := fun p => Classical.choose (hinv p)
    zsmul := zsmulRec
    neg_add_cancel := fun p => by
      change Classical.choose (hinv p) + p = 0
      simpa only [add_comm] using Classical.choose_spec (hinv p) }

/-- Algebraic hypotheses of the finite-rejoin reconstruction. The readout is
kept separate so the derived group does not depend on a readout choice. -/
structure Gate (V : Type*) [AddCommMonoid V] where
  a : AddMonoid.End V
  b : AddMonoid.End V
  period : ℕ
  period_pos : 0 < period
  transparent : a + b = 1
  rejoin : a ^ period = b ^ period
  onto : Function.Surjective (twoPort a b)

namespace Gate

variable (G : Gate V)

include G

/-- Explicit positive inverse word of the first branch. -/
def inverseA : AddMonoid.End V :=
  inverseWordA G.a G.b (G.period - 1) (G.period - 1)

/-- Explicit positive inverse word of the second branch. -/
def inverseB : AddMonoid.End V :=
  inverseWordB G.a G.b (G.period - 1) (G.period - 1)

theorem inverseA_laws : G.inverseA * G.a = 1 ∧ G.a * G.inverseA = 1 := by
  have hp : G.period - 1 + 1 = G.period :=
    Nat.sub_add_cancel (Nat.one_le_of_lt G.period_pos)
  exact geometric_inverse_a (G.period - 1) (G.period - 1) G.transparent
    (by simpa only [hp] using G.rejoin)

theorem inverseB_laws : G.inverseB * G.b = 1 ∧ G.b * G.inverseB = 1 := by
  have hp : G.period - 1 + 1 = G.period :=
    Nat.sub_add_cancel (Nat.one_le_of_lt G.period_pos)
  exact geometric_inverse_b (G.period - 1) (G.period - 1) G.transparent
    (by simpa only [hp] using G.rejoin)

/-- Only the distinguished branch pair is asserted to commute. -/
theorem commute : Commute G.a G.b :=
  commute_of_transparent_finite_rejoin G.period G.period_pos G.transparent G.rejoin

theorem additive_inverses : ∀ p : V, ∃ q : V, p + q = 0 :=
  additive_inverses_of_twoPort_surjective G.a G.b G.inverseA G.inverseB
    G.inverseA_laws.1 G.inverseB_laws.1 G.onto

/-- The derived group preserves the supplied monoid. -/
abbrev additiveGroup : AddCommGroup V := groupFromInverses G.additive_inverses

/-- A type synonym exposes the derived group without an input group instance. -/
def Carrier (_G : Gate V) := V

instance carrierGroup : AddCommGroup G.Carrier := G.additiveGroup

/-- The cross-history coefficient is twice the ordered mixed branch. -/
def cross : AddMonoid.End V := G.a * G.b + G.a * G.b

/-- The same-history coefficient. -/
def same : AddMonoid.End V := G.a * G.a + G.b * G.b

end Gate

/-- Finite-cycle column balance applied to evaluation at a fixed preparation.
The semiring is the original, potentially noncommutative, endomorphism semiring. -/
theorem half_responses (G : Gate V) (W : V → ℝ)
    (vacuum : W 0 = 0) (nonnegative : ∀ p, 0 ≤ W p)
    (conserve : ∀ x y,
      W (G.a x + G.b y) + W (G.b x + G.a y) = W x + W y) :
    ∀ p, W (G.a p) = W p / 2 ∧ W (G.b p) = W p / 2 := by
  have column : ∀ p, W (G.a p) + W (G.b p) = W p := by
    intro p
    simpa only [map_zero, add_zero, vacuum, add_zero] using conserve p 0
  intro p
  have h := FiniteRejoinColumnBalance.half_responses
    G.period_pos G.transparent G.rejoin
    (fun T : AddMonoid.End V => W (T p))
    (fun T => nonnegative (T p))
    (fun T => column (T p)) (1 : AddMonoid.End V)
  simpa only [end_mul_apply, end_one_apply] using h

end Monoid

section Group

variable {V : Type*} [AddCommGroup V]

/-- The group step uses exact branch halves and full conservation. The finite
rejoin is needed upstream to derive those halves and the inverse words. -/
theorem parallelogram_of_reversible_half_conservation
    (a b u v : AddMonoid.End V)
    (hua : u * a = 1) (hau : a * u = 1)
    (hvb : v * b = 1) (hbv : b * v = 1)
    (transparent : a + b = 1)
    (onto : Function.Surjective (twoPort a b))
    (W : V → ℝ)
    (halves : ∀ p, W (a p) = W p / 2 ∧ W (b p) = W p / 2)
    (conserve : ∀ x y,
      W (a x + b y) + W (b x + a y) = W x + W y) :
    ∀ x y, W (x + y) + W (x - y) = 2 * W x + 2 * W y := by
  let r : AddMonoid.End V := a * v
  let s : AddMonoid.End V := b * u
  let R : AddMonoid.End V := r * r
  have hrs : r * s = 1 := by
    change (a * v) * (b * u) = 1
    calc
      (a * v) * (b * u) = a * (v * b) * u := by noncomm_ring
      _ = 1 := by rw [hvb, mul_one, hau]
  have hsr : s * r = 1 := by
    change (b * u) * (a * v) = 1
    calc
      (b * u) * (a * v) = b * (u * a) * v := by noncomm_ring
      _ = 1 := by rw [hua, mul_one, hbv]
  have inverse_a_gain (p : V) : W (u p) = 2 * W p := by
    have h := (halves (u p)).1
    rw [inverse_apply hau] at h
    linarith
  have inverse_b_gain (p : V) : W (v p) = 2 * W p := by
    have h := (halves (v p)).2
    rw [inverse_apply hbv] at h
    linarith
  have phase_invariant (p : V) : W (r p) = W p := by
    have h := (halves (v p)).1
    change W (r p) = W (v p) / 2 at h
    rw [h, inverse_b_gain]
    ring
  have square_invariant (p : V) : W (R p) = W p := by
    change W (r (r p)) = W p
    rw [phase_invariant, phase_invariant]
  have equation (x y : V) :
      W (x + y) + W (x + R y) = 2 * W x + 2 * W y := by
    have h := conserve (u x) (v y)
    rw [inverse_apply hau, inverse_apply hbv, inverse_a_gain, inverse_b_gain] at h
    have houtput : r (b (u x) + a (v y)) = x + R y := by
      rw [map_add]
      change (r * s) x + (r * r) y = x + R y
      rw [hrs]
      rfl
    have hreadout : W (b (u x) + a (v y)) = W (x + R y) := by
      rw [← houtput, phase_invariant]
    rw [hreadout] at h
    exact h
  have symmetric (x y : V) : W (x + R y) = W (R x + y) := by
    have hxy := equation x y
    have hyx := equation y x
    rw [add_comm y x, add_comm y (R x)] at hyx
    linarith
  have square_period (z t : V) : W (z + (R * R - 1) t) = W z := by
    have h := symmetric (z - t) (R t)
    have hout : R (z - t) + R t = R z := by
      rw [← map_add]
      congr 1
      abel
    rw [hout, square_invariant] at h
    have hin : z - t + R (R t) = z + (R * R - 1) t := by
      change z - t + R (R t) = z + ((R * R) t - (1 : AddMonoid.End V) t)
      simp only [end_mul_apply, end_one_apply]
      abel
    rw [hin] at h
    exact h
  have difference_onto : Function.Surjective (a - b : AddMonoid.End V) := by
    intro p
    obtain ⟨⟨x, y⟩, hxy⟩ := onto (p, 0)
    have hp : a x + b y = p := congrArg Prod.fst hxy
    have hz : b x + a y = 0 := congrArg Prod.snd hxy
    refine ⟨x - y, ?_⟩
    calc
      (a - b) (x - y) = (a x + b y) - (b x + a y) := by
        change a (x - y) - b (x - y) = _
        simp only [map_sub]
        abel
      _ = p := by rw [hp, hz, sub_zero]
  have phase_plus_one : r + 1 = v := by
    calc
      r + 1 = (a + b) * v := by
        rw [add_mul, hbv]
      _ = v := by rw [transparent, one_mul]
  have difference_factor : R - 1 = (a - b) * v * v := by
    calc
      R - 1 = (r - 1) * (r + 1) := by dsimp [R]; noncomm_ring
      _ = (r - 1) * v := by rw [phase_plus_one]
      _ = (a - b) * v * v := by
        dsimp [r]
        rw [sub_mul, sub_mul, sub_mul, hbv, one_mul]
  have square_difference_onto : Function.Surjective (R - 1 : AddMonoid.End V) := by
    intro p
    obtain ⟨z, hz⟩ := difference_onto p
    refine ⟨b (b z), ?_⟩
    rw [difference_factor]
    change (a - b) (v (v (b (b z)))) = p
    rw [inverse_apply hvb, inverse_apply hvb]
    exact hz
  have linear_period (z y : V) : W (z + (R + 1) y) = W z := by
    obtain ⟨t, ht⟩ := square_difference_onto y
    have hfactor : (R + 1) * (R - 1) = R * R - 1 := by noncomm_ring
    have harg : (R + 1) y = (R * R - 1) t := by
      rw [← ht]
      change ((R + 1) * (R - 1)) t = (R * R - 1) t
      rw [hfactor]
    rw [harg]
    exact square_period z t
  have negative_output (x y : V) : W (x + R y) = W (x - y) := by
    have h := linear_period (x - y) y
    have harg : x - y + (R + 1) y = x + R y := by
      simp only [end_add_apply, end_one_apply]
      abel
    rw [harg] at h
    exact h
  intro x y
  rw [← negative_output x y]
  exact equation x y

end Group

section Reconstruction

variable {V : Type*} [AddCommMonoid V]

/-- Positive quadratic structure is stated on the explicitly derived group.
Every other field uses the original carrier addition and branch maps. -/
structure Reconstruction (G : Gate V) (W : V → ℝ) : Prop where
  quadratic : PositiveQuadratic (fun p : G.Carrier => W p)
  branch_halves : ∀ p, W (G.a p) = W p / 2 ∧ W (G.b p) = W p / 2
  cross_invariant : ∀ p, W (G.cross p) = W p
  same_null : ∀ p, W (G.same p) = 0

/-- End-to-end conditional reconstruction from the original additive monoid,
positive finite rejoin, complete two-port surjectivity and conserved readout. -/
theorem reconstruct (G : Gate V) (W : V → ℝ)
    (vacuum : W 0 = 0) (nonnegative : ∀ p, 0 ≤ W p)
    (conserve : ∀ x y,
      W (G.a x + G.b y) + W (G.b x + G.a y) = W x + W y) :
    Reconstruction G W := by
  have halves := half_responses G W vacuum nonnegative conserve
  have hp : ∀ x y : G.Carrier,
      W (x + y) + W (x - y) = 2 * W x + 2 * W y :=
    parallelogram_of_reversible_half_conservation (V := G.Carrier)
      G.a G.b G.inverseA G.inverseB
      G.inverseA_laws.1 G.inverseA_laws.2 G.inverseB_laws.1 G.inverseB_laws.2
      G.transparent G.onto W halves conserve
  have hq : PositiveQuadratic (fun p : G.Carrier => W p) := ⟨nonnegative, hp⟩
  have hcross : ∀ p, W (G.cross p) = W p := by
    intro p
    have ha := (halves (G.b p)).1
    have hb := (halves p).2
    have hd := hq.double (G.a (G.b p))
    change W (G.cross p) = 4 * W (G.a (G.b p)) at hd
    rw [hd]
    linarith
  have hsame : ∀ p, W (G.same p) = 0 := by
    intro p
    have h := conserve (G.a p) (G.b p)
    have hc : G.b (G.a p) = G.a (G.b p) := by
      have h' := congrArg (fun f : AddMonoid.End V => f p) G.commute.eq
      exact h'.symm
    rw [hc] at h
    change W (G.same p) + W (G.cross p) = W (G.a p) + W (G.b p) at h
    rw [hcross, (halves p).1, (halves p).2] at h
    linarith
  exact ⟨hq, halves, hcross, hsame⟩

namespace Reconstruction

variable {G : Gate V} {W : V → ℝ} (h : Reconstruction G W)

include h

/-- Evenness uses only the explicitly constructed additive inverse. -/
theorem even (p : G.Carrier) : W (-p) = W p := h.quadratic.even p

/-- Exact square gain for every natural count of the original addition. -/
theorem count_square (n : ℕ) (p : V) :
    W (n • p) = (n : ℝ) ^ 2 * W p := by
  have hz := PositiveQuadraticPolarization.quadratic_zsmul h.quadratic
    (n : ℤ) (p : G.Carrier)
  simpa using hz

/-- Exact square gain for integer repetition on the derived group. -/
theorem integer_square (n : ℤ) (p : G.Carrier) :
    W (n • p) = (n : ℝ) ^ 2 * W p :=
  PositiveQuadraticPolarization.quadratic_zsmul h.quadratic n p

/-- The algebraic third-order interference combination vanishes universally. -/
theorem third_order_zero (x y z : V) :
    W (x + y + z) - W (x + y) - W (x + z) - W (y + z) +
      W x + W y + W z = 0 :=
  OperationalQuadraticReconstruction.third_order_zero_of_parallelogram
    (fun p : G.Carrier => W p) h.quadratic.even h.quadratic.parallelogram x y z

/-- A zero-readout direction is invisible to every original additive translate. -/
theorem null_translate (x y : V) (hy : W y = 0) : W (x + y) = W x :=
  h.quadratic.null_translate x y hy

/-- The derived same-history coefficient is an invisible additive direction. -/
theorem same_translate (x p : V) : W (x + G.same p) = W x :=
  h.null_translate x (G.same p) (h.same_null p)

/-- The two native branch preparations have zero polarized cross term. -/
theorem branch_orthogonal (p : V) :
    PositiveQuadraticPolarization.polarization (fun q : G.Carrier => W q)
      (G.a p) (G.b p) = 0 := by
  have hsum : G.a p + G.b p = p :=
    congrArg (fun f : AddMonoid.End V => f p) G.transparent
  change (W (G.a p + G.b p) - W (G.a p) - W (G.b p)) / 2 = 0
  rw [hsum, (h.branch_halves p).1, (h.branch_halves p).2]
  ring

/-- Exact response for independent natural counts of the two prepared branches. -/
theorem prepared_count_weight (n m : ℕ) (p : V) :
    W (n • G.a p + m • G.b p) =
      (((n : ℝ) ^ 2 + (m : ℝ) ^ 2) / 2) * W p := by
  have hi := PositiveQuadraticPolarization.integer_coordinate_law h.quadratic
    (n : ℤ) (m : ℤ) (G.a p : G.Carrier) (G.b p : G.Carrier)
  have hi' : W (n • G.a p + m • G.b p) =
      (n : ℝ) ^ 2 * W (G.a p) + (m : ℝ) ^ 2 * W (G.b p) := by
    simpa [h.branch_orthogonal p] using hi
  rw [hi', (h.branch_halves p).1, (h.branch_halves p).2]
  ring

/-- Componentwise order of natural branch counts gives prepared readout order.
This is a conclusion of the reconstructed quadratic weight. -/
theorem prepared_count_order (n m r s : ℕ) (hn : n ≤ r) (hm : m ≤ s) (p : V) :
    W (n • G.a p + m • G.b p) ≤ W (r • G.a p + s • G.b p) := by
  simp only [h.prepared_count_weight]
  have hnr : (n : ℝ) ≤ (r : ℝ) := by exact_mod_cast hn
  have hms : (m : ℝ) ≤ (s : ℝ) := by exact_mod_cast hm
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hnprod : 0 ≤ ((r : ℝ) - (n : ℝ)) * ((r : ℝ) + (n : ℝ)) :=
    mul_nonneg (sub_nonneg.mpr hnr) (by linarith)
  have hmprod : 0 ≤ ((s : ℝ) - (m : ℝ)) * ((s : ℝ) + (m : ℝ)) :=
    mul_nonneg (sub_nonneg.mpr hms) (by linarith)
  have hweights : ((n : ℝ) ^ 2 + (m : ℝ) ^ 2) / 2 ≤
      ((r : ℝ) ^ 2 + (s : ℝ) ^ 2) / 2 := by
    nlinarith only [hnprod, hmprod]
  exact mul_le_mul_of_nonneg_right hweights (h.quadratic.nonnegative p)

end Reconstruction

end Reconstruction

end IDT.QMClosure.FiniteRejoinReversibleQuadraticReadout
