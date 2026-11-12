import Mathlib.Algebra.Group.Hom.End
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Pairing from a conserved additive two-port law

This is a conditional algebraic theorem about a full-domain two-port law.
The carrier is an additive commutative monoid. Both first-output branches are
surjective, and every first-axis output has a preimage whose second output is
zero. Conservation then makes the readout's second additive difference
independent of its base preparation.

The centered polarization is symmetric and biadditive. The remaining term is
additive and is retained explicitly. No additive group, carrier scalars,
topology, finite rejoin, positivity, or vacuum normalization is required for
this conclusion. The algebraic third-difference identity supplies no physical
identification with a Sorkin experiment or a Born rule.
-/

noncomputable section

namespace IDT.QMClosure.TwoPortConservationPairing

section Monoid

variable {V : Type*} [AddCommMonoid V]

/-- The second additive difference at a preparation. -/
def delta2 (W : V → ℝ) (z u v : V) : ℝ :=
  W (z + u + v) - W (z + u) - W (z + v) + W z

/-- Independence of the preparation used as the difference base. -/
def BaseIndependent (W : V → ℝ) : Prop :=
  ∀ z u v, delta2 W z u v = delta2 W 0 u v

/-- The complete, potentially asymmetric, additive two-port map. -/
def twoPort (A B C D : AddMonoid.End V) : (V × V) → (V × V) :=
  fun p => (A p.1 + B p.2, C p.1 + D p.2)

/-- Every first-axis output has a preimage. -/
def FirstAxisReachable (A B C D : AddMonoid.End V) : Prop :=
  ∀ z, ∃ x y, A x + B y = z ∧ C x + D y = 0

private theorem output_shift (E F : AddMonoid.End V) (x y h k : V) :
    E (x + h) + F (y + k) = (E x + F y) + E h + F k := by
  simp only [map_add, add_assoc, add_comm, add_left_comm]

/-- The mixed input difference cancels the separate input readouts. -/
theorem mixed_difference
    (A B C D : AddMonoid.End V) (W : V → ℝ)
    (conserve : ∀ x y,
      W (A x + B y) + W (C x + D y) = W x + W y)
    (x y h k : V) :
    delta2 W (A x + B y) (A h) (B k) +
      delta2 W (C x + D y) (C h) (D k) = 0 := by
  have h11 := conserve (x + h) (y + k)
  have h10 := conserve (x + h) (y + 0)
  have h01 := conserve (x + 0) (y + k)
  have h00 := conserve x y
  rw [output_shift A B x y h k, output_shift C D x y h k] at h11
  rw [output_shift A B x y h 0, output_shift C D x y h 0] at h10
  rw [output_shift A B x y 0 k, output_shift C D x y 0 k] at h01
  simp only [map_zero, add_zero] at h10 h01
  dsimp only [delta2]
  linarith only [h11, h10, h01, h00]

/-- Complete first-output branch coverage and first-axis reachability turn
full conservation into base-independent second differences. -/
theorem base_independent_of_conservation
    (A B C D : AddMonoid.End V)
    (ontoA : Function.Surjective A) (ontoB : Function.Surjective B)
    (axis : FirstAxisReachable A B C D)
    (W : V → ℝ)
    (conserve : ∀ x y,
      W (A x + B y) + W (C x + D y) = W x + W y) :
    BaseIndependent W := by
  intro z u v
  obtain ⟨h, hh⟩ := ontoA u
  obtain ⟨k, hk⟩ := ontoB v
  obtain ⟨x, y, hz, hzero⟩ := axis z
  have hzdelta := mixed_difference A B C D W conserve x y h k
  have hzero_delta := mixed_difference A B C D W conserve 0 0 h k
  rw [hz, hzero, hh, hk] at hzdelta
  simp only [map_zero, add_zero] at hzero_delta
  rw [hh, hk] at hzero_delta
  linarith only [hzdelta, hzero_delta]

/-- Surjectivity of the complete map supplies the first-axis hypothesis. -/
theorem first_axis_of_surjective
    (A B C D : AddMonoid.End V)
    (onto : Function.Surjective (twoPort A B C D)) :
    FirstAxisReachable A B C D := by
  intro z
  obtain ⟨⟨x, y⟩, h⟩ := onto (z, 0)
  exact ⟨x, y, congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- A wrapper for a surjective complete map, retaining both branch-coverage
hypotheses explicitly. -/
theorem base_independent_of_surjective_twoPort
    (A B C D : AddMonoid.End V)
    (ontoA : Function.Surjective A) (ontoB : Function.Surjective B)
    (onto : Function.Surjective (twoPort A B C D))
    (W : V → ℝ)
    (conserve : ∀ x y,
      W (A x + B y) + W (C x + D y) = W x + W y) :
    BaseIndependent W :=
  base_independent_of_conservation A B C D ontoA ontoB
    (first_axis_of_surjective A B C D onto) W conserve

/-- For a symmetric additive mixer, swapping and adding axis preimages
recovers a preimage of every output pair. -/
theorem symmetric_surjective_iff_first_axis (A B : AddMonoid.End V) :
    Function.Surjective (twoPort A B B A) ↔ FirstAxisReachable A B B A := by
  constructor
  · exact first_axis_of_surjective A B B A
  · intro axis
    rintro ⟨z, w⟩
    obtain ⟨x, y, hz, hzero⟩ := axis z
    obtain ⟨s, t, hw, hzero'⟩ := axis w
    refine ⟨(x + t, y + s), Prod.ext ?_ ?_⟩
    · change A (x + t) + B (y + s) = z
      calc
        A (x + t) + B (y + s) = (A x + B y) + (B s + A t) := by
          simp only [map_add, add_assoc, add_comm, add_left_comm]
        _ = z := by rw [hz, hzero', add_zero]
    · change B (x + t) + A (y + s) = w
      calc
        B (x + t) + A (y + s) = (B x + A y) + (A s + B t) := by
          simp only [map_add, add_assoc, add_comm, add_left_comm]
        _ = w := by rw [hzero, hw, zero_add]

/-- The seven-term algebraic third-order combination. -/
def i3 (W : V → ℝ) (x y z : V) : ℝ :=
  W (x + y + z) - W (x + y) - W (x + z) - W (y + z) + W x + W y + W z

/-- The vacuum offset is retained in the seven-term identity. -/
theorem i3_eq_vacuum (W : V → ℝ) (independent : BaseIndependent W)
    (x y z : V) : i3 W x y z = W 0 := by
  have h := independent z x y
  dsimp only [delta2] at h
  simp only [zero_add] at h
  have hxyz : z + x + y = x + y + z := by
    simp only [add_assoc, add_comm, add_left_comm]
  have hzx : z + x = x + z := add_comm _ _
  have hzy : z + y = y + z := add_comm _ _
  rw [hxyz, hzx, hzy] at h
  dsimp only [i3]
  linarith only [h]

/-- The eight-term third difference includes the vacuum contribution. -/
theorem third_difference_zero (W : V → ℝ) (independent : BaseIndependent W)
    (x y z : V) : i3 W x y z - W 0 = 0 := by
  rw [i3_eq_vacuum W independent, sub_self]

/-- Vacuum normalization specializes the algebraic third-order identity. -/
theorem i3_zero_of_vacuum (W : V → ℝ) (independent : BaseIndependent W)
    (vacuum : W 0 = 0) (x y z : V) : i3 W x y z = 0 := by
  rw [i3_eq_vacuum W independent, vacuum]

/-- Centered real polarization on the original additive monoid. -/
def polarization (W : V → ℝ) (u v : V) : ℝ :=
  (W (u + v) - W u - W v + W 0) / 2

private theorem polarization_eq_delta2 (W : V → ℝ) (u v : V) :
    polarization W u v = delta2 W 0 u v / 2 := by
  simp only [polarization, delta2, zero_add]

/-- The telescoping identity preceding use of base independence. -/
theorem delta2_add_left (W : V → ℝ) (u v w : V) :
    delta2 W 0 (u + v) w = delta2 W v u w + delta2 W 0 v w := by
  simp only [delta2, zero_add]
  simp only [add_comm v u]
  ring

namespace Polarization

variable (W : V → ℝ)

theorem symmetric (u v : V) : polarization W u v = polarization W v u := by
  simp only [polarization, add_comm u v]
  ring

theorem zero_left (v : V) : polarization W 0 v = 0 := by
  simp only [polarization, zero_add]
  ring

theorem zero_right (u : V) : polarization W u 0 = 0 := by
  rw [symmetric W u 0, zero_left W]

variable {W} (independent : BaseIndependent W)

include independent

theorem add_left (u v w : V) :
    polarization W (u + v) w = polarization W u w + polarization W v w := by
  simp only [polarization_eq_delta2]
  rw [delta2_add_left W u v w, independent v u w]
  ring

theorem add_right (u v w : V) :
    polarization W u (v + w) = polarization W u v + polarization W u w := by
  rw [symmetric W u (v + w), add_left independent,
    symmetric W v u, symmetric W w u]

/-- Each fixed second argument gives an additive real-valued map. -/
def leftAddHom (v : V) : V →+ ℝ where
  toFun := fun u => polarization W u v
  map_zero' := zero_left W v
  map_add' := fun u w => add_left independent u w v

/-- Each fixed first argument gives an additive real-valued map. -/
def rightAddHom (u : V) : V →+ ℝ where
  toFun := fun v => polarization W u v
  map_zero' := zero_right W u
  map_add' := fun v w => add_right independent u v w

end Polarization

/-- The additive remainder is retained in the decomposition. -/
def remainder (W : V → ℝ) (x : V) : ℝ :=
  W x - W 0 - polarization W x x

theorem remainder_zero (W : V → ℝ) : remainder W 0 = 0 := by
  simp only [remainder, Polarization.zero_left]
  ring

/-- Base independence gives an additive remainder. -/
theorem remainder_add (W : V → ℝ) (independent : BaseIndependent W) (x y : V) :
    remainder W (x + y) = remainder W x + remainder W y := by
  have hdiag : polarization W (x + y) (x + y) =
      polarization W x x + 2 * polarization W x y + polarization W y y := by
    simp only [Polarization.add_left independent, Polarization.add_right independent]
    rw [Polarization.symmetric W y x]
    ring
  have hsum : W (x + y) = W x + W y - W 0 + 2 * polarization W x y := by
    dsimp only [polarization]
    ring
  dsimp only [remainder]
  rw [hdiag, hsum]
  ring

/-- The remaining contribution packaged as an additive map. -/
def remainderHom (W : V → ℝ) (independent : BaseIndependent W) : V →+ ℝ where
  toFun := remainder W
  map_zero' := remainder_zero W
  map_add' := remainder_add W independent

/-- The exact decomposition retains its constant and additive contributions. -/
theorem readout_decomposition (W : V → ℝ) (x : V) :
    W x = W 0 + polarization W x x + remainder W x := by
  dsimp only [remainder]
  ring

/-- A constant readout is conserved by every two-port map. -/
theorem constant_conserved (A B C D : AddMonoid.End V) (c : ℝ) (x y : V) :
    (fun _ : V => c) (A x + B y) + (fun _ : V => c) (C x + D y) =
      (fun _ : V => c) x + (fun _ : V => c) y := rfl

/-- Seven-term interference of a constant readout is exactly its offset. -/
theorem constant_i3 (c : ℝ) (x y z : V) : i3 (fun _ : V => c) x y z = c := by
  dsimp only [i3]
  ring

end Monoid

namespace Controls

/-- A linear readout on a carrier with no additive inverses. -/
def natLinearReadout (n : ℕ) : ℝ := n

theorem nat_identity_surjective : Function.Surjective (1 : AddMonoid.End ℕ) := by
  intro n
  exact ⟨n, rfl⟩

theorem nat_zero_not_surjective : ¬ Function.Surjective (0 : AddMonoid.End ℕ) := by
  intro h
  obtain ⟨n, hn⟩ := h 1
  change (0 : ℕ) = 1 at hn
  exact Nat.zero_ne_one hn

/-- This minimal-contract model uses A=B=id and C=D=0. -/
theorem nat_linear_axis : FirstAxisReachable
    (1 : AddMonoid.End ℕ) 1 0 0 := by
  intro z
  refine ⟨0, z, ?_, ?_⟩ <;> simp

/-- The minimal-contract model has no preimage of an output with second port one. -/
theorem nat_linear_twoPort_not_surjective : ¬ Function.Surjective
    (twoPort (1 : AddMonoid.End ℕ) 1 0 0) := by
  intro onto
  obtain ⟨⟨x, y⟩, h⟩ := onto (0, 1)
  have hz : (0 : ℕ) = 1 := congrArg Prod.snd h
  exact Nat.zero_ne_one hz

theorem nat_linear_conserved (x y : ℕ) :
    natLinearReadout ((1 : AddMonoid.End ℕ) x + (1 : AddMonoid.End ℕ) y) +
      natLinearReadout ((0 : AddMonoid.End ℕ) x + (0 : AddMonoid.End ℕ) y) =
      natLinearReadout x + natLinearReadout y := by
  simp [natLinearReadout]

theorem nat_linear_base_independent : BaseIndependent natLinearReadout :=
  base_independent_of_conservation
    (1 : AddMonoid.End ℕ) 1 0 0 nat_identity_surjective nat_identity_surjective
    nat_linear_axis natLinearReadout nat_linear_conserved

theorem nat_linear_nonnegative (n : ℕ) : 0 ≤ natLinearReadout n := by
  change (0 : ℝ) ≤ (n : ℝ)
  exact_mod_cast Nat.zero_le n

theorem nat_linear_vacuum : natLinearReadout 0 = 0 := by
  simp only [natLinearReadout, Nat.cast_zero]

theorem nat_linear_polarization (x y : ℕ) :
    polarization natLinearReadout x y = 0 := by
  simp only [polarization, natLinearReadout, Nat.cast_add, Nat.cast_zero]
  ring

theorem nat_linear_remainder (x : ℕ) :
    remainder natLinearReadout x = natLinearReadout x := by
  simp only [remainder, nat_linear_polarization, nat_linear_vacuum, sub_zero]

theorem nat_linear_remainder_nonzero : remainder natLinearReadout 1 = 1 := by
  rw [nat_linear_remainder]
  norm_num [natLinearReadout]

/-- Positivity and vacuum zero preserve the additive remainder in this model. -/
theorem nat_linear_double_gain :
    natLinearReadout (1 + 1) = 2 ∧
      natLinearReadout (1 + 1) ≠ 4 * natLinearReadout 1 := by
  norm_num [natLinearReadout]

/-- A cubic readout supplies omission controls for the branch coverage. -/
def natCubicReadout (n : ℕ) : ℝ := (n : ℝ) ^ 3

theorem nat_cubic_i3 : i3 natCubicReadout 1 1 1 = 6 := by
  norm_num [i3, natCubicReadout]

theorem nat_cubic_not_base_independent : ¬ BaseIndependent natCubicReadout := by
  intro independent
  have h := i3_eq_vacuum natCubicReadout independent 1 1 1
  rw [nat_cubic_i3] at h
  norm_num [natCubicReadout] at h

/-- The identity complete map is onto, while its B branch is zero. -/
theorem identity_twoPort_surjective : Function.Surjective
    (twoPort (1 : AddMonoid.End ℕ) 0 0 1) := by
  rintro ⟨x, y⟩
  refine ⟨(x, y), ?_⟩
  simp [twoPort]

theorem identity_first_axis : FirstAxisReachable
    (1 : AddMonoid.End ℕ) 0 0 1 :=
  first_axis_of_surjective 1 0 0 1 identity_twoPort_surjective

theorem identity_conserved (W : ℕ → ℝ) (x y : ℕ) :
    W ((1 : AddMonoid.End ℕ) x + (0 : AddMonoid.End ℕ) y) +
      W ((0 : AddMonoid.End ℕ) x + (1 : AddMonoid.End ℕ) y) = W x + W y := by
  simp

/-- Port exchange is onto, while its A branch is zero. -/
theorem swap_twoPort_surjective : Function.Surjective
    (twoPort (0 : AddMonoid.End ℕ) 1 1 0) := by
  rintro ⟨x, y⟩
  refine ⟨(y, x), ?_⟩
  simp [twoPort]

theorem swap_first_axis : FirstAxisReachable
    (0 : AddMonoid.End ℕ) 1 1 0 :=
  first_axis_of_surjective 0 1 1 0 swap_twoPort_surjective

theorem swap_conserved (W : ℕ → ℝ) (x y : ℕ) :
    W ((0 : AddMonoid.End ℕ) x + (1 : AddMonoid.End ℕ) y) +
      W ((1 : AddMonoid.End ℕ) x + (0 : AddMonoid.End ℕ) y) = W x + W y := by
  simp [add_comm]

end Controls

end IDT.QMClosure.TwoPortConservationPairing
