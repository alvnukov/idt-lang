import Proofs.QMClosure.MultiplicativeMixtureReadout

/-!
# Fixed-corner equal-half pair congruence selects the integer Gaussian norm

For a real function on Gaussian integers, the four probes are prescribed as
translations of that same function by `(0,0)`, `(1,0)`, `(0,1)` and `(1,1)`.
The supplied continuation law preserves equal pair sums of these probe vectors
under each signed coordinate unit step. The readout is also supplied globally
Gaussian-multiplicative, calibrated by `f (2,0) = 4`, and nonnegative at `(1,1)`.

An elementary rectangle argument selects the squared integer norm. The proof
propagates one finite seed packet, separates the two coordinates and solves a
one-dimensional quadratic recurrence. Its reusable core requires the zero and
unit values, quarter-turn invariance and scaling by the diagonal generator.

The sign premise is sufficient. The negative-sign branch is left open here.
Global Gaussian multiplication, the real-valued readout, calibration, prescribed
probes and universal pair congruence remain supplied mathematical contracts.
Physical realization, normalized echo and Born/QM closure remain open.
-/

noncomputable section

namespace IDT.FixedCornerHalfMixtureReadout

open FiniteMixtureContinuationRank
open MultiplicativeMixtureReadout

/-- Equal pair sums are preserved by the supplied update. For real probe
vectors these are precisely the equal-half mean comparisons. -/
def PairCongruentUnder {S V : Type*} [Add V] (P : S → V) (T : S → S) : Prop :=
  ∀ a b c d, P a + P b = P c + P d → P (T a) + P (T b) = P (T c) + P (T d)

/-- All four coordinates are translates of the same real readout. -/
def fixedCornerProbes (f : IntegerLattice → ℝ) (z : IntegerLattice) (j : Fin 4) : ℝ :=
  f (z + normCorner j)

/-- One pair-sum equality propagates to every lattice translation using only
congruence under the four signed coordinate unit steps. -/
theorem translated_pair_sum_eq {V : Type*} [Add V]
    (P : IntegerLattice → V)
    (hlocal : ∀ j, PairCongruentUnder P (fun z => z + localStep j))
    {a b c d : IntegerLattice} (hseed : P a + P b = P c + P d)
    (t : IntegerLattice) :
    P (a + t) + P (b + t) = P (c + t) + P (d + t) := by
  have hx (m : ℤ) :
      P (a + (m, 0)) + P (b + (m, 0)) =
        P (c + (m, 0)) + P (d + (m, 0)) := by
    induction m using Int.induction_on with
    | zero =>
        simpa only [show ((0, 0) : IntegerLattice) = 0 from rfl, add_zero] using hseed
    | succ n ih =>
        have h := hlocal 0 (a + ((n : ℤ), 0)) (b + ((n : ℤ), 0))
          (c + ((n : ℤ), 0)) (d + ((n : ℤ), 0)) ih
        simpa [localStep, Matrix.cons_val_two, Matrix.cons_val_three, add_assoc] using h
    | pred n ih =>
        have h := hlocal 1 (a + (-(n : ℤ), 0)) (b + (-(n : ℤ), 0))
          (c + (-(n : ℤ), 0)) (d + (-(n : ℤ), 0)) ih
        simpa [localStep, Matrix.cons_val_two, Matrix.cons_val_three, sub_eq_add_neg, add_assoc] using h
  have hxy (m n : ℤ) :
      P (a + (m, n)) + P (b + (m, n)) =
        P (c + (m, n)) + P (d + (m, n)) := by
    induction n using Int.induction_on with
    | zero => exact hx m
    | succ n ih =>
        have h := hlocal 2 (a + (m, (n : ℤ))) (b + (m, (n : ℤ)))
          (c + (m, (n : ℤ))) (d + (m, (n : ℤ))) ih
        simpa [localStep, Matrix.cons_val_two, Matrix.cons_val_three, add_assoc] using h
    | pred n ih =>
        have h := hlocal 3 (a + (m, -(n : ℤ))) (b + (m, -(n : ℤ)))
          (c + (m, -(n : ℤ))) (d + (m, -(n : ℤ))) ih
        simpa [localStep, Matrix.cons_val_two, Matrix.cons_val_three, sub_eq_add_neg, add_assoc] using h
  exact hxy t.1 t.2

/-- The rectangle packet requires only its seed and local pair congruence. -/
theorem rectangle_packet_of_seed {V : Type*} [Add V]
    (P : IntegerLattice → V)
    (hlocal : ∀ j, PairCongruentUnder P (fun z => z + localStep j))
    (hseed : P (0, 0) + P (-1, -1) = P (-1, 0) + P (0, -1))
    (z : IntegerLattice) :
    P z + P (z - (1, 1)) = P (z - (1, 0)) + P (z - (0, 1)) := by
  have h := translated_pair_sum_eq P hlocal hseed z
  change P z + P (z + (-1, -1)) = P (z + (-1, 0)) + P (z + (0, -1))
  simpa only [show ((0, 0) : IntegerLattice) = 0 from rfl, zero_add, add_zero, add_comm] using h

/-- A successor-invariant function on all integers is constant. -/
theorem integer_successor_invariant_constant (h : ℤ → ℝ)
    (hstep : ∀ n, h (n + 1) = h n) (n : ℤ) : h n = h 0 := by
  induction n using Int.induction_on with
  | zero => rfl
  | succ n ih => exact (hstep n).trans ih
  | pred n ih =>
      have hn : -(n : ℤ) - 1 + 1 = -(n : ℤ) := by ring
      have hback := hstep (-(n : ℤ) - 1)
      rw [hn] at hback
      exact hback.symm.trans ih

/-- Vanishing adjacent rectangle differences separate the two integer
coordinates, with the value at the origin as the overlap correction. -/
theorem integer_rectangle_separates (F : ℤ → ℤ → ℝ)
    (hrect : ∀ a b, F (a + 1) (b + 1) + F a b = F (a + 1) b + F a (b + 1))
    (a b : ℤ) : F a b = F a 0 + F 0 b - F 0 0 := by
  have hvertical (x y : ℤ) :
      F x (y + 1) - F x y = F 0 (y + 1) - F 0 y := by
    apply integer_successor_invariant_constant (fun n => F n (y + 1) - F n y)
    intro n
    have h := hrect n y
    linarith
  have hhorizontal : ∀ n, F a (n + 1) - F 0 (n + 1) = F a n - F 0 n := by
    intro n
    have h := hvertical a n
    linarith
  have h := integer_successor_invariant_constant
    (fun n => F a n - F 0 n) hhorizontal b
  linarith

/-- Two quarter turns give negation invariance for an arbitrary readout. -/
theorem negation_invariant_of_rotation (f : IntegerLattice → ℝ)
    (hrot : ∀ z, f (FiniteTranslationSmallRankSupport.turn z) = f z)
    (z : IntegerLattice) : f (-z) = f z := by
  have h := (hrot (FiniteTranslationSmallRankSupport.turn z)).trans (hrot z)
  simpa [FiniteTranslationSmallRankSupport.turn] using h

/-- Unit calibration, quarter-turn invariance and the diagonal value provide
the finite seed directly, independently of multiplicativity. -/
theorem corner_seed_of_rotation (f : IntegerLattice → ℝ)
    (hzero : f (0, 0) = 0) (hunit : f (1, 0) = 1)
    (hrot : ∀ z, f (FiniteTranslationSmallRankSupport.turn z) = f z)
    (htwo : f (1, 1) = 2) :
    fixedCornerProbes f (0, 0) + fixedCornerProbes f (-1, -1) =
      fixedCornerProbes f (-1, 0) + fixedCornerProbes f (0, -1) := by
  have hi : f (0, 1) = 1 := by
    simpa [FiniteTranslationSmallRankSupport.turn, hunit] using hrot (1, 0)
  have hn : f (-1, 0) = 1 := by
    simpa [hunit] using negation_invariant_of_rotation f hrot (1, 0)
  have hni : f (0, -1) = 1 := by
    simpa [hi] using negation_invariant_of_rotation f hrot (0, 1)
  have hdiag : f (-1, -1) = 2 := by
    simpa [htwo] using negation_invariant_of_rotation f hrot (1, 1)
  have hleft : f (-1, 1) = 2 := by
    simpa [FiniteTranslationSmallRankSupport.turn, htwo] using hrot (1, 1)
  have hright : f (1, -1) = 2 := by
    have h := hrot (1, -1)
    simpa [FiniteTranslationSmallRankSupport.turn, htwo] using h.symm
  funext j
  fin_cases j <;>
    norm_num [fixedCornerProbes, normCorner, hzero, hunit, hi, hn, hni,
      hdiag, hleft, hright, htwo]

section Calibration

variable (f : IntegerLattice → ℝ)
variable (hmul : GaussianMultiplicative f) (hcal : f (2, 0) = 4)

include hmul hcal

/-- The nonzero calibration forces the zero readout to vanish. -/
theorem zero_readout_eq_zero : f (0, 0) = 0 := by
  have h := hmul (2, 0) (0, 0)
  norm_num [gaussianMul] at h
  rw [hcal] at h
  linarith

/-- Multiplication by negative one leaves the raw readout invariant. -/
theorem negation_invariant (z : IntegerLattice) : f (-z) = f z := by
  have hnegative := negative_unit_readout_eq_one f hmul hcal
  have h := hmul (-1, 0) z
  simpa [gaussianMul, hnegative] using h

/-- The remaining Gaussian unit also reads one. -/
theorem negative_imaginary_unit_readout_eq_one : f (0, -1) = 1 := by
  have h := negation_invariant f hmul hcal (0, 1)
  simpa [imaginary_unit_readout_eq_one f hmul hcal] using h

/-- The sole sign premise at `(1,1)` selects its positive quadratic root. -/
theorem diagonal_readout_eq_two (hsign : 0 ≤ f (1, 1)) : f (1, 1) = 2 := by
  have hi := imaginary_unit_readout_eq_one f hmul hcal
  have hsquare := hmul (1, 1) (1, 1)
  norm_num [gaussianMul] at hsquare
  have hdouble := hmul (2, 0) (0, 1)
  norm_num [gaussianMul] at hdouble
  rw [hcal, hi] at hdouble
  have hfactor : (f (1, 1) - 2) * (f (1, 1) + 2) = 0 := by
    nlinarith [hsquare, hdouble]
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith
  · linarith

/-- The finite seed equality is equivalent to the diagonal reading two under
multiplicativity and calibration. This statement classifies the seed itself. -/
theorem corner_seed_iff_diagonal_eq_two :
    (fixedCornerProbes f (0, 0) + fixedCornerProbes f (-1, -1) =
      fixedCornerProbes f (-1, 0) + fixedCornerProbes f (0, -1)) ↔ f (1, 1) = 2 := by
  have hz := zero_readout_eq_zero f hmul hcal
  have hu := unit_readout_eq_one f hmul hcal
  have hn := negative_unit_readout_eq_one f hmul hcal
  have hni := negative_imaginary_unit_readout_eq_one f hmul hcal
  have hdiag : f (-1, -1) = f (1, 1) := by
    simpa using negation_invariant f hmul hcal (1, 1)
  constructor
  · intro hseed
    have h := congrFun hseed 0
    norm_num [fixedCornerProbes, normCorner, hz, hn, hni, hdiag] at h
    exact h
  · intro htwo
    exact corner_seed_of_rotation f hz hu (quarter_turn_invariant f hmul hcal) htwo

end Calibration

section GeneratorSelection

variable (f : IntegerLattice → ℝ)
variable (hlocal : ∀ j, PairCongruentUnder (fixedCornerProbes f)
  (fun z => z + localStep j))
variable (hzero : f (0, 0) = 0) (hunit : f (1, 0) = 1)
variable (hrot : ∀ z, f (FiniteTranslationSmallRankSupport.turn z) = f z)
variable (hdiagonal : ∀ z, f (gaussianMul (1, 1) z) = 2 * f z)

include hlocal hzero hunit hrot hdiagonal

/-- The propagated seed yields every adjacent scalar rectangle identity. -/
theorem readout_rectangle (a b : ℤ) :
    f (a + 1, b + 1) + f (a, b) = f (a + 1, b) + f (a, b + 1) := by
  have htwo : f (1, 1) = 2 := by
    simpa [gaussianMul, hunit] using hdiagonal (1, 0)
  have hseed := corner_seed_of_rotation f hzero hunit hrot htwo
  have hpacket := rectangle_packet_of_seed (fixedCornerProbes f) hlocal hseed
    (a + 1, b + 1)
  have h := congrFun hpacket 0
  simpa [fixedCornerProbes, normCorner, add_comm] using h

/-- The readout is the sum of its two axis responses. -/
theorem readout_separates (a b : ℤ) : f (a, b) = f (a, 0) + f (b, 0) := by
  have hsep := integer_rectangle_separates (fun x y => f (x, y))
    (readout_rectangle f hlocal hzero hunit hrot hdiagonal) a b
  have haxis : f (0, b) = f (b, 0) := by
    simpa [FiniteTranslationSmallRankSupport.turn] using hrot (b, 0)
  simpa [hzero, haxis] using hsep

/-- Diagonal generator scaling supplies the one-dimensional parallelogram law. -/
theorem axis_parallelogram (a b : ℤ) :
    f (a + b, 0) + f (a - b, 0) = 2 * f (a, 0) + 2 * f (b, 0) := by
  have hsepleft := readout_separates f hlocal hzero hunit hrot hdiagonal
    (a - b) (a + b)
  have hsepright := readout_separates f hlocal hzero hunit hrot hdiagonal a b
  have hproduct : f (a - b, a + b) = 2 * f (a, b) := by
    simpa [gaussianMul, add_comm] using hdiagonal (a, b)
  rw [hsepleft, hsepright] at hproduct
  linarith

end GeneratorSelection

/-- The integer quadratic recurrence, unit calibration and evenness determine
all integer values. The natural-number induction carries two adjacent values. -/
theorem integer_quadratic_recurrence (g : ℤ → ℝ)
    (hzero : g 0 = 0) (hone : g 1 = 1)
    (heven : ∀ n, g (-n) = g n)
    (hrec : ∀ n, g (n + 1) + g (n - 1) = 2 * g n + 2)
    (n : ℤ) : g n = (n : ℝ) ^ 2 := by
  have hnat (k : ℕ) :
      g (k : ℤ) = (k : ℝ) ^ 2 ∧ g ((k : ℤ) + 1) = ((k : ℝ) + 1) ^ 2 := by
    induction k with
    | zero => norm_num [hzero, hone]
    | succ k ih =>
        constructor
        · simpa only [Nat.cast_succ] using ih.2
        · have h := hrec ((k : ℤ) + 1)
          simp only [add_sub_cancel_right] at h
          rw [ih.1, ih.2] at h
          simp only [Nat.cast_succ]
          nlinarith [h]
  cases n with
  | ofNat k => exact (hnat k).1
  | negSucc k =>
      have hn : Int.negSucc k = -((k : ℤ) + 1) := by omega
      rw [hn]
      have h := (heven ((k : ℤ) + 1)).trans (hnat k).2
      simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
        neg_sq] using h

/-- The elementary core uses only zero/unit values, quarter-turn invariance
and diagonal generator scaling, together with fixed-corner pair congruence. -/
theorem fixed_corner_readout_eq_norm_of_generator_laws (f : IntegerLattice → ℝ)
    (hlocal : ∀ j, PairCongruentUnder (fixedCornerProbes f)
      (fun z => z + localStep j))
    (hzero : f (0, 0) = 0) (hunit : f (1, 0) = 1)
    (hrot : ∀ z, f (FiniteTranslationSmallRankSupport.turn z) = f z)
    (hdiagonal : ∀ z, f (gaussianMul (1, 1) z) = 2 * f z)
    (z : IntegerLattice) : f z = (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 := by
  have heven (n : ℤ) : f (-n, 0) = f (n, 0) := by
    simpa using negation_invariant_of_rotation f hrot (n, 0)
  have hrec (n : ℤ) : f (n + 1, 0) + f (n - 1, 0) = 2 * f (n, 0) + 2 := by
    simpa [hunit] using axis_parallelogram f hlocal hzero hunit hrot hdiagonal n 1
  have haxis (n : ℤ) : f (n, 0) = (n : ℝ) ^ 2 :=
    integer_quadratic_recurrence (fun n => f (n, 0)) hzero hunit heven hrec n
  rw [readout_separates f hlocal hzero hunit hrot hdiagonal z.1 z.2, haxis, haxis]

/-- Fixed translated probes, four local equal-half pair congruences, global
Gaussian multiplicativity, `f (2,0)=4` and one native sign select the integer norm. -/
theorem fixed_corner_readout_eq_norm (f : IntegerLattice → ℝ)
    (hlocal : ∀ j, PairCongruentUnder (fixedCornerProbes f)
      (fun z => z + localStep j))
    (hmul : GaussianMultiplicative f) (hcal : f (2, 0) = 4)
    (hsign : 0 ≤ f (1, 1)) (z : IntegerLattice) :
    f z = (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 := by
  have htwo := diagonal_readout_eq_two f hmul hcal hsign
  have hdiagonal (w : IntegerLattice) : f (gaussianMul (1, 1) w) = 2 * f w := by
    simpa [htwo] using hmul (1, 1) w
  exact fixed_corner_readout_eq_norm_of_generator_laws f hlocal
    (zero_readout_eq_zero f hmul hcal) (unit_readout_eq_one f hmul hcal)
    (quarter_turn_invariant f hmul hcal) hdiagonal z

section ConcreteWitness

/-- The concrete norm probes preserve equal pair sums under every lattice
translation. This proof uses only their existing explicit affine identity. -/
theorem normReadout_pairCongruent_translation (t : IntegerLattice) :
    PairCongruentUnder (fixedCornerProbes normReadout) (fun z => z + t) := by
  intro a b c d hpair
  have hcoordinate (j : Fin 4) :
      normProbes a j + normProbes b j = normProbes c j + normProbes d j :=
    congrFun hpair j
  have hzero := hcoordinate 0
  have hone := hcoordinate 1
  have htwo := hcoordinate 2
  funext j
  change normReadout ((a + t) + normCorner j) +
    normReadout ((b + t) + normCorner j) =
      normReadout ((c + t) + normCorner j) + normReadout ((d + t) + normCorner j)
  simp only [add_assoc]
  let q := t + normCorner j
  change normReadout (a + q) + normReadout (b + q) =
    normReadout (c + q) + normReadout (d + q)
  rw [normReadout_translate_eq a q, normReadout_translate_eq b q,
    normReadout_translate_eq c q, normReadout_translate_eq d q]
  linear_combination (1 - (q.1 : ℝ) - (q.2 : ℝ)) * hzero +
    (q.1 : ℝ) * hone + (q.2 : ℝ) * htwo

/-- The concrete squared norm satisfies exactly the supplied selection contract. -/
theorem normReadout_contract :
    (∀ j, PairCongruentUnder (fixedCornerProbes normReadout)
      (fun z => z + localStep j)) ∧
      GaussianMultiplicative normReadout ∧ normReadout (2, 0) = 4 ∧
      0 ≤ normReadout (1, 1) := by
  refine ⟨fun j => normReadout_pairCongruent_translation (localStep j),
    normReadout_gaussianMultiplicative, ?_, ?_⟩
  · norm_num [normReadout]
  · norm_num [normReadout]

/-- The mathematical selection contract has a concrete inhabitant. -/
theorem exists_fixed_corner_contract :
    ∃ f : IntegerLattice → ℝ,
      (∀ j, PairCongruentUnder (fixedCornerProbes f)
        (fun z => z + localStep j)) ∧
        GaussianMultiplicative f ∧ f (2, 0) = 4 ∧ 0 ≤ f (1, 1) :=
  ⟨normReadout, normReadout_contract⟩

end ConcreteWitness

end IDT.FixedCornerHalfMixtureReadout
