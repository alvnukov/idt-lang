import Proofs.QMClosure.PreparationDisturbanceTradeoff

namespace IDT.QMClosure.QuadraticRecordRefinement

open PreparationRecordObstruction PreparationDisturbanceTradeoff

noncomputable section

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

/-!
Recordwise positivity and the real parallelogram law are supplied hypotheses.
They are stronger than conservation of a total readout. No scalar structure,
topology, quarter-phase covariance, instrument, or probability actualization
is established here.
-/

variable {U : Type*} [AddCommGroup U]

/-- Minimal real quadratic-weight assumptions on an additive group. -/
structure PositiveQuadratic (Q : U → ℝ) : Prop where
  nonnegative : ∀ u, 0 ≤ Q u
  parallelogram : ∀ u v, Q (u + v) + Q (u - v) = 2 * Q u + 2 * Q v

namespace PositiveQuadratic

variable {Q : U → ℝ} (h : PositiveQuadratic Q)

include h

theorem zero : Q 0 = 0 := by
  have hp := h.parallelogram 0 0
  simp only [add_zero, sub_zero] at hp
  linarith

theorem even (u : U) : Q (-u) = Q u := by
  have hp := h.parallelogram 0 u
  simp only [zero_add, zero_sub, h.zero] at hp
  linarith

theorem double (u : U) : Q (u + u) = 4 * Q u := by
  have hp := h.parallelogram u u
  simp only [sub_self, h.zero] at hp
  linarith

theorem add {R : U → ℝ} (hR : PositiveQuadratic R) :
    PositiveQuadratic (fun u => Q u + R u) := by
  constructor
  · intro u
    exact add_nonneg (h.nonnegative u) (hR.nonnegative u)
  · intro u v
    have hp := h.parallelogram u v
    have hr := hR.parallelogram u v
    linarith

/-- A zero-weight direction gives an arithmetic progression on its translates. -/
theorem null_progression (u v : U) (hv : Q v = 0) (n : ℕ) :
    Q (u + n • v) = Q u + (n : ℝ) * (Q (u + v) - Q u) := by
  have hpairs : ∀ n : ℕ,
      Q (u + n • v) = Q u + (n : ℝ) * (Q (u + v) - Q u) ∧
      Q (u + (n + 1) • v) = Q u + ((n + 1 : ℕ) : ℝ) * (Q (u + v) - Q u) := by
    intro n
    induction n with
    | zero => simp
    | succ n hn =>
      refine ⟨hn.2, ?_⟩
      have hp := h.parallelogram (u + (n + 1) • v) v
      have ha : u + (n + 1) • v + v = u + (n + 1 + 1) • v := by
        simp only [add_nsmul, one_nsmul]
        abel
      have hs : u + (n + 1) • v - v = u + n • v := by
        simp only [add_nsmul, one_nsmul]
        abel
      rw [ha, hs, hv, hn.1, hn.2] at hp
      push_cast at hp ⊢
      linarith
  exact (hpairs n).1

/-- Positivity on all integer translates kills the arithmetic-progression slope. -/
theorem null_translate (u v : U) (hv : Q v = 0) : Q (u + v) = Q u := by
  have lower (w : U) (hw : Q w = 0) : Q u ≤ Q (u + w) := by
    by_contra hh
    have hd : 0 < Q u - Q (u + w) := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (Q u / (Q u - Q (u + w)))
    have hn' : Q u < (n : ℝ) * (Q u - Q (u + w)) :=
      (div_lt_iff₀ hd).mp hn
    have hp := h.nonnegative (u + n • w)
    rw [h.null_progression u w hw n] at hp
    nlinarith
  have hp := h.parallelogram u v
  have hm : Q (-v) = 0 := by rw [h.even, hv]
  have hl := lower v hv
  have hr := lower (-v) hm
  simp only [sub_eq_add_neg] at hp
  rw [hv] at hp
  linarith

end PositiveQuadratic

/-- Preparation and record order are 00, 01, 10, 11. -/
def preparations (E F : U) : Fin 4 → U :=
  ![E + E + F, E + E - F, E + (F + F), E - (F + F)]

/-- Calibration needs only these four preparation points. -/
theorem calibration_null_directions (E F : U) (κ : ℝ)
    (f : Fin 4 → U → ℝ) (hq : ∀ r, PositiveQuadratic (f r))
    (μ : Fin 4 → Fin 4 → ℝ) (law : ProbabilityFamily μ)
    (hreal : ∀ a r, f r (preparations E F a) = 5 * κ * μ a r)
    (hfirst : ∀ a, marginal μ recordZ a = targetZ a) :
    f 0 F = 0 ∧ f 1 F = 0 ∧ f 2 E = 0 ∧ f 3 E = 0 := by
  let Q : U → ℝ := fun u => f 0 u + f 1 u
  let R : U → ℝ := fun u => f 2 u + f 3 u
  have hQ : PositiveQuadratic Q := (hq 0).add (hq 1)
  have hR : PositiveQuadratic R := (hq 2).add (hq 3)
  have hz (a : Fin 4) : Q (preparations E F a) = 5 * κ * targetZ a := by
    have hc := hfirst a
    norm_num [marginal, recordZ, Fin.sum_univ_succ] at hc
    dsimp [Q]
    rw [hreal a 0, hreal a 1, ← mul_add, hc]
  have hr (a : Fin 4) : R (preparations E F a) = 5 * κ * (1 - targetZ a) := by
    have hn := law.normalized a
    have hc := hfirst a
    norm_num [marginal, recordZ, Fin.sum_univ_succ] at hc
    norm_num [Fin.sum_univ_succ] at hn
    dsimp [R]
    change μ a 0 + (μ a 1 + (μ a 2 + μ a 3)) = 1 at hn
    have hc' : μ a 2 + μ a 3 = 1 - targetZ a := by linarith
    rw [hreal a 2, hreal a 3, ← mul_add, hc']
  have hq0 := hz 0
  have hq1 := hz 1
  have hq2 := hz 2
  have hq3 := hz 3
  have hr0 := hr 0
  have hr1 := hr 1
  have hr2 := hr 2
  have hr3 := hr 3
  norm_num [preparations, targetZ] at hq0 hq1 hq2 hq3 hr0 hr1 hr2 hr3
  have hqp := hQ.parallelogram (E + E) F
  have hqq := hQ.parallelogram E (F + F)
  have hrp := hR.parallelogram (E + E) F
  have hrq := hR.parallelogram E (F + F)
  rw [hQ.double E] at hqp
  rw [hQ.double F] at hqq
  rw [hR.double E] at hrp
  rw [hR.double F] at hrq
  have hQF : Q F = 0 := by linarith
  have hRE : R E = 0 := by linarith
  have h0 := (hq 0).nonnegative F
  have h1 := (hq 1).nonnegative F
  have h2 := (hq 2).nonnegative E
  have h3 := (hq 3).nonnegative E
  dsimp [Q] at hQF
  dsimp [R] at hRE
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem paired_preparations_of_null_right {Q : U → ℝ} (h : PositiveQuadratic Q)
    (E F : U) (hF : Q F = 0) :
    Q (preparations E F 0) = Q (preparations E F 1) ∧
    Q (preparations E F 2) = Q (preparations E F 3) := by
  have hn : Q (-F) = 0 := by rw [h.even, hF]
  have hd : Q (F + F) = 0 := by rw [h.double, hF]; ring
  have hdn : Q (-(F + F)) = 0 := by rw [h.even, hd]
  constructor
  · simpa [preparations, sub_eq_add_neg] using
      (h.null_translate (E + E) F hF).trans (h.null_translate (E + E) (-F) hn).symm
  · simpa [preparations, sub_eq_add_neg] using
      (h.null_translate E (F + F) hd).trans (h.null_translate E (-(F + F)) hdn).symm

theorem paired_preparations_of_null_left {Q : U → ℝ} (h : PositiveQuadratic Q)
    (E F : U) (hE : Q E = 0) :
    Q (preparations E F 0) = Q (preparations E F 1) ∧
    Q (preparations E F 2) = Q (preparations E F 3) := by
  have hd : Q (E + E) = 0 := by rw [h.double, hE]; ring
  have hp : Q (E + E + F) = Q F := by
    simpa [add_comm] using h.null_translate F (E + E) hd
  have hm : Q (E + E - F) = Q F := by
    have ht := h.null_translate (-F) (E + E) hd
    simpa [sub_eq_add_neg, add_comm, h.even] using ht
  have hpp : Q (E + (F + F)) = Q (F + F) := by
    simpa [add_comm] using h.null_translate (F + F) E hE
  have hmm : Q (E - (F + F)) = Q (F + F) := by
    have ht := h.null_translate (-(F + F)) E hE
    rw [h.even] at ht
    simpa [sub_eq_add_neg, add_comm] using ht
  exact ⟨by simpa [preparations] using hp.trans hm.symm,
    by simpa [preparations] using hpp.trans hmm.symm⟩

/-- Full record laws coincide in each opposite-X preparation pair. -/
theorem calibrated_paired_laws (E F : U) (κ : ℝ) (hκ : 0 < κ)
    (f : Fin 4 → U → ℝ) (hq : ∀ r, PositiveQuadratic (f r))
    (μ : Fin 4 → Fin 4 → ℝ) (law : ProbabilityFamily μ)
    (hreal : ∀ a r, f r (preparations E F a) = 5 * κ * μ a r)
    (hfirst : ∀ a, marginal μ recordZ a = targetZ a) :
    (∀ r, μ 0 r = μ 1 r) ∧ (∀ r, μ 2 r = μ 3 r) := by
  obtain ⟨h0, h1, h2, h3⟩ := calibration_null_directions E F κ f hq μ law hreal hfirst
  have hp (r : Fin 4) :
      f r (preparations E F 0) = f r (preparations E F 1) ∧
      f r (preparations E F 2) = f r (preparations E F 3) := by
    fin_cases r
    · exact paired_preparations_of_null_right (hq 0) E F h0
    · exact paired_preparations_of_null_right (hq 1) E F h1
    · exact paired_preparations_of_null_left (hq 2) E F h2
    · exact paired_preparations_of_null_left (hq 3) E F h3
  constructor <;> intro r
  · have hh := (hp r).1
    rw [hreal 0 r, hreal 1 r] at hh
    nlinarith
  · have hh := (hp r).2
    rw [hreal 2 r, hreal 3 r] at hh
    nlinarith

/-- Equal paired laws force a fair second score and an exact target-score gap. -/
theorem paired_laws_second_score (μ : Fin 4 → Fin 4 → ℝ)
    (hp : (∀ r, μ 0 r = μ 1 r) ∧ (∀ r, μ 2 r = μ 3 r)) :
    secondSuccess μ = 1 / 2 ∧ standaloneXTargetSuccess - secondSuccess μ = 2 / 5 := by
  have hm0 : marginal μ recordX 0 = marginal μ recordX 1 := by
    unfold marginal
    simp only [hp.1]
  have hm2 : marginal μ recordX 2 = marginal μ recordX 3 := by
    unfold marginal
    simp only [hp.2]
  have hs : secondSuccess μ = 1 / 2 := by
    unfold secondSuccess
    rw [hm0, hm2]
    ring
  exact ⟨hs, by rw [standaloneXTargetSuccess_eq, hs]; norm_num⟩

theorem paired_laws_second_error (μ : Fin 4 → Fin 4 → ℝ)
    (hp : (∀ r, μ 0 r = μ 1 r) ∧ (∀ r, μ 2 r = μ 3 r)) :
    2 / 5 ≤ meanMarginalError μ recordX targetX := by
  have hm0 : marginal μ recordX 0 = marginal μ recordX 1 := by
    unfold marginal
    simp only [hp.1]
  have hm2 : marginal μ recordX 2 = marginal μ recordX 3 := by
    unfold marginal
    simp only [hp.2]
  have h0 := neg_le_abs (marginal μ recordX 0 - targetX 0)
  have h1 := le_abs_self (marginal μ recordX 1 - targetX 1)
  have h2 := neg_le_abs (marginal μ recordX 2 - targetX 2)
  have h3 := le_abs_self (marginal μ recordX 3 - targetX 3)
  norm_num [targetX] at h0 h1 h2 h3
  unfold meanMarginalError
  norm_num [Fin.sum_univ_succ, targetX]
  have hlast : (2 : Fin 3).succ = (3 : Fin 4) := rfl
  simp only [hlast]
  linarith

/-- The strengthened conditional bound requires no parity-equivalence premise. -/
theorem calibrated_second_record_bound (E F : U) (κ : ℝ) (hκ : 0 < κ)
    (f : Fin 4 → U → ℝ) (hq : ∀ r, PositiveQuadratic (f r))
    (μ : Fin 4 → Fin 4 → ℝ) (law : ProbabilityFamily μ)
    (hreal : ∀ a r, f r (preparations E F a) = 5 * κ * μ a r)
    (hfirst : ∀ a, marginal μ recordZ a = targetZ a) :
    secondSuccess μ = 1 / 2 ∧
    standaloneXTargetSuccess - secondSuccess μ = 2 / 5 ∧
    2 / 5 ≤ meanMarginalError μ recordX targetX := by
  have hp := calibrated_paired_laws E F κ hκ f hq μ law hreal hfirst
  exact ⟨(paired_laws_second_score μ hp).1, (paired_laws_second_score μ hp).2,
    paired_laws_second_error μ hp⟩

/-- Null directions form a subgroup, with no scalar structure on the carrier. -/
def PositiveQuadratic.nullSubgroup {Q : U → ℝ} (h : PositiveQuadratic Q) :
    AddSubgroup U where
  carrier := {u | Q u = 0}
  zero_mem' := h.zero
  add_mem' := by
    intro u v hu hv
    change Q (u + v) = 0
    rw [h.null_translate u v hv, hu]
  neg_mem' := by
    intro u hu
    change Q (-u) = 0
    rw [h.even, hu]

/-- Global coarse domination is sufficient for forgetting a null factor. -/
theorem dominated_product_forgets_second {V : Type*} [AddCommGroup V]
    {Q : V × V → ℝ} (h : PositiveQuadratic Q) (W : V → ℝ)
    (hW0 : W 0 = 0) (hdom : ∀ x y, Q (x, y) ≤ W x) (x y : V) :
    Q (x, y) = Q (x, 0) := by
  have hn : Q (0, y) = 0 := by
    have hd := hdom 0 y
    rw [hW0] at hd
    exact le_antisymm hd (h.nonnegative (0, y))
  simpa using h.null_translate (x, 0) (0, y) hn

/-- The disturbed endpoint's first record forces a negative extension value. -/
theorem negative_extension_of_disturbed_values (E F : U) (κ : ℝ) (Q : U → ℝ)
    (hp : ∀ u v, Q (u + v) + Q (u - v) = 2 * Q u + 2 * Q v)
    (h00 : Q (E + E + F) = 5 * κ / 2)
    (h01 : Q (E + E - F) = 3 * κ / 2)
    (h10 : Q (E + (F + F)) = κ)
    (h11 : Q (E - (F + F)) = 0) :
    Q (E - (F + F + F)) = -κ / 4 := by
  have hz : Q 0 = 0 := by
    have hh := hp 0 0
    simp only [add_zero, sub_zero] at hh
    linarith
  have hd (u : U) : Q (u + u) = 4 * Q u := by
    have hh := hp u u
    simp only [sub_self, hz] at hh
    linarith
  have ha := hp (E + E) F
  have hb := hp E (F + F)
  rw [hd E, h00, h01] at ha
  rw [hd F, h10, h11] at hb
  have hE : Q E = κ / 2 := by linarith
  have hF : Q F = 0 := by linarith
  have hc := hp (E - F) F
  have hc1 : E - F + F = E := by abel
  have hc2 : E - F - F = E - (F + F) := by abel
  rw [hc1, hc2, hE, h11, hF] at hc
  have hEF : Q (E - F) = κ / 4 := by linarith
  have he := hp (E - (F + F)) F
  have he1 : E - (F + F) + F = E - F := by abel
  have he2 : E - (F + F) - F = E - (F + F + F) := by abel
  rw [he1, he2, hEF, h11, hF] at he
  linarith

/-- A finite valid endpoint need not admit positive quadratic record weights. -/
theorem disturbed_first_record_has_no_positive_extension (E F : U) (κ : ℝ)
    (hκ : 0 < κ) (Q : U → ℝ) (hQ : PositiveQuadratic Q)
    (hreal : ∀ a, Q (preparations E F a) = 5 * κ * disturbedFamily a 0) : False := by
  have h0 := hreal 0
  have h1 := hreal 1
  have h2 := hreal 2
  have h3 := hreal 3
  norm_num [preparations, disturbedFamily] at h0 h1 h2 h3
  have hn : Q (E - (F + F + F)) = -κ / 4 :=
    negative_extension_of_disturbed_values E F κ Q hQ.parallelogram
      (by linarith) (by linarith) (by linarith) (by linarith)
  have hh := hQ.nonnegative (E - (F + F + F))
  linarith

/-- Machine-visible assumptions and limits of this conditional refinement. -/
inductive BridgeBoundary where
  | recordwiseNonnegativeParallelogramWeightsSupplied
  | recordwiseQuadraticityIsNewBridgeBeyondTotalConservation
  | fixedAdditiveUnnormalizedRecordMapsNeedIndependentJustification
  | totalReadoutConservationCannotBeAppliedToEachBranch
  | probabilityActualizationAndSharedFirstCalibrationSupplied
  | onlyFourPreparationCalibrationPointsUsed
  | noParityEquivalenceAssumptionNeeded
  | noQuarterPhaseCovarianceAssumptionNeeded
  | realParallelogramDoesNotAssertComplexLinearRecordMaps
  | noScalarStructureOrTopologyOnInputCarrier
  | secondRecordScoreHalfAndErrorAtLeastTwoFifthsConditional
  | disturbedSevenTenthsTableRemainsValidFiniteProbabilityFamily
  | disturbedTableHasNoPositiveQuadraticExtensionAtThesePreparations
  | noPhysicalInstrumentOrStateUpdateConstructed
  | noHilbertCompositeOrFullQuantumTheoryConclusion
  deriving DecidableEq, Repr

def bridgeLedger : List BridgeBoundary := [
  .recordwiseNonnegativeParallelogramWeightsSupplied,
  .recordwiseQuadraticityIsNewBridgeBeyondTotalConservation,
  .fixedAdditiveUnnormalizedRecordMapsNeedIndependentJustification,
  .totalReadoutConservationCannotBeAppliedToEachBranch,
  .probabilityActualizationAndSharedFirstCalibrationSupplied,
  .onlyFourPreparationCalibrationPointsUsed,
  .noParityEquivalenceAssumptionNeeded,
  .noQuarterPhaseCovarianceAssumptionNeeded,
  .realParallelogramDoesNotAssertComplexLinearRecordMaps,
  .noScalarStructureOrTopologyOnInputCarrier,
  .secondRecordScoreHalfAndErrorAtLeastTwoFifthsConditional,
  .disturbedSevenTenthsTableRemainsValidFiniteProbabilityFamily,
  .disturbedTableHasNoPositiveQuadraticExtensionAtThesePreparations,
  .noPhysicalInstrumentOrStateUpdateConstructed,
  .noHilbertCompositeOrFullQuantumTheoryConclusion]

end

end IDT.QMClosure.QuadraticRecordRefinement
