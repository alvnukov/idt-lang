import Proofs.QMClosure.ScalarActualizationRefinement
import Mathlib.Analysis.InnerProductSpace.Positive

namespace IDT.QMClosure.CalibratedEffectActualization

noncomputable section

open scoped ComplexOrder
open InnerProductSpace

/-!
# Conditional actualization on all Hilbert-space effects

The complex inner-product space here is a supplied mathematical output space,
not an IDT primitive. A single probability function on all effects explicitly
assumes effect noncontextuality; normalization, positive probabilities, partial
additivity, full effect availability, and calibration are additional bridges.
No physical availability or random outcome generator is constructed here.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev Op := H →L[ℂ] H

def Effect (E : Op (H := H)) : Prop := 0 ≤ E ∧ E ≤ 1

/-- Real scaling, kept explicit to avoid imposing a scalar action on primitives. -/
def scale (t : ℝ) (E : Op (H := H)) : Op (H := H) := (t : ℂ) • E

theorem scale_nonneg {E : Op (H := H)} (hE : 0 ≤ E) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ scale t E := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hE).smul_of_nonneg
    (by exact_mod_cast ht)

theorem scale_le_self {E : Op (H := H)} (hE : 0 ≤ E) {t : ℝ} (ht : t ≤ 1) :
    scale t E ≤ E := by
  rw [ContinuousLinearMap.le_def]
  have h := scale_nonneg hE (sub_nonneg.mpr ht)
  rw [ContinuousLinearMap.nonneg_iff_isPositive] at h
  convert h using 1; simp [scale, sub_smul]

theorem effect_scale {E : Op (H := H)} (hE : Effect E) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : Effect (scale t E) :=
  ⟨scale_nonneg hE.1 ht.1, (scale_le_self hE.1 ht.2).trans hE.2⟩

theorem effect_zero : Effect (0 : Op (H := H)) := by
  constructor
  · exact le_rfl
  · exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      ContinuousLinearMap.isPositive_one

theorem effect_one : Effect (1 : Op (H := H)) := ⟨effect_zero.2, le_rfl⟩

theorem effect_complement {E : Op (H := H)} (hE : Effect E) : Effect (1 - E) := by
  constructor
  · simpa only [ContinuousLinearMap.nonneg_iff_isPositive] using hE.2
  · rw [ContinuousLinearMap.le_def]
    simpa using (ContinuousLinearMap.nonneg_iff_isPositive _).mp hE.1

/-- Laws are restricted to effects. The total function is only an interface;
its values outside the effect interval are unrestricted and unused. -/
structure EventLaw (p : Op (H := H) → ℝ) : Prop where
  normalized : p 1 = 1
  nonnegative : ∀ E, Effect E → 0 ≤ p E
  additive : ∀ E F, 0 ≤ E → 0 ≤ F → E + F ≤ 1 → p (E + F) = p E + p F

variable {p : Op (H := H) → ℝ} (law : EventLaw p)

include law

theorem probability_zero : p 0 = 0 := by
  have h := law.additive 0 0 le_rfl le_rfl (by simpa using effect_zero (H := H) |>.2)
  simp only [add_zero] at h
  linarith

theorem probability_mono {E F : Op (H := H)} (hE : Effect E) (hF : Effect F)
    (hEF : E ≤ F) : p E ≤ p F := by
  have hd : 0 ≤ F - E :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hEF
  have hdF : F - E ≤ F := by
    rw [ContinuousLinearMap.le_def]
    simpa using (ContinuousLinearMap.nonneg_iff_isPositive _).mp hE.1
  have hd1 : Effect (F - E) := ⟨hd, hdF.trans hF.2⟩
  have hadd := law.additive E (F - E) hE.1 hd (by simpa using hF.2)
  rw [add_sub_cancel] at hadd
  linarith [law.nonnegative (F - E) hd1]

theorem probability_le_one {E : Op (H := H)} (hE : Effect E) : p E ≤ 1 := by
  simpa [law.normalized] using probability_mono law hE effect_one hE.2

theorem probability_complement {E : Op (H := H)} (hE : Effect E) :
    p (1 - E) = 1 - p E := by
  have hadd := law.additive E (1 - E) hE.1 (effect_complement hE).1
    (by simp)
  rw [add_sub_cancel, law.normalized] at hadd
  linarith

/-- Real homogeneity is derived, not assumed as a probability-linearity law.
The scalar actualization theorem removes any continuity/normality premise. -/
theorem probability_scale {E : Op (H := H)} (hE : Effect E) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : p (scale t E) = t * p E := by
  by_cases hz : p E = 0
  · have hm := probability_mono law (effect_scale hE ht) hE
      (scale_le_self hE.1 ht.2)
    have hn := law.nonnegative (scale t E) (effect_scale hE ht)
    rw [hz] at hm ⊢
    linarith
  · have hp : 0 < p E := lt_of_le_of_ne (law.nonnegative E hE) (Ne.symm hz)
    have hs (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
        p (scale u E) + p (scale (1 - u) E) = p E := by
      have heq : scale u E + scale (1 - u) E = E := by
        unfold scale
        rw [← add_smul]
        have hc : (u : ℂ) + ((1 - u : ℝ) : ℂ) = 1 := by push_cast; ring
        rw [hc, one_smul]
      have h := law.additive (scale u E) (scale (1 - u) E)
        (scale_nonneg hE.1 hu.1) (scale_nonneg hE.1 (by linarith [hu.2]))
        (by rw [heq]; exact hE.2)
      rw [heq] at h
      exact h.symm
    have hh (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
        p (scale (u / 2) E) = p (scale u E) / 2 := by
      have heq : scale (u / 2) E + scale (u / 2) E = scale u E := by
        unfold scale
        rw [← add_smul]
        congr 1
        push_cast
        ring
      have h := law.additive (scale (u / 2) E) (scale (u / 2) E)
        (scale_nonneg hE.1 (by linarith [hu.1]))
        (scale_nonneg hE.1 (by linarith [hu.1]))
        (by rw [heq]; exact (effect_scale hE hu).2)
      rw [heq] at h
      linarith
    have hf := ScalarActualizationRefinement.probability_response_eq_weight
      (fun u => p (scale u E) / p E) (by
        intro u hu
        constructor
        · exact div_nonneg (law.nonnegative _ (effect_scale hE hu)) hp.le
        · exact (div_le_one hp).mpr
            (probability_mono law (effect_scale hE hu) hE (scale_le_self hE.1 hu.2)))
      (by
        intro u hu
        dsimp
        have h := hs u hu
        apply (div_eq_iff (ne_of_gt hp)).mpr
        field_simp
        linarith)
      (by intro u hu; dsimp; rw [hh u hu]; ring) t ht
    exact (div_eq_iff (ne_of_gt hp)).mp hf

omit law

def projector (ψ : H) : Op (H := H) := rankOne ℂ ψ ψ

theorem projector_effect [CompleteSpace H] {ψ : H} (hψ : ‖ψ‖ = 1) : Effect (projector ψ) := by
  have h := isStarProjection_rankOne_self (𝕜 := ℂ) hψ
  constructor
  · exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (.of_isStarProjection h)
  · exact ContinuousLinearMap.le_def _ _ |>.mpr (.of_isStarProjection h.one_sub)

theorem projector_diagonal (ψ v : H) :
    (inner ℂ v (projector ψ v)).re = ‖inner ℂ ψ v‖ ^ 2 := by
  change (inner ℂ v (rankOne ℂ ψ ψ v)).re = _
  rw [inner_right_rankOne_apply, ← inner_conj_symm v ψ,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem residual_orthogonal {ψ : H} (hψ : ‖ψ‖ = 1) (v : H) :
    inner ℂ ψ (v - inner ℂ ψ v • ψ) = 0 := by
  simp [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hψ]

theorem residual_norm_sq {ψ : H} (hψ : ‖ψ‖ = 1) (v : H) :
    ‖v‖ ^ 2 = ‖inner ℂ ψ v‖ ^ 2 + ‖v - inner ℂ ψ v • ψ‖ ^ 2 := by
  have heq : inner ℂ ψ v • ψ + (v - inner ℂ ψ v • ψ) = v := by abel
  have hz : inner ℂ (inner ℂ ψ v • ψ) (v - inner ℂ ψ v • ψ) = 0 := by
    rw [inner_smul_left, residual_orthogonal hψ v, mul_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hz
  simpa [heq, norm_smul, hψ, sq] using h

/-- The numerical Young inequality used in the off-diagonal block estimate. -/
theorem cross_bound (x y n ε : ℝ) (hε : 0 < ε) :
    2 * x * n * y ≤ ε * x ^ 2 + (n ^ 2 / ε) * y ^ 2 := by
  have h := sq_nonneg (ε * x - n * y)
  have hdiv : ε * (n ^ 2 / ε) = n ^ 2 := by field_simp
  apply (mul_le_mul_iff_right₀ hε).mp
  calc
    ε * (2 * x * n * y) ≤ ε * (ε * x ^ 2) + n ^ 2 * y ^ 2 := by nlinarith
    _ = ε * (ε * x ^ 2 + (n ^ 2 / ε) * y ^ 2) := by rw [mul_add]; nlinarith [hdiv]

theorem expectation_bounds {E : Op (H := H)} (hE : Effect E) {ψ : H}
    (hψ : ‖ψ‖ = 1) :
    0 ≤ (inner ℂ ψ (E ψ)).re ∧ (inner ℂ ψ (E ψ)).re ≤ 1 := by
  constructor
  · exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hE.1).re_inner_nonneg_right ψ
  · have h := (ContinuousLinearMap.le_def _ _ |>.mp hE.2).re_inner_nonneg_right ψ
    simpa [inner_sub_right, inner_self_eq_norm_sq_to_K, hψ] using h

theorem quadratic_smul (E : Op (H := H)) (ψ : H) (z : ℂ) :
    (inner ℂ (z • ψ) (E (z • ψ))).re = ‖z‖ ^ 2 * (inner ℂ ψ (E ψ)).re := by
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
    ← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.normSq_eq_norm_sq]

theorem cross_operator_bound (E : Op (H := H)) (v w : H) :
    (inner ℂ v (E w)).re ≤ ‖v‖ * ‖E‖ * ‖w‖ := by
  calc
    _ ≤ ‖v‖ * ‖E w‖ := re_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ ‖v‖ * (‖E‖ * ‖w‖) := mul_le_mul_of_nonneg_left (E.le_opNorm w) (norm_nonneg v)
    _ = _ := by ring

/-- The block comparison is proved for arbitrary dimensions. Its coefficients
depend on the operator norm only to bound the off-diagonal terms. -/
theorem effect_block_bound [CompleteSpace H] {E : Op (H := H)} (hE : Effect E)
    {ψ : H} (hψ : ‖ψ‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    E ≤ scale ((inner ℂ ψ (E ψ)).re + ε) (projector ψ) +
      scale (1 + ‖E‖ ^ 2 / ε) (1 - projector ψ) := by
  let a := (inner ℂ ψ (E ψ)).re
  let b := 1 + ‖E‖ ^ 2 / ε
  let P := projector ψ
  let R := (1 : Op (H := H)) - P
  have hP : Effect P := projector_effect hψ
  have hR : Effect R := effect_complement hP
  have ha : 0 ≤ a := (expectation_bounds hE hψ).1
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hB : (scale (a + ε) P + scale b R).IsPositive :=
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
      (scale_nonneg hP.1 (by linarith))).add
      ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (scale_nonneg hR.1 hb))
  rw [ContinuousLinearMap.le_def]
  refine ⟨hB.isSymmetric.sub
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hE.1).isSymmetric, ?_⟩
  intro v
  let z := inner ℂ ψ v
  let u := z • ψ
  let w := v - u
  have hv : u + w = v := by dsimp [w]; abel
  have hu : ‖u‖ = ‖z‖ := by simp [u, norm_smul, hψ]
  have hw : ‖v‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 := residual_norm_sq hψ v
  have hww : (inner ℂ w (E w)).re ≤ ‖w‖ ^ 2 := by
    have h := (ContinuousLinearMap.le_def _ _ |>.mp hE.2).re_inner_nonneg_right w
    simpa [inner_sub_right, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using h
  have hc1 := cross_operator_bound E u w
  have hc2 := cross_operator_bound E w u
  rw [hu] at hc1 hc2
  have hy := cross_bound ‖z‖ ‖w‖ ‖E‖ ε hε
  have hexpand : (inner ℂ v (E v)).re = ‖z‖ ^ 2 * a +
      (inner ℂ u (E w)).re + (inner ℂ w (E u)).re + (inner ℂ w (E w)).re := by
    calc
      _ = (inner ℂ (u + w) (E (u + w))).re := by rw [hv]
      _ = _ := by
        simp only [map_add, inner_add_left, inner_add_right, Complex.add_re]
        rw [show (inner ℂ u (E u)).re = ‖z‖ ^ 2 * a from quadratic_smul E ψ z]
        ring
  have hdiag : (inner ℂ v
      ((scale (a + ε) P + scale b R) v)).re =
      (a + ε) * ‖z‖ ^ 2 + b * ‖w‖ ^ 2 := by
    simp only [scale, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      inner_add_right, inner_smul_right, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hpd : (inner ℂ v (P v)).re = ‖z‖ ^ 2 := projector_diagonal ψ v
    have hrd : (inner ℂ v (R v)).re = ‖w‖ ^ 2 := by
      have hself : (inner ℂ v v).re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
      simp only [R, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        inner_sub_right, Complex.sub_re, hself, hpd]
      linarith [hw]
    rw [hpd, hrd]
  have hbound : (inner ℂ v (E v)).re ≤
      (inner ℂ v ((scale (a + ε) P + scale b R) v)).re := by
    rw [hexpand, hdiag]
    dsimp [b]
    nlinarith
  change 0 ≤ (inner ℂ
    ((scale (a + ε) P + scale b R - E) v) v).re
  have hsym : (inner ℂ ((scale (a + ε) P + scale b R - E) v) v).re =
      (inner ℂ v ((scale (a + ε) P + scale b R - E) v)).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  rw [hsym]
  simpa only [ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re]
    using sub_nonneg.mpr hbound

theorem scale_mono {E F : Op (H := H)} (hEF : E ≤ F) {t : ℝ} (ht : 0 ≤ t) :
    scale t E ≤ scale t F := by
  rw [ContinuousLinearMap.le_def]
  have h := scale_nonneg ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hEF) ht
  rw [ContinuousLinearMap.nonneg_iff_isPositive] at h
  simpa only [scale, smul_sub] using h

theorem scale_add (t : ℝ) (E F : Op (H := H)) :
    scale t (E + F) = scale t E + scale t F := by simp [scale, smul_add]

theorem scale_scale (t s : ℝ) (E : Op (H := H)) :
    scale t (scale s E) = scale (t * s) E := by
  simp only [scale, smul_smul, Complex.ofReal_mul]

theorem effect_mix {P : Op (H := H)} (hP : Effect P) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    Effect (scale x P + scale y (1 - P)) := by
  have hR := effect_complement hP
  constructor
  · apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (scale_nonneg hP.1 hx.1)).add
      ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (scale_nonneg hR.1 hy.1))
  · rw [ContinuousLinearMap.le_def]
    have heq : 1 - (scale x P + scale y (1 - P)) =
        scale (1 - x) P + scale (1 - y) (1 - P) := by
      simp only [scale, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
      abel
    rw [heq]
    exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
      (scale_nonneg hP.1 (sub_nonneg.mpr hx.2))).add
      ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
        (scale_nonneg hR.1 (sub_nonneg.mpr hy.2)))

/-- Calibration on the unit-vector projector gives the upper expectation bound.
Every use of probability additivity and homogeneity stays inside the effects. -/
theorem probability_le_expectation [CompleteSpace H] (law : EventLaw p)
    {ψ : H} (hψ : ‖ψ‖ = 1) (calibrated : p (projector ψ) = 1)
    {E : Op (H := H)} (hE : Effect E) : p E ≤ (inner ℂ ψ (E ψ)).re := by
  let a := (inner ℂ ψ (E ψ)).re
  have hupper (ε : ℝ) (hε : 0 < ε) : p E ≤ a + ε := by
    let A := a + ε
    let b := 1 + ‖E‖ ^ 2 / ε
    let c := A + b + 1
    let t := 1 / c
    let P := projector ψ
    let R := (1 : Op (H := H)) - P
    let B := scale A P + scale b R
    have ha : 0 ≤ a := (expectation_bounds hE hψ).1
    have hA : 0 ≤ A := by dsimp [A]; linarith
    have hb : 0 ≤ b := by dsimp [b]; positivity
    have hc1 : 1 ≤ c := by dsimp [c]; linarith
    have hc : 0 < c := by linarith
    have ht : 0 < t := by dsimp [t]; positivity
    have htc : t * c = 1 := by dsimp [t]; field_simp
    have ht1 : t ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hc1 ht.le
      rw [htc, mul_one] at h
      exact h
    have htA : t * A ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact mul_nonneg ht.le hA
      · calc
          t * A ≤ t * c := mul_le_mul_of_nonneg_left (by dsimp [c]; linarith) ht.le
          _ = 1 := htc
    have htb : t * b ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact mul_nonneg ht.le hb
      · calc
          t * b ≤ t * c := mul_le_mul_of_nonneg_left (by dsimp [c]; linarith) ht.le
          _ = 1 := htc
    have hP : Effect P := projector_effect hψ
    have hR : Effect R := effect_complement hP
    have hpR : p R = 0 := by
      have h := probability_complement law hP
      rw [show p P = 1 from calibrated] at h
      simpa [R] using h
    have hBeq : scale t B = scale (t * A) P + scale (t * b) R := by
      dsimp only [B]
      rw [scale_add, scale_scale, scale_scale]
    have hBt : Effect (scale t B) := by
      rw [hBeq]
      exact effect_mix hP htA htb
    have hpBt : p (scale t B) = t * A := by
      rw [hBeq, law.additive _ _ (scale_nonneg hP.1 htA.1)
        (scale_nonneg hR.1 htb.1) (by rw [← hBeq]; exact hBt.2)]
      rw [probability_scale law hP htA, probability_scale law hR htb, hpR,
        show p P = 1 from calibrated]
      ring
    have hEB : E ≤ B := effect_block_bound hE hψ hε
    have hm := probability_mono law (effect_scale hE ⟨ht.le, ht1⟩) hBt
      (scale_mono hEB ht.le)
    rw [probability_scale law hE ⟨ht.le, ht1⟩, hpBt] at hm
    have h := (mul_le_mul_iff_right₀ ht).mp hm
    exact h
  by_contra h
  have hgap : 0 < p E - a := by change ¬ p E ≤ a at h; linarith
  have hu := hupper ((p E - a) / 2) (by linarith)
  linarith

/-- Conditional calibrated actualization on the full real effect interval.
No dimension restriction, Gleason theorem, normality, continuity, or supplied
probability homogeneity is used. Full effect availability/noncontextuality and
the preparation calibration remain explicit additional assumptions. -/
theorem calibrated_probability_eq_expectation [CompleteSpace H] (law : EventLaw p)
    {ψ : H} (hψ : ‖ψ‖ = 1) (calibrated : p (projector ψ) = 1)
    {E : Op (H := H)} (hE : Effect E) : p E = (inner ℂ ψ (E ψ)).re := by
  apply le_antisymm (probability_le_expectation law hψ calibrated hE)
  have h := probability_le_expectation law hψ calibrated (effect_complement hE)
  rw [probability_complement law hE] at h
  have heq : (inner ℂ ψ ((1 - E) ψ)).re = 1 - (inner ℂ ψ (E ψ)).re := by
    simp [inner_sub_right, inner_self_eq_norm_sq_to_K, hψ]
  rw [heq] at h
  linarith

end

end IDT.QMClosure.CalibratedEffectActualization
