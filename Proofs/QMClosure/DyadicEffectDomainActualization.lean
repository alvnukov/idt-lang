import Proofs.QMClosure.CalibratedEffectActualization
import Mathlib.Data.Real.Archimedean

namespace IDT.QMClosure.DyadicEffectDomainActualization

noncomputable section

open scoped ComplexOrder
open InnerProductSpace CalibratedEffectActualization

/-!
# Conditional actualization on a half-closed effect domain

The supplied complex Hilbert space, effect noncontextuality, calibration and
closure under EVERY operator-admissible sum are mathematical bridge assumptions.
In particular this last closure includes incompatible contexts. Positivity alone
does not establish a physically realizable common refinement of those events.
Only halving, complement and admissible sums are supplied as domain operations.
No all-real/rational scaling closure, supplied probability homogeneity,
normality or dimension restriction is assumed. No physical random selector or
full-QM conclusion is derived.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A restricted domain and a single probability function on its operators. -/
structure DomainLaw (D : Set (Op (H := H))) (p : Op (H := H) → ℝ) : Prop where
  effects : ∀ E ∈ D, Effect E
  one_mem : 1 ∈ D
  complement_mem : ∀ E ∈ D, 1 - E ∈ D
  half_mem : ∀ E ∈ D, scale (1 / 2) E ∈ D
  sum_mem : ∀ E ∈ D, ∀ F ∈ D, E + F ≤ 1 → E + F ∈ D
  normalized : p 1 = 1
  nonnegative : ∀ E ∈ D, 0 ≤ p E
  additive : ∀ E ∈ D, ∀ F ∈ D, E + F ≤ 1 → p (E + F) = p E + p F

namespace DomainLaw

variable {D : Set (Op (H := H))} {p : Op (H := H) → ℝ} (law : DomainLaw D p)

include law

theorem zero_mem : (0 : Op (H := H)) ∈ D := by
  simpa using law.complement_mem 1 law.one_mem

theorem probability_zero : p 0 = 0 := by
  have h := law.additive 0 law.zero_mem 0 law.zero_mem
    (by simpa using effect_zero (H := H) |>.2)
  simp only [add_zero] at h
  linarith

theorem probability_complement {E : Op (H := H)} (hE : E ∈ D) :
    p (1 - E) = 1 - p E := by
  have h := law.additive E hE (1 - E) (law.complement_mem E hE) (by simp)
  rw [add_sub_cancel, law.normalized] at h
  linarith

/-- Order monotonicity follows from the domain operations, including a
cross-context admissible sum; it is not an additional probability premise. -/
theorem probability_mono {E F : Op (H := H)} (hE : E ∈ D) (hF : F ∈ D)
    (hEF : E ≤ F) : p E ≤ p F := by
  have hsum : E + (1 - F) ≤ 1 := by
    rw [ContinuousLinearMap.le_def]
    simpa only [show (1 : Op (H := H)) - (E + (1 - F)) = F - E by abel] using hEF
  have hd : F - E ∈ D := by
    have h := law.complement_mem _
      (law.sum_mem E hE (1 - F) (law.complement_mem F hF) hsum)
    convert h using 1
    abel
  have h := law.additive E hE (F - E) hd (by simpa using (law.effects F hF).2)
  rw [add_sub_cancel] at h
  linarith [law.nonnegative _ hd]

theorem probability_le_one {E : Op (H := H)} (hE : E ∈ D) : p E ≤ 1 := by
  simpa [law.normalized] using law.probability_mono hE law.one_mem (law.effects E hE).2

omit law in
theorem scale_add_scalar (s t : ℝ) (E : Op (H := H)) :
    scale (s + t) E = scale s E + scale t E := by
  simp [scale, add_smul]

omit law in
theorem scale_one (E : Op (H := H)) : scale 1 E = E := by simp [scale]

theorem probability_half {E : Op (H := H)} (hE : E ∈ D) :
    p (scale (1 / 2) E) = (1 / 2) * p E := by
  have heq : scale (1 / 2) E + scale (1 / 2) E = E := by
    rw [← scale_add_scalar]
    norm_num [scale_one]
  have h := law.additive _ (law.half_mem E hE) _ (law.half_mem E hE)
    (by rw [heq]; exact (law.effects E hE).2)
  rw [heq] at h
  linarith

theorem iterated_half {E : Op (H := H)} (hE : E ∈ D) (n : ℕ) :
    scale ((1 / 2 : ℝ) ^ n) E ∈ D ∧
      p (scale ((1 / 2 : ℝ) ^ n) E) = (1 / 2 : ℝ) ^ n * p E := by
  induction n with
  | zero => simpa [scale_one] using And.intro hE (rfl : p E = p E)
  | succ n ih =>
    have heq : scale ((1 / 2 : ℝ) ^ (n + 1)) E =
        scale (1 / 2) (scale ((1 / 2 : ℝ) ^ n) E) := by
      rw [scale_scale, pow_succ']
    rw [heq]
    exact ⟨law.half_mem _ ih.1, by rw [law.probability_half ih.1, ih.2, pow_succ']; ring⟩

/-- Bounded repeated sums derive integer homogeneity only when the resulting
operator remains an effect. Every intermediate operator belongs to the domain. -/
theorem repeated_sum {E : Op (H := H)} (hE : E ∈ D) (k : ℕ)
    (hk : scale (k : ℝ) E ≤ 1) :
    scale (k : ℝ) E ∈ D ∧ p (scale (k : ℝ) E) = (k : ℝ) * p E := by
  induction k with
  | zero => simpa [scale, law.probability_zero] using law.zero_mem
  | succ k ih =>
    have heq : scale ((k + 1 : ℕ) : ℝ) E = scale (k : ℝ) E + E := by
      rw [Nat.cast_add, Nat.cast_one, scale_add_scalar, scale_one]
    have hle : scale (k : ℝ) E ≤ scale ((k + 1 : ℕ) : ℝ) E := by
      rw [heq, ContinuousLinearMap.le_def]
      simpa using (ContinuousLinearMap.nonneg_iff_isPositive _).mp (law.effects E hE).1
    have hi := ih (hle.trans hk)
    have hs : scale (k : ℝ) E + E ≤ 1 := by rwa [← heq]
    rw [heq]
    exact ⟨law.sum_mem _ hi.1 E hE hs, by
      rw [law.additive _ hi.1 E hE hs, hi.2, Nat.cast_add, Nat.cast_one]; ring⟩

/-- Dyadic scaling closure and probability homogeneity are consequences of
halving and bounded repeated sums, rather than fields of `DomainLaw`. -/
theorem dyadic_scale {E : Op (H := H)} (hE : E ∈ D) (k n : ℕ)
    (hkn : (k : ℝ) * (1 / 2 : ℝ) ^ n ≤ 1) :
    scale ((k : ℝ) * (1 / 2 : ℝ) ^ n) E ∈ D ∧
      p (scale ((k : ℝ) * (1 / 2 : ℝ) ^ n) E) =
        ((k : ℝ) * (1 / 2 : ℝ) ^ n) * p E := by
  have hh := law.iterated_half hE n
  have hb : scale (k : ℝ) (scale ((1 / 2 : ℝ) ^ n) E) ≤ 1 := by
    rw [scale_scale]
    exact (effect_scale (law.effects E hE) ⟨by positivity, hkn⟩).2
  have h := law.repeated_sum hh.1 k hb
  rw [scale_scale] at h
  exact ⟨h.1, by rw [h.2, hh.2]; ring⟩

omit law in
theorem scale_mono_scalar {E : Op (H := H)} (hE : 0 ≤ E) {s t : ℝ} (hst : s ≤ t) :
    scale s E ≤ scale t E := by
  rw [ContinuousLinearMap.le_def]
  have h := scale_nonneg hE (sub_nonneg.mpr hst)
  rw [ContinuousLinearMap.nonneg_iff_isPositive] at h
  simpa only [scale, Complex.ofReal_sub, sub_smul] using h

omit law in
/-- Nonnegative dyadics are dense above every nonnegative real number. -/
theorem exists_dyadic_between {a r : ℝ} (ha : 0 ≤ a) (har : a < r) :
    ∃ k n : ℕ, a < (k : ℝ) * (1 / 2 : ℝ) ^ n ∧
      (k : ℝ) * (1 / 2 : ℝ) ^ n < r := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr har)
    (by norm_num : (1 / 2 : ℝ) < 1)
  let t := (1 / 2 : ℝ) ^ n
  have ht : 0 < t := by dsimp [t]; positivity
  have hprod : a / t * t = a := div_mul_cancel₀ a ht.ne'
  refine ⟨⌊a / t⌋₊ + 1, n, ?_, ?_⟩
  · have h := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (a / t)) ht
    push_cast
    change a < ((⌊a / t⌋₊ : ℝ) + 1) * t
    linarith
  · have h := mul_le_mul_of_nonneg_right
      (Nat.floor_le (div_nonneg ha ht.le)) ht.le
    push_cast
    change ((⌊a / t⌋₊ : ℝ) + 1) * t < r
    change t < r - a at hn
    nlinarith

/-- A dyadic comparison coefficient may exceed one. A further dyadic scaling
makes BOTH block coefficients admissible before domain closure is used. -/
theorem probability_le_dyadic [CompleteSpace H] {ψ : H} (hψ : ‖ψ‖ = 1)
    (hPmem : projector ψ ∈ D) (calibrated : p (projector ψ) = 1)
    {E : Op (H := H)} (hE : E ∈ D) (k n : ℕ)
    (hq : (inner ℂ ψ (E ψ)).re < (k : ℝ) * (1 / 2 : ℝ) ^ n) :
    p E ≤ (k : ℝ) * (1 / 2 : ℝ) ^ n := by
  let a := (inner ℂ ψ (E ψ)).re
  let q := (k : ℝ) * (1 / 2 : ℝ) ^ n
  let P := projector ψ
  let R := (1 : Op (H := H)) - P
  have hEff := law.effects E hE
  have hP : Effect P := projector_effect hψ
  have hR : Effect R := effect_complement hP
  have hRmem : R ∈ D := law.complement_mem _ hPmem
  have ha : 0 ≤ a := (expectation_bounds hEff hψ).1
  have hqa : 0 < q - a := sub_pos.mpr hq
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  obtain ⟨b, hb⟩ := exists_nat_ge (1 + ‖E‖ ^ 2 / (q - a))
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hEB : E ≤ scale q P + scale (b : ℝ) R := by
    have h := effect_block_bound hEff hψ hqa
    have heq : a + (q - a) = q := by ring
    change E ≤ scale (a + (q - a)) P + scale (1 + ‖E‖ ^ 2 / (q - a)) R at h
    rw [heq] at h
    apply h.trans
    rw [ContinuousLinearMap.le_def]
    have hi := scale_mono_scalar hR.1 hb
    rw [ContinuousLinearMap.le_def] at hi
    convert hi using 1
    abel
  let c := q + (b : ℝ) + 1
  have hc1 : 1 ≤ c := by dsimp [c]; linarith
  have hc : 0 < c := by linarith
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (one_div_pos.mpr hc)
    (by norm_num : (1 / 2 : ℝ) < 1)
  let t := (1 / 2 : ℝ) ^ m
  have ht : 0 < t := by dsimp [t]; positivity
  have htc : t * c ≤ 1 := le_of_lt ((lt_div_iff₀ hc).mp hm)
  have htq : t * q ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg ht.le hq0, (mul_le_mul_of_nonneg_left (by dsimp [c]; linarith) ht.le).trans htc⟩
  have htb : t * (b : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg ht.le hb0, (mul_le_mul_of_nonneg_left (by dsimp [c]; linarith) ht.le).trans htc⟩
  have hqeq : t * q = (k : ℝ) * (1 / 2 : ℝ) ^ (m + n) := by
    dsimp [t, q]; rw [pow_add]; ring
  have hbeq : t * (b : ℝ) = (b : ℝ) * (1 / 2 : ℝ) ^ m := by dsimp [t]; ring
  have hqD : scale (t * q) P ∈ D ∧ p (scale (t * q) P) = t * q * p P := by
    rw [hqeq]
    exact law.dyadic_scale hPmem k (m + n) (by rw [← hqeq]; exact htq.2)
  have hbD : scale (t * (b : ℝ)) R ∈ D ∧
      p (scale (t * (b : ℝ)) R) = t * (b : ℝ) * p R := by
    rw [hbeq]
    exact law.dyadic_scale hRmem b m (by rw [← hbeq]; exact htb.2)
  let U := scale (t * q) P + scale (t * (b : ℝ)) R
  have hU : Effect U := effect_mix hP htq htb
  have hUmem : U ∈ D := law.sum_mem _ hqD.1 _ hbD.1 hU.2
  have hpR : p R = 0 := by
    have h := law.probability_complement hPmem
    rw [calibrated] at h
    simpa [R, P] using h
  have hpU : p U = t * q := by
    rw [law.additive _ hqD.1 _ hbD.1 hU.2, hqD.2, hbD.2, hpR,
      show p P = 1 from calibrated]
    ring
  have hV := law.iterated_half hE m
  have hVU : scale t E ≤ U := by
    have h := scale_mono hEB ht.le
    simpa only [scale_add, scale_scale] using h
  have h := law.probability_mono hV.1 hUmem hVU
  rw [hV.2, hpU] at h
  exact (mul_le_mul_iff_right₀ ht).mp h

theorem probability_le_expectation [CompleteSpace H] {ψ : H} (hψ : ‖ψ‖ = 1)
    (hPmem : projector ψ ∈ D) (calibrated : p (projector ψ) = 1)
    {E : Op (H := H)} (hE : E ∈ D) : p E ≤ (inner ℂ ψ (E ψ)).re := by
  by_contra h
  have hlt : (inner ℂ ψ (E ψ)).re < p E := lt_of_not_ge h
  obtain ⟨k, n, hq, hqp⟩ := exists_dyadic_between
    (expectation_bounds (law.effects E hE) hψ).1 hlt
  exact (not_le_of_gt hqp) (law.probability_le_dyadic hψ hPmem calibrated hE k n hq)

/-- Conditional calibrated actualization on the supplied half-closed domain.
All dyadic closure/homogeneity and order monotonicity used in this theorem have
been derived above. This is a mathematical bridge theorem, not a derivation of
physical event availability, random outcomes, or full QM. -/
theorem calibrated_probability_eq_expectation [CompleteSpace H] {ψ : H} (hψ : ‖ψ‖ = 1)
    (hPmem : projector ψ ∈ D) (calibrated : p (projector ψ) = 1)
    {E : Op (H := H)} (hE : E ∈ D) : p E = (inner ℂ ψ (E ψ)).re := by
  apply le_antisymm (law.probability_le_expectation hψ hPmem calibrated hE)
  have h := law.probability_le_expectation hψ hPmem calibrated (law.complement_mem E hE)
  rw [law.probability_complement hE] at h
  have heq : (inner ℂ ψ ((1 - E) ψ)).re = 1 - (inner ℂ ψ (E ψ)).re := by
    simp [inner_sub_right, inner_self_eq_norm_sq_to_K, hψ]
  rw [heq] at h
  linarith

end DomainLaw

end

end IDT.QMClosure.DyadicEffectDomainActualization
