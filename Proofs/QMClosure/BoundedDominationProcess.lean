import Proofs.QMClosure.InternalReferenceEntropyBridge

/-!
# Closed bounded-domination components of a transparent statistical process

The contract contains probability preparations, full covariance through one
common forward channel, a square root of swap, and a fixed raw diagonal.
Bounded domination is made symmetric by the preorder obstruction. A component
therefore has two-sided bounded likelihoods and finite reference entropy.
-/

namespace IDT.QMClosure.BoundedDominationProcess

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

universe u v
variable {V : Type u} {Ω : Type v} [MeasurableSpace Ω]

/-- A positive finite scalar bounds the first measure by the second. -/
def boundedDom (P Q : Measure Ω) : Prop :=
  ∃ C : ℝ≥0∞, 0 < C ∧ C ≠ ∞ ∧ P ≤ C • Q

namespace boundedDom

theorem refl (P : Measure Ω) : boundedDom P P :=
  ⟨1, zero_lt_one, ENNReal.one_ne_top, by simp⟩

theorem trans {P Q R : Measure Ω} (hPQ : boundedDom P Q)
    (hQR : boundedDom Q R) : boundedDom P R := by
  obtain ⟨C, hC, hCfin, hPQ⟩ := hPQ
  obtain ⟨D, hD, hDfin, hQR⟩ := hQR
  refine ⟨C * D, ENNReal.mul_pos hC.ne' hD.ne', ENNReal.mul_ne_top hCfin hDfin, ?_⟩
  intro s
  exact (hPQ s).trans (by
    simpa only [Measure.smul_apply, smul_eq_mul, mul_assoc] using
      mul_le_mul_right (hQR s) C)

theorem absolutelyContinuous {P Q : Measure Ω} (hPQ : boundedDom P Q) : P ≪ Q := by
  obtain ⟨C, _, _, h⟩ := hPQ
  exact Measure.absolutelyContinuous_of_le_smul h

/-- Products preserve bounded domination, with the product of the constants. -/
theorem prod {P₁ P₂ Q₁ Q₂ : Measure Ω}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
    (h₁ : boundedDom P₁ Q₁) (h₂ : boundedDom P₂ Q₂) :
    boundedDom (P₁.prod P₂) (Q₁.prod Q₂) := by
  obtain ⟨C, hC, hCfin, h₁⟩ := h₁
  obtain ⟨D, hD, hDfin, h₂⟩ := h₂
  refine ⟨C * D, ENNReal.mul_pos hC.ne' hD.ne', ENNReal.mul_ne_top hCfin hDfin, ?_⟩
  have hprod : P₁.prod P₂ ≤ (C • Q₁).prod (D • Q₂) := by
    apply Measure.le_iff.2
    intro s hs
    rw [Measure.prod_apply hs, Measure.prod_apply hs]
    exact lintegral_mono' h₁ (fun x => h₂ (Prod.mk x ⁻¹' s))
  simpa only [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, mul_comm] using hprod

/-- Applying one common kernel preserves the same domination constant. -/
theorem comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {P Q : Measure α} (hPQ : boundedDom P Q) (κ : Kernel α β) :
    boundedDom (κ ∘ₘ P) (κ ∘ₘ Q) := by
  obtain ⟨C, hC, hCfin, h⟩ := hPQ
  refine ⟨C, hC, hCfin, ?_⟩
  have hcomp : κ ∘ₘ P ≤ κ ∘ₘ (C • Q) := by
    apply Measure.le_iff.2
    intro s hs
    rw [Measure.bind_apply hs κ.aemeasurable, Measure.bind_apply hs κ.aemeasurable]
    exact lintegral_mono' h le_rfl
  simpa only [Measure.comp_smul] using hcomp

/-- Probability marginals recover the two coordinate domination relations. -/
theorem of_prod {P₁ P₂ Q₁ Q₂ : Measure Ω}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
    (h : boundedDom (P₁.prod P₂) (Q₁.prod Q₂)) :
    boundedDom P₁ Q₁ ∧ boundedDom P₂ Q₂ := by
  obtain ⟨C, hC, hCfin, h⟩ := h
  constructor
  · refine ⟨C, hC, hCfin, ?_⟩
    have hf := Measure.fst_mono h
    change (P₁.prod P₂).map Prod.fst ≤ (C • Q₁.prod Q₂).map Prod.fst at hf
    rw [Measure.map_smul] at hf
    change (P₁.prod P₂).fst ≤ C • (Q₁.prod Q₂).fst at hf
    simpa only [Measure.fst_prod] using hf
  · refine ⟨C, hC, hCfin, ?_⟩
    have hs := Measure.snd_mono h
    change (P₁.prod P₂).map Prod.snd ≤ (C • Q₁.prod Q₂).map Prod.snd at hs
    rw [Measure.map_smul] at hs
    change (P₁.prod P₂).snd ≤ C • (Q₁.prod Q₂).snd at hs
    simpa only [Measure.snd_prod] using hs

end boundedDom

/-- A full-covariance transparent statistical process, with no supplied
reference preparation, finite entropy, or log-integrability premise. -/
structure Contract (V : Type u) (Ω : Type v) [MeasurableSpace Ω] where
  preparation : V → Measure Ω
  probability : ∀ x, IsProbabilityMeasure (preparation x)
  operation : V × V → V × V
  square : ∀ p, operation (operation p) = p.swap
  transparent : ∀ x, operation (x, x) = (x, x)
  channel : Kernel (Ω × Ω) (Ω × Ω)
  markov : IsMarkovKernel channel
  covariance : ∀ p, channel ∘ₘ ((preparation p.1).prod (preparation p.2)) =
    (preparation (operation p).1).prod (preparation (operation p).2)

namespace Contract

variable (D : Contract V Ω)

local instance (x : V) : IsProbabilityMeasure (D.preparation x) := D.probability x

theorem operation_preserves_boundedDom {p q : V × V}
    (h₁ : boundedDom (D.preparation p.1) (D.preparation q.1))
    (h₂ : boundedDom (D.preparation p.2) (D.preparation q.2)) :
    boundedDom (D.preparation (D.operation p).1) (D.preparation (D.operation q).1) ∧
      boundedDom (D.preparation (D.operation p).2) (D.preparation (D.operation q).2) := by
  have h := (h₁.prod h₂).comp D.channel
  rw [D.covariance p, D.covariance q] at h
  exact h.of_prod

/-- The order obstruction reverses each comparable pair, before introducing a
chosen reference or a finite-entropy process adapter. -/
theorem reverse_boundedDom {x y : V}
    (hxy : boundedDom (D.preparation x) (D.preparation y)) :
    boundedDom (D.preparation y) (D.preparation x) := by
  letI : Preorder V :=
    { le := fun x y => boundedDom (D.preparation x) (D.preparation y)
      le_refl := fun x => boundedDom.refl (D.preparation x)
      le_trans := fun _ _ _ hxy hyz => hxy.trans hyz }
  have hmono : Monotone D.operation := by
    intro p q hpq
    exact D.operation_preserves_boundedDom hpq.1 hpq.2
  exact TransparentSwapRootOrderWall.reverse_le D.operation hmono
    D.square D.transparent hxy

/-- The component anchored at the preparation indexed by `y`. -/
def Component (y : V) := {z : V // boundedDom (D.preparation z) (D.preparation y)}

def origin (y : V) : D.Component y := ⟨y, boundedDom.refl _⟩

theorem operation_closed (y : V) (p : D.Component y × D.Component y) :
    boundedDom (D.preparation (D.operation (p.1.val, p.2.val)).1) (D.preparation y) ∧
      boundedDom (D.preparation (D.operation (p.1.val, p.2.val)).2) (D.preparation y) := by
  simpa only [D.transparent y] using
    D.operation_preserves_boundedDom (p := (p.1.val, p.2.val)) (q := (y, y))
      p.1.property p.2.property

def componentOperation (y : V) (p : D.Component y × D.Component y) :
    D.Component y × D.Component y :=
  (⟨(D.operation (p.1.val, p.2.val)).1, (D.operation_closed y p).1⟩,
    ⟨(D.operation (p.1.val, p.2.val)).2, (D.operation_closed y p).2⟩)

theorem component_square (y : V) (p : D.Component y × D.Component y) :
    D.componentOperation y (D.componentOperation y p) = p.swap := by
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst (D.square (p.1.val, p.2.val))
  · apply Subtype.ext
    exact congrArg Prod.snd (D.square (p.1.val, p.2.val))

theorem component_transparent (y : V) (x : D.Component y) :
    D.componentOperation y (x, x) = (x, x) := by
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst (D.transparent x.val)
  · apply Subtype.ext
    exact congrArg Prod.snd (D.transparent x.val)

theorem component_mutually_absolutelyContinuous (y : V) (x : D.Component y) :
    D.preparation x.val ≪ D.preparation y ∧ D.preparation y ≪ D.preparation x.val :=
  ⟨x.property.absolutelyContinuous, (D.reverse_boundedDom x.property).absolutelyContinuous⟩

end Contract

/-- A measure inequality bounds the RN derivative by its scalar, almost
everywhere with respect to the dominating measure. -/
theorem rnDeriv_le_of_le_smul (P Q : Measure Ω) [IsProbabilityMeasure Q]
    {C : ℝ≥0∞} (h : P ≤ C • Q) : P.rnDeriv Q ≤ᵐ[Q] fun _ => C := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (P.measurable_rnDeriv Q)
  intro s hs _
  rw [setLIntegral_const]
  exact (Measure.setLIntegral_rnDeriv_le s).trans (by
    simpa only [Measure.smul_apply, smul_eq_mul] using h s)

/-- Two finite bounds on measures give a positive finite lower bound and a
finite upper bound for their reference-relative likelihood. -/
theorem rnDeriv_bounds (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : boundedDom P Q) (hQP : boundedDom Q P) :
    ∃ L U : ℝ≥0∞, 0 < L ∧ L ≠ ∞ ∧ 0 < U ∧ U ≠ ∞ ∧
      ∀ᵐ s ∂Q, L ≤ P.rnDeriv Q s ∧ P.rnDeriv Q s ≤ U := by
  obtain ⟨C, hC, hCfin, hPC⟩ := hPQ
  obtain ⟨D, hD, hDfin, hQD⟩ := hQP
  have hQP : Q ≪ P := Measure.absolutelyContinuous_of_le_smul hQD
  refine ⟨D⁻¹, C, ENNReal.inv_pos.mpr hDfin, ENNReal.inv_ne_top.mpr hD.ne', hC, hCfin, ?_⟩
  filter_upwards [rnDeriv_le_of_le_smul P Q hPC,
    hQP.ae_le (rnDeriv_le_of_le_smul Q P hQD), Measure.inv_rnDeriv hQP]
      with s hsU hsD hsInv
  change (Q.rnDeriv P s)⁻¹ = P.rnDeriv Q s at hsInv
  exact ⟨(ENNReal.inv_le_inv' hsD).trans_eq hsInv, hsU⟩

/-- The real log likelihood has a genuine almost-everywhere finite bound. -/
theorem exists_bound_llr (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : boundedDom P Q) (hQP : boundedDom Q P) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ s ∂Q, ‖llr P Q s‖ ≤ B := by
  obtain ⟨L, U, hL, hLfin, hU, hUfin, hbounds⟩ := rnDeriv_bounds P Q hPQ hQP
  refine ⟨|Real.log L.toReal| + |Real.log U.toReal|, by positivity, ?_⟩
  filter_upwards [hbounds, Measure.rnDeriv_ne_top P Q] with s hs hsfin
  have hLreal : 0 < L.toReal := ENNReal.toReal_pos hL.ne' hLfin
  have hlo : L.toReal ≤ (P.rnDeriv Q s).toReal := ENNReal.toReal_mono hsfin hs.1
  have hhi : (P.rnDeriv Q s).toReal ≤ U.toReal := ENNReal.toReal_mono hUfin hs.2
  have hpos : 0 < (P.rnDeriv Q s).toReal := lt_of_lt_of_le hLreal hlo
  have hloglo := Real.log_le_log hLreal hlo
  have hloghi := Real.log_le_log hpos hhi
  rw [Real.norm_eq_abs, abs_le]
  change -(|Real.log L.toReal| + |Real.log U.toReal|) ≤ Real.log (P.rnDeriv Q s).toReal ∧
    Real.log (P.rnDeriv Q s).toReal ≤ |Real.log L.toReal| + |Real.log U.toReal|
  constructor
  · linarith [neg_abs_le (Real.log L.toReal), abs_nonneg (Real.log U.toReal)]
  · linarith [le_abs_self (Real.log U.toReal), abs_nonneg (Real.log L.toReal)]

theorem integrable_llr_reference (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : boundedDom P Q) (hQP : boundedDom Q P) : Integrable (llr P Q) Q := by
  obtain ⟨B, _, hB⟩ := exists_bound_llr P Q hPQ hQP
  exact (integrable_const B).mono' (measurable_llr P Q).aestronglyMeasurable hB

theorem integrable_llr_preparation (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : boundedDom P Q) (hQP : boundedDom Q P) : Integrable (llr P Q) P := by
  obtain ⟨B, _, hB⟩ := exists_bound_llr P Q hPQ hQP
  exact (integrable_const B).mono' (measurable_llr P Q).aestronglyMeasurable
    (hPQ.absolutelyContinuous.ae_le hB)

theorem finite_klDiv (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : boundedDom P Q) (hQP : boundedDom Q P) : klDiv P Q ≠ ∞ :=
  klDiv_ne_top_iff.mpr ⟨hPQ.absolutelyContinuous,
    integrable_llr_preparation P Q hPQ hQP⟩

/-- A constant log likelihood between equivalent probability measures forces
equality by normalization of the actual RN density. -/
theorem eq_of_llr_ae_const (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (hQP : Q ≪ P) {c : ℝ}
    (hconst : llr P Q =ᵐ[Q] fun _ => c) : P = Q := by
  have hreal : (fun s => (P.rnDeriv Q s).toReal) =ᵐ[Q] fun _ => Real.exp c := by
    filter_upwards [exp_llr_of_ac' P Q hQP, hconst] with s hs hc
    exact hs.symm.trans (congrArg Real.exp hc)
  have hmass : Real.exp c = 1 := by
    have hi := integral_congr_ae hreal
    rw [Measure.integral_toReal_rnDeriv hPQ] at hi
    simpa using hi.symm
  apply (Measure.rnDeriv_eq_one_iff_eq hPQ).mp
  filter_upwards [hreal, Measure.rnDeriv_ne_top P Q] with s hs hsfin
  have hone : (P.rnDeriv Q s).toReal = (1 : ℝ≥0∞).toReal := by simpa [hmass] using hs
  exact (ENNReal.toReal_eq_toReal_iff' hsfin ENNReal.one_ne_top).mp hone

namespace Contract

variable (D : Contract V Ω)

local instance (x : V) : IsProbabilityMeasure (D.preparation x) := D.probability x

theorem component_finiteReferenceEntropy (y : V) (x : D.Component y) :
    klDiv (D.preparation x.val) (D.preparation y) ≠ ∞ :=
  finite_klDiv _ _ x.property (D.reverse_boundedDom x.property)

/-- The legacy pointed contract, now constructed with its entropy premise
proved from the two-sided bounded domination in the component. -/
def pointedComponent (y : V) : InternalReferenceEntropyBridge.PointedContract (D.Component y) Ω where
  preparation x := D.preparation x.val
  probability x := D.probability x.val
  chosenReference := D.origin y
  finiteReferenceEntropy := D.component_finiteReferenceEntropy y
  operation := D.componentOperation y
  square := D.component_square y
  transparent := D.component_transparent y
  channel := D.channel
  markov := D.markov
  covariance p := D.covariance (p.1.val, p.2.val)

def referenceFactorization (y : V) : ReferenceEntropyFactorization.Contract (D.Component y) Ω :=
  (D.pointedComponent y).referenceFactorization

/-- The established likelihood-transport interface on the closed component. -/
def logDensityProcess (y : V) : LogDensityProcessTransport.Contract (D.Component y) Ω :=
  InternalReferenceEntropyBridge.ReferenceContract.logDensityProcess
    (D.referenceFactorization y) (D.origin y) rfl (D.component_transparent y)

theorem component_bounded_logDensity (y : V) (x : D.Component y) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ᵐ s ∂(D.logDensityProcess y).reference, ‖(D.logDensityProcess y).logDensity x s‖ ≤ B :=
  exists_bound_llr (D.preparation x.val) (D.preparation y)
    x.property (D.reverse_boundedDom x.property)

end Contract
end
end IDT.QMClosure.BoundedDominationProcess
