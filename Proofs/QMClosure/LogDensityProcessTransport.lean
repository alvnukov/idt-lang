import Proofs.QMClosure.ReferenceEntropyFactorization

/-!
# Finite elimination for actual log transport

This helper starts from an explicitly supplied almost-everywhere log-transport
identity on a common coupling. It proves a reciprocal-log witness by finite
algebraic elimination. No logarithm is assumed integrable. An application must
separately derive the transport premise from its likelihood-saturation result.
-/

namespace IDT.QMClosure.LogDensityProcessTransport

noncomputable section

open MeasureTheory

universe u v

variable {V : Type u} {Ω : Type v} [MeasurableSpace Ω]

/-- A separated zero sum on an independent probability pair has constant terms.
No measurability or integrability of the two functions is needed here. -/
theorem ae_sum_eq_zero_separates (α : Measure Ω) [IsProbabilityMeasure α]
    (f h : Ω → ℝ) (hsum : ∀ᵐ p ∂α.prod α, f p.1 + h p.2 = 0) :
    ∃ c : ℝ, (∀ᵐ s ∂α, f s = c) ∧ (∀ᵐ s ∂α, h s = -c) := by
  have hrows := Measure.ae_ae_of_ae_prod hsum
  obtain ⟨s₀, hs₀⟩ := hrows.exists
  refine ⟨f s₀, ?_, ?_⟩
  · filter_upwards [hrows] with s hs
    obtain ⟨t, ht⟩ := (hs₀.and hs).exists
    linarith [ht.1, ht.2]
  · filter_upwards [hs₀] with s hs
    linarith

/-- If the same function has zero sum on an independent pair, it vanishes. -/
theorem ae_self_sum_eq_zero (α : Measure Ω) [IsProbabilityMeasure α]
    (f : Ω → ℝ) (hsum : ∀ᵐ p ∂α.prod α, f p.1 + f p.2 = 0) :
    ∀ᵐ s ∂α, f s = 0 := by
  obtain ⟨c, hc, hneg⟩ := ae_sum_eq_zero_separates α f f hsum
  obtain ⟨s₀, hs₀⟩ := (hc.and hneg).exists
  have hzero : c = 0 := by linarith [hs₀.1, hs₀.2]
  simpa only [hzero] using hc

/-- Equal values on an independent pair force an almost-everywhere constant. -/
theorem ae_sub_eq_zero_constant (α : Measure Ω) [IsProbabilityMeasure α]
    (f : Ω → ℝ) (hsub : ∀ᵐ p ∂α.prod α, f p.1 - f p.2 = 0) :
    ∃ c : ℝ, ∀ᵐ s ∂α, f s = c := by
  have hsum : ∀ᵐ p ∂α.prod α, f p.1 + (-f p.2) = 0 := by
    simpa only [sub_eq_add_neg] using hsub
  obtain ⟨c, hc, _⟩ := ae_sum_eq_zero_separates α f (fun s => -f s) hsum
  exact ⟨c, hc⟩

/-- The raw operation and the actual common-coupling log identity used by this
helper. The transport field is a premise requiring a separate application proof. -/
structure Contract (V : Type u) (Ω : Type v) [MeasurableSpace Ω] where
  reference : Measure Ω
  referenceProbability : IsProbabilityMeasure reference
  coupling : Measure ((Ω × Ω) × (Ω × Ω))
  couplingProbability : IsProbabilityMeasure coupling
  inputMarginal : coupling.map Prod.fst = reference.prod reference
  outputMarginal : coupling.map Prod.snd = reference.prod reference
  origin : V
  operation : V × V → V × V
  square : ∀ p, operation (operation p) = p.swap
  diagonal : ∀ x, operation (x, x) = (x, x)
  logDensity : V → Ω → ℝ
  measurableLogDensity : ∀ x, Measurable (logDensity x)
  originLogDensity : ∀ᵐ s ∂reference, logDensity origin s = 0
  transport : ∀ p, ∀ᵐ z ∂coupling,
    logDensity p.1 z.1.1 + logDensity p.2 z.1.2 =
      logDensity (operation p).1 z.2.1 + logDensity (operation p).2 z.2.2

attribute [fun_prop] Contract.measurableLogDensity

namespace Contract

variable (D : Contract V Ω)

instance : IsProbabilityMeasure D.reference := D.referenceProbability
instance : IsProbabilityMeasure D.coupling := D.couplingProbability

/-- First raw coordinate after pairing with the chosen origin. -/
def a (x : V) : V := (D.operation (x, D.origin)).1

/-- Second raw coordinate after pairing with the chosen origin. -/
def b (x : V) : V := (D.operation (x, D.origin)).2

private theorem input_ae {P : Ω × Ω → Prop}
    (h : ∀ᵐ p ∂D.reference.prod D.reference, P p) :
    ∀ᵐ z ∂D.coupling, P z.1 := by
  apply ae_of_ae_map measurable_fst.aemeasurable
  simpa only [D.inputMarginal] using h

private theorem output_ae {P : Ω × Ω → Prop}
    (h : ∀ᵐ p ∂D.reference.prod D.reference, P p) :
    ∀ᵐ z ∂D.coupling, P z.2 := by
  apply ae_of_ae_map measurable_snd.aemeasurable
  simpa only [D.outputMarginal] using h

private theorem of_output_ae {P : Ω × Ω → Prop}
    (hP : MeasurableSet {p | P p}) (h : ∀ᵐ z ∂D.coupling, P z.2) :
    ∀ᵐ p ∂D.reference.prod D.reference, P p := by
  have hm := (ae_map_iff measurable_snd.aemeasurable hP).mpr h
  simpa only [D.outputMarginal] using hm

private theorem input_left_ae {P : Ω → Prop} (h : ∀ᵐ s ∂D.reference, P s) :
    ∀ᵐ z ∂D.coupling, P z.1.1 :=
  D.input_ae (Measure.quasiMeasurePreserving_fst.ae h)

private theorem input_right_ae {P : Ω → Prop} (h : ∀ᵐ s ∂D.reference, P s) :
    ∀ᵐ z ∂D.coupling, P z.1.2 :=
  D.input_ae (Measure.quasiMeasurePreserving_snd.ae h)

private theorem output_left_ae {P : Ω → Prop} (h : ∀ᵐ s ∂D.reference, P s) :
    ∀ᵐ z ∂D.coupling, P z.2.1 :=
  D.output_ae (Measure.quasiMeasurePreserving_fst.ae h)

private theorem output_right_ae {P : Ω → Prop} (h : ∀ᵐ s ∂D.reference, P s) :
    ∀ᵐ z ∂D.coupling, P z.2.2 :=
  D.output_ae (Measure.quasiMeasurePreserving_snd.ae h)

private theorem swap_origin (x : V) :
    D.operation (D.origin, x) = (D.b x, D.a x) := by
  simpa only [a, b, Prod.swap_prod_mk, Prod.swap] using
    ReferenceEntropyFactorization.operation_commutes_swap D.operation D.square
      (x, D.origin)

private theorem left_transport (x : V) : ∀ᵐ z ∂D.coupling,
    D.logDensity x z.1.1 =
      D.logDensity (D.a x) z.2.1 + D.logDensity (D.b x) z.2.2 := by
  filter_upwards [D.transport (x, D.origin), D.input_right_ae D.originLogDensity]
    with z ht hz
  simpa only [a, b, hz, add_zero] using ht

private theorem right_transport (x : V) : ∀ᵐ z ∂D.coupling,
    D.logDensity x z.1.2 =
      D.logDensity (D.b x) z.2.1 + D.logDensity (D.a x) z.2.2 := by
  filter_upwards [D.transport (D.origin, x), D.input_left_ae D.originLogDensity]
    with z ht hz
  simpa only [D.swap_origin x, hz, zero_add] using ht

/-- Origin-coordinate logarithms sum exactly, with no additive constant. -/
theorem origin_sum (x : V) : ∀ᵐ s ∂D.reference,
    D.logDensity (D.a x) s + D.logDensity (D.b x) s = D.logDensity x s := by
  let r : Ω → ℝ := fun s =>
    D.logDensity (D.a x) s + D.logDensity (D.b x) s - D.logDensity x s
  have hr : Measurable r := by dsimp [r]; fun_prop
  have hc : ∀ᵐ z ∂D.coupling, r z.2.1 + r z.2.2 = 0 := by
    filter_upwards [D.transport (x, x), D.left_transport x, D.right_transport x]
      with z hd hl hr'
    simp only [D.diagonal x] at hd
    dsimp [r]
    linarith
  have hp : ∀ᵐ p ∂D.reference.prod D.reference, r p.1 + r p.2 = 0 :=
    D.of_output_ae
      (measurableSet_eq_fun ((hr.comp measurable_fst).add (hr.comp measurable_snd))
        measurable_const) hc
  have hz := ae_self_sum_eq_zero D.reference r hp
  filter_upwards [hz] with s hs
  dsimp [r] at hs
  linarith

/-- The first finite elimination supplies two opposite separation constants. -/
theorem second_origin_separation (x : V) : ∃ c : ℝ,
    (∀ᵐ s ∂D.reference,
      D.logDensity (D.a (D.a x)) s + D.logDensity (D.b (D.b x)) s = c) ∧
    (∀ᵐ s ∂D.reference,
      D.logDensity (D.b (D.a x)) s + D.logDensity (D.a (D.b x)) s -
        D.logDensity x s = -c) := by
  let f : Ω → ℝ := fun s =>
    D.logDensity (D.a (D.a x)) s + D.logDensity (D.b (D.b x)) s
  let h : Ω → ℝ := fun s =>
    D.logDensity (D.b (D.a x)) s + D.logDensity (D.a (D.b x)) s -
      D.logDensity x s
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hh : Measurable h := by dsimp [h]; fun_prop
  have hsquare : D.operation (D.a x, D.b x) = (D.origin, x) := by
    simpa only [a, b, Prod.mk.eta, Prod.swap_prod_mk] using
      D.square (x, D.origin)
  have hc : ∀ᵐ z ∂D.coupling, f z.2.1 + h z.2.2 = 0 := by
    filter_upwards [D.left_transport (D.a x), D.right_transport (D.b x),
      D.transport (D.a x, D.b x), D.output_left_ae D.originLogDensity]
      with z hl hr ht hz
    simp only [hsquare, hz, zero_add] at ht
    dsimp [f, h]
    linarith
  have hp : ∀ᵐ p ∂D.reference.prod D.reference, f p.1 + h p.2 = 0 :=
    D.of_output_ae
      (measurableSet_eq_fun ((hf.comp measurable_fst).add (hh.comp measurable_snd))
        measurable_const) hc
  exact ae_sum_eq_zero_separates D.reference f h hp

/-- The mixed second origin coordinates differ by an almost-everywhere constant. -/
theorem mixed_origin_difference (x : V) : ∃ c : ℝ, ∀ᵐ s ∂D.reference,
    D.logDensity (D.a (D.b x)) s - D.logDensity (D.b (D.a x)) s = c := by
  let d : Ω → ℝ := fun s =>
    D.logDensity (D.a (D.b x)) s - D.logDensity (D.b (D.a x)) s
  have hd : Measurable d := by dsimp [d]; fun_prop
  have hc : ∀ᵐ z ∂D.coupling, d z.2.1 - d z.2.2 = 0 := by
    filter_upwards [D.left_transport (D.a x), D.left_transport (D.b x),
      D.left_transport x, D.input_left_ae (D.origin_sum x),
      D.output_left_ae (D.origin_sum (D.a x)),
      D.output_right_ae (D.origin_sum (D.b x))]
      with z ha hb hx hi hoa hob
    dsimp [d]
    linarith
  have hp : ∀ᵐ p ∂D.reference.prod D.reference, d p.1 - d p.2 = 0 :=
    D.of_output_ae
      (measurableSet_eq_fun ((hd.comp measurable_fst).sub (hd.comp measurable_snd))
        measurable_const) hc
  exact ae_sub_eq_zero_constant D.reference d hp

/-- A second-order origin recurrence holds up to one real constant. -/
theorem origin_quadratic_constant (x : V) : ∃ c : ℝ, ∀ᵐ s ∂D.reference,
    D.logDensity (D.a (D.a x)) s - D.logDensity (D.a x) s +
      D.logDensity x s / 2 = c := by
  obtain ⟨c, hc, _⟩ := D.second_origin_separation x
  obtain ⟨d, hd⟩ := D.mixed_origin_difference x
  refine ⟨(c + d) / 2, ?_⟩
  filter_upwards [hc, hd, D.origin_sum x, D.origin_sum (D.a x),
    D.origin_sum (D.b x)] with s hcs hds hx ha hb
  linarith

/-- Four actual raw origin iterates realize the negative quarter logarithm up
 to an almost-everywhere additive constant. This is a pure log-transport result. -/
theorem reciprocal_log_witness (x : V) : ∃ c : ℝ, ∀ᵐ s ∂D.reference,
    D.logDensity (D.a (D.a (D.a (D.a x)))) s = -D.logDensity x s / 4 + c := by
  obtain ⟨c₀, h₀⟩ := D.origin_quadratic_constant x
  obtain ⟨c₁, h₁⟩ := D.origin_quadratic_constant (D.a x)
  obtain ⟨c₂, h₂⟩ := D.origin_quadratic_constant (D.a (D.a x))
  refine ⟨c₂ + c₁ + c₀ / 2, ?_⟩
  filter_upwards [h₀, h₁, h₂] with s hs₀ hs₁ hs₂
  linarith

end Contract
end

end IDT.QMClosure.LogDensityProcessTransport
