import Proofs.QMClosure.LogDensityProcessTransport
import Mathlib.MeasureTheory.Function.EssSup

/-!
# Rigidity of individually bounded transported logarithms

Each preparation has its own finite almost-everywhere interval. No common
interval over preparations or logarithmic integrability premise is supplied.
-/

namespace IDT.QMClosure.BoundedLogProcessRigidity

noncomputable section

open MeasureTheory Filter

universe u v w

/-- Finite sharp almost-everywhere bounds. Sharpness concerns all constant
bounds, without requiring either endpoint to be attained. -/
structure SharpBounds {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) where
  lower : ℝ
  upper : ℝ
  lower_ae : ∀ᵐ s ∂μ, lower ≤ f s
  upper_ae : ∀ᵐ s ∂μ, f s ≤ upper
  lower_sharp : ∀ c : ℝ, (∀ᵐ s ∂μ, c ≤ f s) → c ≤ lower
  upper_sharp : ∀ c : ℝ, (∀ᵐ s ∂μ, f s ≤ c) → upper ≤ c

namespace SharpBounds

variable {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} {f : α → ℝ} {g : β → ℝ}

def width (B : SharpBounds μ f) : ℝ := B.upper - B.lower

theorem exists_of_bounded [IsProbabilityMeasure μ]
    (h : ∃ lo hi : ℝ, ∀ᵐ s ∂μ, lo ≤ f s ∧ f s ≤ hi) :
    Nonempty (SharpBounds μ f) := by
  obtain ⟨lo, hi, h⟩ := h
  have hlo : ∀ᵐ s ∂μ, lo ≤ f s := h.mono fun _ hs => hs.1
  have hhi : ∀ᵐ s ∂μ, f s ≤ hi := h.mono fun _ hs => hs.2
  have hbelow : IsBoundedUnder (· ≥ ·) (ae μ) f := ⟨lo, hlo⟩
  have habove : IsBoundedUnder (· ≤ ·) (ae μ) f := ⟨hi, hhi⟩
  refine ⟨⟨essInf f μ, essSup f μ, ae_essInf_le hbelow, ae_le_essSup habove,
    ?_, ?_⟩⟩
  · intro c hc
    exact le_liminf_of_le habove.isCoboundedUnder_ge hc
  · intro c hc
    exact limsup_le_of_le hbelow.isCoboundedUnder_le hc

theorem width_nonneg [IsProbabilityMeasure μ] (B : SharpBounds μ f) : 0 ≤ B.width := by
  obtain ⟨s, hs⟩ := (B.lower_ae.and B.upper_ae).exists
  dsimp [width]
  linarith [hs.1, hs.2]

theorem endpoints_eq (B C : SharpBounds μ f) :
    B.lower = C.lower ∧ B.upper = C.upper := by
  exact ⟨le_antisymm (C.lower_sharp _ B.lower_ae) (B.lower_sharp _ C.lower_ae),
    le_antisymm (B.upper_sharp _ C.upper_ae) (C.upper_sharp _ B.upper_ae)⟩

theorem width_eq (B C : SharpBounds μ f) : B.width = C.width := by
  obtain ⟨hl, hu⟩ := B.endpoints_eq C
  simp only [width, hl, hu]

def congr {g : α → ℝ} (B : SharpBounds μ f) (h : f =ᵐ[μ] g) :
    SharpBounds μ g where
  lower := B.lower
  upper := B.upper
  lower_ae := by filter_upwards [B.lower_ae, h] with s hs he; simpa [← he] using hs
  upper_ae := by filter_upwards [B.upper_ae, h] with s hs he; simpa [← he] using hs
  lower_sharp := by
    intro c hc
    apply B.lower_sharp c
    filter_upwards [hc, h] with s hs he
    simpa [he] using hs
  upper_sharp := by
    intro c hc
    apply B.upper_sharp c
    filter_upwards [hc, h] with s hs he
    simpa [he] using hs

def pullback (B : SharpBounds ν g) (hg : Measurable g)
    (T : α → β) (hT : Measurable T) (hm : μ.map T = ν) :
    SharpBounds μ (fun s => g (T s)) where
  lower := B.lower
  upper := B.upper
  lower_ae := by
    apply ae_of_ae_map (μ := μ) (p := fun y => B.lower ≤ g y) hT.aemeasurable
    simpa only [hm] using B.lower_ae
  upper_ae := by
    apply ae_of_ae_map (μ := μ) (p := fun y => g y ≤ B.upper) hT.aemeasurable
    simpa only [hm] using B.upper_ae
  lower_sharp := by
    intro c hc
    apply B.lower_sharp c
    have hmap := (ae_map_iff hT.aemeasurable (measurableSet_le measurable_const hg)).mpr hc
    simpa only [hm] using hmap
  upper_sharp := by
    intro c hc
    apply B.upper_sharp c
    have hmap := (ae_map_iff hT.aemeasurable (measurableSet_le hg measurable_const)).mpr hc
    simpa only [hm] using hmap

def productSum [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (B : SharpBounds μ f) (C : SharpBounds ν g) :
    SharpBounds (μ.prod ν) (fun p => f p.1 + g p.2) where
  lower := B.lower + C.lower
  upper := B.upper + C.upper
  lower_ae := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae B.lower_ae,
      Measure.quasiMeasurePreserving_snd.ae C.lower_ae] with p hp hq
    exact add_le_add hp hq
  upper_ae := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae B.upper_ae,
      Measure.quasiMeasurePreserving_snd.ae C.upper_ae] with p hp hq
    exact add_le_add hp hq
  lower_sharp := by
    intro c hc
    have hrows := Measure.ae_ae_of_ae_prod hc
    have hbound : ∀ᵐ s ∂μ, c - C.lower ≤ f s := by
      filter_upwards [hrows] with s hs
      have ht : c - f s ≤ C.lower := C.lower_sharp _ (hs.mono fun t ht => by linarith)
      linarith
    have ht := B.lower_sharp _ hbound
    linarith
  upper_sharp := by
    intro c hc
    have hrows := Measure.ae_ae_of_ae_prod hc
    have hbound : ∀ᵐ s ∂μ, f s ≤ c - C.upper := by
      filter_upwards [hrows] with s hs
      have ht : C.upper ≤ c - f s := C.upper_sharp _ (hs.mono fun t ht => by linarith)
      linarith
    have ht := B.upper_sharp _ hbound
    linarith

@[simp] theorem width_productSum [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (B : SharpBounds μ f) (C : SharpBounds ν g) :
    (B.productSum C).width = B.width + C.width := by
  dsimp [width, productSum]
  ring

def translate (B : SharpBounds μ f) (c : ℝ) :
    SharpBounds μ (fun s => f s + c) where
  lower := B.lower + c
  upper := B.upper + c
  lower_ae := B.lower_ae.mono fun _ hs => by linarith
  upper_ae := B.upper_ae.mono fun _ hs => by linarith
  lower_sharp := by
    intro d hd
    have ht := B.lower_sharp (d - c) (hd.mono fun _ hs => by linarith)
    linarith
  upper_sharp := by
    intro d hd
    have ht := B.upper_sharp (d - c) (hd.mono fun _ hs => by linarith)
    linarith

@[simp] theorem width_translate (B : SharpBounds μ f) (c : ℝ) :
    (B.translate c).width = B.width := by
  dsimp [width, translate]
  ring

def negDivideTranslate (B : SharpBounds μ f) (k c : ℝ) (hk : 0 < k) :
    SharpBounds μ (fun s => -f s / k + c) where
  lower := -B.upper / k + c
  upper := -B.lower / k + c
  lower_ae := B.upper_ae.mono fun _ hs => by
    have ht := (div_le_div_iff_of_pos_right hk).2 (neg_le_neg hs)
    linarith
  upper_ae := B.lower_ae.mono fun _ hs => by
    have ht := (div_le_div_iff_of_pos_right hk).2 (neg_le_neg hs)
    linarith
  lower_sharp := by
    intro d hd
    have hb : ∀ᵐ s ∂μ, f s ≤ (c - d) * k := hd.mono fun s hs => by
      have ht : f s / k ≤ c - d := by
        rw [neg_div] at hs
        linarith
      exact (div_le_iff₀ hk).1 ht
    have ht := B.upper_sharp _ hb
    have ht' : -B.upper / k ≥ d - c :=
      (le_div_iff₀ hk).2 (by nlinarith)
    linarith
  upper_sharp := by
    intro d hd
    have hb : ∀ᵐ s ∂μ, (c - d) * k ≤ f s := hd.mono fun s hs => by
      have ht : c - d ≤ f s / k := by
        rw [neg_div] at hs
        linarith
      have ht' := (le_div_iff₀ hk).1 ht
      linarith
    have ht := B.lower_sharp _ hb
    have ht' : -B.lower / k ≤ d - c :=
      (div_le_iff₀ hk).2 (by nlinarith)
    linarith

@[simp] theorem width_negDivideTranslate (B : SharpBounds μ f) (k c : ℝ) (hk : 0 < k) :
    (B.negDivideTranslate k c hk).width = B.width / k := by
  dsimp [width, negDivideTranslate]
  ring

theorem width_eq_of_difference_constant {g : α → ℝ}
    (B : SharpBounds μ f) (C : SharpBounds μ g)
    (h : ∃ c : ℝ, ∀ᵐ s ∂μ, f s - g s = c) : B.width = C.width := by
  obtain ⟨c, hc⟩ := h
  have he : (fun s => g s + c) =ᵐ[μ] f := hc.mono fun s hs => by linarith
  exact (B.width_eq ((C.translate c).congr he)).trans (C.width_translate c)

theorem width_eq_of_sum_constant {g : α → ℝ}
    (B : SharpBounds μ f) (C : SharpBounds μ g)
    (h : ∃ c : ℝ, ∀ᵐ s ∂μ, f s + g s = c) : B.width = C.width := by
  obtain ⟨c, hc⟩ := h
  have he : (fun s => -g s / 1 + c) =ᵐ[μ] f := by
    filter_upwards [hc] with s hs
    simpa only [div_one] using (show -g s + c = f s by linarith)
  calc
    B.width = ((C.negDivideTranslate 1 c (by norm_num)).congr he).width := B.width_eq _
    _ = C.width := by
      change (C.negDivideTranslate 1 c (by norm_num)).width = C.width
      rw [width_negDivideTranslate, div_one]

theorem ae_constant_of_width_zero [IsProbabilityMeasure μ] (B : SharpBounds μ f)
    (h : B.width = 0) : ∃ c : ℝ, ∀ᵐ s ∂μ, f s = c := by
  refine ⟨B.lower, ?_⟩
  filter_upwards [B.lower_ae, B.upper_ae] with s hlo hhi
  dsimp [width] at h
  linarith

end SharpBounds

namespace Contract

open LogDensityProcessTransport

variable {V : Type u} {Ω : Type v} [MeasurableSpace Ω]

/-- Individually finite essential ranges force every transported logarithm to
be almost-everywhere constant. All raw-operation and coupling assumptions are
exactly those already recorded by `LogDensityProcessTransport.Contract`. -/
theorem ae_constant_of_individually_bounded (D : LogDensityProcessTransport.Contract V Ω)
    (hbounded : ∀ x, ∃ lo hi : ℝ, ∀ᵐ s ∂D.reference,
      lo ≤ D.logDensity x s ∧ D.logDensity x s ≤ hi) :
    ∀ x, ∃ c : ℝ, ∀ᵐ s ∂D.reference, D.logDensity x s = c := by
  let B : ∀ x, SharpBounds D.reference (D.logDensity x) :=
    fun x => Classical.choice (SharpBounds.exists_of_bounded (hbounded x))
  let W : V → ℝ := fun x => (B x).width
  have hsplit : ∀ x, W x = W (D.a x) + W (D.b x) := by
    intro x
    let I := (B x).productSum (B D.origin)
    let O := (B (D.a x)).productSum (B (D.b x))
    let IP := I.pullback
      ((D.measurableLogDensity x).comp measurable_fst |>.add
        ((D.measurableLogDensity D.origin).comp measurable_snd))
      Prod.fst measurable_fst D.inputMarginal
    let OP := O.pullback
      ((D.measurableLogDensity (D.a x)).comp measurable_fst |>.add
        ((D.measurableLogDensity (D.b x)).comp measurable_snd))
      Prod.snd measurable_snd D.outputMarginal
    have he : (fun z : (Ω × Ω) × (Ω × Ω) =>
        D.logDensity x z.1.1 + D.logDensity D.origin z.1.2) =ᵐ[D.coupling]
        (fun z => D.logDensity (D.a x) z.2.1 + D.logDensity (D.b x) z.2.2) := by
      simpa only [LogDensityProcessTransport.Contract.a,
        LogDensityProcessTransport.Contract.b] using D.transport (x, D.origin)
    have hw := (IP.congr he).width_eq OP
    have horigin : (B D.origin).width = 0 := by
      have hl := (B D.origin).lower_sharp 0 (D.originLogDensity.mono fun _ hs => by simp [hs])
      have hu := (B D.origin).upper_sharp 0 (D.originLogDensity.mono fun _ hs => by simp [hs])
      have hn := (B D.origin).width_nonneg
      dsimp [SharpBounds.width] at *
      linarith
    change I.width = O.width at hw
    dsimp [I, O] at hw
    rw [SharpBounds.width_productSum, SharpBounds.width_productSum, horigin,
      add_zero] at hw
    exact hw
  have hhalf : ∀ x, W (D.a x) = W x / 2 := by
    intro x
    obtain ⟨c, hc, _⟩ := D.second_origin_separation x
    have hsame := (B (D.a (D.a x))).width_eq_of_sum_constant
      (B (D.b (D.b x))) ⟨c, hc⟩
    have hmixed := (B (D.a (D.b x))).width_eq_of_difference_constant
      (B (D.b (D.a x))) (D.mixed_origin_difference x)
    change W (D.a (D.a x)) = W (D.b (D.b x)) at hsame
    change W (D.a (D.b x)) = W (D.b (D.a x)) at hmixed
    have h₀ := hsplit x
    have h₁ := hsplit (D.a x)
    have h₂ := hsplit (D.b x)
    linarith
  intro x
  obtain ⟨c, hc⟩ := D.reciprocal_log_witness x
  let ax4 := D.a (D.a (D.a (D.a x)))
  have he : (fun s => -D.logDensity x s / 4 + c) =ᵐ[D.reference]
      D.logDensity ax4 := hc.mono fun _ hs => hs.symm
  have hquarter := (B ax4).width_eq
    (((B x).negDivideTranslate 4 c (by norm_num)).congr he)
  change W ax4 = ((B x).negDivideTranslate 4 c (by norm_num)).width at hquarter
  rw [SharpBounds.width_negDivideTranslate] at hquarter
  change W ax4 = W x / 4 at hquarter
  have h₀ := hhalf x
  have h₁ := hhalf (D.a x)
  have h₂ := hhalf (D.a (D.a x))
  have h₃ := hhalf (D.a (D.a (D.a x)))
  have hzero : (B x).width = 0 := by
    change W x = 0
    dsimp [ax4] at hquarter
    linarith
  exact (B x).ae_constant_of_width_zero hzero

end Contract
end

end IDT.QMClosure.BoundedLogProcessRigidity
