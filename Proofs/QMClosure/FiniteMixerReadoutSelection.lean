import Proofs.QMClosure.DenseExchangeReadoutSelection
import Proofs.QMClosure.DyadicResponseExtension

/-!
# Conditional response selection from one finite physical mixer

The native real differentiable completion, compatible attenuation/refinement,
fixed coherent sum, actual finite physical mixer, uniform scalar row mixing of
its vacuum tangent, common complete raw readout, conservation and reference
calibration remain supplied bridges. Conservation need hold only eventually
along each pair's attenuation sequence. No global linearity, reversibility,
flow, continuous derivative, Hessian, finite dimension or definite pairing is
assumed. The resulting pairing is relative to the supplied coherent sum and
may have a radical. Complex structure, Born actualization, composites and
physical scales are not derived.

The earlier attenuation-tangent result also assumed no flow. The difference
here is finite raw-response conservation in place of infinitesimal balance.
The final native corollary derives uniform attenuation from serial
multiplicativity on the dyadic localization and a supplied compatible dense
completion. Its explicit additive-embedding premise preserves the native
residual coherent merge; half scaling and density alone do not provide this
correspondence. The theorem does not establish that completion's physical
existence or the native origin of its additive embedding.
-/

namespace IDT.QMClosure.FiniteMixerReadoutSelection

noncomputable section
open Filter Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Exact finite response conservation for one scalar channel map. -/
def Conserves (F : V → ℝ) (a b c d : ℝ) : Prop :=
  ∀ x y, F (a • x + b • y) + F (c • x + d • y) = F x + F y

/-- A live nonnegative readout forces positive gain; no gain exponent is supplied. -/
theorem attenuation_gain_positive (F : V → ℝ) (nonnegative : ∀ x, 0 ≤ F x)
    (v₀ : V) (positive : 0 < F v₀) (r g : ℝ) (r_ne : r ≠ 0)
    (attenuation : ∀ z, F (r • z) = g * F z) : 0 < g := by
  have h := attenuation (r⁻¹ • v₀)
  simp only [smul_smul, mul_inv_cancel₀ r_ne, one_smul] at h
  have hp : 0 < g * F (r⁻¹ • v₀) := h ▸ positive
  exact lt_of_not_ge (fun hg => (not_lt_of_ge
    (mul_nonpos_of_nonpos_of_nonneg hg (nonnegative _))) hp)

/-- Finite raw conservation passes to the actual vacuum tangent using only
continuity of the response and one uniform attenuation. -/
theorem finite_conservation_passes_to_vacuum_tangent
    (F : V → ℝ) (hF : Continuous F)
    (r g : ℝ) (r_pos : 0 < r) (r_lt : r < 1) (g_pos : 0 < g)
    (attenuation : ∀ z, F (r • z) = g * F z)
    (P Q : V → V → V) (P_zero : P 0 0 = 0) (Q_zero : Q 0 0 = 0)
    (L₁ L₂ : V → V → V)
    (P_tangent : ∀ x y, HasDerivAt (fun t : ℝ => P (t • x) (t • y)) (L₁ x y) 0)
    (Q_tangent : ∀ x y, HasDerivAt (fun t : ℝ => Q (t • x) (t • y)) (L₂ x y) 0)
    (conservation : ∀ x y, ∀ᶠ n : ℕ in atTop,
      F (P ((r ^ n) • x) ((r ^ n) • y)) +
        F (Q ((r ^ n) • x) ((r ^ n) • y)) = F ((r ^ n) • x) + F ((r ^ n) • y)) :
    ∀ x y, F (L₁ x y) + F (L₂ x y) = F x + F y := by
  intro x y
  have seq : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_pow_atTop_nhds_zero_of_lt_one r_pos.le r_lt,
        Eventually.of_forall (fun n => pow_pos r_pos n)⟩
  have p_limit : Tendsto (fun n : ℕ => (r ^ n)⁻¹ • P ((r ^ n) • x) ((r ^ n) • y))
      atTop (𝓝 (L₁ x y)) := by
    simpa [P_zero] using (P_tangent x y).tendsto_slope_zero_right.comp seq
  have q_limit : Tendsto (fun n : ℕ => (r ^ n)⁻¹ • Q ((r ^ n) • x) ((r ^ n) • y))
      atTop (𝓝 (L₂ x y)) := by
    simpa [Q_zero] using (Q_tangent x y).tendsto_slope_zero_right.comp seq
  have normalized : ∀ᶠ n : ℕ in atTop,
      F ((r ^ n)⁻¹ • P ((r ^ n) • x) ((r ^ n) • y)) +
        F ((r ^ n)⁻¹ • Q ((r ^ n) • x) ((r ^ n) • y)) = F x + F y := by
    filter_upwards [conservation x y] with n hn
    have scale := AttenuationTangentReadoutSelection.attenuation_iterate F r g attenuation n
    have rescale (z : V) : F z = g ^ n * F ((r ^ n)⁻¹ • z) := by
      simpa only [smul_smul, mul_inv_cancel₀ (pow_ne_zero n (ne_of_gt r_pos)), one_smul]
        using scale ((r ^ n)⁻¹ • z)
    rw [rescale (P _ _), rescale (Q _ _), scale x, scale y, ← mul_add, ← mul_add] at hn
    exact mul_left_cancel₀ (pow_ne_zero n (ne_of_gt g_pos)) hn
  have limit := ((hF.tendsto _).comp p_limit).add ((hF.tendsto _).comp q_limit)
  apply tendsto_nhds_unique limit
  apply tendsto_const_nhds.congr'
  filter_upwards [normalized] with n hn using hn.symm

/-- A genuinely mixed row of a conserving live response cannot be singular. -/
theorem determinant_ne_zero (F : V → ℝ) (nonnegative : ∀ x, 0 ≤ F x)
    (zero : F 0 = 0) (v₀ : V) (positive : 0 < F v₀)
    (a b c d : ℝ) (b_ne : b ≠ 0) (conservation : Conserves F a b c d) :
    a * d - b * c ≠ 0 := by
  intro singular
  have vanishes (v : V) : F (b • v) = 0 := by
    have first : a • (b • v) + b • (-a • v) = 0 := by module
    have second : c • (b • v) + d • (-a • v) = 0 := by
      calc
        _ = (c * b - d * a) • v := by module
        _ = 0 := by rw [show c * b - d * a = 0 by nlinarith, zero_smul]
    have h := conservation (b • v) (-a • v)
    rw [first, second, zero] at h
    linarith [nonnegative (b • v), nonnegative (-a • v)]
  have h := vanishes (b⁻¹ • v₀)
  simp only [smul_smul, mul_inv_cancel₀ b_ne, one_smul] at h
  linarith

/-- Differentiating actual finite conservation in the two input slots. -/
theorem derivative_identities (F : V → ℝ) (hF : Differentiable ℝ F)
    (a b c d : ℝ) (conservation : Conserves F a b c d) (x y v : V) :
    (a * (fderiv ℝ F (a • x + b • y)) v +
      c * (fderiv ℝ F (c • x + d • y)) v = (fderiv ℝ F x) v) ∧
    (b * (fderiv ℝ F (a • x + b • y)) v +
      d * (fderiv ℝ F (c • x + d • y)) v = (fderiv ℝ F y) v) := by
  constructor
  · have left := ((hF _).hasFDerivAt.comp x
        (((hasFDerivAt_id x).const_smul a).add_const (b • y))).add
      ((hF _).hasFDerivAt.comp x
        (((hasFDerivAt_id x).const_smul c).add_const (d • y)))
    have right := (hF x).hasFDerivAt.add_const (F y)
    have identity : (fun z => F (a • z + b • y) + F (c • z + d • y)) =
        (fun z => F z + F y) := funext (fun z => conservation z y)
    change HasFDerivAt (fun z => F (a • z + b • y) + F (c • z + d • y)) _ x at left
    rw [identity] at left
    simpa using congrArg (fun L : V →L[ℝ] ℝ => L v) (left.unique right)
  · have left := ((hF _).hasFDerivAt.comp y
        (((hasFDerivAt_id y).const_smul b).const_add (a • x))).add
      ((hF _).hasFDerivAt.comp y
        (((hasFDerivAt_id y).const_smul d).const_add (c • x)))
    have right := (hF y).hasFDerivAt.const_add (F x)
    have identity : (fun z => F (a • x + b • z) + F (c • x + d • z)) =
        (fun z => F x + F z) := funext (fun z => conservation x z)
    change HasFDerivAt (fun z => F (a • x + b • z) + F (c • x + d • z)) _ y at left
    rw [identity] at left
    simpa using congrArg (fun L : V →L[ℝ] ℝ => L v) (left.unique right)

/-- One row mixing both inputs forces additivity of the derivative's base. -/
theorem derivative_additive_in_base (F : V → ℝ) (hF : Differentiable ℝ F)
    (nonnegative : ∀ x, 0 ≤ F x) (zero : F 0 = 0)
    (a b c d : ℝ) (a_ne : a ≠ 0) (b_ne : b ≠ 0)
    (det_ne : a * d - b * c ≠ 0) (conservation : Conserves F a b c d) :
    ∀ x y v, (fderiv ℝ F (x + y)) v = (fderiv ℝ F x) v + (fderiv ℝ F y) v := by
  have vacuum := DenseExchangeReadoutSelection.derivative_zero_at_vacuum F hF nonnegative zero
  have eliminated (x y v : V) :
      (a * d - b * c) * (fderiv ℝ F (a • x + b • y)) v =
        d * (fderiv ℝ F x) v - c * (fderiv ℝ F y) v := by
    obtain ⟨hx, hy⟩ := derivative_identities F hF a b c d conservation x y v
    linear_combination d * hx - c * hy
  have additive (x y v : V) : (fderiv ℝ F (a • x + b • y)) v =
      (fderiv ℝ F (a • x)) v + (fderiv ℝ F (b • y)) v := by
    apply mul_left_cancel₀ det_ne
    have hx := eliminated x 0 v
    have hy := eliminated 0 y v
    simp only [smul_zero, add_zero, zero_add, vacuum, mul_zero, sub_zero, zero_sub] at hx hy
    rw [mul_add, hx, hy, eliminated]
    ring
  intro x y v
  simpa only [smul_smul, mul_inv_cancel₀ a_ne, mul_inv_cancel₀ b_ne, one_smul]
    using additive (a⁻¹ • x) (b⁻¹ • y) v

/-- Additivity plus the actual differentiable potential forces symmetry,
without continuity of the derivative as a function of its base point. -/
theorem derivative_symmetric_of_additive (F : V → ℝ) (hF : Differentiable ℝ F)
    (zero : F 0 = 0)
    (additive : ∀ x y v, (fderiv ℝ F (x + y)) v =
      (fderiv ℝ F x) v + (fderiv ℝ F y) v) :
    ∀ x y, (fderiv ℝ F x) y = (fderiv ℝ F y) x := by
  have expansion (x y : V) : F (x + y) = F x + F y + (fderiv ℝ F y) x := by
    let g : ℝ → ℝ := fun t => F (t • x + y) - F (t • x) - t * (fderiv ℝ F y) x
    have hg (t : ℝ) : HasDerivAt g 0 t := by
      have h₁ := (hF (t • x + y)).hasFDerivAt.comp_hasDerivAt t
        (((hasDerivAt_id t).smul_const x).add_const y)
      have h₂ := InfinitesimalPairReadoutSelection.hasDerivAt_ray F hF x t
      convert (h₁.sub h₂).sub ((hasDerivAt_id t).mul_const ((fderiv ℝ F y) x)) using 1
      simp only [one_smul, additive]
      ring
    have h := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt)
      (fun t => (hg t).deriv) 1 0
    dsimp [g] at h
    simp only [one_smul, zero_smul, zero_add, zero, zero_mul, sub_zero, one_mul] at h
    linarith
  intro x y
  have hxy := expansion x y
  have hyx := expansion y x
  rw [add_comm y x] at hyx
  linarith

/-- Symmetry of the actual derivative integrates to a positive semidefinite
bilinear response, with zero third additive difference. -/
theorem bilinear_of_derivative_symmetry (F : V → ℝ) (hF : Differentiable ℝ F)
    (nonnegative : ∀ x, 0 ≤ F x) (zero : F 0 = 0)
    (symmetric : ∀ x y, (fderiv ℝ F x) y = (fderiv ℝ F y) x) :
    ∃ B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ,
      (∀ x y, B x y = B y x) ∧ (∀ x, F x = B x x / 2) ∧
      (∀ x, 0 ≤ B x x) ∧
      (∀ x y z, F (x + y + z) - F (x + y) - F (x + z) - F (y + z) +
        F x + F y + F z - F 0 = 0) := by
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    { toFun := fun x => (fderiv ℝ F x).toLinearMap
      map_add' := by
        intro x z
        ext y
        change (fderiv ℝ F (x + z)) y = (fderiv ℝ F x) y + (fderiv ℝ F z) y
        rw [symmetric (x + z) y, map_add, symmetric y x, symmetric y z]
      map_smul' := by
        intro r x
        ext y
        change (fderiv ℝ F (r • x)) y = r * (fderiv ℝ F x) y
        rw [symmetric (r • x) y, map_smul, symmetric y x]
        rfl }
  have representation (x : V) : F x = B x x / 2 := by
    have hd (t : ℝ) := InfinitesimalPairReadoutSelection.hasDerivAt_ray F hF x t
    have linear (t : ℝ) : deriv (fun s : ℝ => F (s • x)) t = (fderiv ℝ F x) x * t := by
      rw [(hd t).deriv, symmetric (t • x) x, map_smul]
      simp only [smul_eq_mul, mul_comm]
    have h := InfinitesimalReadoutSelection.quadratic_of_linear_derivative
      (fun t : ℝ => F (t • x)) (fun t => (hd t).differentiableAt)
      (by simpa using zero) ((fderiv ℝ F x) x) linear 1
    simpa [B] using h
  refine ⟨B, symmetric, representation, ?_, ?_⟩
  · intro x
    have h := nonnegative x
    rw [representation] at h
    linarith
  · exact InfinitesimalPairReadoutSelection.third_difference_of_bilinear F B symmetric representation

/-- One genuine row of a single finite conserving scalar map suffices.
An off-diagonal entry alone does not: the swap is a negative control below. -/
theorem finite_linear_mixer_selects_bilinear (F : V → ℝ) (hF : Differentiable ℝ F)
    (nonnegative : ∀ x, 0 ≤ F x) (zero : F 0 = 0)
    (v₀ : V) (positive : 0 < F v₀) (a b c d : ℝ)
    (mixing : a * b ≠ 0 ∨ c * d ≠ 0) (conservation : Conserves F a b c d) :
    ∃ B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ,
      (∀ x y, B x y = B y x) ∧ (∀ x, F x = B x x / 2) ∧
      (∀ x, 0 ≤ B x x) ∧
      (∀ x y z, F (x + y + z) - F (x + y) - F (x + z) - F (y + z) +
        F x + F y + F z - F 0 = 0) := by
  have first_row (a b c d : ℝ) (hab : a * b ≠ 0) (hc : Conserves F a b c d) := by
    have ha : a ≠ 0 := left_ne_zero_of_mul hab
    have hb : b ≠ 0 := right_ne_zero_of_mul hab
    have det := determinant_ne_zero F nonnegative zero v₀ positive a b c d hb hc
    exact bilinear_of_derivative_symmetry F hF nonnegative zero
      (derivative_symmetric_of_additive F hF zero
        (derivative_additive_in_base F hF nonnegative zero a b c d ha hb det hc))
  rcases mixing with hab | hcd
  · exact first_row a b c d hab conservation
  · apply first_row c d a b hcd
    intro x y
    rw [add_comm]
    exact conservation x y

/-- Integrated conditional selection from one finite mixer and one attenuation.
The gain is derived positive first, then selected as the square of attenuation. -/
theorem finite_mixer_selects_bilinear (F : V → ℝ) (hF : Differentiable ℝ F)
    (nonnegative : ∀ x, 0 ≤ F x) (zero : F 0 = 0)
    (v₀ : V) (positive : 0 < F v₀)
    (r g : ℝ) (r_pos : 0 < r) (r_lt : r < 1)
    (attenuation : ∀ z, F (r • z) = g * F z)
    (P Q : V → V → V) (P_zero : P 0 0 = 0) (Q_zero : Q 0 0 = 0)
    (a b c d : ℝ) (mixing : a * b ≠ 0 ∨ c * d ≠ 0)
    (P_tangent : ∀ x y, HasDerivAt (fun t : ℝ => P (t • x) (t • y)) (a • x + b • y) 0)
    (Q_tangent : ∀ x y, HasDerivAt (fun t : ℝ => Q (t • x) (t • y)) (c • x + d • y) 0)
    (conservation : ∀ x y, ∀ᶠ n : ℕ in atTop,
      F (P ((r ^ n) • x) ((r ^ n) • y)) +
        F (Q ((r ^ n) • x) ((r ^ n) • y)) = F ((r ^ n) • x) + F ((r ^ n) • y)) :
    g = r ^ 2 ∧ ∃ B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ,
      (∀ x y, B x y = B y x) ∧ (∀ x, F x = B x x / 2) ∧
      (∀ x, 0 ≤ B x x) ∧
      (∀ x y z, F (x + y + z) - F (x + y) - F (x + z) - F (y + z) +
        F x + F y + F z - F 0 = 0) := by
  have g_pos := attenuation_gain_positive F nonnegative v₀ positive r g (ne_of_gt r_pos) attenuation
  have linear_conservation := finite_conservation_passes_to_vacuum_tangent F hF.continuous
    r g r_pos r_lt g_pos attenuation P Q P_zero Q_zero _ _ P_tangent Q_tangent conservation
  obtain ⟨B, hs, hr, hp, hi⟩ := finite_linear_mixer_selects_bilinear F hF nonnegative zero
    v₀ positive a b c d mixing linear_conservation
  exact ⟨DenseExchangeReadoutSelection.attenuation_gain_of_bilinear F B hr v₀ positive
    r g attenuation, B, hs, hr, hp, hi⟩

/-- Native serial multiplicativity plus a supplied compatible dense completion
provides the attenuation law and a live unit reference. A supplied additive
embedding of native residuals identifies their merge with the completion's
coherent sum. One finite physical
mixer then selects gain 1/4, native doubling response 4, and bilinear readout.
Existence, accessibility and physical interpretation of the supplied completion
and mixer remain open. No quadratic native response is assumed. -/
theorem native_dyadic_finite_mixer_selects_bilinear
    (W : DyadicResponseExtension.Response)
    (doubling_ne : DyadicResponseExtension.doublingValue W ≠ 0)
    (embed : DyadicResponseExtension.Dyadic → V) (dense : DenseRange embed)
    (intertwines : ∀ z, embed (DyadicResponseExtension.half z) = (1 / 2 : ℝ) • embed z)
    (additive_embed : ∀ z w : LocalHistoryReadoutOrderWall.Residual,
      embed (DyadicResponseExtension.base (z + w)) =
        embed (DyadicResponseExtension.base z) + embed (DyadicResponseExtension.base w))
    (F : V → ℝ) (hF : Differentiable ℝ F)
    (nonnegative : ∀ x, 0 ≤ F x) (zero : F 0 = 0)
    (compatible : ∀ z, F (embed z) = DyadicResponseExtension.extension W doubling_ne z)
    (P Q : V → V → V) (P_zero : P 0 0 = 0) (Q_zero : Q 0 0 = 0)
    (a b c d : ℝ) (mixing : a * b ≠ 0 ∨ c * d ≠ 0)
    (P_tangent : ∀ x y, HasDerivAt (fun t : ℝ => P (t • x) (t • y)) (a • x + b • y) 0)
    (Q_tangent : ∀ x y, HasDerivAt (fun t : ℝ => Q (t • x) (t • y)) (c • x + d • y) 0)
    (conservation : ∀ x y, ∀ᶠ n : ℕ in atTop,
      F (P (((1 / 2 : ℝ) ^ n) • x) (((1 / 2 : ℝ) ^ n) • y)) +
        F (Q (((1 / 2 : ℝ) ^ n) • x) (((1 / 2 : ℝ) ^ n) • y)) =
          F (((1 / 2 : ℝ) ^ n) • x) + F (((1 / 2 : ℝ) ^ n) • y)) :
    DyadicResponseExtension.gain W = 1 / 4 ∧
      DyadicResponseExtension.doublingValue W = 4 ∧
      ∃ B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ,
        (∀ x y, B x y = B y x) ∧ (∀ x, F x = B x x / 2) ∧
        (∀ x, 0 ≤ B x x) ∧
        (∀ x y z, F (x + y + z) - F (x + y) - F (x + z) - F (y + z) +
          F x + F y + F z - F 0 = 0) ∧
        (∀ z w : LocalHistoryReadoutOrderWall.Residual,
          W.weight (z + w) = W.weight z + W.weight w +
            B (embed (DyadicResponseExtension.base z)) (embed (DyadicResponseExtension.base w))) ∧
        (∀ x y z : LocalHistoryReadoutOrderWall.Residual,
          W.weight (x + y + z) - W.weight (x + y) - W.weight (x + z) - W.weight (y + z) +
            W.weight x + W.weight y + W.weight z - W.weight 0 = 0) := by
  have attenuation := DyadicResponseExtension.compatible_dense_completion_half_scaling
    W doubling_ne embed dense intertwines F hF.continuous compatible
  have live : F (embed DyadicResponseExtension.one) = 1 :=
    (compatible _).trans (DyadicResponseExtension.extension_unital W doubling_ne)
  obtain ⟨gain, B, hs, hr, hp, hi⟩ := finite_mixer_selects_bilinear F hF nonnegative zero
    (embed DyadicResponseExtension.one) (by rw [live]; norm_num)
    (1 / 2) (DyadicResponseExtension.gain W) (by norm_num) (by norm_num) attenuation
    P Q P_zero Q_zero a b c d mixing P_tangent Q_tangent conservation
  norm_num at gain
  have inverse_product : DyadicResponseExtension.gain W *
      DyadicResponseExtension.doublingValue W = 1 := inv_mul_cancel₀ doubling_ne
  have native_value (z : LocalHistoryReadoutOrderWall.Residual) :
      W.weight z = F (embed (DyadicResponseExtension.base z)) :=
    ((compatible _).trans (DyadicResponseExtension.extension_base W doubling_ne z)).symm
  have embed_zero : embed (DyadicResponseExtension.base 0) = 0 := by
    have h : embed (DyadicResponseExtension.base 0) + 0 =
        embed (DyadicResponseExtension.base 0) + embed (DyadicResponseExtension.base 0) := by
      simpa only [add_zero, zero_add] using additive_embed 0 0
    exact (add_left_cancel h).symm
  refine ⟨gain, ?_, B, hs, hr, hp, hi, ?_, ?_⟩
  · rw [gain] at inverse_product
    linarith
  · intro z w
    simp only [native_value, additive_embed]
    exact InfinitesimalPairReadoutSelection.pair_expansion_of_bilinear F B hs hr _ _
  · intro x y z
    simp only [native_value, additive_embed, embed_zero]
    exact hi _ _ _

/-- A finite involutive reflection mixes both inputs, with no time family. -/
theorem rational_reflection_involutive (x y : V) :
    ((3 / 5 : ℝ) • ((3 / 5 : ℝ) • x + (4 / 5 : ℝ) • y) +
      (4 / 5 : ℝ) • ((4 / 5 : ℝ) • x - (3 / 5 : ℝ) • y) = x) ∧
    ((4 / 5 : ℝ) • ((3 / 5 : ℝ) • x + (4 / 5 : ℝ) • y) -
      (3 / 5 : ℝ) • ((4 / 5 : ℝ) • x - (3 / 5 : ℝ) • y) = y) := by
  constructor <;> module

/-- Once a live quadratic response has been selected, finite conservation
classifies the two scalar columns as orthonormal. -/
theorem finite_mixer_coefficients (F : V → ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (representation : ∀ x, F x = B x x / 2)
    (v₀ : V) (positive : 0 < F v₀) (a b c d : ℝ)
    (conservation : Conserves F a b c d) :
    a ^ 2 + c ^ 2 = 1 ∧ b ^ 2 + d ^ 2 = 1 ∧ a * b + c * d = 0 := by
  have zero : F 0 = 0 := by simp [representation]
  have scaling (t : ℝ) : F (t • v₀) = t ^ 2 * F v₀ := by
    simp only [representation, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have h₁ := conservation v₀ 0
  have h₂ := conservation 0 v₀
  have h₃ := conservation v₀ v₀
  simp only [smul_zero, add_zero, zero_add, zero, scaling] at h₁ h₂
  simp only [← add_smul, scaling] at h₃
  have first : a ^ 2 + c ^ 2 = 1 := by
    apply mul_right_cancel₀ (ne_of_gt positive)
    nlinarith only [h₁]
  have second : b ^ 2 + d ^ 2 = 1 := by
    apply mul_right_cancel₀ (ne_of_gt positive)
    nlinarith only [h₂]
  refine ⟨first, second, ?_⟩
  apply mul_right_cancel₀ (ne_of_gt positive)
  nlinarith [h₃, congrArg (fun t : ℝ => t * F v₀) first,
    congrArg (fun t : ℝ => t * F v₀) second]

/-- The reflection preserves every quadratic response, independently of a
continuous family of transformations or a dense orbit. -/
theorem rational_reflection_preserves_quadratic (F : V → ℝ)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (representation : ∀ x, F x = B x x / 2) :
    Conserves F (3 / 5) (4 / 5) (4 / 5) (-3 / 5) := by
  intro x y
  simp only [representation, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  ring

/-- Swap preserves every readout, including the quartic, but has no mixed row. -/
theorem swap_quartic_control :
    Conserves (fun x : ℝ => x ^ 4) 0 1 1 0 ∧
      ¬ ((0 : ℝ) * 1 ≠ 0 ∨ (1 : ℝ) * 0 ≠ 0) ∧
      ¬ ∃ k : ℝ, ∀ x : ℝ, x ^ 4 = k * x ^ 2 := by
  refine ⟨?_, by norm_num, ?_⟩
  · intro x y
    simp [add_comm]
  · rintro ⟨k, hk⟩
    have h₁ := hk 1
    have h₂ := hk 2
    norm_num at h₁ h₂
    linarith

/-- Data-only native/physical obligations, not conclusions or status upgrades. -/
inductive OpenObligation where
  | deriveNativeRealDifferentiableCompletion
  | deriveCompatibleAttenuationAndRefinement
  | deriveFixedCoherentSumAndScalarAction
  | deriveAdditiveEmbeddingOfNativeResidualMerge
  | deriveActualFinitePhysicalMixer
  | deriveUniformGenuineRowMixingOfActualVacuumTangent
  | deriveCommonCompleteRawReadoutConservationAndCalibration
  | removeOrInterpretPairingRadical
  | deriveComplexStructureAndBornActualization
  | deriveEntangledComposites
  | derivePhysicalScales
  deriving DecidableEq, Repr

def openObligations : List OpenObligation :=
  [ .deriveNativeRealDifferentiableCompletion, .deriveCompatibleAttenuationAndRefinement,
    .deriveFixedCoherentSumAndScalarAction, .deriveAdditiveEmbeddingOfNativeResidualMerge,
    .deriveActualFinitePhysicalMixer,
    .deriveUniformGenuineRowMixingOfActualVacuumTangent,
    .deriveCommonCompleteRawReadoutConservationAndCalibration, .removeOrInterpretPairingRadical,
    .deriveComplexStructureAndBornActualization, .deriveEntangledComposites, .derivePhysicalScales ]

end
end IDT.QMClosure.FiniteMixerReadoutSelection
