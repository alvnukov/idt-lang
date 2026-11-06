import Mathlib

/-!
# Linearization from event midpoint mixing

A zero-containing, midpoint-closed domain in a rational vector space carries
a unique rational-linear readout whenever a single coordinate readout vanishes
at zero, preserves midpoints on that domain, and the domain spans the space.
There is no assumed global additivity, rational mixing, positivity or continuity.

The proof uses the additive subgroup of differences of equally rescaled dyadic
mixtures of graph points, followed by integer saturation (clearing rational
denominators). It therefore needs no finite-dimensional hypothesis.

This is a theorem about classical event mixing and coordinate noncontextuality.
It supplies neither physically generated events nor coherent amplitude mixing,
Born actualization, positivity, density matrices, or full QM closure. In a real
ambient space it only gives rational linearity on the stated rational span;
general real linearity or continuity is not asserted.
-/

namespace IDT.QMClosure.DyadicMixtureLinearization

noncomputable section

private theorem dyadic_coefficient (n m : ℕ) :
    (2 : ℚ) ^ (n + m + 1) * (1 / 2) * ((2 : ℚ) ^ m)⁻¹ = 2 ^ n := by
  rw [pow_add, pow_add]
  field_simp

section DyadicSubgroup

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable (G : Set W) (hzero : (0 : W) ∈ G)
variable (hmid : ∀ x ∈ G, ∀ y ∈ G, (1 / 2 : ℚ) • (x + y) ∈ G)

include hzero hmid in
private theorem down_mem (x : W) (hx : x ∈ G) (n : ℕ) :
    ((2 : ℚ) ^ n)⁻¹ • x ∈ G := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      have hm := hmid _ ih 0 hzero
      simpa [pow_succ, mul_inv_rev, smul_smul, div_eq_mul_inv] using hm

/-- Dyadic rescalings of differences of graph points form an additive group.
The same exponent on both endpoints is the zero-padding discipline. -/
private def dyadicSubgroup : AddSubgroup W where
  carrier := {z | ∃ (n : ℕ) (x : W), x ∈ G ∧ ∃ y ∈ G,
    (2 : ℚ) ^ n • (x - y) = z}
  zero_mem' := ⟨0, 0, hzero, 0, hzero, by simp⟩
  add_mem' := by
    rintro z w ⟨n, x, hx, y, hy, rfl⟩ ⟨m, u, hu, v, hv, rfl⟩
    let a := ((2 : ℚ) ^ m)⁻¹ • x
    let b := ((2 : ℚ) ^ m)⁻¹ • y
    let c := ((2 : ℚ) ^ n)⁻¹ • u
    let d := ((2 : ℚ) ^ n)⁻¹ • v
    refine ⟨n + m + 1, (1 / 2 : ℚ) • (a + c),
      hmid _ (down_mem G hzero hmid x hx m) _ (down_mem G hzero hmid u hu n),
      (1 / 2 : ℚ) • (b + d),
      hmid _ (down_mem G hzero hmid y hy m) _ (down_mem G hzero hmid v hv n), ?_⟩
    dsimp [a, b, c, d]
    simp only [smul_sub, smul_add, smul_smul, ← mul_assoc]
    rw [dyadic_coefficient n m,
      show (2 : ℚ) ^ (n + m + 1) * (1 / 2) * ((2 : ℚ) ^ n)⁻¹ = 2 ^ m by
        simpa [Nat.add_comm n m] using dyadic_coefficient m n]
    abel
  neg_mem' := by
    rintro z ⟨n, x, hx, y, hy, rfl⟩
    exact ⟨n, y, hy, x, hx, by simp [← smul_neg, neg_sub]⟩

private theorem generator_mem_dyadicSubgroup (x : W) (hx : x ∈ G) :
    x ∈ dyadicSubgroup G hzero hmid :=
  ⟨0, x, hx, 0, hzero, by simp⟩

end DyadicSubgroup

section Saturation

variable {W : Type*} [AddCommGroup W] [Module ℚ W]

/-- Clearing denominators gives a rational submodule from an additive subgroup.
Integer witnesses, rather than arbitrary rational witnesses, ensure that
addition never assumes rational closure of the original subgroup. -/
private def integerSaturation (H : AddSubgroup W) : Submodule ℚ W where
  carrier := {z | ∃ n : ℤ, n ≠ 0 ∧ n • z ∈ H}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have hx' := H.zsmul_mem hx m
    have hy' := H.zsmul_mem hy n
    convert H.add_mem hx' hy' using 1
    simp [smul_add, smul_smul, mul_comm]
  smul_mem' := by
    rintro q x ⟨n, hn, hx⟩
    refine ⟨n * (q.den : ℤ), mul_ne_zero hn (by exact_mod_cast q.den_ne_zero), ?_⟩
    have hden : (q.den : ℚ) * q = q.num := by
      conv_lhs => arg 2; rw [← q.num_div_den]
      field_simp
    convert H.zsmul_mem hx q.num using 1
    simp only [← Int.cast_smul_eq_zsmul ℚ, Int.cast_mul, Int.cast_natCast,
      smul_smul]
    congr 1
    calc
      (n : ℚ) * q.den * q = n * (q.den * q) := by ring
      _ = q.num * n := by rw [hden]; ring

private theorem subgroup_le_integerSaturation (H : AddSubgroup W) {x : W}
    (hx : x ∈ H) : x ∈ integerSaturation H :=
  ⟨1, one_ne_zero, by simpa using hx⟩

end Saturation

section Linearization

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (D : Set V) (p : V → ℝ)
variable (hzero : (0 : V) ∈ D) (hpzero : p 0 = 0)
variable (hclosed : ∀ x ∈ D, ∀ y ∈ D, (1 / 2 : ℚ) • (x + y) ∈ D)
variable (hpres : ∀ x ∈ D, ∀ y ∈ D,
  p ((1 / 2 : ℚ) • (x + y)) = (p x + p y) / 2)

private def readoutGraph : Set (V × ℝ) := {z | z.1 ∈ D ∧ z.2 = p z.1}

omit [Module ℚ V] in
include hzero hpzero in
private theorem graph_zero : (0 : V × ℝ) ∈ readoutGraph D p := by
  exact ⟨hzero, hpzero.symm⟩

include hclosed hpres in
private theorem graph_midpoint : ∀ x ∈ readoutGraph D p,
    ∀ y ∈ readoutGraph D p, (1 / 2 : ℚ) • (x + y) ∈ readoutGraph D p := by
  intro x hx y hy
  refine ⟨hclosed x.1 hx.1 y.1 hy.1, ?_⟩
  change (1 / 2 : ℚ) • (x.2 + y.2) = p ((1 / 2 : ℚ) • (x.1 + y.1))
  rw [hx.2, hy.2, hpres x.1 hx.1 y.1 hy.1]
  norm_num [Rat.smul_def, div_eq_mul_inv, mul_comm]
  ring

include hzero hpzero hclosed hpres

private theorem graph_span_no_vertical (z : V × ℝ)
    (hz : z ∈ Submodule.span ℚ (readoutGraph D p)) (hfst : z.1 = 0) : z = 0 := by
  let G := readoutGraph D p
  have gzero : (0 : V × ℝ) ∈ G := graph_zero D p hzero hpzero
  have gmid := graph_midpoint D p hclosed hpres
  let H := dyadicSubgroup G gzero gmid
  have hsat : Submodule.span ℚ G ≤ integerSaturation H := by
    refine Submodule.span_le.mpr ?_
    intro w hw
    exact subgroup_le_integerSaturation H
      (generator_mem_dyadicSubgroup G gzero gmid w hw)
  obtain ⟨k, hk, n, x, hx, y, hy, hxy⟩ := hsat hz
  have hknz : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  have hpow : (2 : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have heq : x.1 = y.1 := by
    have h := congrArg Prod.fst hxy
    change (2 : ℚ) ^ n • (x.1 - y.1) = k • z.1 at h
    rw [hfst, smul_zero] at h
    exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_left hpow)
  have hread : x.2 = y.2 := hx.2.trans ((congrArg p heq).trans hy.2.symm)
  have hwhole : x = y := Prod.ext heq hread
  have hkz : k • z = (0 : V × ℝ) := by simpa [hwhole] using hxy.symm
  rw [← Int.cast_smul_eq_zsmul ℚ] at hkz
  exact (smul_eq_zero.mp hkz).resolve_left hknz

/-- A midpoint readout extends uniquely over its exact rational span.
The spanning hypothesis is explicit; no full event-domain generation follows.
-/
theorem exists_unique_rational_linear_extension
    (hspan : Submodule.span ℚ D = ⊤) :
    ∃! ell : V →ₗ[ℚ] ℝ, ∀ x ∈ D, ell x = p x := by
  let S := Submodule.span ℚ (readoutGraph D p)
  let fst : S →ₗ[ℚ] V := (LinearMap.fst ℚ V ℝ).comp S.subtype
  let snd : S →ₗ[ℚ] ℝ := (LinearMap.snd ℚ V ℝ).comp S.subtype
  have hinj : Function.Injective fst := by
    intro x y hxy
    have hz : (x - y : S).val = 0 := graph_span_no_vertical D p hzero hpzero
      hclosed hpres _ (x - y).property (by simpa [fst] using sub_eq_zero.mpr hxy)
    exact sub_eq_zero.mp (Subtype.val_injective hz)
  have hsurj : Function.Surjective fst := by
    have hrange : Submodule.span ℚ D ≤ LinearMap.range fst := by
      refine Submodule.span_le.mpr ?_
      intro x hx
      exact ⟨⟨(x, p x), Submodule.subset_span ⟨hx, rfl⟩⟩, rfl⟩
    exact LinearMap.range_eq_top.mp (top_le_iff.mp (hspan ▸ hrange))
  let e : S ≃ₗ[ℚ] V := LinearEquiv.ofBijective fst ⟨hinj, hsurj⟩
  let ell : V →ₗ[ℚ] ℝ := snd.comp e.symm.toLinearMap
  have hext : ∀ x ∈ D, ell x = p x := by
    intro x hx
    let z : S := ⟨(x, p x), Submodule.subset_span ⟨hx, rfl⟩⟩
    have hz : e z = x := rfl
    change snd (e.symm x) = p x
    rw [← hz, e.symm_apply_apply]
    rfl
  refine ⟨ell, hext, ?_⟩
  intro other hother
  exact LinearMap.ext_on hspan (fun x hx => (hother x hx).trans (hext x hx).symm)

end Linearization

section FiniteCoordinates

/-- Coordinate inclusion, with the rational and real scalar fields explicit. -/
def rationalCoordinates (d : ℕ) : (Fin d → ℚ) →ₗ[ℚ] (Fin d → ℝ) :=
  LinearMap.pi fun i => (Algebra.linearMap ℚ ℝ).comp (LinearMap.proj i)

@[simp]
theorem rationalCoordinates_apply (d : ℕ) (q : Fin d → ℚ) (i : Fin d) :
    rationalCoordinates d q i = (q i : ℝ) := rfl

@[simp]
theorem rationalCoordinates_single {d : ℕ} (i : Fin d) (q : ℚ) :
    rationalCoordinates d (Pi.single i q) = Pi.single i (q : ℝ) := by
  ext j
  by_cases h : i = j <;> simp [Pi.single_apply, h]

/-- The standard finite coordinate decomposition of a rational-linear readout. -/
theorem rational_linear_coordinate_formula {d : ℕ}
    (ell : (Fin d → ℚ) →ₗ[ℚ] ℝ) (q : Fin d → ℚ) :
    ell q = ∑ i, ell (Pi.single i 1) * (q i : ℝ) := by
  have hdecomp : q = ∑ i : Fin d, (q i) • (Pi.single i (1 : ℚ) : Fin d → ℚ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hdecomp, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa [smul_eq_mul, mul_comm] using
    (map_ratCast_smul ell ℚ ℝ (q i) (Pi.single i (1 : ℚ)))

/-- A finite sum of real coordinate functionals is continuous. This construction
uses the finite rational coordinate model, not the generally false assertion
that every rational-linear functional on a real ambient space is continuous. -/
def continuousRealExtension {d : ℕ} (ell : (Fin d → ℚ) →ₗ[ℚ] ℝ) :
    (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ i, ell (Pi.single i 1) • ContinuousLinearMap.proj i

theorem continuousRealExtension_apply {d : ℕ}
    (ell : (Fin d → ℚ) →ₗ[ℚ] ℝ) (x : Fin d → ℝ) :
    continuousRealExtension ell x = ∑ i, ell (Pi.single i 1) * x i := by
  simp [continuousRealExtension]

@[simp]
theorem continuousRealExtension_agrees {d : ℕ}
    (ell : (Fin d → ℚ) →ₗ[ℚ] ℝ) (q : Fin d → ℚ) :
    continuousRealExtension ell (rationalCoordinates d q) = ell q := by
  rw [continuousRealExtension_apply, rational_linear_coordinate_formula ell q]
  simp

private theorem real_linear_coordinate_formula {d : ℕ}
    (L : (Fin d → ℝ) →ₗ[ℝ] ℝ) (x : Fin d → ℝ) :
    L x = ∑ i, L (Pi.single i 1) * x i := by
  have hdecomp : x = ∑ i : Fin d, (x i) • (Pi.single i (1 : ℝ) : Fin d → ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hdecomp, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

theorem continuousRealExtension_unique {d : ℕ}
    (ell : (Fin d → ℚ) →ₗ[ℚ] ℝ) (L : (Fin d → ℝ) →L[ℝ] ℝ)
    (hagrees : ∀ q, L (rationalCoordinates d q) = ell q) :
    L = continuousRealExtension ell := by
  have hb : ∀ i : Fin d, L (Pi.single i 1) = ell (Pi.single i 1) := by
    intro i
    simpa using hagrees (Pi.single i 1)
  ext x
  rw [show L x = ∑ i, L (Pi.single i 1) * x i from
    real_linear_coordinate_formula L.toLinearMap x, continuousRealExtension_apply]
  simp_rw [hb]

/-- Midpoint accounting in a spanning finite rational coordinate domain gives a
unique continuous real-linear extension. Its agreement with the readout is
asserted only at rational domain points; no irrational event is postulated. -/
theorem exists_unique_continuous_real_extension {d : ℕ}
    (D : Set (Fin d → ℚ)) (p : (Fin d → ℚ) → ℝ)
    (hzero : (0 : Fin d → ℚ) ∈ D) (hpzero : p 0 = 0)
    (hclosed : ∀ x ∈ D, ∀ y ∈ D, (1 / 2 : ℚ) • (x + y) ∈ D)
    (hpres : ∀ x ∈ D, ∀ y ∈ D,
      p ((1 / 2 : ℚ) • (x + y)) = (p x + p y) / 2)
    (hspan : Submodule.span ℚ D = ⊤) :
    ∃! L : (Fin d → ℝ) →L[ℝ] ℝ,
      ∀ q ∈ D, L (rationalCoordinates d q) = p q := by
  obtain ⟨ell, hell, huniq⟩ :=
    exists_unique_rational_linear_extension D p hzero hpzero hclosed hpres hspan
  refine ⟨continuousRealExtension ell, ?_, ?_⟩
  · intro q hq
    rw [continuousRealExtension_agrees, hell q hq]
  · intro L hL
    let ratL : (Fin d → ℚ) →ₗ[ℚ] ℝ :=
      (L.toLinearMap.restrictScalars ℚ).comp (rationalCoordinates d)
    have heq : ratL = ell := huniq ratL hL
    apply continuousRealExtension_unique ell L
    intro q
    exact DFunLike.congr_fun heq q

end FiniteCoordinates

end

end IDT.QMClosure.DyadicMixtureLinearization
