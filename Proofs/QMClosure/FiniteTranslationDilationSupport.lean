import Proofs.QMClosure.FiniteTranslationSpectrum
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-!
# Dilation transport and finite joint-spectral support

The function is complex-valued on the integer lattice. Finite dimension of its
complex translate span and the exact doubling law are explicit hypotheses.
Ambient joint-primary blocks are used before any dilation image is shown to
belong to the original translate span. No injectivity of ambient dilation is
assumed. This module supplies finite support permutation and a common odd
root-of-unity period. Polynomial extraction and rank conclusions are separate.
-/

noncomputable section

namespace FiniteTranslationDilationSupport

open FiniteTranslationSpectrum

attribute [local instance] Classical.propDecidable

abbrev Label := Fin 2 → ℂ

abbrev Ambient := G → ℂ

def square (χ : Label) : Label := fun i => (χ i) ^ 2

def shift (i : Fin 2) : Module.End ℂ Ambient :=
  translateLinearMap (coordinateStep i)

def dilate : Module.End ℂ Ambient where
  toFun g z := g (z + z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def difference (i : Fin 2) (eigenvalue : ℂ) : Module.End ℂ Ambient :=
  shift i - eigenvalue • 1

def quadraticDifference (i : Fin 2) (eigenvalue : ℂ) : Module.End ℂ Ambient :=
  shift i ^ 2 - (eigenvalue ^ 2) • 1

/-- A pointwise intertwining relation also intertwines every natural power. -/
theorem intertwines_pow {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℂ V] [Module ℂ W]
    (A : Module.End ℂ W) (B : Module.End ℂ V) (T : V →ₗ[ℂ] W)
    (h : ∀ v, A (T v) = T (B v)) (n : ℕ) (v : V) :
    (A ^ n) (T v) = T ((B ^ n) v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ]
    change (A ^ n) (A (T v)) = T ((B ^ n) (B v))
    rw [h, ih]

theorem shift_commute (i j : Fin 2) : Commute (shift i) (shift j) := by
  change shift i * shift j = shift j * shift i
  ext g z
  change g ((z + coordinateStep i) + coordinateStep j) =
    g ((z + coordinateStep j) + coordinateStep i)
  congr 1
  abel

/-- These blocks live in the space of all complex lattice functions. -/
def ambientBlock (χ : Label) : Submodule ℂ Ambient :=
  ⨅ i, (shift i).maxGenEigenspace (χ i)

theorem ambientBlock_independent : iSupIndep ambientBlock := by
  apply Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
  intro i j μ
  exact Module.End.mapsTo_maxGenEigenspace_of_comm (shift_commute j i) μ

theorem quadratic_factor (i : Fin 2) (eigenvalue : ℂ) :
    quadraticDifference i eigenvalue = (shift i + eigenvalue • 1) * difference i eigenvalue := by
  ext g z
  change g ((z + coordinateStep i) + coordinateStep i) - eigenvalue ^ 2 * g z =
    (g ((z + coordinateStep i) + coordinateStep i) - eigenvalue * g (z + coordinateStep i)) +
      eigenvalue * (g (z + coordinateStep i) - eigenvalue * g z)
  ring

theorem quadratic_factors_commute (i : Fin 2) (eigenvalue : ℂ) :
    Commute (shift i + eigenvalue • 1) (difference i eigenvalue) := by
  change (shift i + eigenvalue • 1) * difference i eigenvalue =
    difference i eigenvalue * (shift i + eigenvalue • 1)
  ext g z
  change
    (g ((z + coordinateStep i) + coordinateStep i) - eigenvalue * g (z + coordinateStep i)) +
        eigenvalue * (g (z + coordinateStep i) - eigenvalue * g z) =
      (g ((z + coordinateStep i) + coordinateStep i) + eigenvalue * g (z + coordinateStep i)) -
        eigenvalue * (g (z + coordinateStep i) + eigenvalue * g z)
  ring

/-- Coordinate translation after dilation is a squared coordinate translation. -/
theorem difference_dilate (i : Fin 2) (eigenvalue : ℂ) (g : Ambient) :
    difference i (eigenvalue ^ 2) (dilate g) = dilate (quadraticDifference i eigenvalue g) := by
  ext z
  change g ((z + coordinateStep i) + (z + coordinateStep i)) - eigenvalue ^ 2 * g (z + z) =
    g (((z + z) + coordinateStep i) + coordinateStep i) - eigenvalue ^ 2 * g (z + z)
  rw [show (z + coordinateStep i) + (z + coordinateStep i) =
    ((z + z) + coordinateStep i) + coordinateStep i by abel]

/-- Generalized eigenvalue transport permits the transported vector to vanish. -/
theorem dilate_mem_ambientBlock {χ : Label} {g : Ambient}
    (hg : g ∈ ambientBlock χ) : dilate g ∈ ambientBlock (square χ) := by
  apply (Submodule.mem_iInf _).mpr
  intro i
  have hgi := (Submodule.mem_iInf _).mp hg i
  obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace (shift i) (χ i) g).mp hgi
  apply (Module.End.mem_maxGenEigenspace (shift i) (square χ i) (dilate g)).mpr
  refine ⟨n, ?_⟩
  have hquad : (quadraticDifference i (χ i) ^ n) g = 0 := by
    rw [quadratic_factor, (quadratic_factors_commute i (χ i)).mul_pow]
    change ((shift i + (χ i) • 1) ^ n) ((difference i (χ i) ^ n) g) = 0
    change (difference i (χ i) ^ n) g = 0 at hn
    rw [hn, map_zero]
  change (difference i ((χ i) ^ 2) ^ n) (dilate g) = 0
  calc
    _ = dilate ((quadraticDifference i (χ i) ^ n) g) :=
      intertwines_pow _ _ dilate (difference_dilate i (χ i)) n g
    _ = 0 := by rw [hquad, map_zero]

/-- Inclusion into all functions transports the original block's nilpotent powers. -/
theorem coe_mem_ambientBlock (f : Ambient) (χ : Label)
    {v : TranslationSpace f} (hv : v ∈ jointBlock f χ) :
    (v : Ambient) ∈ ambientBlock χ := by
  apply (Submodule.mem_iInf _).mpr
  intro i
  have hvi := (Submodule.mem_iInf _).mp hv i
  obtain ⟨n, hn⟩ :=
    (Module.End.mem_maxGenEigenspace (coordinateEnd f i) (χ i) v).mp hvi
  apply (Module.End.mem_maxGenEigenspace (shift i) (χ i) (v : Ambient)).mpr
  refine ⟨n, ?_⟩
  let J : TranslationSpace f →ₗ[ℂ] Ambient := (translationSpanC f).subtype
  have hinter : ∀ w : TranslationSpace f,
      difference i (χ i) (J w) = J ((coordinateEnd f i - (χ i) • 1) w) := by
    intro w
    ext z
    rfl
  change (difference i (χ i) ^ n) (J v) = 0
  calc
    _ = J (((coordinateEnd f i - (χ i) • 1) ^ n) v) :=
      intertwines_pow _ _ J hinter n v
    _ = 0 := by rw [hn, map_zero]

section FiniteDimension

variable (f : Ambient) [FiniteDimensional ℂ (TranslationSpace f)]

/-- The support is exactly the support of the established readout decomposition. -/
def support : Finset Label := (readoutComponents f).support

def component (χ : Label) : Ambient :=
  ((readoutComponents f χ : TranslationSpace f) : Ambient)

theorem component_eq_zero_iff (χ : Label) :
    component f χ = 0 ↔ readoutComponents f χ = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  · intro h
    simp [component, h]

theorem mem_support_iff (χ : Label) :
    χ ∈ support f ↔ component f χ ≠ 0 := by
  rw [support, DFinsupp.mem_support_iff]
  exact not_congr (component_eq_zero_iff f χ).symm

theorem component_eq_zero_of_not_mem_support {χ : Label}
    (hχ : χ ∉ support f) : component f χ = 0 := by
  by_contra hne
  exact hχ ((mem_support_iff f χ).mpr hne)

theorem component_mem_ambientBlock (χ : Label) :
    component f χ ∈ ambientBlock χ :=
  coe_mem_ambientBlock f χ (readoutComponents_mem f χ)

theorem component_coordinate_ne_zero {χ : Label}
    (hχ : χ ∈ support f) (i : Fin 2) : χ i ≠ 0 := by
  refine readoutComponents_coordinate_ne_zero f χ ?_ i
  intro hz
  apply (mem_support_iff f χ).mp hχ
  change ((readoutComponents f χ : TranslationSpace f) : Ambient) = 0
  rw [hz]
  rfl

theorem sum_components : (∑ χ ∈ support f, component f χ) = f := by
  ext z
  have h := congrArg (fun v : TranslationSpace f => (v : Ambient) z) (sum_readoutComponents f)
  simpa [component, support, original] using h

/-- A fibre is grouped in its ambient squared-eigenvalue block. -/
def grouped (η : Label) : Ambient :=
  ∑ χ ∈ (support f).filter (fun χ => square χ = η), dilate (component f χ)

theorem grouped_mem_ambientBlock (η : Label) :
    grouped f η ∈ ambientBlock η := by
  apply (ambientBlock η).sum_mem
  intro χ hχ
  obtain ⟨_, hsq⟩ := Finset.mem_filter.mp hχ
  rw [← hsq]
  exact dilate_mem_ambientBlock (component_mem_ambientBlock f χ)

theorem sum_grouped (T : Finset Label)
    (hT : ∀ χ ∈ support f, square χ ∈ T) :
    (∑ η ∈ T, grouped f η) = dilate f := by
  calc
    _ = ∑ χ ∈ support f, dilate (component f χ) :=
      Finset.sum_fiberwise_of_maps_to hT (fun χ => dilate (component f χ))
    _ = dilate (∑ χ ∈ support f, component f χ) := by simp only [map_sum]
    _ = dilate f := by rw [sum_components]

theorem sum_scaled_components (T : Finset Label) (hT : support f ⊆ T) :
    (∑ η ∈ T, (4 : ℂ) • component f η) = (4 : ℂ) • f := by
  have heq : (∑ η ∈ support f, component f η) = ∑ η ∈ T, component f η := by
    apply Finset.sum_subset hT
    intro η _ hη
    exact component_eq_zero_of_not_mem_support f hη
  calc
    _ = (4 : ℂ) • (∑ η ∈ T, component f η) := by rw [Finset.smul_sum]
    _ = (4 : ℂ) • f := by rw [← heq, sum_components]

theorem dilate_readout (hscale : ∀ z, f (z + z) = 4 * f z) :
    dilate f = (4 : ℂ) • f := by
  ext z
  exact hscale z

/-- Ambient block independence compares the grouped dilation and scaled readout. -/
theorem grouped_eq_scaled (hscale : ∀ z, f (z + z) = 4 * f z)
    (η : Label) (hη : η ∈ support f ∪ (support f).image square) :
    grouped f η = (4 : ℂ) • component f η := by
  have hunique :=
    (iSupIndep_iff_finset_sum_eq_imp_eq ambientBlock).mp ambientBlock_independent
  apply hunique (support f ∪ (support f).image square) (grouped f)
    (fun θ => (4 : ℂ) • component f θ) ?_ ?_ η hη
  · intro θ _
    exact ⟨grouped_mem_ambientBlock f θ,
      (ambientBlock θ).smul_mem 4 (component_mem_ambientBlock f θ)⟩
  · rw [sum_grouped f _ (fun χ hχ =>
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨χ, hχ, rfl⟩)),
      sum_scaled_components f _ (Finset.subset_union_left), dilate_readout f hscale]

theorem grouped_eq_zero_of_not_mem_image {η : Label}
    (hη : η ∉ (support f).image square) : grouped f η = 0 := by
  apply Finset.sum_eq_zero
  intro χ hχ
  obtain ⟨hχ, hs⟩ := Finset.mem_filter.mp hχ
  exact False.elim (hη (Finset.mem_image.mpr ⟨χ, hχ, hs⟩))

/-- The forward inclusion is obtained without injectivity of ambient dilation. -/
theorem support_subset_square_image (hscale : ∀ z, f (z + z) = 4 * f z) :
    support f ⊆ (support f).image square := by
  intro χ hχ
  by_contra hnot
  have hzero : (4 : ℂ) • component f χ = 0 := by
    rw [← grouped_eq_scaled f hscale χ (Finset.mem_union_left _ hχ)]
    exact grouped_eq_zero_of_not_mem_image f hnot
  have hc : component f χ = 0 :=
    (smul_eq_zero.mp hzero).resolve_left (by norm_num)
  exact (mem_support_iff f χ).mp hχ hc

/-- Finite cardinality upgrades the inclusion to exact support invariance. -/
theorem support_square_eq (hscale : ∀ z, f (z + z) = 4 * f z) :
    (support f).image square = support f := by
  exact (Finset.eq_of_subset_of_card_le (support_subset_square_image f hscale)
    Finset.card_image_le).symm

theorem square_injective_on_support (hscale : ∀ z, f (z + z) = 4 * f z) :
    Set.InjOn square (support f : Set Label) := by
  apply Finset.injOn_of_card_image_eq
  rw [support_square_eq f hscale]

/-- Every source fibre is a singleton after support squaring is a bijection. -/
theorem dilate_component (hscale : ∀ z, f (z + z) = 4 * f z)
    (χ : Label) (hχ : χ ∈ support f) :
    dilate (component f χ) = (4 : ℂ) • component f (square χ) := by
  have hfilter : (support f).filter (fun θ => square θ = square χ) = {χ} := by
    ext θ
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hθ, heq⟩
      exact square_injective_on_support f hscale hθ hχ heq
    · intro heq
      subst θ
      exact ⟨hχ, rfl⟩
  have h := grouped_eq_scaled f hscale (square χ)
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨χ, hχ, rfl⟩))
  simpa only [grouped, hfilter, Finset.sum_singleton] using h

/-- Nonvanishing is concluded only after the finite support permutation is known. -/
theorem dilate_component_ne_zero (hscale : ∀ z, f (z + z) = 4 * f z)
    (χ : Label) (hχ : χ ∈ support f) : dilate (component f χ) ≠ 0 := by
  rw [dilate_component f hscale χ hχ]
  have hsq : square χ ∈ support f := by
    rw [← support_square_eq f hscale]
    exact Finset.mem_image.mpr ⟨χ, hχ, rfl⟩
  exact smul_ne_zero (by norm_num) ((mem_support_iff f (square χ)).mp hsq)

abbrev Supported := {χ : Label // χ ∈ support f}

def squareOnSupport (hscale : ∀ z, f (z + z) = 4 * f z) :
    Supported f → Supported f := fun χ =>
  ⟨square χ.val, by
    have himage : square χ.val ∈ (support f).image square :=
      Finset.mem_image.mpr ⟨χ.val, χ.property, rfl⟩
    rw [support_square_eq f hscale] at himage
    exact himage⟩

theorem squareOnSupport_bijective (hscale : ∀ z, f (z + z) = 4 * f z) :
    Function.Bijective (squareOnSupport f hscale) := by
  constructor
  · intro χ θ h
    apply Subtype.ext
    exact square_injective_on_support f hscale χ.property θ.property
      (congrArg Subtype.val h)
  · intro η
    have hη : η.val ∈ (support f).image square := by
      rw [support_square_eq f hscale]
      exact η.property
    obtain ⟨χ, hχ, heq⟩ := Finset.mem_image.mp hη
    exact ⟨⟨χ, hχ⟩, Subtype.ext heq⟩

def squarePerm (hscale : ∀ z, f (z + z) = 4 * f z) : Equiv.Perm (Supported f) :=
  Equiv.ofBijective (squareOnSupport f hscale) (squareOnSupport_bijective f hscale)

theorem squarePerm_pow_apply (hscale : ∀ z, f (z + z) = 4 * f z)
    (n : ℕ) (χ : Supported f) (i : Fin 2) :
    (((squarePerm f hscale ^ n) χ).val i) = (χ.val i) ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    change ((((squarePerm f hscale ^ n) χ).val i) ^ 2) = (χ.val i) ^ (2 ^ (n + 1))
    rw [ih, ← pow_mul, pow_succ]

/-- One common positive odd exponent works for every supported coordinate. -/
theorem exists_common_odd_period (hscale : ∀ z, f (z + z) = 4 * f z) :
    ∃ M : ℕ, 0 < M ∧ Odd M ∧ ∀ χ ∈ support f, ∀ i : Fin 2, (χ i) ^ M = 1 := by
  let π := squarePerm f hscale
  have hk : 0 < orderOf π := orderOf_pos π
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hcycle : π ^ (n + 1) = 1 := by
    simpa only [hn, Nat.succ_eq_add_one] using pow_orderOf_eq_one π
  have hpowpos : 0 < (2 : ℕ) ^ n := by positivity
  have hpowge : 1 ≤ (2 : ℕ) ^ (n + 1) := by
    rw [pow_succ]
    omega
  refine ⟨2 ^ (n + 1) - 1, ?_, ?_, ?_⟩
  · rw [pow_succ]
    omega
  · refine ⟨2 ^ n - 1, ?_⟩
    rw [pow_succ]
    omega
  · intro χ hχ i
    let x : Supported f := ⟨χ, hχ⟩
    have hχcycle : (χ i) ^ (2 ^ (n + 1)) = χ i := by
      calc
        _ = (((π ^ (n + 1)) x).val i) :=
          (squarePerm_pow_apply f hscale (n + 1) x i).symm
        _ = χ i := by rw [hcycle]; rfl
    have hcancel : (χ i) ^ (2 ^ (n + 1) - 1) * χ i = 1 * χ i := by
      rw [← pow_succ, Nat.sub_add_cancel hpowge, one_mul]
      exact hχcycle
    exact mul_right_cancel₀ (component_coordinate_ne_zero f hχ i) hcancel

end FiniteDimension

end FiniteTranslationDilationSupport

end
