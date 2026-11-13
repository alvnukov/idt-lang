import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic

/-!
# Conditional dimension forced by a finite gate frame

The preparation set spans an initially arbitrary real vector space. Each binary
average has two fixed preparation endpoints and sends every preparation into
their closed segment. Available linear gates obey the explicit finite relations
below. These assumptions imply a four-dimensional linear envelope and three
normalized degrees of freedom. They supply no metric, ball, physical origin,
positivity principle, or completed reconstruction of quantum mechanics.
-/

namespace IDT.QMClosure.FiniteGateFrameDimension

open Module

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

abbrev End := V →ₗ[ℝ] V

def average (J : End (V := V)) : End (V := V) :=
  (1 / 2 : ℝ) • (LinearMap.id + J)

/-- Binary output has two fixed available endpoints for the entire set. -/
def BinarySegment (S : Set V) (E : End (V := V)) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, ∀ s ∈ S,
    ∃ t ∈ Set.Icc (0 : ℝ) 1, E s = (1 - t) • a + t • b

structure Frame (V : Type*) [AddCommGroup V] [Module ℝ V] where
  preparations : Set V
  nonempty : preparations.Nonempty
  normalization : V →ₗ[ℝ] ℝ
  normalized : ∀ s ∈ preparations, normalization s = 1
  spanning : Submodule.span ℝ preparations = ⊤
  Jx : V →ₗ[ℝ] V
  Jz : V →ₗ[ℝ] V
  H : V →ₗ[ℝ] V
  T : V →ₗ[ℝ] V
  Jx_involutive : ∀ v, Jx (Jx v) = v
  Jz_involutive : ∀ v, Jz (Jz v) = v
  commute : ∀ v, Jz (Jx v) = Jx (Jz v)
  Jx_available : ∀ s ∈ preparations, Jx s ∈ preparations
  Jz_available : ∀ s ∈ preparations, Jz s ∈ preparations
  H_available : ∀ s ∈ preparations, H s ∈ preparations
  T_available : ∀ s ∈ preparations, T s ∈ preparations
  binary_x : BinarySegment preparations (average Jx)
  binary_y : BinarySegment preparations (average (Jx.comp Jz))
  binary_z : BinarySegment preparations (average Jz)
  H_involutive : ∀ v, H (H v) = v
  H_conjugates : ∀ v, H (Jz (H v)) = Jx v
  T_cube : ∀ v, T (T (T v)) = v
  T_commutes : ∀ v, Jz (T v) = T (Jz v)
  T_nontrivial : T ≠ LinearMap.id

theorem normalization_of_available (S : Set V) (u : V →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ S = ⊤) (hnorm : ∀ s ∈ S, u s = 1)
    (A : End (V := V)) (hA : ∀ s ∈ S, A s ∈ S) :
    ∀ v, u (A v) = u v := by
  have hle : Submodule.span ℝ S ≤ LinearMap.ker (u.comp A - u) := by
    apply Submodule.span_le.mpr
    intro s hs
    change u (A s) - u s = 0
    rw [hnorm s hs, hnorm (A s) (hA s hs), sub_self]
  intro v
  have hv : v ∈ Submodule.span ℝ S := by rw [hspan]; trivial
  exact sub_eq_zero.mp (hle hv)

namespace Frame

variable (F : Frame V)

theorem norm_Jx (v : V) : F.normalization (F.Jx v) = F.normalization v :=
  normalization_of_available _ _ F.spanning F.normalized _ F.Jx_available v

theorem norm_Jz (v : V) : F.normalization (F.Jz v) = F.normalization v :=
  normalization_of_available _ _ F.spanning F.normalized _ F.Jz_available v

theorem norm_H (v : V) : F.normalization (F.H v) = F.normalization v :=
  normalization_of_available _ _ F.spanning F.normalized _ F.H_available v

theorem norm_T (v : V) : F.normalization (F.T v) = F.normalization v :=
  normalization_of_available _ _ F.spanning F.normalized _ F.T_available v

def Ex : End (V := V) := average F.Jx
def Ey : End (V := V) := average (F.Jx.comp F.Jz)
def Ez : End (V := V) := average F.Jz
def R : End (V := V) :=
  (1 / 4 : ℝ) • (LinearMap.id + F.Jx + F.Jz + F.Jx.comp F.Jz)
def Qx : End (V := V) := F.Ex - F.R
def Qy : End (V := V) := F.Ey - F.R
def Qz : End (V := V) := F.Ez - F.R

def character (i : Fin 4) : End (V := V) :=
  if i = 0 then F.R else if i = 1 then F.Qx else if i = 2 then F.Qy else F.Qz

@[simp] theorem character_zero : F.character 0 = F.R := by simp [character]
@[simp] theorem character_one : F.character 1 = F.Qx := by simp [character]
@[simp] theorem character_two : F.character 2 = F.Qy := by simp [character]
@[simp] theorem character_three : F.character 3 = F.Qz := by simp [character]

/-- Exact Klein-four character multiplication, derived from the gate laws. -/
theorem character_mul (i j : Fin 4) (v : V) :
    F.character i (F.character j v) = if i = j then F.character i v else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [character, Qx, Qy, Qz, Ex, Ey, Ez, R, average,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, map_add, map_sub, map_smul,
      F.commute, F.Jx_involutive, F.Jz_involutive] <;> module

theorem character_sum (v : V) :
    F.character 0 v + F.character 1 v + F.character 2 v + F.character 3 v = v := by
  simp [Qx, Qy, Qz, Ex, Ey, Ez, R, average,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.comp_apply]
  module

theorem Ex_character : F.Ex = F.character 0 + F.character 1 := by
  simp [Qx]

theorem Ey_character : F.Ey = F.character 0 + F.character 2 := by
  simp [Qy]

theorem Ez_character : F.Ez = F.character 0 + F.character 3 := by
  simp [Qz]

theorem norm_R (v : V) : F.normalization (F.R v) = F.normalization v := by
  simp [R, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    map_add, map_smul, norm_Jx, norm_Jz]
  ring

theorem norm_Ez (v : V) : F.normalization (F.Ez v) = F.normalization v := by
  simp [Ez, average, LinearMap.add_apply, LinearMap.smul_apply, map_add,
    map_smul, norm_Jz]
  ring

end Frame

theorem range_le_of_spanning (S : Set V) (hspan : Submodule.span ℝ S = ⊤)
    (E : End (V := V)) (p : Submodule ℝ V) (h : ∀ s ∈ S, E s ∈ p) :
    LinearMap.range E ≤ p := by
  rintro _ ⟨v, rfl⟩
  have hle : Submodule.span ℝ S ≤ p.comap E := Submodule.span_le.mpr h
  apply hle
  rw [hspan]
  trivial

theorem binary_range_bound (S : Set V) (hspan : Submodule.span ℝ S = ⊤)
    (E : End (V := V)) (hbinary : BinarySegment S E) :
    FiniteDimensional ℝ (LinearMap.range E) ∧
      finrank ℝ (LinearMap.range E) ≤ 2 := by
  classical
  obtain ⟨a, _, b, _, hab⟩ := hbinary
  let p : Submodule ℝ V := Submodule.span ℝ ({a, b} : Set V)
  have hle : LinearMap.range E ≤ p := by
    apply range_le_of_spanning S hspan E p
    intro s hs
    obtain ⟨t, _, ht⟩ := hab s hs
    rw [ht]
    apply p.add_mem
    · exact p.smul_mem _ (Submodule.subset_span (by simp))
    · exact p.smul_mem _ (Submodule.subset_span (by simp))
  letI : FiniteDimensional ℝ p :=
    FiniteDimensional.span_of_finite ℝ (Set.toFinite _)
  letI : FiniteDimensional ℝ (LinearMap.range E) :=
    FiniteDimensional.of_injective (Submodule.inclusion hle)
      (Submodule.inclusion_injective hle)
  refine ⟨inferInstance, (Submodule.finrank_mono hle).trans ?_⟩
  have hb := finrank_span_le_card (R := ℝ) ({a, b} : Set V)
  apply hb.trans
  have heq : ({a, b} : Set V).toFinset = ({a, b} : Finset V) := by ext; simp
  rw [heq]
  exact Finset.card_le_two

section Orthogonal

variable (P : Fin 4 → End (V := V))
variable (hP : ∀ i j v, P i (P j v) = if i = j then P i v else 0)
variable (hSum : ∀ v, P 0 v + P 1 v + P 2 v + P 3 v = v)

def characterEquiv : V ≃ₗ[ℝ] (∀ i, LinearMap.range (P i)) where
  toFun v i := ⟨P i v, ⟨v, rfl⟩⟩
  invFun x := x 0 + x 1 + x 2 + x 3
  map_add' v w := by ext i; simp
  map_smul' c v := by ext i; simp
  left_inv := hSum
  right_inv x := by
    have hx (i j : Fin 4) : P i (x j) = if i = j then (x j : V) else 0 := by
      obtain ⟨v, hv⟩ := (x j).property
      calc
        P i (x j) = P i (P j v) := congrArg (P i) hv.symm
        _ = if i = j then P i v else 0 := hP i j v
        _ = if i = j then (x j : V) else 0 := by
          split_ifs with hij
          · subst j; exact hv
          · rfl
    ext i
    fin_cases i <;> simp only [map_add, hx] <;> simp

def pairRangeEquiv (i j : Fin 4) (hij : i ≠ j) :
    LinearMap.range (P i + P j) ≃ₗ[ℝ]
      LinearMap.range (P i) × LinearMap.range (P j) where
  toFun x := (⟨P i x, ⟨x, rfl⟩⟩, ⟨P j x, ⟨x, rfl⟩⟩)
  invFun x := ⟨x.1 + x.2, x.1 + x.2, by
    obtain ⟨a, ha⟩ := x.1.property
    obtain ⟨b, hb⟩ := x.2.property
    simp only [LinearMap.add_apply, map_add]
    rw [← ha, ← hb]
    simp [hP, hij, Ne.symm hij]⟩
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp
  left_inv x := by
    apply Subtype.ext
    obtain ⟨v, hv⟩ := x.property
    simp only [LinearMap.add_apply] at hv
    change P i x + P j x = x
    calc
      P i x + P j x = P i (P i v + P j v) + P j (P i v + P j v) := by rw [hv]
      _ = P i v + P j v := by simp [map_add, hP, hij, Ne.symm hij]
      _ = x := hv
  right_inv x := by
    apply Prod.ext <;> apply Subtype.ext
    all_goals
      obtain ⟨a, ha⟩ := x.1.property
      obtain ⟨b, hb⟩ := x.2.property
      simp only [map_add]
      rw [← ha, ← hb]
      simp [hP, hij, Ne.symm hij]

end Orthogonal

theorem cube_eq_one_real {a : ℝ} (h : a ^ 3 = 1) : a = 1 := by
  have hfactor : (a - 1) * (a ^ 2 + a + 1) = 0 := by nlinarith [h]
  have hpos : 0 < a ^ 2 + a + 1 := by nlinarith [sq_nonneg (a + 1 / 2)]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right (ne_of_gt hpos))

/-- An order-three real endomorphism is trivial in dimension at most one. -/
theorem cube_identity_dim_le_one [FiniteDimensional ℝ V]
    (T : End (V := V)) (hcube : ∀ v, T (T (T v)) = v)
    (hdim : finrank ℝ V ≤ 1) : T = LinearMap.id := by
  ext v
  by_cases hv : v = 0
  · simp [hv]
  have hpos : 0 < finrank ℝ V := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨v, hv⟩
  have hone : finrank ℝ V = 1 := by omega
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one hone hv (T v)
  have hthree : a ^ 3 • v = (1 : ℝ) • v := by
    calc
      a ^ 3 • v = T (T (T v)) := by simp only [← ha, map_smul, smul_smul]; module
      _ = (1 : ℝ) • v := by rw [hcube]; simp
  have ha1 := cube_eq_one_real (smul_left_injective ℝ hv hthree)
  simpa [ha1] using ha.symm

/-- Preserving a nonzero normalization rules out nontrivial order three in a
real space of dimension at most two. -/
theorem cube_identity_normalized_dim_le_two [FiniteDimensional ℝ V]
    (T : End (V := V)) (u : V →ₗ[ℝ] ℝ) (hu : ∃ v, u v ≠ 0)
    (hnorm : ∀ v, u (T v) = u v) (hcube : ∀ v, T (T (T v)) = v)
    (hdim : finrank ℝ V ≤ 2) : T = LinearMap.id := by
  have hrange : finrank ℝ (LinearMap.range u) = 1 := by
    obtain ⟨v, hv⟩ := hu
    have hpos : 0 < finrank ℝ (LinearMap.range u) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr
        ⟨⟨u v, v, rfl⟩, by intro h; apply hv; exact congrArg Subtype.val h⟩
    have hle := (LinearMap.range u).finrank_le
    simp only [Module.finrank_self] at hle
    omega
  have hker : finrank ℝ (LinearMap.ker u) ≤ 1 := by
    have hnull := u.finrank_range_add_finrank_ker
    omega
  let K : LinearMap.ker u →ₗ[ℝ] LinearMap.ker u :=
    { toFun := fun v => ⟨T v, by
        change u (T v) = 0
        rw [hnorm]
        exact v.property⟩
      map_add' := fun v w => by ext; simp
      map_smul' := fun c v => by ext; simp }
  have hKcube : ∀ v, K (K (K v)) = v := by
    intro v
    apply Subtype.ext
    exact hcube v
  have hKid := cube_identity_dim_le_one K hKcube hker
  ext v
  have hd : T (T v - v) = T v - v := by
    have hk : T v - v ∈ LinearMap.ker u := by
      simp [LinearMap.mem_ker, map_sub, hnorm]
    exact congrArg Subtype.val (LinearMap.congr_fun hKid ⟨T v - v, hk⟩)
  have hTd := congrArg T hd
  simp only [map_sub] at hd hTd
  have hz : (3 : ℝ) • (T v - v) = 0 := by
    linear_combination (norm := module) - (2 : ℝ) • hd - hTd + hcube v
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num))

theorem range_left_le_pair (P : Fin 4 → End (V := V))
    (hP : ∀ i j v, P i (P j v) = if i = j then P i v else 0)
    (i j : Fin 4) (hij : i ≠ j) :
    LinearMap.range (P i) ≤ LinearMap.range (P i + P j) := by
  rintro _ ⟨v, rfl⟩
  refine ⟨P i v, ?_⟩
  simp [LinearMap.add_apply, hP, Ne.symm hij]

theorem range_right_le_pair (P : Fin 4 → End (V := V))
    (hP : ∀ i j v, P i (P j v) = if i = j then P i v else 0)
    (i j : Fin 4) (hij : i ≠ j) :
    LinearMap.range (P j) ≤ LinearMap.range (P i + P j) := by
  rintro _ ⟨v, rfl⟩
  refine ⟨P j v, ?_⟩
  simp [LinearMap.add_apply, hP, hij]

namespace Frame

variable (F : Frame V)

theorem finite_dimensional (F : Frame V) : FiniteDimensional ℝ V := by
  have hx := binary_range_bound _ F.spanning F.Ex F.binary_x
  have hy := binary_range_bound _ F.spanning F.Ey F.binary_y
  have hz := binary_range_bound _ F.spanning F.Ez F.binary_z
  letI : FiniteDimensional ℝ (LinearMap.range F.Ex) := hx.1
  letI : FiniteDimensional ℝ (LinearMap.range F.Ey) := hy.1
  letI : FiniteDimensional ℝ (LinearMap.range F.Ez) := hz.1
  have h0 : LinearMap.range (F.character 0) ≤ LinearMap.range F.Ex := by
    rw [F.Ex_character]
    exact range_left_le_pair F.character F.character_mul 0 1 (by decide)
  have h1 : LinearMap.range (F.character 1) ≤ LinearMap.range F.Ex := by
    rw [F.Ex_character]
    exact range_right_le_pair F.character F.character_mul 0 1 (by decide)
  have h2 : LinearMap.range (F.character 2) ≤ LinearMap.range F.Ey := by
    rw [F.Ey_character]
    exact range_right_le_pair F.character F.character_mul 0 2 (by decide)
  have h3 : LinearMap.range (F.character 3) ≤ LinearMap.range F.Ez := by
    rw [F.Ez_character]
    exact range_right_le_pair F.character F.character_mul 0 3 (by decide)
  letI : ∀ i, FiniteDimensional ℝ (LinearMap.range (F.character i)) := by
    intro i
    fin_cases i
    · exact FiniteDimensional.of_injective (Submodule.inclusion h0)
        (Submodule.inclusion_injective h0)
    · exact FiniteDimensional.of_injective (Submodule.inclusion h1)
        (Submodule.inclusion_injective h1)
    · exact FiniteDimensional.of_injective (Submodule.inclusion h2)
        (Submodule.inclusion_injective h2)
    · exact FiniteDimensional.of_injective (Submodule.inclusion h3)
        (Submodule.inclusion_injective h3)
  let e := characterEquiv F.character F.character_mul F.character_sum
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

def rank (i : Fin 4) : ℕ := finrank ℝ (LinearMap.range (F.character i))

theorem rank_total [FiniteDimensional ℝ V] :
    finrank ℝ V = F.rank 0 + F.rank 1 + F.rank 2 + F.rank 3 := by
  have h := (characterEquiv F.character F.character_mul F.character_sum).finrank_eq
  rw [Module.finrank_pi_fintype] at h
  simpa [rank, Fin.sum_univ_succ, add_assoc] using h

theorem rank_Ex [FiniteDimensional ℝ V] :
    finrank ℝ (LinearMap.range F.Ex) = F.rank 0 + F.rank 1 := by
  rw [F.Ex_character]
  have h := (pairRangeEquiv F.character F.character_mul 0 1 (by decide)).finrank_eq
  simpa [rank, Module.finrank_prod] using h

theorem rank_Ey [FiniteDimensional ℝ V] :
    finrank ℝ (LinearMap.range F.Ey) = F.rank 0 + F.rank 2 := by
  rw [F.Ey_character]
  have h := (pairRangeEquiv F.character F.character_mul 0 2 (by decide)).finrank_eq
  simpa [rank, Module.finrank_prod] using h

theorem rank_Ez [FiniteDimensional ℝ V] :
    finrank ℝ (LinearMap.range F.Ez) = F.rank 0 + F.rank 3 := by
  rw [F.Ez_character]
  have h := (pairRangeEquiv F.character F.character_mul 0 3 (by decide)).finrank_eq
  simpa [rank, Module.finrank_prod] using h

theorem rank_common_positive [FiniteDimensional ℝ V] : 1 ≤ F.rank 0 := by
  obtain ⟨s, hs⟩ := F.nonempty
  have hnorm : F.normalization (F.R s) = 1 := by rw [F.norm_R, F.normalized s hs]
  have hne : F.R s ≠ 0 := by
    intro h
    simp [h] at hnorm
  have hpos : 0 < finrank ℝ (LinearMap.range F.R) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨F.R s, s, rfl⟩, by intro h; exact hne (congrArg Subtype.val h)⟩
  change 1 ≤ finrank ℝ (LinearMap.range F.R)
  exact hpos

theorem Ez_idempotent (v : V) : F.Ez (F.Ez v) = F.Ez v := by
  simp [Ez, average, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    F.Jz_involutive]
  module

theorem T_Ez (v : V) : F.Ez (F.T v) = F.T (F.Ez v) := by
  simp [Ez, average, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    F.T_commutes]

theorem H_Ez (v : V) : F.H (F.Ez v) = F.Ex (F.H v) := by
  have hconj : F.H (F.Jz v) = F.Jx (F.H v) := by
    simpa only [F.H_involutive] using F.H_conjugates (F.H v)
  simp [Ez, Ex, average, LinearMap.add_apply, LinearMap.smul_apply,
    map_add, map_smul, hconj]

theorem H_Ex (v : V) : F.H (F.Ex v) = F.Ez (F.H v) := by
  have h := congrArg F.H (F.H_Ez (F.H v))
  simpa only [F.H_involutive] using h.symm

def H_range_equiv : LinearMap.range F.Ez ≃ₗ[ℝ] LinearMap.range F.Ex where
  toFun v := ⟨F.H v, by
    obtain ⟨w, hw⟩ := v.property
    refine ⟨F.H w, ?_⟩
    rw [← F.H_Ez, hw]⟩
  invFun v := ⟨F.H v, by
    obtain ⟨w, hw⟩ := v.property
    refine ⟨F.H w, ?_⟩
    rw [← F.H_Ex, hw]⟩
  left_inv v := by ext; exact F.H_involutive v
  right_inv v := by ext; exact F.H_involutive v
  map_add' v w := by ext; simp
  map_smul' c v := by ext; simp

theorem rank_Ez_eq_Ex [FiniteDimensional ℝ V] :
    finrank ℝ (LinearMap.range F.Ez) = finrank ℝ (LinearMap.range F.Ex) :=
  F.H_range_equiv.finrank_eq

/-- The available order-three gate is identity on the normalized plus sector. -/
theorem T_fixes_Ez [FiniteDimensional ℝ V] (v : V) : F.T (F.Ez v) = F.Ez v := by
  let A : LinearMap.range F.Ez →ₗ[ℝ] LinearMap.range F.Ez :=
    { toFun := fun x => ⟨F.T x, by
        obtain ⟨w, hw⟩ := x.property
        refine ⟨F.T w, ?_⟩
        rw [F.T_Ez, hw]⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp }
  let u := F.normalization.comp (LinearMap.range F.Ez).subtype
  have hu : ∃ x, u x ≠ 0 := by
    obtain ⟨s, hs⟩ := F.nonempty
    refine ⟨⟨F.Ez s, s, rfl⟩, ?_⟩
    change F.normalization (F.Ez s) ≠ 0
    rw [F.norm_Ez, F.normalized s hs]
    norm_num
  have hnorm : ∀ x, u (A x) = u x := fun x => F.norm_T x
  have hcube : ∀ x, A (A (A x)) = x := by
    intro x
    apply Subtype.ext
    exact F.T_cube x
  have hdim := (binary_range_bound _ F.spanning F.Ez F.binary_z).2
  have hid := cube_identity_normalized_dim_le_two A u hu hnorm hcube hdim
  exact congrArg Subtype.val (LinearMap.congr_fun hid ⟨F.Ez v, v, rfl⟩)

theorem rank_minus [FiniteDimensional ℝ V] :
    finrank ℝ (LinearMap.ker F.Ez) = F.rank 1 + F.rank 2 := by
  have hnull := F.Ez.finrank_range_add_finrank_ker
  rw [F.rank_Ez, F.rank_total] at hnull
  omega

/-- Nontrivial order three requires two dimensions in the minus sector. -/
theorem rank_minus_at_least_two [FiniteDimensional ℝ V] :
    2 ≤ F.rank 1 + F.rank 2 := by
  by_contra hdim
  have hle : finrank ℝ (LinearMap.ker F.Ez) ≤ 1 := by rw [F.rank_minus]; omega
  let B : LinearMap.ker F.Ez →ₗ[ℝ] LinearMap.ker F.Ez :=
    { toFun := fun x => ⟨F.T x, by
        change F.Ez (F.T x) = 0
        rw [F.T_Ez, x.property, map_zero]⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp }
  have hcube : ∀ x, B (B (B x)) = x := by
    intro x
    apply Subtype.ext
    exact F.T_cube x
  have hBid := cube_identity_dim_le_one B hcube hle
  apply F.T_nontrivial
  ext v
  have hminus : v - F.Ez v ∈ LinearMap.ker F.Ez := by
    simp [LinearMap.mem_ker, map_sub, F.Ez_idempotent]
  have hfix : F.T (v - F.Ez v) = v - F.Ez v :=
    congrArg Subtype.val (LinearMap.congr_fun hBid ⟨v - F.Ez v, hminus⟩)
  simp only [map_sub, F.T_fixes_Ez] at hfix
  exact sub_left_injective hfix

theorem character_ranks [FiniteDimensional ℝ V] : ∀ i, F.rank i = 1 := by
  have hx := (binary_range_bound _ F.spanning F.Ex F.binary_x).2
  have hy := (binary_range_bound _ F.spanning F.Ey F.binary_y).2
  rw [F.rank_Ex] at hx
  rw [F.rank_Ey] at hy
  have hr := F.rank_common_positive
  have hm := F.rank_minus_at_least_two
  have hconj := F.rank_Ez_eq_Ex
  rw [F.rank_Ez, F.rank_Ex] at hconj
  have h0 : F.rank 0 = 1 := by omega
  have h1 : F.rank 1 = 1 := by omega
  have h2 : F.rank 2 = 1 := by omega
  have h3 : F.rank 3 = 1 := by omega
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- The end-to-end statement starts without a finite-dimensional instance.
Its rank conclusions follow from the preparation and actual gate premises. -/
theorem dimension_forced :
    FiniteDimensional ℝ V ∧ finrank ℝ V = 4 ∧
      finrank ℝ (LinearMap.ker F.normalization) = 3 ∧
      finrank ℝ (LinearMap.range F.Ex) = 2 ∧
      finrank ℝ (LinearMap.range F.Ey) = 2 ∧
      finrank ℝ (LinearMap.range F.Ez) = 2 ∧
      finrank ℝ (LinearMap.range F.R) = 1 ∧
      finrank ℝ (LinearMap.range F.Qx) = 1 ∧
      finrank ℝ (LinearMap.range F.Qy) = 1 ∧
      finrank ℝ (LinearMap.range F.Qz) = 1 := by
  letI : FiniteDimensional ℝ V := F.finite_dimensional
  have hr := F.character_ranks
  have hv : finrank ℝ V = 4 := by rw [F.rank_total]; simp [hr]
  have hx : finrank ℝ (LinearMap.range F.Ex) = 2 := by rw [F.rank_Ex]; simp [hr]
  have hy : finrank ℝ (LinearMap.range F.Ey) = 2 := by rw [F.rank_Ey]; simp [hr]
  have hz : finrank ℝ (LinearMap.range F.Ez) = 2 := by rw [F.rank_Ez]; simp [hr]
  have hu : finrank ℝ (LinearMap.range F.normalization) = 1 := by
    obtain ⟨s, hs⟩ := F.nonempty
    have hsurj : Function.Surjective F.normalization := by
      intro r
      refine ⟨r • s, ?_⟩
      simp [F.normalized s hs]
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp
  have hk : finrank ℝ (LinearMap.ker F.normalization) = 3 := by
    have hn := F.normalization.finrank_range_add_finrank_ker
    omega
  refine ⟨inferInstance, hv, hk, hx, hy, hz, ?_, ?_, ?_, ?_⟩
  · simpa [rank] using hr 0
  · simpa [rank] using hr 1
  · simpa [rank] using hr 2
  · simpa [rank] using hr 3

end Frame

end

end IDT.QMClosure.FiniteGateFrameDimension
