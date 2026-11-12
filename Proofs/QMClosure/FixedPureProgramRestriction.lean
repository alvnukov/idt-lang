import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Tactic

/-! Conditional restriction of reversible controls to a fixed pure program.
Local midpoint symmetry is used only on the supplied local normalized base.
Reference systems use explicit marginal naturality, with atomic factorization
supplied separately. No reference-base symmetry, product-centre interior,
operational control origin, or full atomicity conclusion is asserted here.
Reversibility of the joint control is an explicit additional premise. The
current normalized controlled-process contract does not derive that premise.
-/

namespace IDT.QMClosure.FixedPureProgramRestriction

open Set

variable {A B C : Type*} [AddCommGroup A] [Module ℝ A]
  [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C]

def induced (embed : A →ₗ[ℝ] C) (retract : C →ₗ[ℝ] A)
    (G : C →ₗ[ℝ] C) : A →ₗ[ℝ] A := retract.comp (G.comp embed)

/-- A forward embedding identity already gives a left recovery from the inverse
joint control. No inverse target-fibre invariance is required for this step. -/
theorem left_recovery_of_forward_intertwining
    (embed : A →ₗ[ℝ] C) (retract : C →ₗ[ℝ] A)
    (hretract : retract.comp embed = LinearMap.id)
    (G : C ≃ₗ[ℝ] C) (Fplus : Module.End ℝ A)
    (hforward : G.toLinearMap.comp embed = embed.comp Fplus) :
    induced embed retract G.symm.toLinearMap * Fplus = 1 := by
  ext a
  have hf : G (embed a) = embed (Fplus a) := DFunLike.congr_fun hforward a
  change retract (G.symm (embed (Fplus a))) = a
  rw [← hf, G.symm_apply_apply]
  exact DFunLike.congr_fun hretract a

/-- The induced map preserves the normalized base by the supplied embedding,
joint-map and retraction preservation laws. This also applies to an inverse control. -/
theorem induced_mapsTo
    (KA : Set A) (KC : Set C) (embed : A →ₗ[ℝ] C) (retract : C →ₗ[ℝ] A)
    (G : C →ₗ[ℝ] C)
    (hEmbed : MapsTo embed KA KC) (hRetract : MapsTo retract KC KA)
    (hG : MapsTo G KC KC) : MapsTo (induced embed retract G) KA KA := by
  intro a ha
  exact hRetract (hG (hEmbed ha))

/-- Atomic factorization on the target fibre extends normalized intertwining
to all vectors by the algebraic spanning premise. -/
theorem atomicity_intertwining
    (KA : Set A) (KC : Set C) (embed : A →ₗ[ℝ] C) (retract : C →ₗ[ℝ] A)
    (target : C →ₗ[ℝ] B) (t : B) (G : C →ₗ[ℝ] C)
    (hspan : Submodule.span ℝ KA = ⊤)
    (hEmbed : MapsTo embed KA KC) (hG : MapsTo G KC KC)
    (hatomic : ∀ z ∈ KC, target z = t → embed (retract z) = z)
    (hprogram : ∀ a ∈ KA, target (G (embed a)) = t) :
    embed.comp (induced embed retract G) = G.comp embed := by
  apply LinearMap.ext_on hspan
  intro a ha
  exact hatomic _ (hG (hEmbed ha)) (hprogram a ha)

/-- The induced map fixes every pointer whose embedded image is fixed. -/
theorem induced_pointer_fixed
    (embed : A →ₗ[ℝ] C) (retract : C →ₗ[ℝ] A)
    (hretract : retract.comp embed = LinearMap.id)
    (G : C →ₗ[ℝ] C) (p : A) (hfixed : G (embed p) = embed p) :
    induced embed retract G p = p := by
  change retract (G (embed p)) = p
  rw [hfixed]
  exact DFunLike.congr_fun hretract p

/-- Forward and inverse target-fibre invariance give a genuine reversible local
restriction. The normalized base may have arbitrary shape. -/
theorem reversible_fibre_restriction
    (KA : Set A) (KC : Set C) (embed : A →ₗ[ℝ] C) (retract : C →ₗ[ℝ] A)
    (target : C →ₗ[ℝ] B) (t : B) (G : C ≃ₗ[ℝ] C)
    (hspan : Submodule.span ℝ KA = ⊤)
    (hretract : retract.comp embed = LinearMap.id)
    (hEmbed : MapsTo embed KA KC) (hRetract : MapsTo retract KC KA)
    (hG : MapsTo G KC KC) (hGinv : MapsTo G.symm KC KC)
    (hatomic : ∀ z ∈ KC, target z = t → embed (retract z) = z)
    (hforward : ∀ a ∈ KA, target (G (embed a)) = t)
    (hbackward : ∀ a ∈ KA, target (G.symm (embed a)) = t) :
    ∃ F : A ≃ₗ[ℝ] A,
      F.toLinearMap = induced embed retract G.toLinearMap ∧
      F.symm.toLinearMap = induced embed retract G.symm.toLinearMap ∧
      MapsTo F KA KA ∧ MapsTo F.symm KA KA ∧
      embed.comp F.toLinearMap = G.toLinearMap.comp embed ∧
      embed.comp F.symm.toLinearMap = G.symm.toLinearMap.comp embed := by
  let f := induced embed retract G.toLinearMap
  let g := induced embed retract G.symm.toLinearMap
  have hf := atomicity_intertwining KA KC embed retract target t G.toLinearMap
    hspan hEmbed hG hatomic hforward
  have hg := atomicity_intertwining KA KC embed retract target t G.symm.toLinearMap
    hspan hEmbed hGinv hatomic hbackward
  have hfg : ∀ a, f (g a) = a := by
    intro a
    have hga : embed (g a) = G.symm (embed a) := DFunLike.congr_fun hg a
    change retract (G (embed (g a))) = a
    rw [hga, G.apply_symm_apply]
    exact DFunLike.congr_fun hretract a
  have hgf : ∀ a, g (f a) = a := by
    intro a
    have hfa : embed (f a) = G (embed a) := DFunLike.congr_fun hf a
    change retract (G.symm (embed (f a))) = a
    rw [hfa, G.symm_apply_apply]
    exact DFunLike.congr_fun hretract a
  let F : A ≃ₗ[ℝ] A := { f with invFun := g, left_inv := hgf, right_inv := hfg }
  refine ⟨F, rfl, rfl, ?_, ?_, hf, hg⟩
  · intro a ha
    exact hRetract (hG (hEmbed ha))
  · intro a ha
    exact hRetract (hGinv (hEmbed ha))

/-- Local midpoint symmetry and purity force a centre-fixing control to preserve
the target program on every normalized embedded local preparation. -/
theorem pure_program_target_invariance
    (KA : Set A) (KB : Set B) (KC : Set C)
    (embed : A →ₗ[ℝ] C) (target : C →ₗ[ℝ] B) (t : B)
    (G : C →ₗ[ℝ] C) (m : A) (hm : m ∈ KA)
    (hsymmetric : ∀ a ∈ KA, ∃ a' ∈ KA, m = (1 / 2 : ℝ) • (a + a'))
    (hpure : ∀ b ∈ KB, ∀ b' ∈ KB, (1 / 2 : ℝ) • (b + b') = t → b = t)
    (hEmbed : MapsTo embed KA KC) (hTarget : MapsTo target KC KB)
    (hG : MapsTo G KC KC)
    (hprogram : ∀ a ∈ KA, target (embed a) = t)
    (hfixed : G (embed m) = embed m) :
    ∀ a ∈ KA, target (G (embed a)) = t := by
  intro a ha
  obtain ⟨a', ha', hmid⟩ := hsymmetric a ha
  apply hpure _ (hTarget (hG (hEmbed ha))) _ (hTarget (hG (hEmbed ha')))
  calc
    (1 / 2 : ℝ) • (target (G (embed a)) + target (G (embed a'))) =
        target (G (embed ((1 / 2 : ℝ) • (a + a')))) := by simp only [map_smul, map_add]
    _ = target (G (embed m)) := by rw [← hmid]
    _ = t := by rw [hfixed]; exact hprogram m hm

/-- The local symmetric-base proof supplies both invariances, then the generic
restriction theorem packages the induced map and its inverse as an equivalence. -/
theorem fixed_pure_program_restriction
    (KA : Set A) (KB : Set B) (KC : Set C)
    (embed : A →ₗ[ℝ] C) (retract : C →ₗ[ℝ] A) (target : C →ₗ[ℝ] B)
    (t : B) (G : C ≃ₗ[ℝ] C) (m : A) (hm : m ∈ KA)
    (hspan : Submodule.span ℝ KA = ⊤)
    (hretract : retract.comp embed = LinearMap.id)
    (hEmbed : MapsTo embed KA KC) (hRetract : MapsTo retract KC KA)
    (hTarget : MapsTo target KC KB)
    (hG : MapsTo G KC KC) (hGinv : MapsTo G.symm KC KC)
    (hatomic : ∀ z ∈ KC, target z = t → embed (retract z) = z)
    (hprogram : ∀ a ∈ KA, target (embed a) = t)
    (hsymmetric : ∀ a ∈ KA, ∃ a' ∈ KA, m = (1 / 2 : ℝ) • (a + a'))
    (hpure : ∀ b ∈ KB, ∀ b' ∈ KB, (1 / 2 : ℝ) • (b + b') = t → b = t)
    (hfixed : G (embed m) = embed m) :
    ∃ F : A ≃ₗ[ℝ] A,
      F.toLinearMap = induced embed retract G.toLinearMap ∧
      F.symm.toLinearMap = induced embed retract G.symm.toLinearMap ∧
      MapsTo F KA KA ∧ MapsTo F.symm KA KA ∧
      embed.comp F.toLinearMap = G.toLinearMap.comp embed ∧
      embed.comp F.symm.toLinearMap = G.symm.toLinearMap.comp embed := by
  have hfixedInv : G.symm (embed m) = embed m := by
    apply G.injective
    rw [G.apply_symm_apply, hfixed]
  have hforward := pure_program_target_invariance KA KB KC embed target t G.toLinearMap
    m hm hsymmetric hpure hEmbed hTarget hG hprogram hfixed
  have hbackward := pure_program_target_invariance KA KB KC embed target t G.symm.toLinearMap
    m hm hsymmetric hpure hEmbed hTarget hGinv hprogram hfixedInv
  exact reversible_fibre_restriction KA KC embed retract target t G hspan hretract
    hEmbed hRetract hG hGinv hatomic hforward hbackward

section Reference

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

/-- Reference-system target invariance transfers by supplied marginal naturality.
The same lemma applies to the inverse maps, and uses no reference-base symmetry. -/
theorem reference_target_transfer
    (KX : Set X) (KA : Set A) (ρ : X →ₗ[ℝ] A) (σ : Y →ₗ[ℝ] C)
    (append : X →ₗ[ℝ] Y) (GY : Y →ₗ[ℝ] Y) (G : C →ₗ[ℝ] C)
    (embed : A →ₗ[ℝ] C) (target : C →ₗ[ℝ] B) (targetY : Y →ₗ[ℝ] B) (t : B)
    (hρ : MapsTo ρ KX KA)
    (hnatural : σ.comp (GY.comp append) = G.comp (embed.comp ρ))
    (htarget : targetY = target.comp σ)
    (hlocal : ∀ a ∈ KA, target (G (embed a)) = t) :
    ∀ x ∈ KX, targetY (GY (append x)) = t := by
  intro x hx
  have hn : σ (GY (append x)) = G (embed (ρ x)) := DFunLike.congr_fun hnatural x
  rw [htarget, LinearMap.comp_apply, hn]
  exact hlocal _ (hρ hx)

end Reference

end IDT.QMClosure.FixedPureProgramRestriction
