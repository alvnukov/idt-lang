import Proofs.QMClosure.NativeAllocatedGaussianResidue
import Proofs.QMClosure.NativeAllocatedStableObservation
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.Separation.Basic

/-!
# Arbitrary finite Boolean observations do not decide the response-law criterion

Any Boolean labels on finitely many generated scalar values extend both to a
nonconstant separating signature with the existing single-basis law and to a
nonconstant nonseparating signature with no such law and no settling reference.
The positive signature has finite true support and an open false patch. No
settling assertion is made for that positive signature.

The negative signature uses full Gaussian residues modulo a sufficiently large
odd modulus, which may be composite. Its collapsed response pair consists of
actual generated known preparations. These are exact supplied arithmetic
observations, without physical-detector or probability-provenance claims.
Finite evaluated context outputs are generated values to which this theorem
applies. No adaptive-execution syntax, infinite-tail finite-family control,
actualization, multi-source probability extension, or QM closure is asserted.
-/

namespace IDT.QMClosure.NativeAllocatedFiniteObservationBoundary

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open ResponseContextQuotient NativeAllocatedObservationBoundary
open NativeAllocatedGaussianResidue NativeAllocatedSignatureLaw
open NativeAllocatedStableObservation

local instance : Infinite G := Infinite.of_injective naturalG naturalG_injective

/-- The two extensions agree on every supplied finite observation. Law and
settling conclusions below are proved separately; the positive branch carries
no settling claim. -/
structure ExtensionPair (S : Finset G) (f : G → Bool) where
  positive : G → Bool
  negative : G → Bool
  positive_agrees : ∀ s ∈ S, positive s = f s
  negative_agrees : ∀ s ∈ S, negative s = f s
  positive_nonconstant : ∃ x y, positive x ≠ positive y
  negative_nonconstant : ∃ x y, negative x ≠ negative y
  positive_separates : Separates positive
  positive_law : Nonempty (ResponseNativeProbabilitySelection.Law (signatureData positive) unitG)
  negative_not_separates : ¬ Separates negative
  negative_no_law : ¬ Nonempty (ResponseNativeProbabilitySelection.Law (signatureData negative) unitG)
  negative_no_reference_settles : ¬ ReferenceSettles negative

private def finiteSignature (T : Finset G) (x : G) : Bool := by
  classical
  exact decide (x ∈ T)

private theorem continuous_value : Continuous (fun x : G => x.val) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  exact ⟨ε, hε, fun _ h => h⟩

local instance generatedT1Space : T1Space G :=
  t1Space_of_injective_of_continuous Subtype.val_injective continuous_value

private theorem finiteSignature_open_patch (T : Finset G) (u : G) (hu : u ∉ T) :
    HasOpenConstantPatch (finiteSignature T) := by
  classical
  refine ⟨(T : Set G)ᶜ, T.isClosed.isOpen_compl, ⟨u, hu⟩, false, ?_⟩
  intro z hz
  have hzT : z ∉ T := hz
  simp [finiteSignature, hzT]

/-- No assumptions are imposed on the finite labels. -/
theorem finite_observation_boundary (S : Finset G) (f : G → Bool) :
    Nonempty (ExtensionPair S f) := by
  classical
  obtain ⟨t, ht⟩ := S.exists_notMem
  obtain ⟨u, hu⟩ := (insert t S).exists_notMem
  have hsplit : u ≠ t ∧ u ∉ S := by simpa only [Finset.mem_insert, not_or] using hu
  have hut : u ≠ t := hsplit.1
  have huS : u ∉ S := hsplit.2
  let S' := insert t (insert u S)
  let labels : G → Bool := fun x => if x = t then true else if x = u then false else f x
  let T := S'.filter (fun x => labels x = true)
  let positive := finiteSignature T
  have htT : t ∈ T := by simp [T, S', labels]
  have huT : u ∉ T := by simp [T, S', labels, hut]
  have htS' : t ∈ S' := by simp [S']
  have huS' : u ∈ S' := by simp [S']
  have hpos_agrees : ∀ s ∈ S, positive s = f s := by
    intro s hs
    have hst : s ≠ t := by intro he; subst s; exact ht hs
    have hsu : s ≠ u := by intro he; subst s; exact huS hs
    cases hf : f s <;> simp [positive, finiteSignature, T, S', labels, hs, hst, hsu, hf]
  have hpos_t : positive t = true := by simp [positive, finiteSignature, htT]
  have hpos_u : positive u = false := by simp [positive, finiteSignature, huT]
  have hpos_nc : ∃ x y, positive x ≠ positive y := by
    refine ⟨t, u, ?_⟩
    rw [hpos_t, hpos_u]
    decide
  have hpos_sep : Separates positive :=
    (separates_iff_nonconstant_of_open_constant_patch positive
      (finiteSignature_open_patch T u huT)).mpr hpos_nc
  obtain ⟨M, hM, hMlarge, hinj⟩ := exists_finite_injective_residue S'
  let χ : Residue M → Bool := fun r => decide (r ∈ T.image (residue M hM))
  let negative : G → Bool := fun x => χ (residue M hM x)
  have hmem : ∀ s ∈ S', residue M hM s ∈ T.image (residue M hM) ↔ s ∈ T := by
    intro s hs
    constructor
    · intro he
      obtain ⟨v, hv, hvs⟩ := Finset.mem_image.mp he
      have hvS' : v ∈ S' := (Finset.mem_filter.mp hv).1
      have heq : v = s := hinj hvS' hs hvs
      simpa only [heq] using hv
    · intro hsT
      exact Finset.mem_image.mpr ⟨s, hsT, rfl⟩
  have hneg_pos : ∀ s ∈ S', negative s = positive s := by
    intro s hs
    simp only [negative, χ, positive, finiteSignature, hmem s hs]
  have hneg_nc : ∃ x y, negative x ≠ negative y := by
    refine ⟨t, u, ?_⟩
    rw [hneg_pos t htS', hneg_pos u huS', hpos_t, hpos_u]
    decide
  have hcollapsed : ResponseEq operationG negative zeroG (naturalG M) := by
    apply responseEq_of_residue_eq M hM χ
    rw [residue_zeroG, residue_natural_modulus]
  have hdistinct : zeroG ≠ naturalG M := by
    intro he
    have hv := congrArg Subtype.val he
    simp only [val_zeroG, val_naturalG] at hv
    have hz : M = 0 := by exact_mod_cast hv.symm
    omega
  have hneg_sep : ¬ Separates negative := by
    intro hsep
    exact hdistinct (hsep _ _ hcollapsed)
  refine ⟨{
    positive := positive
    negative := negative
    positive_agrees := hpos_agrees
    negative_agrees := ?_
    positive_nonconstant := hpos_nc
    negative_nonconstant := hneg_nc
    positive_separates := hpos_sep
    positive_law := (law_nonempty_iff_separates positive).mpr hpos_sep
    negative_not_separates := hneg_sep
    negative_no_law := ?_
    negative_no_reference_settles := ?_ }⟩
  · intro s hs
    exact (hneg_pos s (by simp [S', hs])).trans (hpos_agrees s hs)
  · intro hL
    exact hneg_sep ((law_nonempty_iff_separates negative).mp hL)
  · intro hsettles
    exact hneg_sep ((separates_iff_nonconstant_of_reference_settles negative hsettles).mpr hneg_nc)

end
end IDT.QMClosure.NativeAllocatedFiniteObservationBoundary
