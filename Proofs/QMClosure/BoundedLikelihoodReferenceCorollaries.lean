import Proofs.QMClosure.BoundedLikelihoodProcessRigidity
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Reference-density consequences of bounded likelihood rigidity

A positive lower RN bound supplies reverse bounded domination. An upper RN
bound supplies forward bounded domination when the preparation is absolutely
continuous with respect to the reference. Distinct absolutely continuous laws
therefore have essential density supremum infinity and infimum zero.

An internal reference given by a finite sum of positive finite weighted Dirac
measures forces every preparation dominated by that reference to equal it.
The sample space is an arbitrary measurable space. No measurability of its
singletons is assumed.
-/

namespace IDT.QMClosure.BoundedLikelihoodReferenceCorollaries

noncomputable section

open MeasureTheory
open BoundedDominationProcess
open scoped ENNReal NNReal

universe u v w
variable {V : Type u} {Ω : Type v} [MeasurableSpace Ω]

/-- An upper bound on the actual RN density bounds the entire measure when
absolute continuity excludes a singular part. -/
theorem boundedDom_of_ae_upper_rnDeriv (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) {C : ℝ≥0∞} (hC : 0 < C) (hCfin : C ≠ ∞)
    (hupper : ∀ᵐ s ∂Q, P.rnDeriv Q s ≤ C) : boundedDom P Q := by
  refine ⟨C, hC, hCfin, ?_⟩
  calc
    P = Q.withDensity (P.rnDeriv Q) := (Measure.withDensity_rnDeriv_eq P Q hPQ).symm
    _ ≤ Q.withDensity (fun _ => C) := withDensity_mono hupper
    _ = C • Q := withDensity_const C

/-- A positive lower RN bound controls the reference by the preparation even
when the preparation may have an additional singular part. -/
theorem reverse_boundedDom_of_ae_lower_rnDeriv (P Q : Measure Ω)
    {c : ℝ≥0∞} (hc : 0 < c) (hcfin : c ≠ ∞)
    (hlower : ∀ᵐ s ∂Q, c ≤ P.rnDeriv Q s) : boundedDom Q P := by
  have hsmall : c • Q ≤ P := by
    calc
      c • Q = Q.withDensity (fun _ => c) := (withDensity_const c).symm
      _ ≤ Q.withDensity (P.rnDeriv Q) := withDensity_mono hlower
      _ ≤ P := Measure.withDensity_rnDeriv_le P Q
  refine ⟨c⁻¹, ENNReal.inv_pos.mpr hcfin, ENNReal.inv_ne_top.mpr hc.ne', ?_⟩
  intro s
  have h := mul_le_mul_right (hsmall s) c⁻¹
  simpa only [Measure.smul_apply, smul_eq_mul,
    ENNReal.inv_mul_cancel_left hc.ne' hcfin] using h

/-- On an explicitly finite atomic probability reference, each preparation's
RN density has a finite bound. The bound may depend on the preparation.
The `NNReal` weights encode finite masses, and their positivity is explicit. -/
theorem exists_bound_rnDeriv_of_finite_atomic (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ι : Type w} [Fintype ι] (atom : ι → Ω) (weight : ι → ℝ≥0)
    (hweight : ∀ i, 0 < weight i)
    (hQ : Q = ∑ i, (weight i : ℝ≥0∞) • Measure.dirac (atom i)) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C ≠ ∞ ∧ ∀ᵐ s ∂Q, P.rnDeriv Q s ≤ C := by
  classical
  have hfiniteSum : ∀ᵐ s ∂(∑ i, (weight i : ℝ≥0∞) • Measure.dirac (atom i)),
      P.rnDeriv Q s < ∞ := by
    simpa only [← hQ] using (Measure.rnDeriv_lt_top P Q)
  have hfinite (i : ι) : P.rnDeriv Q (atom i) < ∞ := by
    have hi : ∀ᵐ s ∂((weight i : ℝ≥0∞) • Measure.dirac (atom i)),
        P.rnDeriv Q s < ∞ :=
      (ae_finsetSum_measure_iff.mp hfiniteSum) i (Finset.mem_univ i)
    have hd : ∀ᵐ s ∂Measure.dirac (atom i), P.rnDeriv Q s < ∞ :=
      (Measure.ae_ennreal_smul_measure_iff
        (ENNReal.coe_ne_zero.mpr (hweight i).ne')).mp hi
    exact (ae_dirac_iff
      (measurableSet_lt (P.measurable_rnDeriv Q) measurable_const)).mp hd
  let M : ℝ≥0∞ := Finset.univ.sup (fun i => P.rnDeriv Q (atom i))
  have hMfin : M ≠ ∞ := by
    intro hM
    obtain ⟨i, _, hi⟩ := Finset.sup_eq_top_iff.mp hM
    exact (hfinite i).ne hi
  have hboundSum : ∀ᵐ s ∂(∑ i, (weight i : ℝ≥0∞) • Measure.dirac (atom i)),
      P.rnDeriv Q s ≤ M := by
    apply ae_finsetSum_measure_iff.mpr
    intro i _
    apply Measure.ae_smul_measure
    apply (ae_dirac_iff
      (measurableSet_le (P.measurable_rnDeriv Q) measurable_const)).mpr
    exact Finset.le_sup (s := Finset.univ)
      (f := fun j => P.rnDeriv Q (atom j)) (Finset.mem_univ i)
  have hbound : ∀ᵐ s ∂Q, P.rnDeriv Q s ≤ M := by
    simpa only [← hQ] using hboundSum
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right M 1), ?_, ?_⟩
  · exact ne_of_lt (max_lt_iff.mpr ⟨lt_top_iff_ne_top.mpr hMfin, by simp⟩)
  · exact hbound.mono fun _ hs => hs.trans (le_max_left M 1)

namespace Contract

variable (D : BoundedDominationProcess.Contract V Ω)

local instance (x : V) : IsProbabilityMeasure (D.preparation x) := D.probability x

/-- A finite upper bound for the full reference-relative likelihood implies
equality. Absolute continuity remains an explicit premise. -/
theorem eq_of_ae_upper_rnDeriv {x y : V}
    (hxy : D.preparation x ≪ D.preparation y) {C : ℝ≥0∞}
    (hC : 0 < C) (hCfin : C ≠ ∞)
    (hupper : ∀ᵐ s ∂D.preparation y,
      (D.preparation x).rnDeriv (D.preparation y) s ≤ C) :
    D.preparation x = D.preparation y :=
  BoundedLikelihoodProcessRigidity.Contract.eq_of_boundedDom D
    (boundedDom_of_ae_upper_rnDeriv _ _ hxy hC hCfin hupper)

/-- A positive finite lower bound implies equality by bounding the reference
law by the preparation law. No absolute-continuity premise is needed. -/
theorem eq_of_ae_positive_lower_rnDeriv {x y : V} {c : ℝ≥0∞}
    (hc : 0 < c) (hcfin : c ≠ ∞)
    (hlower : ∀ᵐ s ∂D.preparation y,
      c ≤ (D.preparation x).rnDeriv (D.preparation y) s) :
    D.preparation x = D.preparation y :=
  (BoundedLikelihoodProcessRigidity.Contract.eq_of_boundedDom D
    (reverse_boundedDom_of_ae_lower_rnDeriv _ _ hc hcfin hlower)).symm

/-- Distinct absolutely continuous preparation laws have no finite essential
upper bound on their directed reference-relative density. -/
theorem essSup_rnDeriv_eq_top_of_ne {x y : V}
    (hxy : D.preparation x ≪ D.preparation y)
    (hne : D.preparation x ≠ D.preparation y) :
    essSup ((D.preparation x).rnDeriv (D.preparation y)) (D.preparation y) = ∞ := by
  by_contra hfin
  let U := essSup ((D.preparation x).rnDeriv (D.preparation y)) (D.preparation y)
  have hUfin : U ≠ ∞ := hfin
  have hCfin : max U 1 ≠ ∞ :=
    ne_of_lt (max_lt_iff.mpr ⟨lt_top_iff_ne_top.mpr hUfin, by simp⟩)
  have hupper : ∀ᵐ s ∂D.preparation y,
      (D.preparation x).rnDeriv (D.preparation y) s ≤ max U 1 :=
    (ae_le_essSup (f := (D.preparation x).rnDeriv (D.preparation y))
      (μ := D.preparation y)).mono fun _ hs => hs.trans (le_max_left U 1)
  exact hne (eq_of_ae_upper_rnDeriv D hxy
    (lt_of_lt_of_le zero_lt_one (le_max_right U 1)) hCfin hupper)

/-- The lower density endpoint of a distinct absolutely continuous pair is
zero. Its lower-bound argument also applies in the presence of singular mass. -/
theorem essInf_rnDeriv_eq_zero_of_ne {x y : V}
    (_hxy : D.preparation x ≪ D.preparation y)
    (hne : D.preparation x ≠ D.preparation y) :
    essInf ((D.preparation x).rnDeriv (D.preparation y)) (D.preparation y) = 0 := by
  by_contra hzero
  let L := essInf ((D.preparation x).rnDeriv (D.preparation y)) (D.preparation y)
  have hLpos : 0 < L := pos_iff_ne_zero.mpr hzero
  have hcpos : 0 < min L 1 := lt_min_iff.mpr ⟨hLpos, zero_lt_one⟩
  have hcfin : min L 1 ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (min_le_right L 1) (by simp))
  have hlower : ∀ᵐ s ∂D.preparation y,
      min L 1 ≤ (D.preparation x).rnDeriv (D.preparation y) s :=
    (ae_essInf_le (f := (D.preparation x).rnDeriv (D.preparation y))
      (μ := D.preparation y)).mono fun _ hs => (min_le_left L 1).trans hs
  exact hne (eq_of_ae_positive_lower_rnDeriv D hcpos hcfin hlower)

theorem essential_density_endpoints_of_ne {x y : V}
    (hxy : D.preparation x ≪ D.preparation y)
    (hne : D.preparation x ≠ D.preparation y) :
    essSup ((D.preparation x).rnDeriv (D.preparation y)) (D.preparation y) = ∞ ∧
      essInf ((D.preparation x).rnDeriv (D.preparation y)) (D.preparation y) = 0 :=
  ⟨essSup_rnDeriv_eq_top_of_ne D hxy hne, essInf_rnDeriv_eq_zero_of_ne D hxy hne⟩

/-- An explicitly finite atomic internal reference collapses all preparations
that are absolutely continuous with respect to it. Each finite RN bound is
constructed for the selected preparation separately. -/
theorem eq_reference_of_finite_atomic (y : V)
    {ι : Type w} [Fintype ι] (atom : ι → Ω) (weight : ι → ℝ≥0)
    (hweight : ∀ i, 0 < weight i)
    (hreference : D.preparation y = ∑ i, (weight i : ℝ≥0∞) • Measure.dirac (atom i))
    (hdominated : ∀ x, D.preparation x ≪ D.preparation y) :
    ∀ x, D.preparation x = D.preparation y := by
  intro x
  obtain ⟨C, hC, hCfin, hupper⟩ := exists_bound_rnDeriv_of_finite_atomic
    (D.preparation x) (D.preparation y) atom weight hweight hreference
  exact eq_of_ae_upper_rnDeriv D (hdominated x) hC hCfin hupper

theorem constant_of_finite_atomic_reference (y : V)
    {ι : Type w} [Fintype ι] (atom : ι → Ω) (weight : ι → ℝ≥0)
    (hweight : ∀ i, 0 < weight i)
    (hreference : D.preparation y = ∑ i, (weight i : ℝ≥0∞) • Measure.dirac (atom i))
    (hdominated : ∀ x, D.preparation x ≪ D.preparation y) :
    ∀ x z, D.preparation x = D.preparation z := by
  have heq := eq_reference_of_finite_atomic D y atom weight hweight hreference hdominated
  intro x z
  exact (heq x).trans (heq z).symm

end Contract
end
end IDT.QMClosure.BoundedLikelihoodReferenceCorollaries
