import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Finite real mixture congruence and finite continuation rank

Classical probability averaging and local congruence of all
finite real-weight ensembles are supplied premises. The theorem gives an
algebraic affine-closure consequence. Its premises supply no physical origin
of probe-mean sufficiency and no Born, norm-selection, or full-QM conclusion.
-/

noncomputable section

namespace FiniteMixtureContinuationRank

open scoped BigOperators

variable {X : Type*} {k : ℕ}

/-- Weights outside the finite carrier are irrelevant. Zero weights and empty
carriers are allowed by the representation, with normalization deciding whether
the represented ensemble is a probability ensemble. -/
def ProbabilityWeights (s : Finset X) (w : X → ℝ) : Prop :=
  (∀ x ∈ s, 0 ≤ w x) ∧ ∑ x ∈ s, w x = 1

def meanP (P : X → Fin k → ℝ) (s : Finset X) (w : X → ℝ) : Fin k → ℝ :=
  fun i => ∑ x ∈ s, w x * P x i

/-- Both finite carriers and all nonnegative real weights are quantified.
The updated vector is the mean of the raw functions after the source action. -/
def MixtureCongruent (P : X → Fin k → ℝ) (U : X → X) : Prop :=
  ∀ (s t : Finset X) (μ ν : X → ℝ),
    ProbabilityWeights s μ → ProbabilityWeights t ν →
    meanP P s μ = meanP P t ν →
    meanP (fun x => P (U x)) s μ = meanP (fun x => P (U x)) t ν

def augmentedProbe (P : X → Fin k → ℝ) : Option (Fin k) → X → ℝ
  | none => fun _ => 1
  | some i => fun x => P x i

def probeSpace (P : X → Fin k → ℝ) : Submodule ℝ (X → ℝ) :=
  Submodule.span ℝ (Set.range (augmentedProbe P))

theorem augmentedProbe_mem (P : X → Fin k → ℝ) (a : Option (Fin k)) :
    augmentedProbe P a ∈ probeSpace P :=
  Submodule.subset_span ⟨a, rfl⟩

instance probeSpace_finiteDimensional (P : X → Fin k → ℝ) :
    FiniteDimensional ℝ (probeSpace P) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range (augmentedProbe P))

theorem finrank_probeSpace_le (P : X → Fin k → ℝ) :
    Module.finrank ℝ (probeSpace P) ≤ k + 1 := by
  simpa [probeSpace, Set.finrank] using
    (finrank_range_le_card (R := ℝ) (augmentedProbe P))

private theorem positive_negative_difference (r : ℝ) :
    max r 0 - max (-r) 0 = r := by
  simp only [max_def]
  split_ifs <;> linarith

/-- The real normalization argument turns mixture congruence into preservation
of every finite affine dependence. No rational-weight restriction is used. -/
theorem signed_relation_preserved (P : X → Fin k → ℝ) (U : X → X)
    (hU : MixtureCongruent P U) (s : Finset X) (c : X → ℝ)
    (hmass : ∑ x ∈ s, c x = 0)
    (hprobe : ∀ i, ∑ x ∈ s, c x * P x i = 0) :
    ∀ i, ∑ x ∈ s, c x * P (U x) i = 0 := by
  classical
  let p : X → ℝ := fun x => max (c x) 0
  let n : X → ℝ := fun x => max (-c x) 0
  let M : ℝ := ∑ x ∈ s, p x
  have hp (x : X) : 0 ≤ p x := le_max_right _ _
  have hn (x : X) : 0 ≤ n x := le_max_right _ _
  have hpn (x : X) : p x - n x = c x := positive_negative_difference (c x)
  have htot : ∑ x ∈ s, p x = ∑ x ∈ s, n x := by
    have hh : (∑ x ∈ s, p x) - (∑ x ∈ s, n x) = 0 := by
      rw [← Finset.sum_sub_distrib]
      simpa only [hpn] using hmass
    linarith
  have hM : 0 ≤ M := Finset.sum_nonneg (fun x _ => hp x)
  have hdiff (v : X → ℝ) :
      (∑ x ∈ s, p x * v x) - (∑ x ∈ s, n x * v x) =
        ∑ x ∈ s, c x * v x := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [← sub_mul, hpn]
  by_cases hzero : M = 0
  · have hpzero : ∀ x ∈ s, p x = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hp x)).mp hzero
    have hnzero : ∀ x ∈ s, n x = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hn x)).mp
      exact htot.symm.trans hzero
    intro i
    apply Finset.sum_eq_zero
    intro x hx
    have hc : c x = 0 := by rw [← hpn x, hpzero x hx, hnzero x hx]; ring
    rw [hc, zero_mul]
  · let μ : X → ℝ := fun x => p x / M
    let ν : X → ℝ := fun x => n x / M
    have hμ : ProbabilityWeights s μ := by
      refine ⟨fun x _ => div_nonneg (hp x) hM, ?_⟩
      change (∑ x ∈ s, p x / M) = 1
      rw [← Finset.sum_div]
      exact div_self hzero
    have hν : ProbabilityWeights s ν := by
      refine ⟨fun x _ => div_nonneg (hn x) hM, ?_⟩
      change (∑ x ∈ s, n x / M) = 1
      rw [← Finset.sum_div, ← htot]
      exact div_self hzero
    have hmeans : meanP P s μ = meanP P s ν := by
      funext i
      have hbalance : ∑ x ∈ s, p x * P x i = ∑ x ∈ s, n x * P x i := by
        have hh := hdiff (fun x => P x i)
        rw [hprobe i] at hh
        linarith
      change (∑ x ∈ s, p x / M * P x i) = ∑ x ∈ s, n x / M * P x i
      simp_rw [div_mul_eq_mul_div]
      rw [← Finset.sum_div, ← Finset.sum_div, hbalance]
    have hupdated := hU s s μ ν hμ hν hmeans
    intro i
    have hh := congrFun hupdated i
    change (∑ x ∈ s, p x / M * P (U x) i) =
      ∑ x ∈ s, n x / M * P (U x) i at hh
    simp_rw [div_mul_eq_mul_div] at hh
    rw [← Finset.sum_div, ← Finset.sum_div] at hh
    have hbalance := (div_left_inj' hzero).mp hh
    rw [← hdiff (fun x => P (U x) i), hbalance, sub_self]

/-- Affine sufficiency follows from the ensemble premise. The linear forms
act on the free real module of finite signed source combinations. -/
theorem updated_coordinate_mem (P : X → Fin k → ℝ) (U : X → X)
    (hU : MixtureCongruent P U) (i : Fin k) :
    (fun x => P (U x) i) ∈ probeSpace P := by
  classical
  let L : Option (Fin k) → (X →₀ ℝ) →ₗ[ℝ] ℝ :=
    fun a => Finsupp.linearCombination ℝ (augmentedProbe P a)
  let K : (X →₀ ℝ) →ₗ[ℝ] ℝ :=
    Finsupp.linearCombination ℝ (fun x => P (U x) i)
  have hker : (⨅ a, LinearMap.ker (L a)) ≤ LinearMap.ker K := by
    intro c hc
    have hz (a : Option (Fin k)) : L a c = 0 :=
      (Submodule.mem_iInf _).mp hc a
    have hmass : ∑ x ∈ c.support, c x = 0 := by
      simpa [L, Finsupp.linearCombination_apply, Finsupp.sum, augmentedProbe] using hz none
    have hprobe (j : Fin k) : ∑ x ∈ c.support, c x * P x j = 0 := by
      simpa [L, Finsupp.linearCombination_apply, Finsupp.sum, augmentedProbe] using hz (some j)
    have hh := signed_relation_preserved P U hU c.support c hmass hprobe i
    simpa [K, Finsupp.linearCombination_apply, Finsupp.sum] using hh
  have hmem : K ∈ Submodule.span ℝ (Set.range L) :=
    mem_span_of_iInf_ker_le_ker hker
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  apply (Submodule.mem_span_range_iff_exists_fun ℝ).mpr
  refine ⟨a, ?_⟩
  funext x
  have hx := LinearMap.congr_fun ha (Finsupp.single x 1)
  simpa [L, K] using hx

def precompose (U : X → X) : Module.End ℝ (X → ℝ) where
  toFun g := fun x => g (U x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem precompose_mem (P : X → Fin k → ℝ) (U : X → X)
    (hU : MixtureCongruent P U) {g : X → ℝ} (hg : g ∈ probeSpace P) :
    (fun x => g (U x)) ∈ probeSpace P := by
  have hclosed : probeSpace P ≤ (probeSpace P).comap (precompose U) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    cases a with
    | none => exact augmentedProbe_mem P none
    | some i => exact updated_coordinate_mem P U hU i
  exact hclosed hg

/-- A word is composed as source functions, with its head acting last. -/
def wordAction {J : Type*} (U : J → X → X) : List J → X → X
  | [] => id
  | j :: w => U j ∘ wordAction U w

theorem word_precompose_mem {J : Type*} (P : X → Fin k → ℝ)
    (U : J → X → X) (hU : ∀ j, MixtureCongruent P (U j))
    (w : List J) {g : X → ℝ} (hg : g ∈ probeSpace P) :
    (fun x => g (wordAction U w x)) ∈ probeSpace P := by
  induction w generalizing g with
  | nil => simpa [wordAction] using hg
  | cons j w ih =>
    exact ih (precompose_mem P (U j) (hU j) hg)

theorem word_coordinate_mem {J : Type*} (P : X → Fin k → ℝ)
    (U : J → X → X) (hU : ∀ j, MixtureCongruent P (U j))
    (w : List J) (i : Fin k) :
    (fun x => P (wordAction U w x) i) ∈ probeSpace P :=
  word_precompose_mem P U hU w (augmentedProbe_mem P (some i))

/-- Equality of expectations of the generators gives equality for their span. -/
theorem weighted_sum_eq_of_mem (P : X → Fin k → ℝ)
    (s t : Finset X) (μ ν : X → ℝ)
    (hμ : ProbabilityWeights s μ) (hν : ProbabilityWeights t ν)
    (hmean : meanP P s μ = meanP P t ν)
    {g : X → ℝ} (hg : g ∈ probeSpace P) :
    (∑ x ∈ s, μ x * g x) = ∑ x ∈ t, ν x * g x := by
  classical
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hg
  have hgen (j : Option (Fin k)) :
      (∑ x ∈ s, μ x * augmentedProbe P j x) =
        ∑ x ∈ t, ν x * augmentedProbe P j x := by
    cases j with
    | none => simpa [augmentedProbe, hμ.2, hν.2]
    | some j => exact congrFun hmean j
  have hvalue (x : X) : g x = ∑ j, a j * augmentedProbe P j x := by
    simpa using (congrFun ha x).symm
  have hfactor (r : Finset X) (w : X → ℝ) (j : Option (Fin k)) :
      (∑ x ∈ r, w x * (a j * augmentedProbe P j x)) =
        a j * ∑ x ∈ r, w x * augmentedProbe P j x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp_rw [hvalue, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [hfactor, hfactor, hgen j]

theorem mixtureCongruent_iff_updated_coordinates_mem
    (P : X → Fin k → ℝ) (U : X → X) :
    MixtureCongruent P U ↔ ∀ i, (fun x => P (U x) i) ∈ probeSpace P := by
  constructor
  · exact fun h i => updated_coordinate_mem P U h i
  · intro h s t μ ν hμ hν hmean
    funext i
    exact weighted_sum_eq_of_mem P s t μ ν hμ hν hmean (h i)

section IntegerLattice

abbrev IntegerLattice := ℤ × ℤ

def translationSpan (f : IntegerLattice → ℝ) : Submodule ℝ (IntegerLattice → ℝ) :=
  Submodule.span ℝ (Set.range (fun a : IntegerLattice => fun z => f (z + a)))

def localStep : Fin 4 → IntegerLattice := ![(1, 0), (-1, 0), (0, 1), (0, -1)]

/-- Integer continuation is derived by iteration of a positive and a negative
elementary action. It is not supplied as arbitrary-translation congruence. -/
private theorem coordinate_translate_mem
    (P : IntegerLattice → Fin k → ℝ) (a : IntegerLattice)
    (hp : MixtureCongruent P (fun x => x + a))
    (hn : MixtureCongruent P (fun x => x - a))
    (m : ℤ) {g : IntegerLattice → ℝ} (hg : g ∈ probeSpace P) :
    (fun x => g (x + m • a)) ∈ probeSpace P := by
  induction m using Int.induction_on with
  | zero => simpa using hg
  | succ n ih =>
    have hh := precompose_mem P (fun x => x + a) hp ih
    simpa [add_zsmul, add_mul, add_assoc, add_left_comm, add_comm] using hh
  | pred n ih =>
    have hh := precompose_mem P (fun x => x - a) hn ih
    simpa [sub_eq_add_neg, add_zsmul, add_mul, add_assoc, add_left_comm, add_comm] using hh

theorem lattice_translate_mem
    (P : IntegerLattice → Fin k → ℝ)
    (hlocal : ∀ j, MixtureCongruent P (fun x => x + localStep j))
    (a : IntegerLattice) {g : IntegerLattice → ℝ} (hg : g ∈ probeSpace P) :
    (fun x => g (x + a)) ∈ probeSpace P := by
  have hxplus : MixtureCongruent P (fun x => x + ((1, 0) : IntegerLattice)) := by
    simpa [localStep] using hlocal 0
  have hxmin : MixtureCongruent P (fun x => x - ((1, 0) : IntegerLattice)) := by
    simpa [localStep, sub_eq_add_neg] using hlocal 1
  have hyplus : MixtureCongruent P (fun x => x + ((0, 1) : IntegerLattice)) := by
    simpa [localStep] using hlocal 2
  have hymin : MixtureCongruent P (fun x => x - ((0, 1) : IntegerLattice)) := by
    simpa [localStep, sub_eq_add_neg] using hlocal 3
  have hx := coordinate_translate_mem P (1, 0) hxplus hxmin a.1 hg
  have hxy := coordinate_translate_mem P (0, 1) hyplus hymin a.2 hx
  convert hxy using 1
  funext x
  congr 1
  ext <;> simp [add_assoc, add_comm, add_left_comm]

theorem translationSpan_le_probeSpace
    (P : IntegerLattice → Fin k → ℝ)
    (hlocal : ∀ j, MixtureCongruent P (fun x => x + localStep j)) (i : Fin k) :
    translationSpan (fun z => P z i) ≤ probeSpace P := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact lattice_translate_mem P hlocal a (augmentedProbe_mem P (some i))

theorem translationSpan_finiteDimensional
    (P : IntegerLattice → Fin k → ℝ)
    (hlocal : ∀ j, MixtureCongruent P (fun x => x + localStep j)) (i : Fin k) :
    FiniteDimensional ℝ (translationSpan (fun z => P z i)) :=
  Submodule.finiteDimensional_of_le (translationSpan_le_probeSpace P hlocal i)

theorem finrank_translationSpan_le
    (P : IntegerLattice → Fin k → ℝ)
    (hlocal : ∀ j, MixtureCongruent P (fun x => x + localStep j)) (i : Fin k) :
    Module.finrank ℝ (translationSpan (fun z => P z i)) ≤ k + 1 :=
  (Submodule.finrank_mono (translationSpan_le_probeSpace P hlocal i)).trans
    (finrank_probeSpace_le P)

theorem four_probe_translation_rank_le_five
    (P : IntegerLattice → Fin 4 → ℝ)
    (hlocal : ∀ j, MixtureCongruent P (fun x => x + localStep j)) :
    FiniteDimensional ℝ (translationSpan (fun z => P z 0)) ∧
      Module.finrank ℝ (translationSpan (fun z => P z 0)) ≤ 5 :=
  ⟨translationSpan_finiteDimensional P hlocal 0, finrank_translationSpan_le P hlocal 0⟩

/-- The unfiltered squared Euclidean norm is a concrete algebraic model of the
supplied real-mixture congruence premise. -/
def normReadout (z : IntegerLattice) : ℝ :=
  (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2

def normCorner : Fin 4 → IntegerLattice := ![(0, 0), (1, 0), (0, 1), (1, 1)]

def normProbes (z : IntegerLattice) (i : Fin 4) : ℝ :=
  normReadout (z + normCorner i)

/-- Every translated norm is an explicit affine combination of the first three
corner probes. This is an exact identity of raw real functions. -/
theorem normReadout_translate_eq (z a : IntegerLattice) :
    normReadout (z + a) =
      (1 - (a.1 : ℝ) - (a.2 : ℝ)) * normProbes z 0 +
      (a.1 : ℝ) * normProbes z 1 + (a.2 : ℝ) * normProbes z 2 +
      (normReadout a - (a.1 : ℝ) - (a.2 : ℝ)) := by
  simp [normReadout, normProbes, normCorner]
  ring

theorem normReadout_translate_mem (a : IntegerLattice) :
    (fun z => normReadout (z + a)) ∈ probeSpace normProbes := by
  let W := probeSpace normProbes
  have hzero : (fun z => normProbes z 0) ∈ W :=
    augmentedProbe_mem normProbes (some 0)
  have hone : (fun z => normProbes z 1) ∈ W :=
    augmentedProbe_mem normProbes (some 1)
  have htwo : (fun z => normProbes z 2) ∈ W :=
    augmentedProbe_mem normProbes (some 2)
  have hconst : (fun _ => (1 : ℝ)) ∈ W :=
    augmentedProbe_mem normProbes none
  have hcomb := W.add_mem
    (W.add_mem
      (W.add_mem (W.smul_mem (1 - (a.1 : ℝ) - (a.2 : ℝ)) hzero)
        (W.smul_mem (a.1 : ℝ) hone))
      (W.smul_mem (a.2 : ℝ) htwo))
    (W.smul_mem (normReadout a - (a.1 : ℝ) - (a.2 : ℝ)) hconst)
  have heq : (fun z => normReadout (z + a)) =
      (1 - (a.1 : ℝ) - (a.2 : ℝ)) • (fun z => normProbes z 0) +
      (a.1 : ℝ) • (fun z => normProbes z 1) +
      (a.2 : ℝ) • (fun z => normProbes z 2) +
      (normReadout a - (a.1 : ℝ) - (a.2 : ℝ)) • (fun _ => (1 : ℝ)) := by
    funext z
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one] using
      normReadout_translate_eq z a
  rw [heq]
  exact hcomb

theorem normProbes_updated_coordinate_mem (a : IntegerLattice) (i : Fin 4) :
    (fun z => normProbes (z + a) i) ∈ probeSpace normProbes := by
  change (fun z => normReadout ((z + a) + normCorner i)) ∈ probeSpace normProbes
  simpa only [add_assoc] using normReadout_translate_mem (a + normCorner i)

/-- All integer translations satisfy the supplied mean-congruence contract for
the concrete norm probes. No readout-selection theorem is asserted. -/
theorem normProbes_mixtureCongruent (a : IntegerLattice) :
    MixtureCongruent normProbes (fun z => z + a) :=
  (mixtureCongruent_iff_updated_coordinates_mem normProbes (fun z => z + a)).mpr
    (normProbes_updated_coordinate_mem a)

/-- The conditional four-probe rank theorem has a concrete norm-model instance.
This result establishes nonvacuity of the mathematical premise. -/
theorem normReadout_finite_translation_rank :
    FiniteDimensional ℝ (translationSpan normReadout) ∧
      Module.finrank ℝ (translationSpan normReadout) ≤ 5 := by
  have hlocal (j : Fin 4) :
      MixtureCongruent normProbes (fun z => z + localStep j) :=
    normProbes_mixtureCongruent (localStep j)
  have hcoordinate : (fun z => normProbes z 0) = normReadout := by
    funext z
    change normReadout (z + 0) = normReadout z
    rw [add_zero]
  have hrank := four_probe_translation_rank_le_five normProbes hlocal
  rw [hcoordinate] at hrank
  exact hrank

end IntegerLattice

end FiniteMixtureContinuationRank
