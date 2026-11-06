import Proofs.QMClosure.PositiveQuadraticPolarization
import Mathlib.Topology.NhdsWithin
import Mathlib.GroupTheory.OrderOfElement

namespace IDT.QMClosure.PositiveQuadraticGram

open QuadraticRecordRefinement PositiveQuadraticPolarization
open scoped BigOperators

noncomputable section

variable {V : Type*} [AddCommGroup V] {Q : V → ℝ}

/-- Finite real coefficient polynomial; the carrier has no real scalar action. -/
def gram {ι : Type*} [Fintype ι] (v : ι → V) (c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * polarization Q (v i) (v j)

theorem polarization_sum_left (h : PositiveQuadratic Q) {ι : Type*}
    (s : Finset ι) (v : ι → V) (y : V) :
    polarization Q (∑ i ∈ s, v i) y = ∑ i ∈ s, polarization Q (v i) y := by
  exact map_sum (leftAddHom h y) v s

theorem polarization_sum_right (h : PositiveQuadratic Q) {ι : Type*}
    (s : Finset ι) (v : ι → V) (x : V) :
    polarization Q x (∑ i ∈ s, v i) = ∑ i ∈ s, polarization Q x (v i) := by
  rw [symmetric, polarization_sum_left h]
  exact Finset.sum_congr rfl (fun i _ => symmetric (v i) x)

/-- Every integer-coefficient Gram value is the readout of a coherent sum. -/
theorem integer_gram (h : PositiveQuadratic Q) {ι : Type*} [Fintype ι]
    (v : ι → V) (m : ι → ℤ) :
    gram (Q := Q) v (fun i => (m i : ℝ)) = Q (∑ i, m i • v i) := by
  rw [← diagonal h, polarization_sum_left h]
  simp only [polarization_sum_right h, zsmul_left h, zsmul_right h]
  unfold gram
  congr 1
  ext i
  congr 1
  ext j
  ring

/-- A finite rational tuple admits one positive integer denominator. -/
theorem clear_denominators {ι : Type*} (s : Finset ι) (c : ι → ℚ) :
    ∃ d : ℤ, 0 < d ∧ ∀ i ∈ s, ∃ m : ℤ, (m : ℚ) = (d : ℚ) * c i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨d, hd, hm⟩ := ih
    refine ⟨d * (c a).den, mul_pos hd (by exact_mod_cast (c a).pos), ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with hia | hi
    · subst i
      refine ⟨d * (c a).num, ?_⟩
      have hn : ((c a).num : ℚ) = c a * ((c a).den : ℚ) :=
        (div_eq_iff (by exact_mod_cast (c a).den_ne_zero)).mp (Rat.num_div_den (c a))
      push_cast
      rw [hn]
      ring
    · obtain ⟨m, hm⟩ := hm i hi
      refine ⟨(c a).den * m, ?_⟩
      push_cast
      rw [hm]
      ring

/-- Integer positivity extends to rational coefficient tuples by homogeneity. -/
theorem rational_gram_nonnegative (h : PositiveQuadratic Q) {ι : Type*} [Fintype ι]
    (v : ι → V) (c : ι → ℚ) : 0 ≤ gram (Q := Q) v (fun i => (c i : ℝ)) := by
  classical
  obtain ⟨d, hd, hm⟩ := clear_denominators Finset.univ c
  choose m hm using fun i => hm i (Finset.mem_univ i)
  have he (i : ι) : (m i : ℝ) = (d : ℝ) * (c i : ℝ) := by exact_mod_cast hm i
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hid : (d : ℝ)^2 * gram (Q := Q) v (fun i => (c i : ℝ)) =
      gram (Q := Q) v (fun i => (m i : ℝ)) := by
    simp only [gram, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [he i, he j]
    ring
  apply nonneg_of_mul_nonneg_right _ (sq_pos_of_pos hdR)
  rw [hid, integer_gram h]
  exact h.nonnegative _

/-- Full finite Gram positivity, derived rather than supplied as a premise.
Density/continuity apply solely to a polynomial on the finite coefficient plane.
Neither the carrier nor its quadratic readout receives topology or real scalars. -/
theorem gram_nonnegative (h : PositiveQuadratic Q) {ι : Type*} [Fintype ι]
    (v : ι → V) (c : ι → ℝ) : 0 ≤ gram (Q := Q) v c := by
  have hd : DenseRange (fun c : ι → ℚ => fun i => (c i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  apply hd.induction_on (p := fun c => 0 ≤ gram (Q := Q) v c) c
  · exact isClosed_le continuous_const (by unfold gram; fun_prop)
  · exact rational_gram_nonnegative h v

/-- A finite additive carrier supports only the zero positive quadratic readout. -/
theorem finite_carrier_zero [Finite V] (h : PositiveQuadratic Q) (x : V) : Q x = 0 := by
  have hp : 0 < addOrderOf x := addOrderOf_pos x
  have hz := quadratic_zsmul h (addOrderOf x : ℤ) x
  have he : (addOrderOf x : ℤ) • x = 0 := by
    exact_mod_cast addOrderOf_nsmul_eq_zero x
  rw [he, h.zero] at hz
  have hpR : 0 < (addOrderOf x : ℝ) := by exact_mod_cast hp
  have hs : (addOrderOf x : ℝ)^2 ≠ 0 := ne_of_gt (sq_pos_of_pos hpR)
  exact (mul_eq_zero.mp hz.symm).resolve_left hs

end

end IDT.QMClosure.PositiveQuadraticGram
