import Proofs.QMClosure.RawProcessComparisonBridge
import Proofs.QMClosure.NativeMixerEventConeExclusion

/-!
# Reconstruction from an additive pair comparison

Square-swap, a fixed diagonal, and nonexpansion of a supplied additive
comparison imply conservation and contextual mediality. The comparison is
symmetric, nonnegative, and zero on the diagonal. Its Hilbert representation
is a conclusion of these explicit mathematical premises.

Nonexpansion compares two arbitrary input pairs, so it is a global
four-preparation assumption about the supplied separable sum. No Gram
positivity, carrier addition, affinity factorization, or roots are premises.
The radial weight is defined from the comparison and chosen vacuum. Its
identification with any independently specified detector remains a separate
physical obligation. This conditional mathematical theorem asserts no
primitive derivation, Born actualization, or full QM closure.
-/

namespace IDT.QMClosure.PairComparisonReconstruction

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

open RawSparseConservationSelection OperationalContextQuotient

universe u
variable {V : Type u}

structure Contract (V : Type u) where
  chosenZero : V
  operation : V × V → V × V
  comparison : V → V → ℝ
  square : ∀ p, operation (operation p) = p.swap
  transparent : ∀ x, operation (x, x) = (x, x)
  symmetric : ∀ x y, comparison x y = comparison y x
  nonnegative : ∀ x y, 0 ≤ comparison x y
  diagonal : ∀ x, comparison x x = 0
  nonexpanding : RawProcessComparisonBridge.PairComparisonNonexpanding comparison operation

namespace Contract

variable (D : Contract V)

def raw : RawSparseConservationSelection.Contract V where
  chosenZero := D.chosenZero
  operation := D.operation
  weight x := D.comparison x D.chosenZero
  vacuum := D.diagonal _
  square := D.square
  transparent := D.transparent

def G (x y : V) : ℝ :=
  ((D.raw).weight x + (D.raw).weight y - D.comparison x y) / 2

theorem G_symmetric (x y : V) : D.G x y = D.G y x := by
  dsimp [G]
  rw [D.symmetric x y]
  ring

theorem G_diagonal (x : V) : D.G x x = D.raw.weight x := by
  simp [G, D.diagonal]

theorem G_zero (x : V) : D.G x D.chosenZero = 0 := by
  simp [G, raw, D.diagonal]

theorem comparison_isometry (p q : V × V) :
    RawProcessComparisonBridge.pairComparison D.comparison (D.operation p) (D.operation q) =
      RawProcessComparisonBridge.pairComparison D.comparison p q :=
  RawProcessComparisonBridge.pairComparison_isometry_of_nonexpanding
    D.comparison D.operation D.square D.nonexpanding p q

theorem conserved : PairConserved D.raw := by
  intro x y
  have h := D.comparison_isometry (x, y) (D.chosenZero, D.chosenZero)
  rw [D.transparent] at h
  exact h

def S (p q : V × V) : ℝ := D.G p.1 q.1 + D.G p.2 q.2

theorem S_isometry (p q : V × V) : D.S (D.operation p) (D.operation q) = D.S p q := by
  have hp := D.conserved p.1 p.2
  have hq := D.conserved q.1 q.2
  change D.raw.weight (D.operation p).1 + D.raw.weight (D.operation p).2 =
    D.raw.weight p.1 + D.raw.weight p.2 at hp
  change D.raw.weight (D.operation q).1 + D.raw.weight (D.operation q).2 =
    D.raw.weight q.1 + D.raw.weight q.2 at hq
  have hc := D.comparison_isometry p q
  dsimp [RawProcessComparisonBridge.pairComparison] at hc
  dsimp [S, G]
  linarith

theorem S_transfer (p q : V × V) : D.S (D.operation p) q = D.S p (D.operation q).swap := by
  have h := D.S_isometry p (D.operation q).swap
  have hc : D.operation (D.operation q).swap = q := by
    have hh := D.square (D.operation q)
    rw [D.square q] at hh
    rw [← hh, D.square]
    rfl
  rwa [hc] at h

theorem G_m (x y z : V) :
    D.G (m D.raw x y) z = D.G x (B D.raw z) + D.G y (A D.raw z) := by
  have h := D.S_transfer (x, y) (z, D.chosenZero)
  change D.G (m D.raw x y) z + D.G (D.operation (x, y)).2 D.chosenZero =
    D.G x (D.operation (z, D.chosenZero)).2 + D.G y (A D.raw z) at h
  rw [D.G_zero, add_zero] at h
  change D.G (m D.raw x y) z =
    D.G x (D.raw.operation (z, D.chosenZero)).2 + D.G y (A D.raw z) at h
  simpa only [second_eq_reverse D.raw] using h

theorem G_A (x z : V) : D.G (A D.raw x) z = D.G x (B D.raw z) := by
  have h := D.G_m x D.chosenZero z
  rw [D.G_symmetric D.chosenZero, D.G_zero, add_zero] at h
  exact h

theorem G_B (x z : V) : D.G (B D.raw x) z = D.G x (A D.raw z) := by
  have h := D.G_m D.chosenZero x z
  rw [D.G_symmetric D.chosenZero, D.G_zero, zero_add] at h
  exact h

theorem G_m_sum (x y z : V) :
    D.G (m D.raw x y) z = D.G (A D.raw x) z + D.G (B D.raw y) z := by
  rw [D.G_A, D.G_B, D.G_m]

def GramEq (x y : V) : Prop := ∀ z, D.G x z = D.G y z

theorem gramEq_weight (x y : V) (h : D.GramEq x y) : D.raw.weight x = D.raw.weight y := by
  rw [← D.G_diagonal x, ← D.G_diagonal y]
  calc
    D.G x x = D.G y x := h x
    _ = D.G x y := D.G_symmetric _ _
    _ = D.G y y := h y

theorem gramEq_observationalEq {x y : V} (h : D.GramEq x y) :
    ObservationalEq D.operation D.raw.weight x y := by
  apply relation_le_observationalEq D.operation D.raw.weight D.GramEq
    D.gramEq_weight ?_ ?_ h
  · intro s a b r hab z
    cases s with
    | first =>
      change D.G (m D.raw a r) z = D.G (m D.raw b r) z
      rw [D.G_m, D.G_m, hab (B D.raw z)]
    | second =>
      change D.G (D.raw.operation (a, r)).2 z = D.G (D.raw.operation (b, r)).2 z
      rw [second_eq_reverse D.raw, second_eq_reverse D.raw, D.G_m, D.G_m, hab (A D.raw z)]
  · intro s a b r hab z
    cases s with
    | first =>
      change D.G (m D.raw r a) z = D.G (m D.raw r b) z
      rw [D.G_m, D.G_m, hab (A D.raw z)]
    | second =>
      change D.G (D.raw.operation (r, a)).2 z = D.G (D.raw.operation (r, b)).2 z
      rw [second_eq_reverse D.raw, second_eq_reverse D.raw, D.G_m, D.G_m, hab (B D.raw z)]

theorem G_split (x z : V) : D.G (A D.raw x) z + D.G (B D.raw x) z = D.G x z := by
  have h := D.G_m x x z
  rw [m_diagonal D.raw] at h
  rw [D.G_A, D.G_B]
  exact h.symm

theorem G_commute (x z : V) : D.G x (A D.raw (B D.raw z)) = D.G x (B D.raw (A D.raw z)) := by
  have h3 := D.G_split (B D.raw z) x
  have h4 := D.G_split z (A D.raw x)
  rw [← D.G_B (A D.raw z) x, ← D.G_B (B D.raw z) x, ← D.G_B z x] at h4
  rw [D.G_symmetric x, D.G_symmetric x]
  linarith

theorem observed_medial : ObservedMedial D.raw := by
  intro a b c d
  apply D.gramEq_observationalEq
  intro z
  simp only [D.G_m]
  rw [D.G_commute b z, D.G_commute c z]
  ring

theorem sparse : SparseMarginalLaw D.raw :=
  sparse_of_conserved_and_observed_medial D.raw D.conserved D.observed_medial

def observedData : ObservedData V :=
  RawSparseConservationSelection.observedData D.raw D.sparse (fun x => D.nonnegative x _)

abbrev Hilbert := D.observedData.Hilbert

def feature (x : V) : D.Hilbert := D.observedData.feature x

theorem norm_feature_sq (x : V) : ‖D.feature x‖ ^ 2 = D.comparison x D.chosenZero :=
  D.observedData.norm_feature_sq x

theorem G_cross (x y : V) : D.G x (B D.raw (A D.raw y)) = D.G x y / 2 := by
  have h := D.G_m_sum (B D.raw y) (A D.raw y) x
  rw [m_B_A D.raw, D.G_symmetric y x,
    D.G_symmetric (A D.raw (B D.raw y)) x,
    D.G_symmetric (B D.raw (A D.raw y)) x] at h
  have hc := D.G_commute x y
  linarith

theorem G_half_A (x y : V) : D.G (A D.raw x) (A D.raw y) = D.G x y / 2 := by
  rw [D.G_A, D.G_cross]

theorem G_half_B (x y : V) : D.G (B D.raw x) (B D.raw y) = D.G x y / 2 := by
  rw [D.G_B, D.G_commute, D.G_cross]

/-- Attenuation of the complete supplied comparison is derived. -/
theorem comparison_half_A (x y : V) :
    D.comparison (A D.raw x) (A D.raw y) = D.comparison x y / 2 := by
  have ha := D.G_half_A x y
  have hx := D.G_half_A x x
  have hy := D.G_half_A y y
  rw [D.G_diagonal, D.G_diagonal] at hx hy
  dsimp [G] at ha
  linarith

theorem K_eq_G (x y : V) : K D.raw x y = 2 * D.G x (B D.raw (B D.raw y)) := by
  have hm := D.G_m_sum x y (m D.raw x y)
  have h1 := D.G_m_sum x y (A D.raw x)
  have h2 := D.G_m_sum x y (B D.raw y)
  rw [D.G_symmetric (A D.raw x) (m D.raw x y),
    D.G_symmetric (B D.raw y) (m D.raw x y)] at hm
  rw [D.G_diagonal] at hm
  rw [D.G_diagonal] at h1 h2
  have hcross : D.G (A D.raw x) (B D.raw y) = D.G x (B D.raw (B D.raw y)) :=
    D.G_A x (B D.raw y)
  have hsym := D.G_symmetric (B D.raw y) (A D.raw x)
  unfold K u v
  linarith

theorem G_eq_two_K (x y : V) :
    D.G x y = 2 * K D.raw x (A D.raw (A D.raw y)) := by
  rw [D.K_eq_G]
  have hc := D.G_commute (A D.raw x) (A D.raw y)
  rw [D.G_A, D.G_A] at hc
  have h1 := D.G_cross x (B D.raw (A D.raw y))
  have h2 := D.G_cross x y
  linarith

theorem observationalEq_gramEq {x y : V}
    (h : ObservationalEq D.operation D.raw.weight x y) : D.GramEq x y := by
  have hk := RawSparseMarginalReconstruction.observationalEq_implies_kernelEq
    (toConservedContract D.raw D.conserved) h
  intro z
  rw [D.G_eq_two_K, D.G_eq_two_K]
  exact congrArg (fun t : ℝ => 2 * t) (hk (A D.raw (A D.raw z)))

/-- The Gram kernel descends through the existing finite-context equivalence. -/
def quotientG : D.observedData.Space → D.observedData.Space → ℝ :=
  Quotient.lift₂ D.G (by
    intro a b c d hab hcd
    have h1 := D.observationalEq_gramEq hab b
    have h2 := D.observationalEq_gramEq hcd c
    calc
      D.G a b = D.G c b := h1
      _ = D.G b c := D.G_symmetric _ _
      _ = D.G d c := h2
      _ = D.G c d := D.G_symmetric _ _)

@[simp] theorem quotientG_class (x y : V) :
    D.quotientG (D.observedData.classOf x) (D.observedData.classOf y) = D.G x y := rfl

theorem quotientG_symmetric (x y : D.observedData.Space) :
    D.quotientG x y = D.quotientG y x := by
  induction x using Quotient.inductionOn with | _ x =>
    induction y using Quotient.inductionOn with | _ y => exact D.G_symmetric x y

theorem quotientG_diagonal (x : D.observedData.Space) :
    D.quotientG x x = D.observedData.quotientWeight x := by
  induction x using Quotient.inductionOn with | _ x => exact D.G_diagonal x

theorem quotientG_m (x y z : D.observedData.Space) :
    D.quotientG (D.observedData.quotientOutput .first x y) z =
      D.quotientG (D.observedData.quotientOutput .first x (D.observedData.classOf D.chosenZero)) z +
      D.quotientG (D.observedData.quotientOutput .first (D.observedData.classOf D.chosenZero) y) z := by
  induction x using Quotient.inductionOn with | _ x =>
    induction y using Quotient.inductionOn with | _ y =>
      induction z using Quotient.inductionOn with | _ z =>
        exact D.G_m_sum x y z

theorem quotient_normalized (x y : D.observedData.Space) :
    MedialSwapRoot.DiagonalNormalization.normalized
      (MedialSwapRoot.firstChannel D.observedData.quotientOperation) x y =
      D.observedData.quotientOutput .first x y := by
  change D.observedData.quotientOutput .first
    (D.observedData.quotientOutput .first x y)
    (D.observedData.quotientOutput .first x y) = _
  generalize D.observedData.quotientOutput .first x y = z
  induction z using Quotient.inductionOn with | _ z =>
    change D.observedData.classOf (m D.raw z z) = D.observedData.classOf z
    rw [m_diagonal D.raw]

theorem quotientG_add (x y z : D.observedData.Space) :
    D.quotientG (D.observedData.quotientData.addition x y) z =
      D.quotientG x z + D.quotientG y z := by
  letI : Zero D.observedData.Space := ⟨D.observedData.classOf D.chosenZero⟩
  let n := MedialSwapRoot.DiagonalNormalization.normalized
    (MedialSwapRoot.firstChannel D.observedData.quotientOperation)
  have hrow (a b c : D.observedData.Space) :
      D.quotientG (n a b) c =
        D.quotientG (MedialSwapRoot.portA n a) c +
        D.quotientG (MedialSwapRoot.portB n b) c := by
    simpa only [n, MedialSwapRoot.portA, MedialSwapRoot.portB, D.quotient_normalized]
      using D.quotientG_m a b c
  change D.quotientG (n (MedialSwapRoot.inverseATerm n x) (MedialSwapRoot.inverseBTerm n y)) z = _
  have ha : MedialSwapRoot.portA n (MedialSwapRoot.inverseATerm n x) = x :=
    MedialSwapRoot.portA_inverseATerm D.observedData.quotientData.normalizedLaws x
  have hb : MedialSwapRoot.portB n (MedialSwapRoot.inverseBTerm n y) = y :=
    MedialSwapRoot.portB_inverseBTerm D.observedData.quotientData.normalizedLaws y
  rw [hrow, ha, hb]

theorem quotientWeight_add (x y : D.observedData.Space) :
    D.observedData.quotientWeight (D.observedData.quotientData.addition x y) =
      D.observedData.quotientWeight x + D.observedData.quotientWeight y + 2 * D.quotientG x y := by
  rw [← D.quotientG_diagonal, D.quotientG_add]
  rw [D.quotientG_symmetric x, D.quotientG_symmetric y, D.quotientG_add, D.quotientG_add]
  rw [D.quotientG_symmetric y x, D.quotientG_diagonal, D.quotientG_diagonal]
  ring

theorem inner_feature_re (x y : V) :
    (inner ℂ (D.feature x) (D.feature y)).re = D.G x y := by
  change (inner ℂ (D.observedData.quotientData.feature (D.observedData.classOf x))
    (D.observedData.quotientData.feature (D.observedData.classOf y))).re = _
  rw [D.observedData.quotientData.inner_feature, QuadraticHermitianKernel.kernel_re]
  unfold PositiveQuadraticPolarization.polarization
  rw [D.observedData.quotientData.carrier_add]
  change (D.observedData.quotientWeight (D.observedData.quotientData.addition
    (D.observedData.classOf x) (D.observedData.classOf y)) -
    D.observedData.quotientWeight (D.observedData.classOf x) -
    D.observedData.quotientWeight (D.observedData.classOf y)) / 2 = _
  rw [D.quotientWeight_add]
  change (D.raw.weight x + D.raw.weight y + 2 * D.G x y - D.raw.weight x - D.raw.weight y) / 2 = _
  ring

/-- The entire supplied comparison is the squared feature distance. -/
theorem comparison_eq_norm_sub_sq (x y : V) :
    D.comparison x y = ‖D.feature x - D.feature y‖ ^ 2 := by
  rw [@norm_sub_sq ℂ D.Hilbert, D.norm_feature_sq, D.norm_feature_sq]
  change D.comparison x y = D.comparison x D.chosenZero -
    2 * (inner ℂ (D.feature x) (D.feature y)).re + D.comparison y D.chosenZero
  rw [D.inner_feature_re]
  dsimp [G, raw]
  ring

theorem feature_eq_iff_observationalEq (x y : V) :
    D.feature x = D.feature y ↔ ObservationalEq D.operation D.raw.weight x y :=
  D.observedData.feature_eq_iff_observationalEq x y

theorem comparison_eq_zero_iff_observationalEq (x y : V) :
    D.comparison x y = 0 ↔ ObservationalEq D.operation D.raw.weight x y := by
  rw [D.comparison_eq_norm_sub_sq, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero,
    D.feature_eq_iff_observationalEq]

end Contract

namespace ComplexWitness

/-- An existing complex mixer supplies a consistency model of every premise. -/
def model : Contract ℂ where
  chosenZero := 0
  operation := NativeMixerEventConeExclusion.mixer
  comparison x y := Complex.normSq (x - y)
  square := NativeMixerEventConeExclusion.mixer_square
  transparent := NativeMixerEventConeExclusion.mixer_transparent
  symmetric x y := by rw [← neg_sub y x, Complex.normSq_neg]
  nonnegative x y := Complex.normSq_nonneg _
  diagonal x := by simp
  nonexpanding p q := by
    change Complex.normSq (NativeMixerEventConeExclusion.mixer p -
        NativeMixerEventConeExclusion.mixer q).1 +
      Complex.normSq (NativeMixerEventConeExclusion.mixer p -
        NativeMixerEventConeExclusion.mixer q).2 ≤
      Complex.normSq (p.1 - q.1) + Complex.normSq (p.2 - q.2)
    rw [← map_sub]
    exact le_of_eq (NativeMixerEventConeExclusion.mixer_conserves _ _)

theorem comparison_one_zero : model.comparison 1 0 = 1 := by
  norm_num [model]

/-- The reconstructed representation of this supplied example is nonzero. -/
theorem feature_one_ne_zero : model.feature 1 ≠ 0 := by
  intro h
  have hn := model.norm_feature_sq 1
  rw [h, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hn
  have hc := comparison_one_zero
  change 0 = model.comparison 1 0 at hn
  linarith

end ComplexWitness
end
end IDT.QMClosure.PairComparisonReconstruction
