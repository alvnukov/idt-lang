import Proofs.QMClosure.QuadraticHermitianKernel
import Proofs.QMClosure.MixerRecordNaturality

namespace IDT.QMClosure.CompositeProductKernel

open QuadraticRecordRefinement PositiveQuadraticPolarization QuadraticHermitianKernel

noncomputable section

/-- A complex sesquilinear comparison is determined by its diagonal, even when
the native carrier has no scalar multiplication or halves. -/
theorem zero_of_diagonal {B : Type*} [AddCommGroup B] (J : B →+ B)
    (F : B → B → ℂ)
    (addL : ∀ u v w, F (u + v) w = F u w + F v w)
    (addR : ∀ u v w, F u (v + w) = F u v + F u w)
    (phaseL : ∀ u v, F (J u) v = -Complex.I * F u v)
    (phaseR : ∀ u v, F u (J v) = Complex.I * F u v)
    (diag : ∀ u, F u u = 0) (u v : B) : F u v = 0 := by
  have hs := diag (u + v)
  rw [addL, addR, addR, diag u, diag v] at hs
  have ht := diag (u + J v)
  rw [addL, addR, addR, diag u, diag (J v), phaseR, phaseL] at ht
  have hsr := congrArg Complex.re hs
  have hsi := congrArg Complex.im hs
  have htr := congrArg Complex.re ht
  have hti := congrArg Complex.im ht
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.zero_re, Complex.zero_im,
      Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im] at * <;> linarith

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable {QA : A → ℝ} {QB : B → ℝ} {QC : C → ℝ}

omit [AddCommGroup B] in
/-- Polarization in the first product coordinate follows directly from the
universal readout factor and separate additivity. -/
theorem polarization_same_right (p : A → B → C)
    (addA : ∀ x x' y, p (x + x') y = p x y + p x' y)
    (factor : ∀ x y, QC (p x y) = QA x * QB y) (x x' : A) (y : B) :
    polarization QC (p x y) (p x' y) = polarization QA x x' * QB y := by
  simp only [polarization, ← addA, factor]
  ring

omit [AddCommGroup B] in
theorem kernel_same_right (jA : QuadraticPhase QA) (jC : QuadraticPhase QC)
    (p : A → B → C)
    (addA : ∀ x x' y, p (x + x') y = p x y + p x' y)
    (phaseA : ∀ x y, p (jA.J x) y = jC.J (p x y))
    (factor : ∀ x y, QC (p x y) = QA x * QB y) (x x' : A) (y : B) :
    kernel jC (p x y) (p x' y) = kernel jA x x' * (QB y : ℂ) := by
  simp only [kernel, ← phaseA, polarization_same_right p addA factor,
    Complex.ofReal_mul]
  ring

/-- Product kernels are forced by separate additive phase compatibility and
the universal product readout law. This is a sufficient bridge; it does not
establish physical availability, tensor exhaustion, or actualization. -/
theorem product_kernel (hB : PositiveQuadratic QB)
    (hC : PositiveQuadratic QC)
    (jA : QuadraticPhase QA) (jB : QuadraticPhase QB) (jC : QuadraticPhase QC)
    (p : A → B → C)
    (addA : ∀ x x' y, p (x + x') y = p x y + p x' y)
    (addB : ∀ x y y', p x (y + y') = p x y + p x y')
    (phaseA : ∀ x y, p (jA.J x) y = jC.J (p x y))
    (phaseB : ∀ x y, p x (jB.J y) = jC.J (p x y))
    (factor : ∀ x y, QC (p x y) = QA x * QB y)
    (x x' : A) (y y' : B) :
    kernel jC (p x y) (p x' y') = kernel jA x x' * kernel jB y y' := by
  let F : B → B → ℂ := fun u v =>
    kernel jC (p x u) (p x' v) - kernel jA x x' * kernel jB u v
  have hz : F y y' = 0 := zero_of_diagonal jB.J F
    (by intros; dsimp [F]; rw [addB, QuadraticHermitianKernel.add_left hC,
        QuadraticHermitianKernel.add_left hB]; ring)
    (by intros; dsimp [F]; rw [addB, QuadraticHermitianKernel.add_right hC,
        QuadraticHermitianKernel.add_right hB]; ring)
    (by intros; dsimp [F]; rw [phaseB, phase_left hC, phase_left hB]; ring)
    (by intros; dsimp [F]; rw [phaseB, phase_right hC, phase_right hB]; ring)
    (by intro u; dsimp [F]; rw [kernel_same_right jA jC p addA phaseA factor,
        QuadraticHermitianKernel.diagonal hB]; ring) y y'
  exact sub_eq_zero.mp hz

variable {V : Type*} [AddCommGroup V] {Q : V → ℝ}

theorem null_kernel_left (h : PositiveQuadratic Q) (j : QuadraticPhase Q)
    (n : V) (hn : Q n = 0) (z : V) : kernel j n z = 0 := by
  have hr := cauchy_schwarz h n z
  have hi := cauchy_schwarz h (j.J n) z
  rw [hn, zero_mul] at hr
  rw [j.preserves, hn, zero_mul] at hi
  have hpr : polarization Q n z = 0 := by nlinarith [sq_nonneg (polarization Q n z)]
  have hpi : polarization Q (j.J n) z = 0 := by
    nlinarith [sq_nonneg (polarization Q (j.J n) z)]
  simp [kernel, hpr, hpi]

theorem null_kernel_right (h : PositiveQuadratic Q) (j : QuadraticPhase Q)
    (n : V) (hn : Q n = 0) (z : V) : kernel j z n = 0 := by
  rw [← hermitian h j, null_kernel_left h j n hn, star_zero]

theorem null_translate_left (h : PositiveQuadratic Q) (j : QuadraticPhase Q)
    (x n z : V) (hn : Q n = 0) : kernel j (x + n) z = kernel j x z := by
  rw [QuadraticHermitianKernel.add_left h, null_kernel_left h j n hn, add_zero]

theorem null_translate_right (h : PositiveQuadratic Q) (j : QuadraticPhase Q)
    (x z n : V) (hn : Q n = 0) : kernel j x (z + n) = kernel j x z := by
  rw [QuadraticHermitianKernel.add_right h, null_kernel_right h j n hn, add_zero]

/-- Double centering removes affine offsets without identifying native null
vectors with zero. -/
def normalized (p : A → B → C) (x : A) (y : B) : C :=
  p x y - p x 0 - p 0 y + p 0 0

/-- A sufficient native mixer bridge. Its quarter-turns are explicitly the
ones used in the kernels. Neither raw nor normalized mixer naturality is
claimed necessary for observable kernel compatibility. -/
structure MixerBridge (jA : QuadraticPhase QA) (jB : QuadraticPhase QB)
    (jC : QuadraticPhase QC) (p : A → B → C) where
  TA : (A × A) →+ (A × A)
  TB : (B × B) →+ (B × B)
  TC : (C × C) →+ (C × C)
  transparentA : ∀ x, TA (x, x) = (x, x)
  transparentB : ∀ y, TB (y, y) = (y, y)
  transparentC : ∀ z, TC (z, z) = (z, z)
  squareA : ∀ z, TA (TA z) = z.swap
  squareB : ∀ z, TB (TB z) = z.swap
  squareC : ∀ z, TC (TC z) = z.swap
  phaseA : ∀ x, OperationalQuadraticReconstruction.phase TA x = jA.J x
  phaseB : ∀ y, OperationalQuadraticReconstruction.phase TB y = jB.J y
  phaseC : ∀ z, OperationalQuadraticReconstruction.phase TC z = jC.J z
  naturalA : ∀ y, MixerRecordNaturality.Intertwines TA TC (fun x => p x y)
  naturalB : ∀ x, MixerRecordNaturality.Intertwines TB TC (p x)

namespace MixerBridge

variable {jA : QuadraticPhase QA} {jB : QuadraticPhase QB} {jC : QuadraticPhase QC}
variable {p : A → B → C} (bridge : MixerBridge jA jB jC p)

include bridge

theorem affineA (y : B) : ∃ M : A →+ C,
    (∀ x, p x y = M x + p 0 y) ∧ (∀ x, M (jA.J x) = jC.J (M x)) := by
  obtain ⟨M, hm, hp⟩ := (MixerRecordNaturality.affine_classification bridge.TA bridge.TC
    bridge.transparentA bridge.squareA bridge.transparentC bridge.squareC
    (fun x => p x y)).mp (bridge.naturalA y)
  exact ⟨M, hm, by simpa only [bridge.phaseA, bridge.phaseC] using hp⟩

theorem affineB (x : A) : ∃ M : B →+ C,
    (∀ y, p x y = M y + p x 0) ∧ (∀ y, M (jB.J y) = jC.J (M y)) := by
  obtain ⟨M, hm, hp⟩ := (MixerRecordNaturality.affine_classification bridge.TB bridge.TC
    bridge.transparentB bridge.squareB bridge.transparentC bridge.squareC
    (p x)).mp (bridge.naturalB x)
  exact ⟨M, hm, by simpa only [bridge.phaseB, bridge.phaseC] using hp⟩

theorem normalized_add_phase :
    (∀ x x' y, normalized p (x + x') y = normalized p x y + normalized p x' y) ∧
    (∀ x y y', normalized p x (y + y') = normalized p x y + normalized p x y') ∧
    (∀ x y, normalized p (jA.J x) y = jC.J (normalized p x y)) ∧
    (∀ x y, normalized p x (jB.J y) = jC.J (normalized p x y)) := by
  have hA (y : B) : ∃ M : A →+ C,
      (∀ x, normalized p x y = M x) ∧ (∀ x, M (jA.J x) = jC.J (M x)) := by
    obtain ⟨M, hm, hp⟩ := bridge.affineA y
    obtain ⟨N, hn, hnp⟩ := bridge.affineA 0
    refine ⟨M - N, ?_, ?_⟩
    · intro x; dsimp [normalized]; rw [hm x, hn x]; abel
    · intro x; simp only [AddMonoidHom.sub_apply, hp, hnp, map_sub]
  have hB (x : A) : ∃ M : B →+ C,
      (∀ y, normalized p x y = M y) ∧ (∀ y, M (jB.J y) = jC.J (M y)) := by
    obtain ⟨M, hm, hp⟩ := bridge.affineB x
    obtain ⟨N, hn, hnp⟩ := bridge.affineB 0
    refine ⟨M - N, ?_, ?_⟩
    · intro y; dsimp [normalized]; rw [hm y, hn y]; abel
    · intro y; simp only [AddMonoidHom.sub_apply, hp, hnp, map_sub]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x x' y; obtain ⟨M, hm, _⟩ := hA y; simp only [hm, map_add]
  · intro x y y'; obtain ⟨M, hm, _⟩ := hB x; simp only [hm, map_add]
  · intro x y; obtain ⟨M, hm, hp⟩ := hA y; simp only [hm, hp]
  · intro x y; obtain ⟨M, hm, hp⟩ := hB x; simp only [hm, hp]

end MixerBridge

theorem normalized_readout (hA : PositiveQuadratic QA) (hB : PositiveQuadratic QB)
    (hC : PositiveQuadratic QC) (p : A → B → C)
    (factor : ∀ x y, QC (p x y) = QA x * QB y) (x : A) (y : B) :
    QC (normalized p x y) = QC (p x y) := by
  have h1 : QC (-p x 0) = 0 := by rw [hC.even, factor, hB.zero, mul_zero]
  have h2 : QC (-p 0 y) = 0 := by rw [hC.even, factor, hA.zero, zero_mul]
  have h3 : QC (p 0 0) = 0 := by rw [factor, hA.zero, zero_mul]
  dsimp [normalized]
  rw [hC.null_translate _ _ h3]
  simp only [sub_eq_add_neg]
  rw [hC.null_translate _ _ h2, hC.null_translate _ _ h1]

theorem normalized_kernel (hA : PositiveQuadratic QA) (hB : PositiveQuadratic QB)
    (hC : PositiveQuadratic QC) (jC : QuadraticPhase QC) (p : A → B → C)
    (factor : ∀ x y, QC (p x y) = QA x * QB y) (x x' : A) (y y' : B) :
    kernel jC (normalized p x y) (normalized p x' y') =
      kernel jC (p x y) (p x' y') := by
  have h1 (a : A) : QC (-p a 0) = 0 := by rw [hC.even, factor, hB.zero, mul_zero]
  have h2 (b : B) : QC (-p 0 b) = 0 := by rw [hC.even, factor, hA.zero, zero_mul]
  have h3 : QC (p 0 0) = 0 := by rw [factor, hA.zero, zero_mul]
  dsimp [normalized]
  simp only [sub_eq_add_neg]
  rw [null_translate_left hC jC _ _ _ h3,
    null_translate_left hC jC _ _ _ (h2 y), null_translate_left hC jC _ _ _ (h1 x),
    null_translate_right hC jC _ _ _ h3,
    null_translate_right hC jC _ _ _ (h2 y'), null_translate_right hC jC _ _ _ (h1 x')]

/-- Affine mixer naturality and the universal factor law suffice. No strict
equation p(0,y)=0 is assumed; all three offsets are only readout-null. -/
theorem mixer_product_kernel (hA : PositiveQuadratic QA) (hB : PositiveQuadratic QB)
    (hC : PositiveQuadratic QC)
    (jA : QuadraticPhase QA) (jB : QuadraticPhase QB) (jC : QuadraticPhase QC)
    (p : A → B → C) (bridge : MixerBridge jA jB jC p)
    (factor : ∀ x y, QC (p x y) = QA x * QB y) (x x' : A) (y y' : B) :
    kernel jC (p x y) (p x' y') = kernel jA x x' * kernel jB y y' := by
  obtain ⟨ha, hb, hpa, hpb⟩ := bridge.normalized_add_phase
  rw [← normalized_kernel hA hB hC jC p factor]
  exact product_kernel hB hC jA jB jC (normalized p) ha hb hpa hpb
    (fun a b => (normalized_readout hA hB hC p factor a b).trans (factor a b)) x x' y y'

/-- Native affine defects can be nonzero; every such defect is invisible to
the positive quadratic readout under the universal factor law. -/
theorem observable_defects_null (hA : PositiveQuadratic QA) (hB : PositiveQuadratic QB)
    (hC : PositiveQuadratic QC)
    (jA : QuadraticPhase QA) (jB : QuadraticPhase QB) (jC : QuadraticPhase QC)
    (p : A → B → C) (bridge : MixerBridge jA jB jC p)
    (factor : ∀ x y, QC (p x y) = QA x * QB y) :
    (∀ x x' y, QC (p (x + x') y - p x y - p x' y) = 0) ∧
    (∀ x y y', QC (p x (y + y') - p x y - p x y') = 0) ∧
    (∀ x y, QC (p (jA.J x) y - jC.J (p x y)) = 0) ∧
    (∀ x y, QC (p x (jB.J y) - jC.J (p x y)) = 0) := by
  have hnA (y : B) : QC (p 0 y) = 0 := by rw [factor, hA.zero, zero_mul]
  have hnB (x : A) : QC (p x 0) = 0 := by rw [factor, hB.zero, mul_zero]
  have hnull (z : C) (hz : QC z = 0) : QC (z - jC.J z) = 0 := by
    have hj : QC (-jC.J z) = 0 := by rw [hC.even, jC.preserves, hz]
    simpa only [sub_eq_add_neg, hz] using hC.null_translate z (-jC.J z) hj
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x x' y
    obtain ⟨M, hm, _⟩ := bridge.affineA y
    have he : p (x + x') y - p x y - p x' y = -p 0 y := by
      rw [hm (x + x'), hm x, hm x', map_add]; abel
    rw [he, hC.even, hnA]
  · intro x y y'
    obtain ⟨M, hm, _⟩ := bridge.affineB x
    have he : p x (y + y') - p x y - p x y' = -p x 0 := by
      rw [hm (y + y'), hm y, hm y', map_add]; abel
    rw [he, hC.even, hnB]
  · intro x y
    obtain ⟨M, hm, hp⟩ := bridge.affineA y
    have he : p (jA.J x) y - jC.J (p x y) = p 0 y - jC.J (p 0 y) := by
      rw [hm (jA.J x), hm x, hp, map_add]; abel
    rw [he]; exact hnull _ (hnA y)
  · intro x y
    obtain ⟨M, hm, hp⟩ := bridge.affineB x
    have he : p x (jB.J y) - jC.J (p x y) = p x 0 - jC.J (p x 0) := by
      rw [hm (jB.J y), hm y, hp, map_add]; abel
    rw [he]; exact hnull _ (hnB x)

/-- Explicit boundary: this module proves a supplied bridge's kernel law,
without tensor completion, physical product availability, coherence,
actualization, Bell closure, full QM, or any public status upgrade. -/
inductive BoundaryRole where
  | suppliedUniversalProductReadout
  | suppliedSeparatePhaseCompatibility
  | mixerNaturalitySufficientNotNecessary
  | affineOffsetsMayBeNonzeroNullVectors
  | noNativeScalarsTopologyHalvesOrHilbertPremise
  | tensorCompletionAndExhaustionRemainOpen
  | physicalProductAvailabilityAndCoherenceRemainOpen
  | actualizationBellAndFullQMRemainOpen
  | noManifestStatusUpgrade
  deriving DecidableEq, Repr

end

end IDT.QMClosure.CompositeProductKernel
