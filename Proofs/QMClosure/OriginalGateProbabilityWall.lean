import Proofs.QMClosure.RawOperationalHilbert
import Proofs.QMClosure.CompositeProductControls
import Proofs.QMClosure.MixerGeneratedProcessWall

/-!
# Original-gate probability nonuniqueness

This explicit mathematical countermodel satisfies the raw operational data
contract with positive-definite supplied weight and a positive-weight reference.
Its original gate acts by the standard normalized mixer on one complex sector
and by its negative on the other. The reconstructed normalized gate acts by the
standard mixer on both sectors.

On the original-gate grammar, a continuum of probability fields satisfies the
same six structural conditions at every finite width. A literal three-gate word
distinguishes those fields from the supplied weight ratio. These mathematical
sector weights are not calibrated or asserted to be physical probabilities.
The result does not contradict selection on normalized-only circuits, establish
physical gate availability, or prove Born actualization or full QM. Mixed
original/normalized circuit grammars are not formalized in this module.
-/

namespace IDT.QMClosure.OriginalGateProbabilityWall

noncomputable section
open MixerGeneratedProcessWall
open scoped BigOperators

abbrev V := ℂ × ℂ

private abbrev n := CompositeProductControls.RawSign.n

def operation (p : V × V) : V × V :=
  ((n p.1.1 p.2.1, -n p.1.2 p.2.2),
    (n p.2.1 p.1.1, -n p.2.2 p.1.2))

def diagonal (x : V) : V := (x.1, -x.2)

def normalized (p : V × V) : V × V :=
  ((n p.1.1 p.2.1, n p.1.2 p.2.2),
    (n p.2.1 p.1.1, n p.2.2 p.1.2))

def weight (x : V) : ℝ := Complex.normSq x.1 + Complex.normSq x.2

def reference : V := (1, 1)

theorem operation_square (p : V × V) : operation (operation p) = p.swap := by
  apply Prod.ext <;> apply Prod.ext <;> apply Complex.ext <;>
    simp only [operation, n, CompositeProductControls.RawSign.n_re,
      CompositeProductControls.RawSign.n_im, Complex.neg_re, Complex.neg_im,
      Prod.fst_swap, Prod.snd_swap] <;> ring

theorem operation_medial (x y z w : V) :
    MedialSwapRoot.firstChannel operation
        (MedialSwapRoot.firstChannel operation x y)
        (MedialSwapRoot.firstChannel operation z w) =
      MedialSwapRoot.firstChannel operation
        (MedialSwapRoot.firstChannel operation x z)
        (MedialSwapRoot.firstChannel operation y w) := by
  apply Prod.ext
  · exact CompositeProductControls.RawSign.first_channel_medial _ _ _ _
  · exact CompositeProductControls.RawSign.rawB_first_channel_medial _ _ _ _

theorem operation_diagonal (x : V) : operation (x, x) = (diagonal x, diagonal x) := by
  simp [operation, diagonal, n, CompositeProductControls.RawSign.n_diagonal]

theorem weight_nonnegative (x : V) : 0 ≤ weight x :=
  add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

theorem weight_conserved (x y : V) :
    weight (operation (x, y)).1 + weight (operation (x, y)).2 = weight x + weight y := by
  have hp := CompositeProductControls.RawSign.norm_conservation (x.1, y.1)
  have hm := CompositeProductControls.RawSign.norm_conservation (x.2, y.2)
  simp only [CompositeProductControls.RawSign.N] at hp hm
  simp only [weight, operation, n, Complex.normSq_neg]
  linarith

def rawData : RawOperationalHilbert.Data V where
  chosenZero := 0
  operation := operation
  square := operation_square
  medial := operation_medial
  weight := weight
  vacuum := by simp [weight]
  nonnegative := weight_nonnegative
  conserved := weight_conserved

theorem normalized_operation (x y : V) :
    rawData.normalizedOperation (x, y) = normalized (x, y) := by
  change (MedialSwapRoot.DiagonalNormalization.normalized
      (MedialSwapRoot.firstChannel operation) x y,
    MedialSwapRoot.DiagonalNormalization.normalized
      (MedialSwapRoot.firstChannel operation) y x) = _
  simp [MedialSwapRoot.DiagonalNormalization.normalized,
    MedialSwapRoot.DiagonalNormalization.diagonal, MedialSwapRoot.firstChannel,
    operation, normalized, n, CompositeProductControls.RawSign.n_diagonal]

theorem original_differs_from_normalized :
    rawData.operation (reference, reference) ≠
      rawData.normalizedOperation (reference, reference) := by
  rw [normalized_operation]
  norm_num [rawData, operation, normalized, reference, n,
    CompositeProductControls.RawSign.n]

def rawGate : (V × V) →+ (V × V) where
  toFun := operation
  map_zero' := by simp [operation, n, CompositeProductControls.RawSign.n]
  map_add' p q := by
    apply Prod.ext <;> apply Prod.ext <;> apply Complex.ext <;>
      simp only [operation, n, CompositeProductControls.RawSign.n_re,
        CompositeProductControls.RawSign.n_im, Prod.fst_add, Prod.snd_add,
        Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im] <;> ring

theorem rawGate_eq_operation (p : V × V) : rawGate p = rawData.operation p := rfl

abbrev Original (ι : Type) := Circuit (ι := ι) rawGate

def source {ι : Type} [DecidableEq ι] (s : ι) : ι → V := single s reference

def padState {ι κ : Type} (x : ι → V) : ι ⊕ κ → V :=
  Sum.elim x (fun _ => 0)

def padCircuit {ι : Type} (κ : Type) : Original ι → Original (ι ⊕ κ)
  | .identity => .identity
  | .pair i j hij => .pair (.inl i) (.inl j) (fun h => hij (Sum.inl.inj h))
  | .permute e => .permute (Equiv.sumCongr e (Equiv.refl κ))
  | .seq c d => .seq (padCircuit κ c) (padCircuit κ d)

theorem padCircuit_eval {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (c : Original ι) (x : ι → V) :
    (padCircuit κ c).eval (padState x) = padState (c.eval x) := by
  induction c generalizing x with
  | identity => rfl
  | pair i j hij =>
      funext w
      cases w <;> simp [padCircuit, padState, Circuit.eval, pairGate, pairReplace]
  | permute e =>
      funext w
      cases w <;> simp [padCircuit, padState, Circuit.eval]
  | seq c d hc hd =>
      change (padCircuit κ d).eval ((padCircuit κ c).eval (padState x)) = _
      rw [hc, hd]
      rfl

theorem pad_source {ι κ : Type} [DecidableEq ι] [DecidableEq κ] (s : ι) :
    source (Sum.inl s : ι ⊕ κ) = padState (source s) := by
  funext w
  cases w <;> simp [source, single, padState]

theorem pad_prepared {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (s : ι) (c : Original ι) :
    (padCircuit κ c).eval (source (.inl s)) = padState (c.eval (source s)) := by
  rw [pad_source, padCircuit_eval]

/-- Exactly the six structural fields, now evaluated on the original raw gate. -/
structure OriginalLaw where
  prob : {ι : Type} → [Fintype ι] → [DecidableEq ι] → ι → Original ι → ι → ℝ
  nonnegative : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Original ι) i,
    0 ≤ prob s c i
  normalized : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Original ι),
    ∑ i, prob s c i = 1
  prepared_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c d : Original ι), c.eval (source s) = d.eval (source s) → prob s c = prob s d
  output_perm : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Original ι) (e : Equiv.Perm ι) i,
    prob s (.seq c (.permute e)) i = prob s c (e i)
  spectator_pair : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Original ι) (i j k : ι) (hij : i ≠ j),
    k ≠ i → k ≠ j → prob s (.seq c (.pair i j hij)) k = prob s c k
  vacuum : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (s : ι) (c : Original ι) i,
    prob (.inl s) (padCircuit κ c) (.inl i) = prob s c i

def quadratic (t : ℝ) (x : V) : ℝ :=
  t * Complex.normSq x.1 + (1 - t) * Complex.normSq x.2

theorem quadratic_zero (t : ℝ) : quadratic t 0 = 0 := by simp [quadratic]

theorem quadratic_reference (t : ℝ) : quadratic t reference = 1 := by
  simp [quadratic, reference]

theorem quadratic_nonnegative (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : V) :
    0 ≤ quadratic t x :=
  add_nonneg (mul_nonneg ht0 (Complex.normSq_nonneg _))
    (mul_nonneg (sub_nonneg.mpr ht1) (Complex.normSq_nonneg _))

theorem quadratic_positive (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (x : V) (hx : x ≠ 0) : 0 < quadratic t x := by
  by_cases hp : x.1 = 0
  · have hm : x.2 ≠ 0 := fun hm => hx (Prod.ext hp hm)
    have hn := mul_pos (sub_pos.mpr ht1) (Complex.normSq_pos.mpr hm)
    simpa [quadratic, hp] using hn
  · exact add_pos_of_pos_of_nonneg (mul_pos ht0 (Complex.normSq_pos.mpr hp))
      (mul_nonneg (sub_pos.mpr ht1).le (Complex.normSq_nonneg _))

theorem supplied_weight_positive (x : V) (hx : x ≠ 0) : 0 < rawData.weight x := by
  have h := quadratic_positive (1 / 2) (by norm_num) (by norm_num) x hx
  change 0 < weight x
  unfold weight
  unfold quadratic at h
  linarith

theorem quadratic_conserved (t : ℝ) (x y : V) :
    quadratic t (rawGate (x, y)).1 + quadratic t (rawGate (x, y)).2 =
      quadratic t x + quadratic t y := by
  have hp := CompositeProductControls.RawSign.norm_conservation (x.1, y.1)
  have hm := CompositeProductControls.RawSign.norm_conservation (x.2, y.2)
  simp only [CompositeProductControls.RawSign.N] at hp hm
  change quadratic t (operation (x, y)).1 + quadratic t (operation (x, y)).2 = _
  simp only [quadratic, operation, n, Complex.normSq_neg]
  calc
    _ = t * (Complex.normSq (CompositeProductControls.RawSign.n x.1 y.1) +
          Complex.normSq (CompositeProductControls.RawSign.n y.1 x.1)) +
        (1 - t) * (Complex.normSq (CompositeProductControls.RawSign.n x.2 y.2) +
          Complex.normSq (CompositeProductControls.RawSign.n y.2 x.2)) := by ring
    _ = _ := by rw [hp, hm]; ring

def law (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : OriginalLaw where
  prob s c i := quadratic t (c.eval (source s) i)
  nonnegative _ _ _ := quadratic_nonnegative t ht0 ht1 _
  normalized s c := by
    change totalReadout (quadratic t) (c.eval (single s reference)) = 1
    rw [c.preserves_readout (quadratic t) (quadratic_conserved t),
      totalReadout_single (quadratic t) (quadratic_zero t), quadratic_reference]
  prepared_eq _ _ _ h := by
    funext i
    rw [h]
  output_perm _ _ _ _ := rfl
  spectator_pair s c i j k hij hki hkj := by
    change quadratic t (pairReplace rawGate i j (c.eval (source s)) k) = _
    simp [pairReplace, hki, hkj]
  vacuum s c i := by
    rw [pad_prepared]
    rfl

/-- Chronological order is 01, then 02, then 12. -/
def witness : Original (Fin 3) :=
  .seq (.seq (.pair 0 1 (by decide)) (.pair 0 2 (by decide)))
    (.pair 1 2 (by decide))

theorem witness_port_one :
    witness.eval (source 0) 1 = ((3 - Complex.I) / 4, (1 + Complex.I) / 4) := by
  apply Prod.ext <;> apply Complex.ext <;>
    norm_num [witness, Circuit.eval, pairGate, pairReplace, rawGate,
      operation, source, single, reference, n, CompositeProductControls.RawSign.n_re,
      CompositeProductControls.RawSign.n_im, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.mul_im,
      show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
      show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

theorem witness_plus_weight :
    Complex.normSq (witness.eval (source 0) 1).1 = 5 / 8 := by
  rw [witness_port_one]
  norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im]

theorem witness_minus_weight :
    Complex.normSq (witness.eval (source 0) 1).2 = 1 / 8 := by
  rw [witness_port_one]
  norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im]

theorem witness_probability (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (law t ht0 ht1).prob 0 witness 1 = (1 + 4 * t) / 8 := by
  change quadratic t (witness.eval (source 0) 1) = _
  unfold quadratic
  rw [witness_plus_weight, witness_minus_weight]
  ring

theorem reference_weight : rawData.weight reference = 2 := by
  norm_num [rawData, weight, reference]

theorem positive_reference : 0 < rawData.weight reference := by rw [reference_weight]; norm_num

theorem witness_weight_ratio :
    rawData.weight (witness.eval (source 0) 1) / rawData.weight reference = 3 / 8 := by
  rw [reference_weight]
  change weight (witness.eval (source 0) 1) / 2 = _
  unfold weight
  rw [witness_plus_weight, witness_minus_weight]
  norm_num

theorem witness_probability_eq_ratio_iff (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (law t ht0 ht1).prob 0 witness 1 =
        rawData.weight (witness.eval (source 0) 1) / rawData.weight reference ↔ t = 1 / 2 := by
  rw [witness_probability, witness_weight_ratio]
  constructor <;> intro h <;> linarith

def quarterLaw : OriginalLaw := law (1 / 4) (by norm_num) (by norm_num)
def threeQuarterLaw : OriginalLaw := law (3 / 4) (by norm_num) (by norm_num)

theorem quarter_probability : quarterLaw.prob 0 witness 1 = 1 / 4 := by
  rw [quarterLaw, witness_probability]
  norm_num

theorem three_quarter_probability : threeQuarterLaw.prob 0 witness 1 = 1 / 2 := by
  rw [threeQuarterLaw, witness_probability]
  norm_num

theorem original_probability_nonunique :
    quarterLaw.prob 0 witness 1 ≠ threeQuarterLaw.prob 0 witness 1 := by
  rw [quarter_probability, three_quarter_probability]
  norm_num

theorem quarter_not_weight_ratio :
    quarterLaw.prob 0 witness 1 ≠
      rawData.weight (witness.eval (source 0) 1) / rawData.weight reference := by
  rw [quarter_probability, witness_weight_ratio]
  norm_num

theorem three_quarter_not_weight_ratio :
    threeQuarterLaw.prob 0 witness 1 ≠
      rawData.weight (witness.eval (source 0) 1) / rawData.weight reference := by
  rw [three_quarter_probability, witness_weight_ratio]
  norm_num

theorem alternative_readouts_strictly_positive (x : V) (hx : x ≠ 0) :
    0 < quadratic (1 / 4) x ∧ 0 < quadratic (3 / 4) x :=
  ⟨quadratic_positive _ (by norm_num) (by norm_num) x hx,
    quadratic_positive _ (by norm_num) (by norm_num) x hx⟩

end

end IDT.QMClosure.OriginalGateProbabilityWall
