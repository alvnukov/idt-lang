import Proofs.QMClosure.OriginalGateProbabilityWall

/-!
# Probability nonuniqueness with mixed original, normalized, and swap controls

The carrier has two internal coordinates, each containing two outer sectors.
The original gate is the previously checked positive/negative mixer in each
internal coordinate. The normalized gate uses the same normalized mixer in
every coordinate, and an additional unary control swaps the outer sectors.

These explicit controls leave an internal-coordinate multiplicity. A common
positive readout can assign different weights to the two internal coordinates.
The probability families below satisfy six structural conditions on arbitrary
mixed words at every finite width, including a strengthened locality condition
for every named local generator and literal vacuum padding. This enriched
grammar and locality condition are not the unchanged normalized-only contract.

The construction is a mathematical countermodel for these named controls. It
does not claim that all possible controls fail to select a probability law,
calibrate the alternative weights, establish physical availability, or prove
Born actualization or full QM.
-/

namespace IDT.QMClosure.MixedControlProbabilityWall

noncomputable section
open MixerGeneratedProcessWall
open scoped BigOperators

abbrev Sector := OriginalGateProbabilityWall.V

/-- Coordinates are `((u₁,w₁),(u₂,w₂))`, regrouping the outer vectors `(u,w)`. -/
abbrev V := Sector × Sector

def productOperation (T : (Sector × Sector) → (Sector × Sector)) (p : V × V) : V × V :=
  (((T (p.1.1, p.2.1)).1, (T (p.1.2, p.2.2)).1),
    ((T (p.1.1, p.2.1)).2, (T (p.1.2, p.2.2)).2))

def productGate (T : (Sector × Sector) →+ (Sector × Sector)) : (V × V) →+ (V × V) where
  toFun := productOperation T
  map_zero' := by
    have hz : T (0, 0) = 0 := T.map_zero
    simp [productOperation, hz]
  map_add' p q := by
    simp only [productOperation, Prod.fst_add, Prod.snd_add, ← Prod.mk_add_mk, map_add]

def rawGate : (V × V) →+ (V × V) := productGate OriginalGateProbabilityWall.rawGate

def normalizedBaseGate : (Sector × Sector) →+ (Sector × Sector) where
  toFun := OriginalGateProbabilityWall.normalized
  map_zero' := by
    simp [OriginalGateProbabilityWall.normalized, CompositeProductControls.RawSign.n]
  map_add' p q := by
    apply Prod.ext <;> apply Prod.ext <;> apply Complex.ext <;>
      simp only [OriginalGateProbabilityWall.normalized,
        CompositeProductControls.RawSign.n_re, CompositeProductControls.RawSign.n_im,
        Prod.fst_add, Prod.snd_add, Complex.add_re, Complex.add_im] <;> ring

def normalizedGate : (V × V) →+ (V × V) := productGate normalizedBaseGate

def outerSwap : V →+ V where
  toFun x := (x.1.swap, x.2.swap)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem outerSwap_involutive (x : V) : outerSwap (outerSwap x) = x := rfl

def reference : V := ((1, 0), (0, 1))

theorem outerSwap_changes_reference : outerSwap reference ≠ reference := by
  norm_num [outerSwap, reference]

def weight (x : V) : ℝ :=
  OriginalGateProbabilityWall.weight x.1 + OriginalGateProbabilityWall.weight x.2

def quadratic (t : ℝ) (x : V) : ℝ :=
  t * OriginalGateProbabilityWall.weight x.1 +
    (1 - t) * OriginalGateProbabilityWall.weight x.2

theorem weight_nonnegative (x : V) : 0 ≤ weight x :=
  add_nonneg (OriginalGateProbabilityWall.weight_nonnegative _)
    (OriginalGateProbabilityWall.weight_nonnegative _)

theorem weight_positive (x : V) (hx : x ≠ 0) : 0 < weight x := by
  by_cases h₁ : x.1 = 0
  · have h₂ : x.2 ≠ 0 := fun h₂ => hx (Prod.ext h₁ h₂)
    simpa [weight, h₁, OriginalGateProbabilityWall.weight] using
      OriginalGateProbabilityWall.supplied_weight_positive x.2 h₂
  · exact add_pos_of_pos_of_nonneg
      (OriginalGateProbabilityWall.supplied_weight_positive x.1 h₁)
      (OriginalGateProbabilityWall.weight_nonnegative _)

theorem quadratic_zero (t : ℝ) : quadratic t 0 = 0 := by
  simp [quadratic, OriginalGateProbabilityWall.weight]

theorem quadratic_reference (t : ℝ) : quadratic t reference = 1 := by
  simp [quadratic, reference, OriginalGateProbabilityWall.weight]

theorem quadratic_nonnegative (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : V) :
    0 ≤ quadratic t x :=
  add_nonneg (mul_nonneg ht0 (OriginalGateProbabilityWall.weight_nonnegative _))
    (mul_nonneg (sub_nonneg.mpr ht1) (OriginalGateProbabilityWall.weight_nonnegative _))

theorem quadratic_positive (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (x : V) (hx : x ≠ 0) : 0 < quadratic t x := by
  by_cases h₁ : x.1 = 0
  · have h₂ : x.2 ≠ 0 := fun h₂ => hx (Prod.ext h₁ h₂)
    have h := mul_pos (sub_pos.mpr ht1)
      (OriginalGateProbabilityWall.supplied_weight_positive x.2 h₂)
    simpa [quadratic, h₁, OriginalGateProbabilityWall.weight] using h
  · exact add_pos_of_pos_of_nonneg
      (mul_pos ht0 (OriginalGateProbabilityWall.supplied_weight_positive x.1 h₁))
      (mul_nonneg (sub_pos.mpr ht1).le (OriginalGateProbabilityWall.weight_nonnegative _))

private theorem product_weight_conserved
    (T : (Sector × Sector) →+ (Sector × Sector))
    (hT : ∀ x y, OriginalGateProbabilityWall.weight (T (x, y)).1 +
      OriginalGateProbabilityWall.weight (T (x, y)).2 =
        OriginalGateProbabilityWall.weight x + OriginalGateProbabilityWall.weight y)
    (x y : V) : weight (productGate T (x, y)).1 + weight (productGate T (x, y)).2 =
      weight x + weight y := by
  have h₁ := hT x.1 y.1
  have h₂ := hT x.2 y.2
  simp only [weight, productGate, AddMonoidHom.coe_mk, ZeroHom.coe_mk, productOperation]
  linarith

private theorem product_quadratic_conserved
    (T : (Sector × Sector) →+ (Sector × Sector))
    (hT : ∀ x y, OriginalGateProbabilityWall.weight (T (x, y)).1 +
      OriginalGateProbabilityWall.weight (T (x, y)).2 =
        OriginalGateProbabilityWall.weight x + OriginalGateProbabilityWall.weight y)
    (t : ℝ) (x y : V) :
    quadratic t (productGate T (x, y)).1 + quadratic t (productGate T (x, y)).2 =
      quadratic t x + quadratic t y := by
  have h₁ := hT x.1 y.1
  have h₂ := hT x.2 y.2
  simp only [quadratic, productGate, AddMonoidHom.coe_mk, ZeroHom.coe_mk, productOperation]
  calc
    _ = t * (OriginalGateProbabilityWall.weight (T (x.1, y.1)).1 +
          OriginalGateProbabilityWall.weight (T (x.1, y.1)).2) +
        (1 - t) * (OriginalGateProbabilityWall.weight (T (x.2, y.2)).1 +
          OriginalGateProbabilityWall.weight (T (x.2, y.2)).2) := by ring
    _ = _ := by rw [h₁, h₂]; ring

theorem raw_weight_conserved (x y : V) :
    weight (rawGate (x, y)).1 + weight (rawGate (x, y)).2 = weight x + weight y :=
  product_weight_conserved _ OriginalGateProbabilityWall.weight_conserved x y

def rawData : RawOperationalHilbert.Data V where
  chosenZero := 0
  operation := rawGate
  square p := by
    change
      (((OriginalGateProbabilityWall.operation
          (OriginalGateProbabilityWall.operation (p.1.1, p.2.1))).1,
        (OriginalGateProbabilityWall.operation
          (OriginalGateProbabilityWall.operation (p.1.2, p.2.2))).1),
       ((OriginalGateProbabilityWall.operation
          (OriginalGateProbabilityWall.operation (p.1.1, p.2.1))).2,
        (OriginalGateProbabilityWall.operation
          (OriginalGateProbabilityWall.operation (p.1.2, p.2.2))).2)) = p.swap
    rw [OriginalGateProbabilityWall.operation_square,
      OriginalGateProbabilityWall.operation_square]
    rfl
  medial x y z w := by
    apply Prod.ext
    · exact OriginalGateProbabilityWall.operation_medial x.1 y.1 z.1 w.1
    · exact OriginalGateProbabilityWall.operation_medial x.2 y.2 z.2 w.2
  weight := weight
  vacuum := by simp [weight, OriginalGateProbabilityWall.weight]
  nonnegative := weight_nonnegative
  conserved := raw_weight_conserved

theorem rawGate_eq_operation (p : V × V) : rawGate p = rawData.operation p := rfl

theorem normalizedGate_eq_operation (x y : V) :
    normalizedGate (x, y) = rawData.normalizedOperation (x, y) := by
  change _ =
    (((OriginalGateProbabilityWall.rawData.normalizedOperation (x.1, y.1)).1,
      (OriginalGateProbabilityWall.rawData.normalizedOperation (x.2, y.2)).1),
     ((OriginalGateProbabilityWall.rawData.normalizedOperation (x.1, y.1)).2,
      (OriginalGateProbabilityWall.rawData.normalizedOperation (x.2, y.2)).2))
  rw [OriginalGateProbabilityWall.normalized_operation,
    OriginalGateProbabilityWall.normalized_operation]
  rfl

private theorem normalized_base_weight (x y : Sector) :
    OriginalGateProbabilityWall.weight (normalizedBaseGate (x, y)).1 +
      OriginalGateProbabilityWall.weight (normalizedBaseGate (x, y)).2 =
        OriginalGateProbabilityWall.weight x + OriginalGateProbabilityWall.weight y := by
  have h₁ := CompositeProductControls.RawSign.norm_conservation (x.1, y.1)
  have h₂ := CompositeProductControls.RawSign.norm_conservation (x.2, y.2)
  simp only [CompositeProductControls.RawSign.N] at h₁ h₂
  simp only [normalizedBaseGate, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    OriginalGateProbabilityWall.normalized, OriginalGateProbabilityWall.weight]
  linarith

theorem quadratic_outerSwap (t : ℝ) (x : V) : quadratic t (outerSwap x) = quadratic t x := by
  simp only [quadratic, outerSwap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    OriginalGateProbabilityWall.weight,
    Prod.fst_swap, Prod.snd_swap]
  ring

theorem weight_outerSwap (x : V) : weight (outerSwap x) = weight x := by
  simp only [weight, outerSwap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    OriginalGateProbabilityWall.weight,
    Prod.fst_swap, Prod.snd_swap]
  ring

inductive PairKind where
  | original
  | normalized

def pairOperation : PairKind → (V × V) →+ (V × V)
  | .original => rawGate
  | .normalized => normalizedGate

theorem pair_quadratic_conserved (kind : PairKind) (t : ℝ) (x y : V) :
    quadratic t (pairOperation kind (x, y)).1 +
      quadratic t (pairOperation kind (x, y)).2 = quadratic t x + quadratic t y := by
  cases kind with
  | original =>
      exact product_quadratic_conserved _ OriginalGateProbabilityWall.weight_conserved t x y
  | normalized => exact product_quadratic_conserved _ normalized_base_weight t x y

inductive LocalGate (ι : Type) where
  | pair (kind : PairKind) (i j : ι) (distinct : i ≠ j)
  | sectorSwap (i : ι)

def LocalGate.touches {ι : Type} : LocalGate ι → ι → Prop
  | .pair _ i j _, k => k = i ∨ k = j
  | .sectorSwap i, k => k = i

def unaryGate {ι : Type} [DecidableEq ι] (i : ι) : (ι → V) →+ (ι → V) where
  toFun x k := if k = i then outerSwap (x k) else x k
  map_zero' := by funext k; simp
  map_add' x y := by
    funext k
    simp only [Pi.add_apply]
    split_ifs <;> simp only [map_add]

def LocalGate.eval {ι : Type} [DecidableEq ι] : LocalGate ι → (ι → V) →+ (ι → V)
  | .pair kind i j _ => pairGate (pairOperation kind) i j
  | .sectorSwap i => unaryGate i

theorem LocalGate.eval_untouched {ι : Type} [DecidableEq ι] (g : LocalGate ι)
    (x : ι → V) (k : ι) (hk : ¬g.touches k) : g.eval x k = x k := by
  cases g with
  | pair kind i j hij =>
      have hi : k ≠ i := fun h => hk (Or.inl h)
      have hj : k ≠ j := fun h => hk (Or.inr h)
      simp [LocalGate.eval, pairGate, pairReplace, hi, hj]
  | sectorSwap i =>
      change (if k = i then outerSwap (x k) else x k) = x k
      exact if_neg hk

theorem LocalGate.preserves_readout {ι : Type} [Fintype ι] [DecidableEq ι]
    (g : LocalGate ι) (t : ℝ) (x : ι → V) :
    totalReadout (quadratic t) (g.eval x) = totalReadout (quadratic t) x := by
  cases g with
  | pair kind i j hij =>
      exact pairGate_preserves_readout (pairOperation kind) (quadratic t)
        (pair_quadratic_conserved kind t) i j hij x
  | sectorSwap i =>
      apply Finset.sum_congr rfl
      intro k _
      change quadratic t (if k = i then outerSwap (x k) else x k) = _
      split_ifs <;> simp only [quadratic_outerSwap]

inductive Mixed (ι : Type) where
  | identity
  | gate (g : LocalGate ι)
  | permute (e : ι ≃ ι)
  | seq (first second : Mixed ι)

def Mixed.eval {ι : Type} [DecidableEq ι] : Mixed ι → (ι → V) →+ (ι → V)
  | .identity => AddMonoidHom.id _
  | .gate g => g.eval
  | .permute e =>
      { toFun := fun x k => x (e k)
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
  | .seq c d => d.eval.comp c.eval

theorem Mixed.preserves_readout {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Mixed ι) (t : ℝ) (x : ι → V) :
    totalReadout (quadratic t) (c.eval x) = totalReadout (quadratic t) x := by
  induction c generalizing x with
  | identity => rfl
  | gate g => exact g.preserves_readout t x
  | permute e => exact e.sum_comp (fun k => quadratic t (x k))
  | seq c d hc hd => exact (hd (c.eval x)).trans (hc x)

def source {ι : Type} [DecidableEq ι] (s : ι) : ι → V := single s reference

def padState {ι κ : Type} (x : ι → V) : ι ⊕ κ → V := Sum.elim x (fun _ => 0)

def padLocal {ι : Type} (κ : Type) : LocalGate ι → LocalGate (ι ⊕ κ)
  | .pair kind i j hij => .pair kind (.inl i) (.inl j) (fun h => hij (Sum.inl.inj h))
  | .sectorSwap i => .sectorSwap (.inl i)

def padCircuit {ι : Type} (κ : Type) : Mixed ι → Mixed (ι ⊕ κ)
  | .identity => .identity
  | .gate g => .gate (padLocal κ g)
  | .permute e => .permute (Equiv.sumCongr e (Equiv.refl κ))
  | .seq c d => .seq (padCircuit κ c) (padCircuit κ d)

theorem padCircuit_eval {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (c : Mixed ι) (x : ι → V) :
    (padCircuit κ c).eval (padState x) = padState (c.eval x) := by
  induction c generalizing x with
  | identity => rfl
  | gate g =>
      funext w
      cases g <;> cases w <;>
        simp [padCircuit, padLocal, padState, Mixed.eval, LocalGate.eval,
          pairGate, pairReplace, unaryGate]
  | permute e =>
      funext w
      cases w <;> simp [padCircuit, padState, Mixed.eval]
  | seq c d hc hd =>
      change (padCircuit κ d).eval ((padCircuit κ c).eval (padState x)) = _
      rw [hc, hd]
      rfl

theorem pad_source {ι κ : Type} [DecidableEq ι] [DecidableEq κ] (s : ι) :
    source (Sum.inl s : ι ⊕ κ) = padState (source s) := by
  funext w
  cases w <;> simp [source, single, padState]

theorem pad_prepared {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (s : ι) (c : Mixed ι) :
    (padCircuit κ c).eval (source (.inl s)) = padState (c.eval (source s)) := by
  rw [pad_source, padCircuit_eval]

/-- Six structural conditions on the enriched grammar. Locality explicitly
covers both pair kinds and unary sector exchange outside their supports. -/
structure Law where
  prob : {ι : Type} → [Fintype ι] → [DecidableEq ι] → ι → Mixed ι → ι → ℝ
  nonnegative : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Mixed ι) i,
    0 ≤ prob s c i
  normalized : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Mixed ι),
    ∑ i, prob s c i = 1
  prepared_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c d : Mixed ι), c.eval (source s) = d.eval (source s) → prob s c = prob s d
  output_perm : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Mixed ι) (e : Equiv.Perm ι) i,
    prob s (.seq c (.permute e)) i = prob s c (e i)
  spectator_local : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Mixed ι) (g : LocalGate ι) k,
    ¬g.touches k → prob s (.seq c (.gate g)) k = prob s c k
  vacuum : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (s : ι) (c : Mixed ι) i,
    prob (.inl s) (padCircuit κ c) (.inl i) = prob s c i

def law (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Law where
  prob s c i := quadratic t (c.eval (source s) i)
  nonnegative _ _ _ := quadratic_nonnegative t ht0 ht1 _
  normalized s c := by
    change totalReadout (quadratic t) (c.eval (single s reference)) = 1
    rw [c.preserves_readout t,
      totalReadout_single (quadratic t) (quadratic_zero t), quadratic_reference]
  prepared_eq _ _ _ h := by funext i; rw [h]
  output_perm _ _ _ _ := rfl
  spectator_local s c g k hk := by
    change quadratic t (g.eval (c.eval (source s)) k) = _
    rw [g.eval_untouched _ k hk]
  vacuum s c i := by rw [pad_prepared]; rfl

theorem Law.spectator_pair (L : Law) {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Mixed ι) (kind : PairKind) (i j k : ι) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) :
    L.prob s (.seq c (.gate (.pair kind i j hij))) k = L.prob s c k :=
  L.spectator_local s c _ k (fun h => h.elim hki hkj)

theorem Law.spectator_swap (L : Law) {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Mixed ι) (i k : ι) (hki : k ≠ i) :
    L.prob s (.seq c (.gate (.sectorSwap i))) k = L.prob s c k :=
  L.spectator_local s c _ k hki

/-- Chronological order is original 01, then original 02, then original 12. -/
def witness : Mixed (Fin 3) :=
  .seq (.seq (.gate (.pair .original 0 1 (by decide)))
      (.gate (.pair .original 0 2 (by decide))))
    (.gate (.pair .original 1 2 (by decide)))

theorem witness_port_one :
    witness.eval (source 0) 1 =
      (((3 - Complex.I) / 4, 0), (0, (1 + Complex.I) / 4)) := by
  apply Prod.ext <;> apply Prod.ext <;> apply Complex.ext <;>
    norm_num [witness, Mixed.eval, LocalGate.eval, pairOperation, pairGate, pairReplace,
      rawGate, productGate, productOperation, OriginalGateProbabilityWall.rawGate,
      OriginalGateProbabilityWall.operation, source, single, reference,
      CompositeProductControls.RawSign.n_re, CompositeProductControls.RawSign.n_im,
      Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,
      show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
      show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

theorem witness_probability (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (law t ht0 ht1).prob 0 witness 1 = (1 + 4 * t) / 8 := by
  change quadratic t (witness.eval (source 0) 1) = _
  rw [witness_port_one]
  norm_num [quadratic, OriginalGateProbabilityWall.weight, Complex.normSq_apply,
    Complex.div_re, Complex.div_im]
  ring

theorem reference_weight : rawData.weight reference = 2 := by
  norm_num [rawData, weight, reference, OriginalGateProbabilityWall.weight]

theorem positive_reference : 0 < rawData.weight reference := by rw [reference_weight]; norm_num

theorem supplied_weight_positive (x : V) (hx : x ≠ 0) : 0 < rawData.weight x :=
  weight_positive x hx

theorem witness_weight_ratio :
    rawData.weight (witness.eval (source 0) 1) / rawData.weight reference = 3 / 8 := by
  rw [reference_weight, witness_port_one]
  norm_num [rawData, weight, OriginalGateProbabilityWall.weight, Complex.normSq_apply,
    Complex.div_re, Complex.div_im]

/-- This word also exercises the added unary control at the selected port. -/
def witnessWithSwap : Mixed (Fin 3) := .seq witness (.gate (.sectorSwap 1))

theorem witnessWithSwap_port_one :
    witnessWithSwap.eval (source 0) 1 =
      ((0, (3 - Complex.I) / 4), ((1 + Complex.I) / 4, 0)) := by
  change outerSwap (witness.eval (source 0) 1) = _
  rw [witness_port_one]
  rfl

theorem witnessWithSwap_probability (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (law t ht0 ht1).prob 0 witnessWithSwap 1 = (1 + 4 * t) / 8 := by
  change quadratic t (outerSwap (witness.eval (source 0) 1)) = _
  rw [quadratic_outerSwap]
  exact witness_probability t ht0 ht1

theorem witnessWithSwap_weight_ratio :
    rawData.weight (witnessWithSwap.eval (source 0) 1) / rawData.weight reference = 3 / 8 := by
  change weight (outerSwap (witness.eval (source 0) 1)) / rawData.weight reference = _
  rw [weight_outerSwap]
  exact witness_weight_ratio

theorem witnessWithSwap_probability_eq_ratio_iff (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (law t ht0 ht1).prob 0 witnessWithSwap 1 =
        rawData.weight (witnessWithSwap.eval (source 0) 1) / rawData.weight reference ↔
      t = 1 / 2 := by
  rw [witnessWithSwap_probability, witnessWithSwap_weight_ratio]
  constructor <;> intro h <;> linarith

def quarterLaw : Law := law (1 / 4) (by norm_num) (by norm_num)
def threeQuarterLaw : Law := law (3 / 4) (by norm_num) (by norm_num)

theorem quarter_probability : quarterLaw.prob 0 witnessWithSwap 1 = 1 / 4 := by
  rw [quarterLaw, witnessWithSwap_probability]
  norm_num

theorem three_quarter_probability : threeQuarterLaw.prob 0 witnessWithSwap 1 = 1 / 2 := by
  rw [threeQuarterLaw, witnessWithSwap_probability]
  norm_num

theorem mixed_probability_nonunique :
    quarterLaw.prob 0 witnessWithSwap 1 ≠ threeQuarterLaw.prob 0 witnessWithSwap 1 := by
  rw [quarter_probability, three_quarter_probability]
  norm_num

theorem quarter_not_weight_ratio :
    quarterLaw.prob 0 witnessWithSwap 1 ≠
      rawData.weight (witnessWithSwap.eval (source 0) 1) / rawData.weight reference := by
  rw [quarter_probability, witnessWithSwap_weight_ratio]
  norm_num

theorem three_quarter_not_weight_ratio :
    threeQuarterLaw.prob 0 witnessWithSwap 1 ≠
      rawData.weight (witnessWithSwap.eval (source 0) 1) / rawData.weight reference := by
  rw [three_quarter_probability, witnessWithSwap_weight_ratio]
  norm_num

theorem alternative_readouts_strictly_positive (x : V) (hx : x ≠ 0) :
    0 < quadratic (1 / 4) x ∧ 0 < quadratic (3 / 4) x :=
  ⟨quadratic_positive _ (by norm_num) (by norm_num) x hx,
    quadratic_positive _ (by norm_num) (by norm_num) x hx⟩

end

end IDT.QMClosure.MixedControlProbabilityWall
