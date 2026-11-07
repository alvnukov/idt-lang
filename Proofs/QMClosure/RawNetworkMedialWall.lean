import Proofs.QMClosure.WeightFreeRawProbability

/-!
# Network meaning of mediality and a balanced-reference finite countermodel

For a complete raw square-root of swap, first-channel mediality is equivalent
to exact commutation of the row and column layers of a two-by-two network.
Those layers overlap; this is not a consequence of disjoint-support locality.

The explicit four-state routing table below satisfies square-swap, diagonal
transparency, and conserved nonnegative weight. A declared reference of weight
two splits into two weight-one outputs. Its literal raw circuit probabilities
satisfy all six all-width conditions, yet a two-gate word disagrees with the
native squared-amplitude assignment. Balance is asserted for that reference
only, not for every nonzero vacuum input. Mediality fails.

The countermodel uses its own literal raw prepared-state equality. It is not
an inhabitant of RawOperationalData, which already requires mediality, or of
the scalar native Law. No physical actualization or full QM claim is made.
-/

namespace IDT.QMClosure.RawNetworkMedialWall

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open MedialSwapRoot MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open WeightFreeRawProbability (evalRaw)
open scoped BigOperators

abbrev Quad (V : Type*) := (V × V) × (V × V)

def rows {V : Type*} (F : V × V → V × V) (x : Quad V) : Quad V :=
  (F x.1, F x.2)

def columns {V : Type*} (F : V × V → V × V) (x : Quad V) : Quad V :=
  (((F (x.1.1, x.2.1)).1, (F (x.1.2, x.2.2)).1),
    ((F (x.1.1, x.2.1)).2, (F (x.1.2, x.2.2)).2))

def FirstChannelMedial {V : Type*} (F : V × V → V × V) : Prop :=
  ∀ a b c d,
    firstChannel F (firstChannel F a b) (firstChannel F c d) =
      firstChannel F (firstChannel F a c) (firstChannel F b d)

def RowColumnCommutes {V : Type*} (F : V × V → V × V) : Prop :=
  ∀ x, columns F (rows F x) = rows F (columns F x)

/-- Top-left projection requires no square law or additive structure. -/
theorem medial_of_rowColumnCommutes {V : Type*} (F : V × V → V × V)
    (h : RowColumnCommutes F) : FirstChannelMedial F := by
  intro a b c d
  exact congrArg (fun x : Quad V => x.1.1) (h ((a,b),(c,d)))

/-- Square-swap is used only to recover the symmetric second channel. -/
theorem rowColumnCommutes_of_medial {V : Type*} (F : V × V → V × V)
    (square : ∀ p, F (F p) = p.swap) (h : FirstChannelMedial F) :
    RowColumnCommutes F := by
  have hf (x y : V) : (F (x,y)).1 = firstChannel F x y := rfl
  have hs (x y : V) : (F (x,y)).2 = firstChannel F y x :=
    congrArg Prod.snd (raw_operation_eq_symmetric F square (x,y))
  rintro ⟨⟨a,b⟩,⟨c,d⟩⟩
  apply Prod.ext
  · apply Prod.ext
    · simpa only [rows, columns, hf, hs] using h a b c d
    · simpa only [rows, columns, hf, hs] using h b a d c
  · apply Prod.ext
    · simpa only [rows, columns, hf, hs] using h c d a b
    · simpa only [rows, columns, hf, hs] using h d c b a

theorem rowColumnCommutes_iff_medial {V : Type*} (F : V × V → V × V)
    (square : ∀ p, F (F p) = p.swap) :
    RowColumnCommutes F ↔ FirstChannelMedial F :=
  ⟨medial_of_rowColumnCommutes F, rowColumnCommutes_of_medial F square⟩

/-! ## Probability laws for arbitrary literal raw semantics -/

def rawSource {V ι : Type*} [DecidableEq ι] (zero reference : V) (s : ι) : ι → V :=
  fun i => if i = s then reference else zero

def prepared {V : Type*} {ι : Type} [DecidableEq ι]
    (F : V × V → V × V) (zero reference : V) (s : ι) (c : Native ι) : ι → V :=
  evalRaw F c (rawSource zero reference s)

/-- The same six fields, with equality of the actual raw arrays as semantics. -/
structure RawSemanticsLaw {V : Type*} (F : V × V → V × V) (zero reference : V) where
  prob : {ι : Type} → [Fintype ι] → [DecidableEq ι] → ι → Native ι → ι → ℝ
  nonnegative : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι) i,
    0 ≤ prob s c i
  normalized : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c : Native ι),
    ∑ i, prob s c i = 1
  prepared_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) (c e : Native ι),
    prepared F zero reference s c = prepared F zero reference s e → prob s c = prob s e
  output_perm : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (e : Equiv.Perm ι) i,
    prob s (.seq c (.permute e)) i = prob s c (e i)
  spectator_pair : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (i j k : ι) (hij : i ≠ j),
    k ≠ i → k ≠ j → prob s (.seq c (.pair i j hij)) k = prob s c k
  vacuum : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (s : ι) (c : Native ι) i,
    prob (.inl s) (padCircuit κ c) (.inl i) = prob s c i

section RawReadout

variable {V : Type*} (F : V × V → V × V) (zero reference : V)
variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]

def padRaw (x : ι → V) : ι ⊕ κ → V := Sum.elim x (fun _ => zero)

theorem evalRaw_padCircuit (c : Native ι) (x : ι → V) :
    evalRaw F (padCircuit κ c) (padRaw zero x) = padRaw zero (evalRaw F c x) := by
  induction c generalizing x with
  | identity => rfl
  | pair i j hij =>
    funext k
    cases k <;> simp [evalRaw, padCircuit, padRaw]
  | permute e =>
    funext k
    cases k <;> rfl
  | seq c e hc he =>
    simp only [evalRaw, padCircuit, hc, he]

theorem prepared_pad (s : ι) (c : Native ι) :
    prepared F zero reference (.inl s) (padCircuit κ c) =
      padRaw zero (prepared F zero reference s c) := by
  have hsource : rawSource zero reference (Sum.inl s : ι ⊕ κ) =
      padRaw zero (rawSource zero reference s) := by
    funext k
    cases k <;> simp [rawSource, padRaw]
  unfold prepared
  rw [hsource, evalRaw_padCircuit]

variable [Fintype ι]

private theorem sum_two (f : ι → ℝ) (i j : ι) (hij : i ≠ j) :
    ∑ k, f k = f i + f j + ∑ k ∈ (Finset.univ.erase i).erase j, f k := by
  have hi := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  have hj := Finset.sum_erase_add (Finset.univ.erase i) f
    (show j ∈ Finset.univ.erase i by simp [Ne.symm hij])
  rw [← hi, ← hj]
  simp only [add_comm, add_left_comm]

private theorem sum_pair_readout (Q : V → ℝ) (i j : ι) (hij : i ≠ j) (x : ι → V) :
    (∑ k, Q (evalRaw F (.pair i j hij) x k)) =
      Q (F (x i,x j)).1 + Q (F (x i,x j)).2 +
        ∑ k ∈ (Finset.univ.erase i).erase j, Q (x k) := by
  rw [sum_two (fun k => Q (evalRaw F (.pair i j hij) x k)) i j hij]
  simp only [evalRaw, if_neg (Ne.symm hij)]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  have hkj := (Finset.mem_erase.mp hk).1
  simp only [if_neg hki, if_neg hkj]

/-- Global readout conservation uses the literal evaluator, with no raw algebra. -/
theorem evalRaw_preserves_readout (Q : V → ℝ)
    (conserved : ∀ x y, Q (F (x,y)).1 + Q (F (x,y)).2 = Q x + Q y)
    (c : Native ι) (x : ι → V) :
    (∑ i, Q (evalRaw F c x i)) = ∑ i, Q (x i) := by
  induction c generalizing x with
  | identity => rfl
  | pair i j hij =>
    rw [sum_pair_readout, conserved, sum_two (fun k => Q (x k)) i j hij]
  | permute e => exact e.sum_comp (fun i => Q (x i))
  | seq c e hc he => exact (he (evalRaw F c x)).trans (hc x)

end RawReadout

/-- A supplied conserved normalized readout yields all six raw-semantic fields.
No square-swap, transparency, or mediality is required for this construction. -/
def readoutLaw {V : Type*} (F : V × V → V × V) (zero reference : V)
    (Q : V → ℝ) (vacuum : Q zero = 0) (unitReference : Q reference = 1)
    (nonnegative : ∀ x, 0 ≤ Q x)
    (conserved : ∀ x y, Q (F (x,y)).1 + Q (F (x,y)).2 = Q x + Q y) :
    RawSemanticsLaw F zero reference where
  prob s c i := Q (prepared F zero reference s c i)
  nonnegative _ _ _ := nonnegative _
  normalized s c := by
    have h := evalRaw_preserves_readout F Q conserved c (rawSource zero reference s)
    simpa [prepared, rawSource, apply_ite, vacuum, unitReference] using h
  prepared_eq _ _ _ h := by
    funext i
    exact congrArg Q (congrFun h i)
  output_perm _ _ _ _ := rfl
  spectator_pair _ _ _ _ _ _ hki hkj := by
    simp only [prepared, evalRaw, if_neg hki, if_neg hkj]
  vacuum s c i := by
    rw [prepared_pad]
    rfl

/-! ## The four-state countermodel -/

abbrev State := Fin 4

attribute [local simp] Fin.ext_iff Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

def gate (p : State × State) : State × State :=
  ![![(0,0), (0,2), (1,0), (2,1)],
    ![(2,0), (1,1), (0,3), (2,3)],
    ![(0,1), (3,0), (2,2), (3,1)],
    ![(1,2), (3,2), (1,3), (3,3)]] p.1 p.2

def weight : State → ℕ := ![0,1,1,2]

def readout (x : State) : ℝ := (weight x : ℝ) / 2

theorem gate_square : ∀ p, gate (gate p) = p.swap := by decide

theorem gate_transparent : ∀ x, gate (x,x) = (x,x) := by decide

theorem weight_conserved : ∀ x y,
    weight (gate (x,y)).1 + weight (gate (x,y)).2 = weight x + weight y := by decide

theorem readout_conserved (x y : State) :
    readout (gate (x,y)).1 + readout (gate (x,y)).2 = readout x + readout y := by
  have h := congrArg (fun n : ℕ => (n : ℝ) / 2) (weight_conserved x y)
  simpa only [Nat.cast_add, add_div, readout] using h

theorem gate_not_medial : ¬ FirstChannelMedial gate := by
  intro h
  have hw := h 0 0 1 0
  norm_num [firstChannel, gate] at hw

theorem raw_network_witness :
    columns gate (rows gate ((0,0),(1,0))) = ((1,0),(0,0)) ∧
      rows gate (columns gate ((0,0),(1,0))) = ((0,0),(0,1)) := by decide

theorem gate_not_rowColumnCommutes : ¬ RowColumnCommutes gate :=
  fun h => gate_not_medial (medial_of_rowColumnCommutes gate h)

/-- Balance holds for the declared reference 3, with weight 2. -/
theorem declared_reference_balanced :
    weight 3 = 2 ∧ gate (3,0) = (1,2) ∧
      readout (gate (3,0)).1 = 1/2 ∧ readout (gate (3,0)).2 = 1/2 := by
  norm_num [gate, readout, weight]

/-- The balance assertion is deliberately not global over nonzero inputs. -/
theorem other_vacuum_inputs_unbalanced :
    gate (1,0) = (2,0) ∧ gate (2,0) = (0,1) ∧
      readout (gate (1,0)).2 = 0 ∧ readout (gate (2,0)).1 = 0 := by
  norm_num [gate, readout, weight]

def finiteModelLaw : RawSemanticsLaw gate 0 3 :=
  readoutLaw gate 0 3 readout (by norm_num [readout, weight])
    (by norm_num [readout, weight])
    (fun x => div_nonneg (Nat.cast_nonneg _) (by norm_num)) readout_conserved

def twoGate : Native (Fin 3) :=
  .seq (.pair 0 1 (by decide)) (.pair 0 2 (by decide))

theorem twoGate_output : prepared gate 0 3 0 twoGate = ![2,2,0] := by
  funext i
  fin_cases i <;> rfl

theorem twoGate_probabilities : finiteModelLaw.prob 0 twoGate = ![1/2,1/2,0] := by
  change (fun i => readout (prepared gate 0 3 0 twoGate i)) = _
  rw [twoGate_output]
  funext i
  fin_cases i <;> norm_num [readout, weight]

theorem twoGate_scalar_output :
    twoGate.eval (source 0) = ![Complex.I/2, (1-Complex.I)/2, 1/2] := by
  funext i
  fin_cases i <;> apply Complex.ext <;>
    norm_num [twoGate, Circuit.eval, pairGate, pairReplace, source, single,
      NativeMixerEventConeExclusion.mixer, NativeMixerEventConeExclusion.Raw,
      CompositeProductControls.RawSign.N, CompositeProductControls.RawSign.n,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem twoGate_native_norms :
    (fun i => Complex.normSq (twoGate.eval (source 0) i)) = ![1/4,1/2,1/4] := by
  rw [twoGate_scalar_output]
  funext i
  fin_cases i <;> norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im]

theorem balanced_reference_does_not_select_native_normSq :
    finiteModelLaw.prob 0 twoGate 0 ≠ Complex.normSq (twoGate.eval (source 0) 0) := by
  have hp := congrFun twoGate_probabilities 0
  have hn := congrFun twoGate_native_norms 0
  norm_num at hp hn
  rw [hp, hn]
  norm_num

/-! ## An actual reference-prepared network disagreement with a spectator -/

def splitPrefix : Native (Fin 5) := .pair 2 4 (by decide)
def rowLayer : Native (Fin 5) :=
  .seq (.pair 0 1 (by decide)) (.pair 2 3 (by decide))
def columnLayer : Native (Fin 5) :=
  .seq (.pair 0 2 (by decide)) (.pair 1 3 (by decide))
def rowsThenColumns : Native (Fin 5) := .seq splitPrefix (.seq rowLayer columnLayer)
def columnsThenRows : Native (Fin 5) := .seq splitPrefix (.seq columnLayer rowLayer)

theorem splitPrefix_output : prepared gate 0 3 2 splitPrefix = ![0,0,1,0,2] := by
  funext i
  fin_cases i <;> rfl

theorem rowsThenColumns_output :
    prepared gate 0 3 2 rowsThenColumns = ![1,0,0,0,2] := by
  funext i
  fin_cases i <;> rfl

theorem columnsThenRows_output :
    prepared gate 0 3 2 columnsThenRows = ![0,0,0,1,2] := by
  funext i
  fin_cases i <;> rfl

theorem prepared_network_readout_difference :
    finiteModelLaw.prob 2 rowsThenColumns 0 = 1/2 ∧
      finiteModelLaw.prob 2 columnsThenRows 0 = 0 := by
  change readout (prepared gate 0 3 2 rowsThenColumns 0) = 1/2 ∧
    readout (prepared gate 0 3 2 columnsThenRows 0) = 0
  rw [rowsThenColumns_output, columnsThenRows_output]
  norm_num [readout, weight]

end

end IDT.QMClosure.RawNetworkMedialWall
