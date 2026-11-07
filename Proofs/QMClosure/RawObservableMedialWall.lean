import Proofs.QMClosure.RawNetworkMedialWall
import Proofs.QMClosure.OperationalContextQuotient
import Proofs.QMClosure.NativeAttenuationCircuit

/-!
# Named observations do not force literal raw mediality

The existing native complex mixer is paired with the existing nonmedial finite
gate. Squared-norm readout sees the complex coordinate only. The product has
square-swap, transparency, balanced vacuum readouts, conservation, and all six
literal raw probability fields. Its observed laws inhabit the existing
OperationalContextQuotient.ObservedData, while its raw operation is nonmedial.

An actual five-wire single-source preparation gives two distinct raw arrays
with identical visible coordinates. Every subsequent named circuit and every
existing one-hole context has the same readout. The arbitrary references in
that grammar separate visible complex coordinates, not the finite coordinate.

The visible law witnesses existence, not uniqueness among raw probability
assignments. The finite coordinate supplies another conserved readout and an
all-six-field law that distinguishes these prepared states. Thus literal raw
probability consistency alone does not imply descent through the supplied
visible observational quotient.

This is a supplied mathematical countermodel. It neither asserts completeness
of physical contexts nor rejects mediality of an operational quotient. No
topological or scalar-homogeneity property of this raw product is asserted.
-/

namespace IDT.QMClosure.RawObservableMedialWall

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open MedialSwapRoot MixerGeneratedProcessWall NativeVacuumProbabilityFamily
open WeightFreeRawProbability (evalRaw)
open OperationalContextQuotient
open RawNetworkMedialWall (Quad rows columns FirstChannelMedial)
open scoped BigOperators

attribute [local simp] Fin.ext_iff Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

/-! ## Immediate conservation and the additional after-analyzer equation -/

def rowReadout {V : Type*} (Q : V → ℝ) (x : Quad V) : ℝ :=
  Q x.1.1 + Q x.1.2

theorem rowReadout_rows {V : Type*} (F : V × V → V × V) (Q : V → ℝ)
    (conserved : ∀ x y, Q (F (x,y)).1 + Q (F (x,y)).2 = Q x + Q y)
    (x : Quad V) : rowReadout Q (rows F x) = rowReadout Q x :=
  conserved x.1.1 x.1.2

/-- This merely isolates the extra equation; it is not a physical locality law. -/
theorem row_order_eq_iff_after_analyzer {V : Type*}
    (F : V × V → V × V) (Q : V → ℝ)
    (conserved : ∀ x y, Q (F (x,y)).1 + Q (F (x,y)).2 = Q x + Q y)
    (x : Quad V) :
    rowReadout Q (columns F (rows F x)) = rowReadout Q (rows F (columns F x)) ↔
      rowReadout Q (columns F (rows F x)) = rowReadout Q (columns F x) := by
  rw [rowReadout_rows F Q conserved]

/-! ## A generic projection theorem for the literal named evaluator -/

theorem evalRaw_project {V W : Type*} {ι : Type} [DecidableEq ι]
    (F : V × V → V × V) (G : W × W → W × W) (π : V → W)
    (projects : ∀ x y, (π (F (x,y)).1, π (F (x,y)).2) = G (π x, π y))
    (c : Native ι) (x : ι → V) :
    (fun i => π (evalRaw F c x i)) = evalRaw G c (fun i => π (x i)) := by
  induction c generalizing x with
  | identity => rfl
  | pair i j hij =>
    funext l
    by_cases hi : l = i
    · subst l
      simpa only [evalRaw, if_pos rfl] using congrArg Prod.fst (projects (x i) (x j))
    · by_cases hj : l = j
      · subst l
        simpa only [evalRaw, if_neg hi, if_pos rfl] using
          congrArg Prod.snd (projects (x i) (x j))
      · simp only [evalRaw, if_neg hi, if_neg hj]
  | permute e => rfl
  | seq c e hc he =>
    change (fun i => π (evalRaw F e (evalRaw F c x) i)) =
      evalRaw G e (evalRaw G c (fun i => π (x i)))
    rw [he, hc]

theorem prepared_project {V W : Type*} {ι : Type} [DecidableEq ι]
    (F : V × V → V × V) (G : W × W → W × W) (π : V → W)
    (projects : ∀ x y, (π (F (x,y)).1, π (F (x,y)).2) = G (π x, π y))
    (zero reference : V) (s : ι) (c : Native ι) :
    (fun i => π (RawNetworkMedialWall.prepared F zero reference s c i)) =
      RawNetworkMedialWall.prepared G (π zero) (π reference) s c := by
  unfold RawNetworkMedialWall.prepared
  rw [evalRaw_project F G π projects]
  congr 1
  funext i
  by_cases hi : i = s <;> simp [RawNetworkMedialWall.rawSource, hi]

/-! ## The visible-native / hidden-finite product -/

abbrev State := ℂ × RawNetworkMedialWall.State

def zero : State := (0, 0)
def reference : State := (1, 3)
def visible (x : State) : ℂ := x.1
def hidden (x : State) : RawNetworkMedialWall.State := x.2
def readout (x : State) : ℝ := Complex.normSq (visible x)

def gate (p : State × State) : State × State :=
  (((NativeMixerEventConeExclusion.mixer (p.1.1, p.2.1)).1,
      (RawNetworkMedialWall.gate (p.1.2, p.2.2)).1),
    ((NativeMixerEventConeExclusion.mixer (p.1.1, p.2.1)).2,
      (RawNetworkMedialWall.gate (p.1.2, p.2.2)).2))

theorem visible_gate (x y : State) :
    (visible (gate (x,y)).1, visible (gate (x,y)).2) =
      NativeMixerEventConeExclusion.mixer (visible x, visible y) := rfl

theorem hidden_gate (x y : State) :
    (hidden (gate (x,y)).1, hidden (gate (x,y)).2) =
      RawNetworkMedialWall.gate (hidden x, hidden y) := rfl

theorem gate_square (p : State × State) : gate (gate p) = p.swap := by
  have hv := NativeMixerEventConeExclusion.mixer_square (p.1.1, p.2.1)
  have hh := RawNetworkMedialWall.gate_square (p.1.2, p.2.2)
  change (((NativeMixerEventConeExclusion.mixer
      (NativeMixerEventConeExclusion.mixer (p.1.1,p.2.1))).1,
      (RawNetworkMedialWall.gate (RawNetworkMedialWall.gate (p.1.2,p.2.2))).1),
    ((NativeMixerEventConeExclusion.mixer
      (NativeMixerEventConeExclusion.mixer (p.1.1,p.2.1))).2,
      (RawNetworkMedialWall.gate (RawNetworkMedialWall.gate (p.1.2,p.2.2))).2)) =
    ((p.2.1,p.2.2),(p.1.1,p.1.2))
  rw [hv, hh]
  rfl

theorem gate_transparent (x : State) : gate (x,x) = (x,x) := by
  have hv := NativeMixerEventConeExclusion.mixer_transparent x.1
  have hh := RawNetworkMedialWall.gate_transparent x.2
  change (((NativeMixerEventConeExclusion.mixer (x.1,x.1)).1,
      (RawNetworkMedialWall.gate (x.2,x.2)).1),
    ((NativeMixerEventConeExclusion.mixer (x.1,x.1)).2,
      (RawNetworkMedialWall.gate (x.2,x.2)).2)) = ((x.1,x.2),(x.1,x.2))
  rw [hv, hh]

theorem readout_conserved (x y : State) :
    readout (gate (x,y)).1 + readout (gate (x,y)).2 = readout x + readout y :=
  NativeMixerEventConeExclusion.mixer_conserves x.1 y.1

theorem all_vacuum_readouts_balanced (x : State) :
    readout (gate (x,zero)).1 = readout x / 2 ∧
      readout (gate (x,zero)).2 = readout x / 2 := by
  constructor
  · change Complex.normSq (NativeMixerEventConeExclusion.mixer (x.1,0)).1 =
      Complex.normSq x.1 / 2
    rw [NativeAttenuationCircuit.mixer_fst]
    simp only [mul_zero, add_zero, Complex.normSq_mul]
    norm_num [NativeAttenuationCircuit.a, Complex.normSq_apply,
      Complex.div_re, Complex.div_im]
    ring
  · change Complex.normSq (NativeMixerEventConeExclusion.mixer (x.1,0)).2 =
      Complex.normSq x.1 / 2
    rw [NativeAttenuationCircuit.mixer_snd]
    simp only [mul_zero, add_zero, Complex.normSq_mul]
    norm_num [NativeAttenuationCircuit.b, Complex.normSq_apply,
      Complex.div_re, Complex.div_im]
    ring

def rawLaw : RawNetworkMedialWall.RawSemanticsLaw gate zero reference :=
  RawNetworkMedialWall.readoutLaw gate zero reference readout
    (by norm_num [readout, visible, zero])
    (by norm_num [readout, visible, reference])
    (fun x => Complex.normSq_nonneg (visible x)) readout_conserved

/-- A different readout of the same raw operation; it is not the weight of
the visible ObservedData below. -/
def hiddenReadout (x : State) : ℝ := RawNetworkMedialWall.readout (hidden x)

theorem hiddenReadout_conserved (x y : State) :
    hiddenReadout (gate (x,y)).1 + hiddenReadout (gate (x,y)).2 =
      hiddenReadout x + hiddenReadout y :=
  RawNetworkMedialWall.readout_conserved x.2 y.2

def hiddenLaw : RawNetworkMedialWall.RawSemanticsLaw gate zero reference :=
  RawNetworkMedialWall.readoutLaw gate zero reference hiddenReadout
    (by norm_num [hiddenReadout, hidden, zero,
      RawNetworkMedialWall.readout, RawNetworkMedialWall.weight])
    (by norm_num [hiddenReadout, hidden, reference,
      RawNetworkMedialWall.readout, RawNetworkMedialWall.weight])
    (fun x => div_nonneg (Nat.cast_nonneg _) (by norm_num)) hiddenReadout_conserved

theorem visible_eval {ι : Type} [DecidableEq ι] (c : Native ι) (x : ι → State) :
    (fun i => visible (evalRaw gate c x i)) =
      evalRaw NativeMixerEventConeExclusion.mixer c (fun i => visible (x i)) :=
  evalRaw_project gate NativeMixerEventConeExclusion.mixer visible visible_gate c x

theorem hidden_eval {ι : Type} [DecidableEq ι] (c : Native ι) (x : ι → State) :
    (fun i => hidden (evalRaw gate c x i)) =
      evalRaw RawNetworkMedialWall.gate c (fun i => hidden (x i)) :=
  evalRaw_project gate RawNetworkMedialWall.gate hidden hidden_gate c x

/-- This supplied law is native on every named word. This is not a uniqueness
statement about other members of RawSemanticsLaw for the same raw operation. -/
theorem rawLaw_native_readout {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) (i : ι) :
    rawLaw.prob s c i = Complex.normSq
      (RawNetworkMedialWall.prepared NativeMixerEventConeExclusion.mixer 0 1 s c i) := by
  change Complex.normSq (visible (RawNetworkMedialWall.prepared gate zero reference s c i)) = _
  exact congrArg Complex.normSq (congrFun
    (prepared_project gate NativeMixerEventConeExclusion.mixer visible visible_gate
      zero reference s c) i)

theorem native_medial : FirstChannelMedial NativeMixerEventConeExclusion.mixer := by
  intro a b c d
  simp only [firstChannel, NativeAttenuationCircuit.mixer_fst]
  ring

theorem gate_not_medial : ¬ FirstChannelMedial gate := by
  intro h
  apply RawNetworkMedialWall.gate_not_medial
  intro a b c d
  have hh := congrArg hidden (h (0,a) (0,b) (0,c) (0,d))
  simpa only [hidden, firstChannel, gate] using hh

/-! ## The already-defined copying-free observational quotient -/

theorem observationalEq_of_visible_eq {x y : State} (h : visible x = visible y) :
    ObservationalEq gate readout x y := by
  apply relation_le_observationalEq gate readout
    (fun a b => visible a = visible b) _ _ _ h
  · intro a b hab
    exact congrArg Complex.normSq hab
  · intro s a b r hab
    cases s <;> simp only [select, gate, visible] at hab ⊢ <;> rw [hab]
  · intro s a b r hab
    cases s <;> simp only [select, gate, visible] at hab ⊢ <;> rw [hab]

theorem native_reference_one_readout (z : ℂ) :
    Complex.normSq (NativeMixerEventConeExclusion.mixer (z,1)).1 =
      (Complex.normSq z + 1) / 2 - z.im := by
  rw [NativeAttenuationCircuit.mixer_fst]
  norm_num [NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
    Complex.normSq_apply, Complex.div_re, Complex.div_im]
  ring

theorem native_reference_I_readout (z : ℂ) :
    Complex.normSq (NativeMixerEventConeExclusion.mixer (z,Complex.I)).1 =
      (Complex.normSq z + 1) / 2 + z.re := by
  rw [NativeAttenuationCircuit.mixer_fst]
  norm_num [NativeAttenuationCircuit.a, NativeAttenuationCircuit.b,
    Complex.normSq_apply, Complex.div_re, Complex.div_im]
  ring

/-- These are tests in the existing arbitrary-reference grammar, not a claim
that these references exhaust or are available among physical controls. -/
theorem visible_eq_of_observationalEq {x y : State}
    (h : ObservationalEq gate readout x y) : visible x = visible y := by
  have h0 := weight_eq h
  have h1 := h (.left .first .hole (1,0))
  have hI := h (.left .first .hole (Complex.I,0))
  change Complex.normSq (NativeMixerEventConeExclusion.mixer (x.1,1)).1 =
    Complex.normSq (NativeMixerEventConeExclusion.mixer (y.1,1)).1 at h1
  change Complex.normSq (NativeMixerEventConeExclusion.mixer (x.1,Complex.I)).1 =
    Complex.normSq (NativeMixerEventConeExclusion.mixer (y.1,Complex.I)).1 at hI
  change Complex.normSq x.1 = Complex.normSq y.1 at h0
  rw [native_reference_one_readout, native_reference_one_readout] at h1
  rw [native_reference_I_readout, native_reference_I_readout] at hI
  apply Complex.ext <;> dsimp [visible] <;> linarith

theorem observationalEq_iff_visible_eq (x y : State) :
    ObservationalEq gate readout x y ↔ visible x = visible y :=
  ⟨visible_eq_of_observationalEq, observationalEq_of_visible_eq⟩

def observedData : ObservedData State where
  chosenZero := zero
  operation := gate
  weight := readout
  vacuum := by norm_num [readout, visible, zero]
  nonnegative x := Complex.normSq_nonneg (visible x)
  conserved := readout_conserved
  square p := by
    constructor
    · apply observationalEq_of_visible_eq
      rw [gate_square]
      rfl
    · apply observationalEq_of_visible_eq
      rw [gate_square]
      rfl
  medial a b c d := by
    apply observationalEq_of_visible_eq
    simpa only [visible, firstChannel, gate] using native_medial a.1 b.1 c.1 d.1

/-! ## Universal projected interchange and the weaker marginal equation -/

def visibleQuad (x : Quad State) : Quad ℂ :=
  ((visible x.1.1, visible x.1.2), (visible x.2.1, visible x.2.2))

theorem visibleQuad_rows (x : Quad State) :
    visibleQuad (rows gate x) = rows NativeMixerEventConeExclusion.mixer (visibleQuad x) := rfl

theorem visibleQuad_columns (x : Quad State) :
    visibleQuad (columns gate x) = columns NativeMixerEventConeExclusion.mixer (visibleQuad x) := rfl

theorem visible_row_column_equal (x : Quad State) :
    visibleQuad (columns gate (rows gate x)) = visibleQuad (rows gate (columns gate x)) := by
  rw [visibleQuad_columns, visibleQuad_rows, visibleQuad_rows, visibleQuad_columns]
  exact RawNetworkMedialWall.rowColumnCommutes_of_medial
    NativeMixerEventConeExclusion.mixer NativeMixerEventConeExclusion.mixer_square native_medial
    (visibleQuad x)

theorem row_order_readout_equal (x : Quad State) :
    rowReadout readout (columns gate (rows gate x)) =
      rowReadout readout (rows gate (columns gate x)) :=
  congrArg (rowReadout Complex.normSq) (visible_row_column_equal x)

theorem after_analyzer_readout_invariant (x : Quad State) :
    rowReadout readout (columns gate (rows gate x)) = rowReadout readout (columns gate x) :=
  (row_order_eq_iff_after_analyzer gate readout readout_conserved x).mp (row_order_readout_equal x)

/-! ## Actual single-source prepared states, without variable duplication -/

def leftState : Fin 5 → State :=
  RawNetworkMedialWall.prepared gate zero reference 2 RawNetworkMedialWall.rowsThenColumns

def rightState : Fin 5 → State :=
  RawNetworkMedialWall.prepared gate zero reference 2 RawNetworkMedialWall.columnsThenRows

theorem leftState_hidden : (fun i => hidden (leftState i)) = ![1,0,0,0,2] := by
  change (fun i => hidden (RawNetworkMedialWall.prepared gate zero reference 2
    RawNetworkMedialWall.rowsThenColumns i)) = _
  rw [prepared_project gate RawNetworkMedialWall.gate hidden hidden_gate]
  exact RawNetworkMedialWall.rowsThenColumns_output

theorem rightState_hidden : (fun i => hidden (rightState i)) = ![0,0,0,1,2] := by
  change (fun i => hidden (RawNetworkMedialWall.prepared gate zero reference 2
    RawNetworkMedialWall.columnsThenRows i)) = _
  rw [prepared_project gate RawNetworkMedialWall.gate hidden hidden_gate]
  exact RawNetworkMedialWall.columnsThenRows_output

def commonVisible : Fin 5 → ℂ :=
  ![(1+Complex.I)/4, (1-Complex.I)/4, (-1+Complex.I)/4,
    (1+Complex.I)/4, (1-Complex.I)/2]

theorem leftState_visible : (fun i => visible (leftState i)) = commonVisible := by
  change (fun i => visible (RawNetworkMedialWall.prepared gate zero reference 2
    RawNetworkMedialWall.rowsThenColumns i)) = _
  rw [prepared_project gate NativeMixerEventConeExclusion.mixer visible visible_gate]
  funext i
  fin_cases i <;> apply Complex.ext <;>
    norm_num [RawNetworkMedialWall.prepared, RawNetworkMedialWall.rawSource,
      RawNetworkMedialWall.rowsThenColumns, RawNetworkMedialWall.splitPrefix,
      RawNetworkMedialWall.rowLayer, RawNetworkMedialWall.columnLayer, evalRaw,
      visible, zero, reference, commonVisible, NativeAttenuationCircuit.mixer_fst,
      NativeAttenuationCircuit.mixer_snd, NativeAttenuationCircuit.a,
      NativeAttenuationCircuit.b, Complex.div_re, Complex.div_im]

theorem rightState_visible : (fun i => visible (rightState i)) = commonVisible := by
  change (fun i => visible (RawNetworkMedialWall.prepared gate zero reference 2
    RawNetworkMedialWall.columnsThenRows i)) = _
  rw [prepared_project gate NativeMixerEventConeExclusion.mixer visible visible_gate]
  funext i
  fin_cases i <;> apply Complex.ext <;>
    norm_num [RawNetworkMedialWall.prepared, RawNetworkMedialWall.rawSource,
      RawNetworkMedialWall.columnsThenRows, RawNetworkMedialWall.splitPrefix,
      RawNetworkMedialWall.rowLayer, RawNetworkMedialWall.columnLayer, evalRaw,
      visible, zero, reference, commonVisible, NativeAttenuationCircuit.mixer_fst,
      NativeAttenuationCircuit.mixer_snd, NativeAttenuationCircuit.a,
      NativeAttenuationCircuit.b, Complex.div_re, Complex.div_im]

theorem prepared_visible_equal :
    (fun i => visible (leftState i)) = (fun i => visible (rightState i)) :=
  leftState_visible.trans rightState_visible.symm

theorem prepared_raw_ne : leftState ≠ rightState := by
  intro h
  have hl := congrFun leftState_hidden 0
  have hr := congrFun rightState_hidden 0
  have he := congrArg (fun x : Fin 5 → State => hidden (x 0)) h
  change hidden (leftState 0) = hidden (rightState 0) at he
  rw [hl, hr] at he
  norm_num at he

theorem commonVisible_readout :
    (fun i => Complex.normSq (commonVisible i)) = (![1/8,1/8,1/8,1/8,1/2] : Fin 5 → ℝ) := by
  funext i
  fin_cases i <;> norm_num [commonVisible, Complex.normSq_apply, Complex.div_re, Complex.div_im]

theorem prepared_readouts :
    (fun i => readout (leftState i)) = ![1/8,1/8,1/8,1/8,1/2] ∧
      (fun i => readout (rightState i)) = ![1/8,1/8,1/8,1/8,1/2] := by
  constructor
  · change (fun i => Complex.normSq (visible (leftState i))) = _
    simpa only [← leftState_visible] using commonVisible_readout
  · change (fun i => Complex.normSq (visible (rightState i))) = _
    simpa only [← rightState_visible] using commonVisible_readout

theorem prepared_pointwise_observationalEq (i : Fin 5) :
    ObservationalEq gate readout (leftState i) (rightState i) :=
  observationalEq_of_visible_eq (congrFun prepared_visible_equal i)

theorem downstream_visible_equal (c : Native (Fin 5)) :
    (fun i => visible (evalRaw gate c leftState i)) =
      (fun i => visible (evalRaw gate c rightState i)) := by
  rw [visible_eval, visible_eval, prepared_visible_equal]

theorem downstream_readout_equal (c : Native (Fin 5)) :
    (fun i => readout (evalRaw gate c leftState i)) =
      (fun i => readout (evalRaw gate c rightState i)) := by
  funext i
  exact congrArg Complex.normSq (congrFun (downstream_visible_equal c) i)

/-- Fresh spectator wires begin at the declared raw zero. The following word
may subsequently couple them to the original five wires. -/
theorem padded_downstream_visible_equal {κ : Type} [DecidableEq κ]
    (c : Native (Fin 5 ⊕ κ)) :
    (fun i => visible (evalRaw gate c (RawNetworkMedialWall.padRaw zero leftState) i)) =
      (fun i => visible (evalRaw gate c (RawNetworkMedialWall.padRaw zero rightState) i)) := by
  rw [visible_eval, visible_eval]
  congr 1
  funext i
  cases i with
  | inl j => exact congrFun prepared_visible_equal j
  | inr j => rfl

theorem padded_downstream_readout_equal {κ : Type} [DecidableEq κ]
    (c : Native (Fin 5 ⊕ κ)) :
    (fun i => readout (evalRaw gate c (RawNetworkMedialWall.padRaw zero leftState) i)) =
      (fun i => readout (evalRaw gate c (RawNetworkMedialWall.padRaw zero rightState) i)) := by
  funext i
  exact congrArg Complex.normSq (congrFun (padded_downstream_visible_equal c) i)

theorem padded_downstream_observationalEq {κ : Type} [DecidableEq κ]
    (c : Native (Fin 5 ⊕ κ)) (i : Fin 5 ⊕ κ) :
    ObservationalEq gate readout
      (evalRaw gate c (RawNetworkMedialWall.padRaw zero leftState) i)
      (evalRaw gate c (RawNetworkMedialWall.padRaw zero rightState) i) :=
  observationalEq_of_visible_eq (congrFun (padded_downstream_visible_equal c) i)

/-! ## Literal raw probability laws need not descend to this observed quotient -/

theorem hiddenLaw_network_probabilities :
    hiddenLaw.prob 2 RawNetworkMedialWall.rowsThenColumns 0 = 1/2 ∧
      hiddenLaw.prob 2 RawNetworkMedialWall.columnsThenRows 0 = 0 := by
  constructor
  · change RawNetworkMedialWall.readout (hidden (leftState 0)) = 1/2
    rw [congrFun leftState_hidden 0]
    norm_num [RawNetworkMedialWall.readout, RawNetworkMedialWall.weight]
  · change RawNetworkMedialWall.readout (hidden (rightState 0)) = 0
    rw [congrFun rightState_hidden 0]
    norm_num [RawNetworkMedialWall.readout, RawNetworkMedialWall.weight]

/-- The six fields require equality on literally equal prepared arrays. They
do not require equality on arrays identified by the separately supplied Q. -/
theorem hiddenLaw_not_observationally_extensional :
    ¬ (∀ c e : Native (Fin 5),
      (∀ i, ObservationalEq gate readout
        (RawNetworkMedialWall.prepared gate zero reference 2 c i)
        (RawNetworkMedialWall.prepared gate zero reference 2 e i)) →
      hiddenLaw.prob 2 c = hiddenLaw.prob 2 e) := by
  intro h
  have he := h RawNetworkMedialWall.rowsThenColumns RawNetworkMedialWall.columnsThenRows
    prepared_pointwise_observationalEq
  have hp := congrFun he 0
  rw [hiddenLaw_network_probabilities.1, hiddenLaw_network_probabilities.2] at hp
  norm_num at hp

end

end IDT.QMClosure.RawObservableMedialWall
