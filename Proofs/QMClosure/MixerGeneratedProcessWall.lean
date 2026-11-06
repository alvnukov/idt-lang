import Proofs.QMClosure.OperationalQuadraticReconstruction
import Proofs.QMClosure.QuadraticRecordRefinement

namespace IDT.QMClosure.MixerGeneratedProcessWall

open QuadraticRecordRefinement
open scoped BigOperators

noncomputable section

/-!
# A finite normalized-mixer process wall

This is a conditional algebraic obstruction for the explicitly generated process
language below: normalized transparent additive roots of exchange, wire
permutations, identity, and finite composition. The coherent sum and the total
supplied quadratic readout are proved invariant from those generators.

The exact vacuum theorem needs no readout assumption. The readout theorem uses
the null ideal of a supplied positive quadratic readout; zero weight is not a
proof that an environment can physically be discarded. No scalar action,
Hilbert representation, topology, physical phase implementation, event
probability, or QM closure is derived. Fixed finite width is formalized.
Embedding arbitrary finite vacuum insertion/removal into a common width is an
interpretation of this scope, not a separately formalized variable-width syntax.

An original raw mixer with an additional decoration need not preserve coherent
sum (for example its negative), and is outside this normalized language.
Escaping this wall requires an independently justified process breaking coherent
sum modulo the null ideal, or a change of conditioning/nonlinear/infinite scope.
This does not establish impossibility of physical phase gates.
-/

variable {V ι : Type*} [AddCommGroup V] [Fintype ι] [DecidableEq ι]

def coherentSum (v : ι → V) : V := ∑ k, v k

def totalReadout (Q : V → ℝ) (v : ι → V) : ℝ := ∑ k, Q (v k)

/-- Literal replacement of two distinct coordinates using their old values. -/
def pairReplace (T : (V × V) →+ (V × V)) (i j : ι) (v : ι → V) : ι → V :=
  fun k => if k = i then (T (v i, v j)).1
    else if k = j then (T (v i, v j)).2 else v k

def pairGate (T : (V × V) →+ (V × V)) (i j : ι) : (ι → V) →+ (ι → V) where
  toFun := pairReplace T i j
  map_zero' := by
    have hz : T (0, 0) = 0 := T.map_zero
    ext k
    simp [pairReplace, hz]
  map_add' v w := by
    ext k
    simp only [pairReplace, Pi.add_apply]
    split_ifs <;> simp [← Prod.mk_add_mk, map_add]

private theorem sum_two {M : Type*} [AddCommMonoid M] (f : ι → M)
    (i j : ι) (hij : i ≠ j) :
    ∑ k, f k = f i + f j + ∑ k ∈ (Finset.univ.erase i).erase j, f k := by
  have hi := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  have hj := Finset.sum_erase_add (Finset.univ.erase i) f
    (show j ∈ Finset.univ.erase i by simp [Ne.symm hij])
  rw [← hi, ← hj]
  simp only [add_comm, add_left_comm]

private theorem sum_pairReplace {M : Type*} [AddCommMonoid M]
    (f : V → M) (T : (V × V) →+ (V × V))
    (i j : ι) (hij : i ≠ j) (v : ι → V) :
    ∑ k, f (pairReplace T i j v k) =
      f (T (v i, v j)).1 + f (T (v i, v j)).2 +
        ∑ k ∈ (Finset.univ.erase i).erase j, f (v k) := by
  rw [sum_two (fun k => f (pairReplace T i j v k)) i j hij]
  simp only [pairReplace, if_neg (Ne.symm hij)]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
  simp [hki, hkj]

/-- Transparency and square-swap derive the coherent-sum law for the gate. -/
theorem operation_preserves_sum (T : (V × V) →+ (V × V))
    (transparent : ∀ x, T (x, x) = (x, x))
    (square : ∀ p, T (T p) = p.swap) (x y : V) :
    (T (x, y)).1 + (T (x, y)).2 = x + y := by
  have hm := TransparentSwapRoot.operation_eq_symmetric_mixer T square
  have ht (z : V) : TransparentSwapRoot.portA T z +
      TransparentSwapRoot.portB T z = z := by
    have hz := congrArg Prod.fst (transparent z)
    rw [congrFun hm] at hz
    exact hz
  rw [congrFun hm]
  change (_ + _) + (_ + _) = x + y
  calc
    _ = (TransparentSwapRoot.portA T x + TransparentSwapRoot.portB T x) +
        (TransparentSwapRoot.portA T y + TransparentSwapRoot.portB T y) := by ac_rfl
    _ = x + y := by rw [ht, ht]

theorem pairGate_preserves_sum (T : (V × V) →+ (V × V))
    (hs : ∀ x y, (T (x, y)).1 + (T (x, y)).2 = x + y)
    (i j : ι) (hij : i ≠ j) (v : ι → V) :
    coherentSum (pairGate T i j v) = coherentSum v := by
  change (∑ k, pairReplace T i j v k) = ∑ k, v k
  rw [sum_pairReplace (fun x : V => x) T i j hij v, hs, sum_two v i j hij]

theorem pairGate_preserves_readout (T : (V × V) →+ (V × V)) (Q : V → ℝ)
    (hq : ∀ x y, Q (T (x, y)).1 + Q (T (x, y)).2 = Q x + Q y)
    (i j : ι) (hij : i ≠ j) (v : ι → V) :
    totalReadout Q (pairGate T i j v) = totalReadout Q v := by
  change (∑ k, Q (pairReplace T i j v k)) = ∑ k, Q (v k)
  rw [sum_pairReplace Q T i j hij v, hq, sum_two (fun k => Q (v k)) i j hij]

/-- Syntax contains actual generators, not arbitrary invariant-certified maps. -/
inductive Circuit (T : (V × V) →+ (V × V)) where
  | identity : Circuit T
  | pair (i j : ι) (distinct : i ≠ j) : Circuit T
  | permute (e : ι ≃ ι) : Circuit T
  | seq (first second : Circuit T) : Circuit T

def Circuit.eval {T : (V × V) →+ (V × V)} : Circuit (ι := ι) T →
    ((ι → V) →+ (ι → V))
  | .identity => AddMonoidHom.id _
  | .pair i j _ => pairGate T i j
  | .permute e =>
    { toFun := fun v k => v (e k)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  | .seq c d => d.eval.comp c.eval

theorem Circuit.preserves_sum {T : (V × V) →+ (V × V)}
    (c : Circuit (ι := ι) T)
    (transparent : ∀ x, T (x, x) = (x, x))
    (square : ∀ p, T (T p) = p.swap) (v : ι → V) :
    coherentSum (c.eval v) = coherentSum v := by
  induction c generalizing v with
  | identity => rfl
  | pair i j hij =>
      exact pairGate_preserves_sum T
        (operation_preserves_sum T transparent square) i j hij v
  | permute e => exact e.sum_comp v
  | seq c d hc hd => exact (hd (c.eval v)).trans (hc v)

theorem Circuit.preserves_readout {T : (V × V) →+ (V × V)}
    (c : Circuit (ι := ι) T) (Q : V → ℝ)
    (conserve : ∀ x y, Q (T (x, y)).1 + Q (T (x, y)).2 = Q x + Q y)
    (v : ι → V) : totalReadout Q (c.eval v) = totalReadout Q v := by
  induction c generalizing v with
  | identity => rfl
  | pair i j hij => exact pairGate_preserves_readout T Q conserve i j hij v
  | permute e => exact e.sum_comp (fun k => Q (v k))
  | seq c d hc hd => exact (hd (c.eval v)).trans (hc v)

def single (i : ι) (x : V) : ι → V := fun k => if k = i then x else 0

@[simp] theorem coherentSum_single (i : ι) (x : V) : coherentSum (single i x) = x := by
  simp [coherentSum, single]

@[simp] theorem totalReadout_single (Q : V → ℝ) (hzero : Q 0 = 0)
    (i : ι) (x : V) : totalReadout Q (single i x) = Q x := by
  simp [totalReadout, single, apply_ite Q, hzero]

/-- Exact vacuum output forces exact identity between the occupied ports. -/
theorem exact_vacuum_identity {T : (V × V) →+ (V × V)}
    (c : Circuit (ι := ι) T)
    (transparent : ∀ x, T (x, x) = (x, x))
    (square : ∀ p, T (T p) = p.swap) (i o : ι) (x y : V)
    (output : c.eval (single i x) = single o y) : y = x := by
  have hs := c.preserves_sum transparent square (single i x)
  rw [output, coherentSum_single, coherentSum_single] at hs
  exact hs

theorem exact_vacuum_phase_forces_zero {T : (V × V) →+ (V × V)}
    (c : Circuit (ι := ι) T)
    (transparent : ∀ x, T (x, x) = (x, x))
    (square : ∀ p, T (T p) = p.swap)
    (J h : V →+ V) (quarter : ∀ x, J (J x) = -x)
    (halves : ∀ x, h x + h x = x) (i o : ι) (x : V)
    (output : c.eval (single i x) = single o (J x)) : x = 0 := by
  have hx := exact_vacuum_identity c transparent square i o x (J x) output
  have hj := congrArg J hx
  rw [quarter, hx] at hj
  apply PhaseMixerCancellation.doubling_injective h halves
  simpa only [zero_add] using (show x + x = 0 from by
    calc
      x + x = -x + x := congrArg (fun z => z + x) hj.symm
      _ = 0 := neg_add_cancel x)

/-- The actual normalized operation supplies the phase and genuine half needed
for the exact theorem. In particular this conclusion needs no readout. -/
theorem reconstructed_exact_phase_forces_zero {T : (V × V) →+ (V × V)}
    (c : Circuit (ι := ι) T)
    (transparent : ∀ x, T (x, x) = (x, x))
    (square : ∀ p, T (T p) = p.swap) (i o : ι) (x : V)
    (output : c.eval (single i x) =
      single o (OperationalQuadraticReconstruction.phase T x)) : x = 0 := by
  let r := (TransparentSwapRoot.reconstruct_operation T transparent square).1
  have anti (y : V) : OperationalQuadraticReconstruction.phase T
      (OperationalQuadraticReconstruction.phase T y) = -y :=
    add_left_cancel ((r.cancellation y).trans (add_neg_cancel y).symm)
  exact exact_vacuum_phase_forces_zero c transparent square
    (OperationalQuadraticReconstruction.phase T) (OperationalQuadraticReconstruction.half T)
    anti r.halves i o x output

omit [Fintype ι] in
private theorem sum_null (Q : V → ℝ) (hq : PositiveQuadratic Q)
    (s : Finset ι) (v : ι → V) (hv : ∀ k ∈ s, Q (v k) = 0) :
    Q (∑ k ∈ s, v k) = 0 := by
  induction s using Finset.induction_on with
  | empty => simpa using hq.zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, add_comm,
      hq.null_translate _ _ (hv a (Finset.mem_insert_self a s))]
    exact ih (fun k hk => hv k (Finset.mem_insert_of_mem hk))

/-- Lossless retained weight forces every other output into the null ideal. -/
theorem lossless_other_outputs_null {Q : V → ℝ} (hq : PositiveQuadratic Q)
    (v : ι → V) (o : ι) (x : V)
    (conserve : totalReadout Q v = Q x) (lossless : Q (v o) = Q x) :
    ∀ k, k ≠ o → Q (v k) = 0 := by
  have hs := Finset.sum_erase_add Finset.univ (fun k => Q (v k))
    (Finset.mem_univ o)
  have hz : ∑ k ∈ Finset.univ.erase o, Q (v k) = 0 := by
    change totalReadout Q v = Q x at conserve
    change _ + Q (v o) = totalReadout Q v at hs
    linarith
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k (_ : k ∈ Finset.univ.erase o) => hq.nonnegative (v k))).mp hz
  intro k hk
  exact hall k (by simp [hk])

/-- A generated lossless one-port process is identity modulo the null ideal. -/
theorem lossless_identity_mod_null {T : (V × V) →+ (V × V)}
    (c : Circuit (ι := ι) T)
    (transparent : ∀ x, T (x, x) = (x, x))
    (square : ∀ p, T (T p) = p.swap)
    (Q : V → ℝ) (hq : PositiveQuadratic Q)
    (conserve : ∀ x y, Q (T (x, y)).1 + Q (T (x, y)).2 = Q x + Q y)
    (i o : ι) (x : V) (lossless : Q (c.eval (single i x) o) = Q x) :
    Q (x - c.eval (single i x) o) = 0 := by
  let v := c.eval (single i x)
  have hc : totalReadout Q v = Q x := by
    rw [show v = c.eval (single i x) from rfl, c.preserves_readout Q conserve,
      totalReadout_single Q hq.zero]
  have hn := lossless_other_outputs_null hq v o x hc lossless
  have hs := c.preserves_sum transparent square (single i x)
  rw [coherentSum_single] at hs
  have he := Finset.sum_erase_add Finset.univ v (Finset.mem_univ o)
  have heq : x - v o = ∑ k ∈ Finset.univ.erase o, v k := by
    change coherentSum v = x at hs
    change _ + v o = coherentSum v at he
    rw [hs] at he
    rw [← he]
    abel
  rw [show c.eval (single i x) o = v o from rfl, heq]
  exact sum_null Q hq _ v (fun k hk => hn k (Finset.mem_erase.mp hk).1)

theorem phase_difference_weight (Q : V → ℝ) (hq : PositiveQuadratic Q)
    (J : V →+ V) (invariant : ∀ x, Q (J x) = Q x)
    (mixed : ∀ x, Q (x + J x) = 2 * Q x) (x : V) :
    Q (x - J x) = 2 * Q x := by
  have hp := hq.parallelogram x (J x)
  rw [invariant, mixed] at hp
  linarith

/-- A phase-preserving retained weight cannot be a nonnull phase process in
this language, even when the other output vectors are not literally zero. -/
theorem retained_phase_requires_null {T : (V × V) →+ (V × V)}
    (c : Circuit (ι := ι) T)
    (transparent : ∀ x, T (x, x) = (x, x))
    (square : ∀ p, T (T p) = p.swap)
    (Q : V → ℝ) (hq : PositiveQuadratic Q)
    (conserve : ∀ x y, Q (T (x, y)).1 + Q (T (x, y)).2 = Q x + Q y)
    (J : V →+ V) (invariant : ∀ x, Q (J x) = Q x)
    (mixed : ∀ x, Q (x + J x) = 2 * Q x)
    (i o : ι) (x : V) (output : c.eval (single i x) o = J x) : Q x = 0 := by
  have hn := lossless_identity_mod_null c transparent square Q hq conserve i o x
    (by rw [output, invariant])
  rw [output, phase_difference_weight Q hq J invariant mixed] at hn
  linarith

/-- A fixed input reference is insufficient for an exact phase map correct at
both x and zero: subtracting the two additive evolutions removes that reference.
No returned-reference or unconsumed-reference assumption is needed. -/
theorem fixed_reference_phase_requires_null {T : (V × V) →+ (V × V)}
    (c : Circuit (ι := ι) T)
    (transparent : ∀ x, T (x, x) = (x, x))
    (square : ∀ p, T (T p) = p.swap)
    (Q : V → ℝ) (hq : PositiveQuadratic Q)
    (conserve : ∀ x y, Q (T (x, y)).1 + Q (T (x, y)).2 = Q x + Q y)
    (J : V →+ V) (invariant : ∀ x, Q (J x) = Q x)
    (mixed : ∀ x, Q (x + J x) = 2 * Q x)
    (i o : ι) (x : V) (r : ι → V)
    (at_zero : c.eval r o = 0)
    (at_x : c.eval (single i x + r) o = J x) : Q x = 0 := by
  apply retained_phase_requires_null c transparent square Q hq conserve J invariant mixed i o x
  have ha := congrFun (c.eval.map_add (single i x) r) o
  change c.eval (single i x + r) o = c.eval (single i x) o + c.eval r o at ha
  rw [at_x, at_zero, add_zero] at ha
  exact ha.symm

/-- Isolated zero-reference weights coincide, but the coherent reference -Jx
distinguishes x and Jx whenever Qx is positive. Availability is not derived. -/
theorem coherent_reference_test (Q : V → ℝ) (hq : PositiveQuadratic Q)
    (J : V →+ V) (invariant : ∀ x, Q (J x) = Q x)
    (mixed : ∀ x, Q (x + J x) = 2 * Q x) (x : V) :
    Q (x + -J x) = 2 * Q x ∧ Q (J x + -J x) = 0 := by
  constructor
  · simpa only [sub_eq_add_neg] using phase_difference_weight Q hq J invariant mixed x
  · simpa using hq.zero

/-- The preceding obstruction applies to the operation's reconstructed phase;
its positive quadratic and phase geometry are derived by the existing checked
operational theorem, rather than supplied as a physical phase-gate primitive. -/
theorem reconstructed_phase_requires_null {T : (V × V) →+ (V × V)}
    (c : Circuit (ι := ι) T)
    (transparent : ∀ x, T (x, x) = (x, x))
    (square : ∀ p, T (T p) = p.swap)
    (Q : V → ℝ) (vacuum : Q 0 = 0) (positive : ∀ x, 0 ≤ Q x)
    (conserve : ∀ x y, Q (T (x, y)).1 + Q (T (x, y)).2 = Q x + Q y)
    (i o : ι) (x : V)
    (output : c.eval (single i x) o = OperationalQuadraticReconstruction.phase T x) :
    Q x = 0 := by
  let r := OperationalQuadraticReconstruction.reconstruct_positive_operation
    T transparent square Q vacuum positive conserve
  have anti (y : V) : OperationalQuadraticReconstruction.phase T
      (OperationalQuadraticReconstruction.phase T y) = -y :=
    add_left_cancel ((r.antipodes y).trans (add_neg_cancel y).symm)
  have hq : PositiveQuadratic Q := by
    refine ⟨positive, ?_⟩
    intro u v
    simpa only [anti, ← sub_eq_add_neg] using r.parallelogram u v
  exact retained_phase_requires_null c transparent square Q hq conserve
    (OperationalQuadraticReconstruction.phase T) r.phase_invariant r.mixed_square i o x output

/-- Positive control: selecting the A branch twice produces a quarter-weight
phase refinement. This is an algebraic branch weight, not an event probability
or a derived postselection operation; the whole circuit has other outputs. -/
theorem selected_two_A_branch (T : (V × V) →+ (V × V))
    (transparent : ∀ x, T (x, x) = (x, x))
    (square : ∀ p, T (T p) = p.swap)
    (Q : V → ℝ) (vacuum : Q 0 = 0) (positive : ∀ x, 0 ≤ Q x)
    (conserve : ∀ x y, Q (T (x, y)).1 + Q (T (x, y)).2 = Q x + Q y)
    (x : V) :
    TransparentSwapRoot.portA T (TransparentSwapRoot.portA T x) =
        OperationalQuadraticReconstruction.half T
          (OperationalQuadraticReconstruction.phase T x) ∧
      Q (TransparentSwapRoot.portA T (TransparentSwapRoot.portA T x)) = Q x / 4 := by
  let r := OperationalQuadraticReconstruction.reconstruct_positive_operation
    T transparent square Q vacuum positive conserve
  have branch : TransparentSwapRoot.portA T (TransparentSwapRoot.portA T x) =
      OperationalQuadraticReconstruction.half T
        (OperationalQuadraticReconstruction.phase T x) := by
    exact (PhaseMixerCancellation.refinement_of_double
      (OperationalQuadraticReconstruction.half T) r.halves
        (TransparentSwapRoot.portA T (TransparentSwapRoot.portA T x))).symm
  refine ⟨branch, ?_⟩
  rw [branch, r.half_scaling, r.phase_invariant]

end
end IDT.QMClosure.MixerGeneratedProcessWall
