import Proofs.QMClosure.RationalCountOrderReadout
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Reversible echo and raw accounting boundaries

These controls use the supplied rational Gaussian algebra. Actual inverse
return, conjugate-return reciprocity and same-scale exhaustive raw accounting
are distinct contracts. Context normalization of detector values supplies no
raw scale. The quartic family is already present in NormalizedEchoReadoutControls;
the controls here add explicit reversible operations and their return tests.
No physical bridge or all-input weight conservation is derived.
-/

namespace IDT.QMClosure.ReversibleEchoAccountingBoundary

open RationalEchoRegularityControl RationalCountOrderReadout

noncomputable section

def absWeight (z : Carrier) : ℝ := Real.sqrt (normQ z : ℝ)

theorem absWeight_scalar_nonneg (q : ℚ) (hq : 0 ≤ q) :
    absWeight (scalar q) = (q : ℝ) := by
  have h : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  simpa [absWeight, scalar, normQ] using Real.sqrt_sq h

theorem absWeight_laws : WeightLaws absWeight := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z; exact Real.sqrt_nonneg _
  · norm_num [absWeight, normQ]
  · norm_num [absWeight, normQ, gone]
  · intro z t
    unfold absWeight
    rw [normQ_mul, Rat.cast_mul, Real.sqrt_mul (by exact_mod_cast normQ_nonneg z)]
  · intro z; simp only [absWeight, normQ_conjugation]
  · intro n
    rw [absWeight_scalar_nonneg _ (by positivity),
      absWeight_scalar_nonneg _ (by positivity)]
    exact_mod_cast (Nat.le_succ n)

def unequalA : Carrier := (1 / 3, 0)
def unequalB : Carrier := (2 / 3, 0)

def unequalForward (p : Carrier × Carrier) : Carrier × Carrier :=
  (gmul unequalA p.1 + p.2, gmul unequalB p.1 - p.2)

def unequalUndo (p : Carrier × Carrier) : Carrier × Carrier :=
  (p.1 + p.2, gmul unequalB p.1 - gmul unequalA p.2)

theorem unequal_undo_forward (p : Carrier × Carrier) :
    unequalUndo (unequalForward p) = p := by
  rcases p with ⟨⟨x, y⟩, ⟨z, t⟩⟩
  ext <;> dsimp [unequalUndo, unequalForward, unequalA, unequalB, gmul] <;> ring

theorem unequal_forward_undo (p : Carrier × Carrier) :
    unequalForward (unequalUndo p) = p := by
  rcases p with ⟨⟨x, y⟩, ⟨z, t⟩⟩
  ext <;> dsimp [unequalUndo, unequalForward, unequalA, unequalB, gmul] <;> ring

theorem unequal_unit_branches :
    unequalForward (gone, (0, 0)) = (unequalA, unequalB) := by
  ext <;> norm_num [unequalForward, unequalA, unequalB, gmul, gone]

theorem unequal_branches_nonzero : unequalA ≠ (0, 0) ∧ unequalB ≠ (0, 0) := by
  constructor <;> intro h <;> have hf := congrArg Prod.fst h <;>
    norm_num [unequalA, unequalB] at hf

theorem unequal_raw_normalization : absWeight unequalA + absWeight unequalB = 1 := by
  change absWeight (scalar (1 / 3)) + absWeight (scalar (2 / 3)) = 1
  rw [absWeight_scalar_nonneg _ (by norm_num), absWeight_scalar_nonneg _ (by norm_num)]
  norm_num

theorem unequal_actual_return :
    gmul gone unequalA + gmul gone unequalB = gone := by
  ext <;> norm_num [gmul, gone, unequalA, unequalB]

theorem unequal_conjugate_echo :
    gmul unequalA (gconj unequalA) + gmul unequalB (gconj unequalB) =
      scalar (5 / 9) := by
  ext <;> norm_num [gmul, gconj, unequalA, unequalB, scalar]

theorem unequal_echo_weight :
    absWeight (gmul unequalA (gconj unequalA) + gmul unequalB (gconj unequalB)) =
      5 / 9 := by
  rw [unequal_conjugate_echo, absWeight_scalar_nonneg _ (by norm_num)]
  norm_num

theorem unequal_echo_not_normalized :
    absWeight (gmul unequalA (gconj unequalA) + gmul unequalB (gconj unequalB)) ≠ 1 := by
  rw [unequal_echo_weight]; norm_num

def balancedA : Carrier := (1 / 2, 1 / 2)
def balancedB : Carrier := (1 / 2, -(1 / 2))

def balancedForward (p : Carrier × Carrier) : Carrier × Carrier :=
  (gmul balancedA p.1 + gmul balancedB p.2,
    gmul balancedB p.1 + gmul balancedA p.2)

def balancedUndo (p : Carrier × Carrier) : Carrier × Carrier :=
  (gmul balancedB p.1 + gmul balancedA p.2,
    gmul balancedA p.1 + gmul balancedB p.2)

theorem balanced_coefficients :
    balancedA + balancedB = gone ∧
    gmul balancedA balancedA + gmul balancedB balancedB = (0, 0) ∧
    gmul balancedA balancedB + gmul balancedB balancedA = gone := by
  norm_num [balancedA, balancedB, gone, gmul, Prod.mk_add_mk]

theorem balanced_square_swap (p : Carrier × Carrier) :
    balancedForward (balancedForward p) = (p.2, p.1) := by
  rcases p with ⟨⟨x, y⟩, ⟨z, t⟩⟩
  ext <;> dsimp [balancedForward, balancedA, balancedB, gmul] <;> ring

theorem balanced_diagonal (z : Carrier) : balancedForward (z, z) = (z, z) := by
  rcases z with ⟨x, y⟩
  ext <;> dsimp [balancedForward, balancedA, balancedB, gmul] <;> ring

theorem balanced_undo_forward (p : Carrier × Carrier) :
    balancedUndo (balancedForward p) = p := by
  rcases p with ⟨⟨x, y⟩, ⟨z, t⟩⟩
  ext <;> dsimp [balancedUndo, balancedForward, balancedA, balancedB, gmul] <;> ring

theorem balanced_forward_undo (p : Carrier × Carrier) :
    balancedForward (balancedUndo p) = p := by
  rcases p with ⟨⟨x, y⟩, ⟨z, t⟩⟩
  ext <;> dsimp [balancedUndo, balancedForward, balancedA, balancedB, gmul] <;> ring

theorem balanced_conjugation : gconj balancedA = balancedB ∧
    gconj balancedB = balancedA := by
  norm_num [balancedA, balancedB, gconj]

theorem balanced_unit_branches :
    balancedForward (gone, (0, 0)) = (balancedA, balancedB) := by
  ext <;> norm_num [balancedForward, balancedA, balancedB, gone, gmul]

theorem balanced_branches_nonzero : balancedA ≠ (0, 0) ∧ balancedB ≠ (0, 0) := by
  constructor <;> intro h <;> have hf := congrArg Prod.fst h <;>
    norm_num [balancedA, balancedB] at hf

theorem balanced_scalar_echo :
    gmul balancedA (gconj balancedA) + gmul balancedB (gconj balancedB) = gone := by
  ext <;> norm_num [balancedA, balancedB, gmul, gconj, gone]

def quarticWeight (z : Carrier) : ℝ := (normQ z : ℝ) ^ 2

theorem quarticWeight_scalar (q : ℚ) : quarticWeight (scalar q) = (q : ℝ) ^ 4 := by
  simp [quarticWeight, scalar, normQ]; ring

theorem quarticWeight_laws : WeightLaws quarticWeight := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z; exact sq_nonneg _
  · norm_num [quarticWeight, normQ]
  · norm_num [quarticWeight, normQ, gone]
  · intro z t; simp [quarticWeight, normQ_mul, mul_pow]
  · intro z; simp only [quarticWeight, normQ_conjugation]
  · intro n
    rw [quarticWeight_scalar, quarticWeight_scalar]
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.le_succ n) 4

theorem quartic_balanced_weights :
    quarticWeight balancedA = 1 / 4 ∧ quarticWeight balancedB = 1 / 4 := by
  norm_num [quarticWeight, normQ, balancedA, balancedB]

theorem quartic_raw_sum : quarticWeight balancedA + quarticWeight balancedB = 1 / 2 := by
  rw [quartic_balanced_weights.1, quartic_balanced_weights.2]; norm_num

theorem quartic_raw_not_normalized :
    quarticWeight balancedA + quarticWeight balancedB ≠ 1 := by
  rw [quartic_raw_sum]; norm_num

theorem quartic_echo :
    quarticWeight (gmul balancedA (gconj balancedA) +
      gmul balancedB (gconj balancedB)) = 1 := by
  rw [balanced_scalar_echo]; exact quarticWeight_laws.one

def detectorFirst (p : Carrier × Carrier) : ℝ :=
  quarticWeight p.1 / (quarticWeight p.1 + quarticWeight p.2)

def detectorSecond (p : Carrier × Carrier) : ℝ :=
  quarticWeight p.2 / (quarticWeight p.1 + quarticWeight p.2)

theorem detector_balanced : detectorFirst (balancedA, balancedB) = 1 / 2 ∧
    detectorSecond (balancedA, balancedB) = 1 / 2 := by
  norm_num [detectorFirst, detectorSecond, quarticWeight, normQ, balancedA, balancedB]

theorem detector_return : detectorFirst (gone, (0, 0)) = 1 ∧
    detectorSecond (gone, (0, 0)) = 0 := by
  norm_num [detectorFirst, detectorSecond, quarticWeight, normQ, gone]

/-- Each operational premise is supplied separately. No matrix law is needed. -/
theorem nondegenerateEcho_of_return_accounting (w : Carrier → ℝ)
    (a b u v : Carrier) (ha : a ≠ (0, 0)) (hb : b ≠ (0, 0))
    (actualReturn : gmul u a + gmul v b = gone)
    (reciprocityA : u = gconj a) (reciprocityB : v = gconj b)
    (accounting : w a + w b = 1) (unitWeight : w gone = 1) :
    NondegenerateEcho w := by
  refine ⟨a, b, ha, hb, accounting, ?_⟩
  have comm (z t : Carrier) : gmul z t = gmul t z := by
    ext <;> dsimp [gmul] <;> ring
  rw [reciprocityA, reciprocityB, comm (gconj a) a, comm (gconj b) b] at actualReturn
  rw [actualReturn, unitWeight]

end

end IDT.QMClosure.ReversibleEchoAccountingBoundary
