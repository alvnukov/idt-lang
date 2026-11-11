import Proofs.QMClosure.TransparentFourthInitialHistoryPresentation
import Proofs.QMClosure.NativeInitialHistoryPresentation
import Proofs.QMClosure.DuplicationGainDestructiveCore

/-!
# The destructive quotient of the literal fourth-rejoin presentation

The statements below concern this algebraic presentation and its maps.
The quotient adds exactly e=0 to the independent initial semiring. It is
identified with the existing destructive presentation by mutually inverse
universal maps. A complex model is used only downstream for separation.
This identifies an additional algebraic quotient. Physical selection of it
remains an independent obligation. The classical e=1 quotient is deferred.
-/

namespace IDT.QMClosure.TransparentFourthDestructiveQuotient

noncomputable section

attribute [local instance] NativeInitialHistoryPresentation.presentationCommRing

/-- The only new equation imposed on the fourth-rejoin initial carrier. -/
inductive DestructiveRel : TransparentFourthInitialHistoryPresentation.Presentation → TransparentFourthInitialHistoryPresentation.Presentation → Prop
  | killSector : DestructiveRel TransparentFourthInitialHistoryPresentation.e 0

def destructiveCon : RingCon TransparentFourthInitialHistoryPresentation.Presentation := ringConGen DestructiveRel

abbrev Quotient := destructiveCon.Quotient

def q : TransparentFourthInitialHistoryPresentation.Presentation →+* Quotient := destructiveCon.mk'

def qa : Quotient := q TransparentFourthInitialHistoryPresentation.a

def qb : Quotient := q TransparentFourthInitialHistoryPresentation.b

@[simp] theorem q_e : q TransparentFourthInitialHistoryPresentation.e = 0 := by
  change destructiveCon.mk' TransparentFourthInitialHistoryPresentation.e = destructiveCon.mk' 0
  exact destructiveCon.eq.mpr (RingConGen.Rel.of _ _ DestructiveRel.killSector)

theorem quotient_transparent : qa + qb = 1 := by
  simpa only [qa, qb, map_add, map_one] using congrArg q TransparentFourthInitialHistoryPresentation.transparent

theorem quotient_fourth_rejoin : qa ^ 4 = qb ^ 4 := by
  simpa only [qa, qb, map_pow] using congrArg q TransparentFourthInitialHistoryPresentation.fourth_rejoin

def quotientContract : FourthRejoinIdempotent.Contract qa qb :=
  FourthRejoinIdempotent.contract_of_transparent_fourth
    quotient_transparent quotient_fourth_rejoin

theorem quotient_sector_zero : FourthRejoinIdempotent.sector qa qb = 0 := by
  simpa only [TransparentFourthInitialHistoryPresentation.e, TransparentFourthInitialHistoryPresentation.T, qa, qb, FourthRejoinIdempotent.sector,
    FourthRejoinIdempotent.defect, map_mul, map_add, map_pow, map_ofNat] using q_e

/-- The destructive equation is derived after the e=0 quotient is installed. -/
theorem quotient_destructive : qa ^ 2 + qb ^ 2 = 0 :=
  (FourthRejoinIdempotent.sector_eq_zero_iff quotientContract).mp quotient_sector_zero

/-- The old destructive presentation satisfies the new fourth-power equation. -/
theorem native_fourth_rejoin : NativeInitialHistoryPresentation.a ^ 4 = NativeInitialHistoryPresentation.b ^ 4 := by
  have hd : NativeInitialHistoryPresentation.a ^ 2 + NativeInitialHistoryPresentation.b ^ 2 = 0 := by
    simpa only [pow_two] using NativeInitialHistoryPresentation.destructive
  have heq : NativeInitialHistoryPresentation.a ^ 2 = -(NativeInitialHistoryPresentation.b ^ 2) := eq_neg_of_add_eq_zero_left hd
  calc
    NativeInitialHistoryPresentation.a ^ 4 = (NativeInitialHistoryPresentation.a ^ 2) ^ 2 := by ring
    _ = (-(NativeInitialHistoryPresentation.b ^ 2)) ^ 2 := by rw [heq]
    _ = NativeInitialHistoryPresentation.b ^ 4 := by ring

/-- Initiality of P supplies the map to the old destructive presentation. -/
def toNative : TransparentFourthInitialHistoryPresentation.Presentation →+* NativeInitialHistoryPresentation.Presentation :=
  TransparentFourthInitialHistoryPresentation.eval NativeInitialHistoryPresentation.a NativeInitialHistoryPresentation.b NativeInitialHistoryPresentation.transparent native_fourth_rejoin

@[simp] theorem toNative_a : toNative TransparentFourthInitialHistoryPresentation.a = NativeInitialHistoryPresentation.a := by simp [toNative]

@[simp] theorem toNative_b : toNative TransparentFourthInitialHistoryPresentation.b = NativeInitialHistoryPresentation.b := by simp [toNative]

@[simp] theorem toNative_T : toNative TransparentFourthInitialHistoryPresentation.T = 0 := by
  simpa only [TransparentFourthInitialHistoryPresentation.T, map_add, map_mul, map_pow, toNative_a, toNative_b, pow_two] using NativeInitialHistoryPresentation.destructive

@[simp] theorem toNative_e : toNative TransparentFourthInitialHistoryPresentation.e = 0 := by
  simp only [TransparentFourthInitialHistoryPresentation.e, map_mul, toNative_T, mul_zero]

theorem destructiveCon_le_kernel : destructiveCon ≤ RingCon.ker toNative := by
  apply RingCon.ringConGen_le
  intro x y h
  cases h with
  | killSector =>
      simpa only [RingCon.ker_apply, toNative_e, map_zero]

/-- The descended map from the generated e=0 quotient. -/
def F : Quotient →+* NativeInitialHistoryPresentation.Presentation :=
  destructiveCon.lift toNative destructiveCon_le_kernel

@[simp] theorem F_q (p : TransparentFourthInitialHistoryPresentation.Presentation) : F (q p) = toNative p := by
  exact RingCon.lift_mk' destructiveCon_le_kernel p

@[simp] theorem F_qa : F qa = NativeInitialHistoryPresentation.a := by simp [qa]

@[simp] theorem F_qb : F qb = NativeInitialHistoryPresentation.b := by simp [qb]

/-- Native initiality applies because the quotient destructive law is proved. -/
def G : NativeInitialHistoryPresentation.Presentation →+* Quotient :=
  NativeInitialHistoryPresentation.eval qa qb quotient_transparent quotient_destructive

@[simp] theorem G_a : G NativeInitialHistoryPresentation.a = qa := by simp [G]

@[simp] theorem G_b : G NativeInitialHistoryPresentation.b = qb := by simp [G]

theorem F_comp_G : F.comp G = RingHom.id NativeInitialHistoryPresentation.Presentation := by
  apply NativeInitialHistoryPresentation.hom_ext
  · change F (G NativeInitialHistoryPresentation.a) = NativeInitialHistoryPresentation.a
    simp
  · change F (G NativeInitialHistoryPresentation.b) = NativeInitialHistoryPresentation.b
    simp

theorem G_comp_F : G.comp F = RingHom.id Quotient := by
  apply RingCon.Quotient.hom_ext
  apply TransparentFourthInitialHistoryPresentation.hom_ext
  · change G (F qa) = qa
    simp
  · change G (F qb) = qb
    simp

/-- An exact algebraic quotient equivalence, preserving both generators. -/
def destructiveEquiv : Quotient ≃+* NativeInitialHistoryPresentation.Presentation where
  toFun := F
  invFun := G
  left_inv p := by
    have h := DFunLike.congr_fun G_comp_F p
    exact h
  right_inv p := by
    have h := DFunLike.congr_fun F_comp_G p
    exact h
  map_mul' := F.map_mul
  map_add' := F.map_add

/-- The kernel of the natural destructive map is exactly the generated e=0 relation. -/
theorem destructiveCon_eq_kernel : destructiveCon = RingCon.ker toNative := by
  apply RingCon.ext
  intro x y
  change destructiveCon x y ↔ toNative x = toNative y
  rw [← destructiveCon.eq]
  constructor
  · intro h
    simpa only [F_q] using congrArg F h
  · intro h
    apply destructiveEquiv.injective
    change F (q x) = F (q y)
    simpa only [F_q] using h

/-- A downstream separating model excludes the unit sector in TransparentFourthInitialHistoryPresentation. -/
theorem initial_e_ne_one : TransparentFourthInitialHistoryPresentation.e ≠ 1 := by
  intro h
  have hc := congrArg (NativeInitialHistoryPresentation.complexEval.comp toNative) h
  have h01 : (0 : ℂ) = 1 := by
    simpa only [RingHom.comp_apply, toNative_e, map_zero, map_one] using hc
  exact zero_ne_one h01

theorem initial_a_ne_b : TransparentFourthInitialHistoryPresentation.a ≠ TransparentFourthInitialHistoryPresentation.b := by
  intro h
  exact initial_e_ne_one (TransparentFourthInitialHistoryPresentation.e_one_iff_a_eq_b.mpr h)

theorem initial_nontrivial_idempotent :
    TransparentFourthInitialHistoryPresentation.e * TransparentFourthInitialHistoryPresentation.e = TransparentFourthInitialHistoryPresentation.e ∧ TransparentFourthInitialHistoryPresentation.e ≠ 0 ∧ TransparentFourthInitialHistoryPresentation.e ≠ 1 :=
  ⟨TransparentFourthInitialHistoryPresentation.e_idempotent, TransparentFourthInitialHistoryPresentation.e_ne_zero, initial_e_ne_one⟩

/-- Zero detection has no implication of injectivity. -/
theorem classical_shadow_not_injective : ¬ Function.Injective TransparentFourthInitialHistoryPresentation.shadow := by
  intro h
  apply initial_a_ne_b
  apply h
  rw [TransparentFourthInitialHistoryPresentation.shadow_a, TransparentFourthInitialHistoryPresentation.shadow_b]

theorem classical_shadow_identifies_sector_unit :
    TransparentFourthInitialHistoryPresentation.shadow TransparentFourthInitialHistoryPresentation.e = TransparentFourthInitialHistoryPresentation.shadow 1 ∧ TransparentFourthInitialHistoryPresentation.e ≠ 1 := by
  exact ⟨by simp, initial_e_ne_one⟩

/-- The obstruction quantifies over every proposed full readout and gain on TransparentFourthInitialHistoryPresentation. -/
theorem no_full_duplication_gain_contract :
    ¬ ∃ (W : TransparentFourthInitialHistoryPresentation.Presentation → ℝ) (k : ℝ),
      DuplicationGainDestructive.Contract TransparentFourthInitialHistoryPresentation.a TransparentFourthInitialHistoryPresentation.b W k :=
  DuplicationGainDestructive.no_contract_of_real_shadow
    TransparentFourthInitialHistoryPresentation.realShadow TransparentFourthInitialHistoryPresentation.realShadow_a TransparentFourthInitialHistoryPresentation.realShadow_b

end

end IDT.QMClosure.TransparentFourthDestructiveQuotient
