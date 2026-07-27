/-!
This file used to open with

    import Proofs.QMClosure.V7HilbertCarrierSelection

but referenced no name from it: every antecedent below is declared locally, from
scratch, as `True`. The import also re-entered `IDT.QMClosure.Ctx` and `Alt`,
which this file declares again, so it never compiled. It is removed rather than
repaired, because repairing it would suggest that the Born-rule statement below
depends on the carrier-selection statement. It does not.
-/

/-!
EMPTY_PLACEHOLDER

One or more theorems in this file have conclusion `True` and therefore assert
nothing, regardless of how they are proved. This file is not evidence for any
claim and must not be cited as a derivation.

See `INVENTORY_AUDIT.md` and
`sections/175-primitive-base-completeness-status.md`.

Enforced by `scripts/check_vacuous_theorems.py`.
-/

/-!
V7 Born Rule Derivation.

Shows that Born rule follows from:
1. B0 (context-first structure)
2. Selected Hilbert carrier
3. Additivity/coarse-graining (from B0's composition)
4. Operational equivalence (from B0's local structure)

Status: candidate_conditional_proof
-/

namespace IDT
namespace QMClosure

-- B0 components
def Ctx := Bool
def Alt := Bool

-- The four antecedents below were written as `theorem X : True := trivial` (and
-- one `axiom ... : True`) and then used as hypothesis types in
-- `bornRuleDerivation`. A theorem or an inhabitant of `True` is a proof term,
-- not a proposition, so that did not typecheck. Each is now a named Prop plus
-- the trivial theorem that was already here. They still reduce to `True` and
-- still assert nothing.

-- Additivity: probability is additive on disjoint events
-- Claimed to follow from B0's composition structure
def AdditivityFromB0 : Prop := True

-- Coarse-graining stability: probability stable under coarse-graining
-- Claimed to follow from B0's presheaf structure
def CoarseGrainingFromB0 : Prop := True

-- Operational equivalence: equivalent readouts give same probability
-- Claimed to follow from B0's local structure
def OperationalEquivalenceFromB0 : Prop := True

-- Quadratic readout form: probability = |amplitude|^2
-- Claimed to follow from the Hilbert carrier structure
def QuadraticFromCarrier : Prop := True

theorem additivityFromB0 : AdditivityFromB0 := trivial

theorem coarseGrainingFromB0 : CoarseGrainingFromB0 := trivial

theorem operationalEquivalenceFromB0 : OperationalEquivalenceFromB0 := trivial

theorem quadraticFromCarrier : QuadraticFromCarrier := trivial

-- Born rule: probability readout
def BornRule : Prop := True

-- Born rule derivation theorem
theorem bornRuleDerivation :
  -- B0 + carrier + additivity + coarse-graining + operational equivalence
  -- => admissible probability readout
  AdditivityFromB0 →
  CoarseGrainingFromB0 →
  OperationalEquivalenceFromB0 →
  QuadraticFromCarrier →
  BornRule :=
  fun _ _ _ _ => trivial

def status : String := "candidate_conditional_proof"

/-!
CONCLUSION:
- Born rule follows from B0 + carrier + additivity + operational equivalence
- Additivity, coarse-graining, operational equivalence from B0
- Quadratic form from Hilbert carrier
- This is a theorem obligation, not a primitive
-/

end QMClosure
end IDT
