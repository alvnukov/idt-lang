import Proofs.QMClosure.NativeThreeWireProbabilityDenominator
import Proofs.QMClosure.FiniteDeterministicRecordFrequency
import Proofs.QMClosure.ResponseSourceLocalProbability

/-!
# Exact single-history readout frequencies and finite complete-state memory

The native complex backend and the supplied six-axiom probability Law remain
premises. The detector contract is a finite COMPLETE recurrent state, a
deterministic fixed time-homogeneous trial step, a Boolean record, and its exact
limiting empirical frequency along one history. For each fixed preparation n,
the rule, record and initial state may depend on n. The lower bound counts
2^(2*n-1) states: binary encoding requires at least 2*n-1 bits, not exponentially
many memory bits. Three circuit ports do not imply finite complete-state memory.

These results do not exclude stochastic detectors, external streams, ensembles,
continuous or unbounded memory, approximate frequencies or finite precision.
They supply no physical finite-memory assumption, outcome or exclusivity proof,
detector or probability provenance, Born derivation, actualization, or QM closure.
-/

namespace IDT.QMClosure.NativeFiniteMemoryReadoutWall

open Filter
open scoped Topology

open NativeThreeWireProbabilityDenominator
open FiniteDeterministicRecordFrequency

variable {S : Type*}

/-- Exact frequency matching forces the denominator to fit in the state count. -/
theorem selectedWeight_requires_states [Fintype S] (step : S → S)
    (record : S → Bool) (initial : S) (n : ℕ) (hn : 0 < n)
    (hfreq : Tendsto (recordFrequency step record initial) atTop (𝓝 (selectedWeight n))) :
    2 ^ (2 * n - 1) ≤ Fintype.card S := by
  obtain ⟨k, ell, _hk, hell, hcard, heq⟩ :=
    fraction_of_recordFrequency_tendsto step record initial hfreq
  exact (Nat.le_of_dvd hell (denominator_dvd n hn k ell hell heq)).trans hcard

/-- Even preparation-dependent rules cannot fit every target on one finite carrier. -/
theorem no_fixed_finite_carrier_matches_all [Fintype S]
    (step : ℕ → S → S) (record : ℕ → S → Bool) (initial : ℕ → S) :
    ¬ (∀ n : ℕ, 0 < n →
      Tendsto (recordFrequency (step n) (record n) (initial n)) atTop
        (𝓝 (selectedWeight n))) := by
  intro h
  have hbound := selectedWeight_requires_states
    (step (Fintype.card S + 1)) (record (Fintype.card S + 1))
    (initial (Fintype.card S + 1)) (Fintype.card S + 1) (by omega)
    (h (Fintype.card S + 1) (by omega))
  have hexp : Fintype.card S ≤ 2 * (Fintype.card S + 1) - 1 := by omega
  have hpow : 2 ^ Fintype.card S ≤ 2 ^ (2 * (Fintype.card S + 1) - 1) :=
    Nat.pow_le_pow_right (by decide) hexp
  exact (Nat.lt_two_pow_self : Fintype.card S < 2 ^ Fintype.card S).not_ge
    (hpow.trans hbound)

variable {V Ω : Type*}

/-- Both contextual diagonal-fixed premises are retained in the raw Law bridge. -/
theorem rawLaw_repeatedWord_probability (d : ResponseContextQuotient.Data V Ω) (v : V)
    (hz : ResponseSourceLocalProbability.DiagonalFixed d d.chosenZero)
    (hv : ResponseSourceLocalProbability.DiagonalFixed d v)
    (L : ResponseNativeProbabilitySelection.Law d v) (n : ℕ) :
    L.prob (0 : Fin 3) (repeatedWord n) 0 = selectedWeight n := by
  rw [ResponseSourceLocalProbability.probability_eq_normSq d v hz hv L]
  simpa only [NativeVacuumProbabilityFamily.source,
    ← NativeThreeWireProbabilityDenominator.source_eq_single] using
    repeatedWord_selectedWeight n

/-- An exact single-history frequency matching the supplied raw Law needs states. -/
theorem rawLaw_probability_requires_states [Fintype S]
    (d : ResponseContextQuotient.Data V Ω) (v : V)
    (hz : ResponseSourceLocalProbability.DiagonalFixed d d.chosenZero)
    (hv : ResponseSourceLocalProbability.DiagonalFixed d v)
    (L : ResponseNativeProbabilitySelection.Law d v)
    (step : S → S) (record : S → Bool) (initial : S) (n : ℕ) (hn : 0 < n)
    (hfreq : Tendsto (recordFrequency step record initial) atTop
      (𝓝 (L.prob (0 : Fin 3) (repeatedWord n) 0))) :
    2 ^ (2 * n - 1) ≤ Fintype.card S := by
  rw [rawLaw_repeatedWord_probability d v hz hv L n] at hfreq
  exact selectedWeight_requires_states step record initial n hn hfreq

end IDT.QMClosure.NativeFiniteMemoryReadoutWall
