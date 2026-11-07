import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

/-!
# Exact reversible erasure transfers distinctions to retained output

If a complete output encoding is injective and the subsystem output is fixed,
the retained environment output distinguishes every admissible input label.
The update adapter starts the environment in one fixed state, independent of
the input. Its preparation adapter explicitly requires injective preparation:
syntactically different labels alone do not establish distinguishable states.

All controls and unreset registers that retain input distinctions must be part
of the environment output. There are no discarded outputs or postselection.
The finite bound counts exact classical labels. The block result quantifies
over every word; restricted languages have their own cardinality. No
probabilistic independence, quantum capacity, logarithmic entropy, heat,
energy, or cosmological interpretation is supplied. The SWAP example is an
exact mathematical control, without physical preparation availability or a
claim of perpetual reset or a freely replenished environment.
-/

namespace IDT.QMClosure.ReversibleErasureEnvironment

universe uA uS uIn uOut uI

variable {A : Type uA} {S : Type uS} {Ein : Type uIn} {Eout : Type uOut}

/-- An injective complete encoding with a constant subsystem retains every
input distinction in its environment coordinate. -/
theorem environment_injective_of_constant_subsystem
    (encode : A → S × Eout) (hencode : Function.Injective encode)
    (reset : S) (hreset : ∀ a, (encode a).1 = reset) :
    Function.Injective (fun a => (encode a).2) := by
  intro a b hab
  apply hencode
  apply Prod.ext
  · exact (hreset a).trans (hreset b).symm
  · exact hab

/-- The same initial environment is used for every input to a complete
injective update. Input and output subsystem/environment types may differ. -/
theorem environment_injective_of_update
    (update : A × Ein → S × Eout) (hupdate : Function.Injective update)
    (initial : Ein) (reset : S)
    (hreset : ∀ a, (update (a, initial)).1 = reset) :
    Function.Injective (fun a => (update (a, initial)).2) := by
  apply environment_injective_of_constant_subsystem
    (fun a => update (a, initial)) _ reset hreset
  intro a b hab
  exact congrArg Prod.fst (hupdate hab)

/-- Preparation must itself distinguish the labels before the injective
complete update can transfer those distinctions into the environment. -/
theorem environment_injective_of_prepared_update {I : Type uI}
    (prepare : A → I) (hprepare : Function.Injective prepare)
    (update : I × Ein → S × Eout) (hupdate : Function.Injective update)
    (initial : Ein) (reset : S)
    (hreset : ∀ a, (update (prepare a, initial)).1 = reset) :
    Function.Injective (fun a => (update (prepare a, initial)).2) := by
  apply environment_injective_of_constant_subsystem
    (fun a => update (prepare a, initial)) _ reset hreset
  intro a b hab
  exact hprepare (congrArg Prod.fst (hupdate hab))

/-- Exact finite classical labels require at least as many retained
environment outputs as admissible input labels. -/
theorem capacity_of_constant_subsystem [Fintype A] [Fintype Eout]
    (encode : A → S × Eout) (hencode : Function.Injective encode)
    (reset : S) (hreset : ∀ a, (encode a).1 = reset) :
    Fintype.card A ≤ Fintype.card Eout :=
  Fintype.card_le_of_injective (fun a => (encode a).2)
    (environment_injective_of_constant_subsystem encode hencode reset hreset)

theorem capacity_of_update [Fintype A] [Fintype Eout]
    (update : A × Ein → S × Eout) (hupdate : Function.Injective update)
    (initial : Ein) (reset : S)
    (hreset : ∀ a, (update (a, initial)).1 = reset) :
    Fintype.card A ≤ Fintype.card Eout :=
  Fintype.card_le_of_injective (fun a => (update (a, initial)).2)
    (environment_injective_of_update update hupdate initial reset hreset)

/-- Every word in the complete length-n language is an admissible input.
The exponent is a finite label count, with no statistical-independence premise. -/
theorem full_block_capacity [Fintype A] [Fintype Eout] (n : ℕ)
    (update : (Fin n → A) × Ein → S × Eout)
    (hupdate : Function.Injective update) (initial : Ein) (reset : S)
    (hreset : ∀ word, (update (word, initial)).1 = reset) :
    Fintype.card A ^ n ≤ Fintype.card Eout := by
  have h := capacity_of_update update hupdate initial reset hreset
  rw [Fintype.card_pi_const] at h
  exact h

/-- A restricted language is counted by its own subtype cardinality.
The constant-subsystem premise is required only on its admissible words. -/
theorem restricted_block_capacity [Fintype Eout] {n : ℕ}
    (language : Set (Fin n → A)) [Fintype language]
    (update : (Fin n → A) × Ein → S × Eout)
    (hupdate : Function.Injective update) (initial : Ein) (reset : S)
    (hreset : ∀ word : language, (update (word.val, initial)).1 = reset) :
    Fintype.card language ≤ Fintype.card Eout := by
  apply capacity_of_constant_subsystem
    (fun word : language => update (word.val, initial)) _ reset hreset
  intro a b hab
  apply Subtype.ext
  exact congrArg Prod.fst (hupdate hab)

/-- SWAP is a complete reversible update. Its second register holds the old
input after resetting the first register to the supplied initial value. -/
def swapUpdate : A × A ≃ A × A := Equiv.prodComm A A

theorem swapUpdate_injective : Function.Injective (swapUpdate (A := A)) :=
  (swapUpdate (A := A)).injective

theorem swapUpdate_reset (initial a : A) :
    swapUpdate (a, initial) = (initial, a) := rfl

theorem swapUpdate_environment_identity (initial : A) :
    (fun a => (swapUpdate (a, initial)).2) = id := rfl

/-- The environmental record is a bijection onto A: SWAP attains the exact
capacity bound with an environment of the same type as the input register.
The type A can itself be an entire block tape. -/
theorem swapUpdate_environment_bijective (initial : A) :
    Function.Bijective (fun a => (swapUpdate (a, initial)).2) :=
  Function.bijective_id

end IDT.QMClosure.ReversibleErasureEnvironment
