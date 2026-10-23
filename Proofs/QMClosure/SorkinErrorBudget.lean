import Proofs.QMClosure.PublishedSorkinNull

namespace IDT.QMClosure.SorkinErrorBudget

open PublishedSorkinNull

/-!
Universal scalar transfer under SUPPLIED simultaneous signed bounds. Here mu
denotes the expectation of the identical acquisition/reduction estimator under
a supplied ensemble, not an observed mean or fitted null. Ensemble validity,
complete error accounting and physical readout coverage are external inputs.
No independence/Gaussian premise, kappa propagation, Python verification,
empirical acceptance, primitive rejection or full-QM upgrade is asserted.
-/

def lower (ehat sU bU : ℝ) : ℝ := ehat - sU - bU
def upper (ehat sL bL : ℝ) : ℝ := ehat - sL - bL

theorem scalar_transfer_sound (ehat mu q sL sU bL bU : ℝ)
    (hsL : sL ≤ ehat - mu) (hsU : ehat - mu ≤ sU)
    (hbL : bL ≤ mu - q) (hbU : mu - q ≤ bU) :
    lower ehat sU bU ≤ q ∧ q ≤ upper ehat sL bL := by
  unfold lower upper
  constructor <;> linarith

theorem null_forces_zero_containment (ehat mu q sL sU bL bU : ℝ)
    (hsL : sL ≤ ehat - mu) (hsU : ehat - mu ≤ sU)
    (hbL : bL ≤ mu - q) (hbU : mu - q ≤ bU) (hq : q = 0) :
    lower ehat sU bU ≤ 0 ∧ 0 ≤ upper ehat sL bL := by
  simpa only [hq] using scalar_transfer_sound ehat mu q sL sU bL bU hsL hsU hbL hbU

/-- Strict exclusion refutes the conjunction of null and supplied assumptions. -/
theorem strict_exclusion_contradicts_joint_null (ehat mu q sL sU bL bU : ℝ)
    (hsL : sL ≤ ehat - mu) (hsU : ehat - mu ≤ sU)
    (hbL : bL ≤ mu - q) (hbU : mu - q ≤ bU)
    (hex : upper ehat sL bL < 0 ∨ 0 < lower ehat sU bU) : q ≠ 0 := by
  intro hq
  obtain ⟨hl, hu⟩ := null_forces_zero_containment ehat mu q sL sU bL bU hsL hsU hbL hbU hq
  rcases hex with hex | hex <;> linarith

/-- Widen either or both supplied intervals: an already retained zero stays retained. -/
theorem widening_retains_zero (ehat sL sU bL bU sL' sU' bL' bU' : ℝ)
    (hsL : sL' ≤ sL) (hsU : sU ≤ sU') (hbL : bL' ≤ bL) (hbU : bU ≤ bU')
    (hzero : lower ehat sU bU ≤ 0 ∧ 0 ≤ upper ehat sL bL) :
    lower ehat sU' bU' ≤ 0 ∧ 0 ≤ upper ehat sL' bL' := by
  unfold lower upper at *
  constructor <;> linarith [hzero.1, hzero.2]

/-- Endpoint witnesses ONLY in the unconstrained scalar abstraction, not apparatus feasibility. -/
theorem lower_endpoint_sharp (ehat sL sU bL bU : ℝ) (hs : sL ≤ sU) (hb : bL ≤ bU) :
    ∃ mu q : ℝ, sL ≤ ehat - mu ∧ ehat - mu ≤ sU ∧
      bL ≤ mu - q ∧ mu - q ≤ bU ∧ q = lower ehat sU bU := by
  refine ⟨ehat - sU, ehat - sU - bU, ?_⟩
  unfold lower
  refine ⟨?_, ?_, ?_, ?_, rfl⟩ <;> linarith

theorem upper_endpoint_sharp (ehat sL sU bL bU : ℝ) (hs : sL ≤ sU) (hb : bL ≤ bU) :
    ∃ mu q : ℝ, sL ≤ ehat - mu ∧ ehat - mu ≤ sU ∧
      bL ≤ mu - q ∧ mu - q ≤ bU ∧ q = upper ehat sL bL := by
  refine ⟨ehat - sL, ehat - sL - bL, ?_⟩
  unfold upper
  refine ⟨?_, ?_, ?_, ?_, rfl⟩ <;> linarith

/-- Fixed independent open/closed amplitudes, with coherent closed-path baseline.
    Not a theorem for arbitrary imperfect shutters or context-dependent paths. -/
def affineCubeRates (eta gain background : ℝ) (base a b c : Amplitude) : ContextRates :=
  { abc := rate eta gain background (add base (add (add a b) c))
    ab := rate eta gain background (add base (add a b))
    ac := rate eta gain background (add base (add a c))
    bc := rate eta gain background (add base (add b c))
    a := rate eta gain background (add base a)
    b := rate eta gain background (add base b)
    c := rate eta gain background (add base c)
    empty := rate eta gain background base }

theorem affine_cube_epsilon_zero (eta gain background : ℝ) (base a b c : Amplitude) :
    epsilon (affineCubeRates eta gain background base a b c) = 0 := by
  simp only [epsilon, affineCubeRates, rate, weight, add]
  ring

/-- Composition with the supplied model identity, not a derived physical bridge. -/
theorem supplied_affine_cube_bounds_retain_zero (ehat mu sL sU bL bU eta gain background : ℝ)
    (base a b c : Amplitude)
    (hsL : sL ≤ ehat - mu) (hsU : ehat - mu ≤ sU)
    (hbL : bL ≤ mu - epsilon (affineCubeRates eta gain background base a b c))
    (hbU : mu - epsilon (affineCubeRates eta gain background base a b c) ≤ bU) :
    lower ehat sU bU ≤ 0 ∧ 0 ≤ upper ehat sL bL := by
  exact null_forces_zero_containment ehat mu _ sL sU bL bU hsL hsU hbL hbU
    (affine_cube_epsilon_zero eta gain background base a b c)

end IDT.QMClosure.SorkinErrorBudget
