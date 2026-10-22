import Mathlib

namespace IDT.QMClosure.PublishedSorkinNull

/-!
A literal supplied quadratic weight, with an ASSUMED real-coordinate extension.
This is fixed-path algebra, not a derived physical continuum, a formal check of
Python, or an assertion that switching real slits leaves path contributions fixed.
Common gain/background and fixed path assignment are explicit bridge inputs.
Actual apparatus bias, nonclassical interslit paths and preparability are unmodeled.
No primitive, Born, Hilbert, or full-QM claim is upgraded by this artifact.
-/

abbrev Amplitude := ℝ × ℝ

def add (a b : Amplitude) : Amplitude := (a.1 + b.1, a.2 + b.2)

def weight (eta : ℝ) (a : Amplitude) : ℝ := a.1 ^ 2 + eta * a.2 ^ 2

def rate (eta gain background : ℝ) (a : Amplitude) : ℝ :=
  gain * weight eta a + background

structure ContextRates where
  abc : ℝ
  ab : ℝ
  ac : ℝ
  bc : ℝ
  a : ℝ
  b : ℝ
  c : ℝ
  empty : ℝ

def fixedPathRates (eta gain background : ℝ) (a b c : Amplitude) : ContextRates :=
  { abc := rate eta gain background (add (add a b) c)
    ab := rate eta gain background (add a b)
    ac := rate eta gain background (add a c)
    bc := rate eta gain background (add b c)
    a := rate eta gain background a
    b := rate eta gain background b
    c := rate eta gain background c
    empty := rate eta gain background (0, 0) }

def epsilon (r : ContextRates) : ℝ :=
  r.abc - r.ab - r.ac - r.bc + r.a + r.b + r.c - r.empty

def delta (r : ContextRates) : ℝ :=
  |r.ab - r.a - r.b + r.empty| + |r.ac - r.a - r.c + r.empty| +
    |r.bc - r.b - r.c + r.empty|

/-- Undefined at zero denominator: total field division does not license a readout. -/
noncomputable def kappa (r : ContextRates) : Option ℝ :=
  if delta r = 0 then none else some (epsilon r / delta r)

theorem supplied_weight_nonnegative (eta : ℝ) (h : 0 ≤ eta) (a : Amplitude) :
    0 ≤ weight eta a := by
  unfold weight
  positivity

theorem fixed_path_affine_epsilon_zero (eta gain background : ℝ) (a b c : Amplitude) :
    epsilon (fixedPathRates eta gain background a b c) = 0 := by
  simp only [epsilon, fixedPathRates, rate, weight, add]
  ring

/-- The equality is the supplied bridge, not a theorem about experimental apparatus. -/
theorem supplied_bridge_kappa_zero (r : ContextRates) (eta gain background : ℝ)
    (a b c : Amplitude) (bridge : r = fixedPathRates eta gain background a b c)
    (nonzero : delta r ≠ 0) : kappa r = some 0 := by
  have h : epsilon r = 0 := by
    rw [bridge]
    exact fixed_path_affine_epsilon_zero eta gain background a b c
  simp [kappa, nonzero, h]

theorem zero_denominator_is_undefined (r : ContextRates) (h : delta r = 0) :
    kappa r = none := by
  simp [kappa, h]

end IDT.QMClosure.PublishedSorkinNull
