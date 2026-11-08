import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Rational finite distributions on arbitrary carriers

This is a mathematical classical process envelope. Its coefficients and TV
comparison carry no physical outcome or response-calibration interpretation.
-/

namespace IDT.QMClosure.RationalFiniteDistribution

noncomputable section

set_option maxHeartbeats 1000000

open Finset

variable {V W X Y : Type*}

def mass (d : V →₀ ℚ) : ℚ := d.sum fun _ q => q

def extend (K : V → W →₀ ℚ) : (V →₀ ℚ) →ₗ[ℚ] (W →₀ ℚ) :=
  Finsupp.lift (W →₀ ℚ) ℚ V K

@[simp] theorem extend_apply (K : V → W →₀ ℚ) (d : V →₀ ℚ) :
    extend K d = d.sum (fun v q => q • K v) := rfl

@[simp] theorem extend_single (K : V → W →₀ ℚ) (v : V) (q : ℚ) :
    extend K (Finsupp.single v q) = q • K v := by
  classical
  simp [extend_apply]

@[simp] theorem mass_zero : mass (0 : V →₀ ℚ) = 0 := by simp [mass]

@[simp] theorem mass_add (d e : V →₀ ℚ) : mass (d + e) = mass d + mass e := by
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

@[simp] theorem mass_smul (q : ℚ) (d : V →₀ ℚ) : mass (q • d) = q * mass d := by
  rw [mass, Finsupp.sum_smul_index (fun _ => rfl)]
  simp [mass, Finsupp.sum, Finset.mul_sum]

@[simp] theorem mass_single (v : V) (q : ℚ) : mass (Finsupp.single v q) = q := by
  classical
  simp [mass]

theorem mass_extend (K : V → W →₀ ℚ) (d : V →₀ ℚ) :
    mass (extend K d) = d.sum (fun v q => q * mass (K v)) := by
  classical
  change (extend K d).sum (fun _ q => q) = _
  rw [extend_apply, Finsupp.sum_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  exact Finsupp.sum_congr fun v _ => mass_smul _ _

structure FinDist (V : Type*) where
  coeff : V →₀ ℚ
  nonneg : ∀ v, 0 ≤ coeff v
  mass_one : mass coeff = 1

@[ext] theorem FinDist.ext {μ ν : FinDist V} (h : μ.coeff = ν.coeff) : μ = ν := by
  cases μ; cases ν; cases h; rfl

def dirac (v : V) : FinDist V where
  coeff := Finsupp.single v 1
  nonneg w := by
    classical
    simp only [Finsupp.single_apply]
    split_ifs <;> norm_num
  mass_one := mass_single v 1

def bind (μ : FinDist V) (K : V → FinDist W) : FinDist W where
  coeff := extend (fun v => (K v).coeff) μ.coeff
  nonneg w := by
    classical
    simp only [extend_apply, Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Finsupp.sum_nonneg' fun v => mul_nonneg (μ.nonneg v) ((K v).nonneg w)
  mass_one := by
    rw [mass_extend]
    simpa only [(K _).mass_one, mul_one] using μ.mass_one

@[simp] theorem bind_coeff (μ : FinDist V) (K : V → FinDist W) :
    (bind μ K).coeff = extend (fun v => (K v).coeff) μ.coeff := rfl

@[simp] theorem dirac_bind (v : V) (K : V → FinDist W) : bind (dirac v) K = K v := by
  apply FinDist.ext
  simp [dirac]

@[simp] theorem bind_dirac (μ : FinDist V) : bind μ dirac = μ := by
  apply FinDist.ext
  simp [extend_apply, dirac, Finsupp.smul_single, Finsupp.sum_single]

theorem extend_extend (d : V →₀ ℚ) (K : V → W →₀ ℚ) (L : W → X →₀ ℚ) :
    extend L (extend K d) = extend (fun v => extend L (K v)) d := by
  change extend L (∑ v ∈ d.support, d v • K v) =
    ∑ v ∈ d.support, d v • extend L (K v)
  simp only [map_sum, map_smul]

theorem bind_bind (μ : FinDist V) (K : V → FinDist W) (L : W → FinDist X) :
    bind (bind μ K) L = bind μ (fun v => bind (K v) L) := by
  apply FinDist.ext
  exact extend_extend _ _ _

def map (f : V → W) (μ : FinDist V) : FinDist W := bind μ (dirac ∘ f)

@[simp] theorem map_dirac (f : V → W) (v : V) : map f (dirac v) = dirac (f v) :=
  dirac_bind _ _

@[simp] theorem map_id (μ : FinDist V) : map id μ = μ := bind_dirac μ

theorem map_comp (g : W → X) (f : V → W) (μ : FinDist V) :
    map g (map f μ) = map (g ∘ f) μ := by
  simp [map, bind_bind, Function.comp_def]

theorem map_bind (f : W → X) (μ : FinDist V) (K : V → FinDist W) :
    map f (bind μ K) = bind μ (fun v => map f (K v)) := bind_bind _ _ _

theorem bind_map (f : V → W) (μ : FinDist V) (K : W → FinDist X) :
    bind (map f μ) K = bind μ (K ∘ f) := by
  simp [map, bind_bind, Function.comp_def]

theorem bind_const (μ : FinDist V) (ν : FinDist W) : bind μ (fun _ => ν) = ν := by
  apply FinDist.ext
  simp only [bind_coeff, extend_apply, Finsupp.sum, ← Finset.sum_smul]
  change mass μ.coeff • ν.coeff = ν.coeff
  rw [μ.mass_one, one_smul]

theorem bind_comm (μ : FinDist V) (ν : FinDist W) (K : V → W → FinDist X) :
    bind μ (fun v => bind ν (K v)) = bind ν (fun w => bind μ (fun v => K v w)) := by
  apply FinDist.ext
  simp only [bind_coeff, extend_apply, Finsupp.sum, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

def product (μ : FinDist V) (ν : FinDist W) : FinDist (V × W) :=
  bind μ (fun v => map (fun w => (v, w)) ν)

@[simp] theorem map_fst_product (μ : FinDist V) (ν : FinDist W) :
    map Prod.fst (product μ ν) = μ := by
  simp [product, map, bind_bind, bind_const]

@[simp] theorem map_snd_product (μ : FinDist V) (ν : FinDist W) :
    map Prod.snd (product μ ν) = ν := by
  simp [product, map, bind_bind, bind_const]

def mixture (t : ℚ) (ht : 0 ≤ t) (ht' : t ≤ 1) (μ ν : FinDist V) : FinDist V where
  coeff := t • μ.coeff + (1 - t) • ν.coeff
  nonneg v := by
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ht (μ.nonneg v))
      (mul_nonneg (sub_nonneg.mpr ht') (ν.nonneg v))
  mass_one := by simp [μ.mass_one, ν.mass_one]

def l1 (d : V →₀ ℚ) : ℚ := d.sum (fun _ q => |q|)

theorem l1_nonneg (d : V →₀ ℚ) : 0 ≤ l1 d := Finsupp.sum_nonneg' fun _ => abs_nonneg _

theorem l1_of_nonneg (d : V →₀ ℚ) (h : ∀ v, 0 ≤ d v) : l1 d = mass d := by
  apply Finsupp.sum_congr
  intro v _
  exact abs_of_nonneg (h v)

@[simp] theorem l1_zero : l1 (0 : V →₀ ℚ) = 0 := by simp [l1]

theorem l1_smul (q : ℚ) (d : V →₀ ℚ) : l1 (q • d) = |q| * l1 d := by
  rw [l1, Finsupp.sum_smul_index (fun _ => abs_zero)]
  simp [abs_mul, l1, Finsupp.sum, Finset.mul_sum]

theorem l1_add_le (d e : V →₀ ℚ) : l1 (d + e) ≤ l1 d + l1 e := by
  classical
  let s := d.support ∪ e.support
  rw [l1, Finsupp.sum_of_support_subset _ Finsupp.support_add _ (by simp),
    l1, Finsupp.sum_of_support_subset _ Finset.subset_union_left _ (by simp),
    l1, Finsupp.sum_of_support_subset _ Finset.subset_union_right _ (by simp),
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun v _ => abs_add_le (d v) (e v)

theorem l1_sum_le (s : Finset X) (f : X → V →₀ ℚ) :
    l1 (∑ x ∈ s, f x) ≤ ∑ x ∈ s, l1 (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    simp only [Finset.sum_insert hx]
    exact (l1_add_le _ _).trans (add_le_add_right ih _)

theorem l1_extend_le (K : V → FinDist W) (d : V →₀ ℚ) :
    l1 (extend (fun v => (K v).coeff) d) ≤ l1 d := by
  rw [extend_apply, Finsupp.sum]
  calc
    _ ≤ ∑ v ∈ d.support, l1 (d v • (K v).coeff) := l1_sum_le _ _
    _ = l1 d := by
      simp only [l1_smul, l1_of_nonneg _ (K _).nonneg, (K _).mass_one, mul_one]
      rfl

def tv (μ ν : FinDist V) : ℚ := l1 (μ.coeff - ν.coeff) / 2

theorem tv_bind_le (μ ν : FinDist V) (K : V → FinDist W) :
    tv (bind μ K) (bind ν K) ≤ tv μ ν := by
  unfold tv
  simp only [bind_coeff, ← map_sub]
  exact div_le_div_of_nonneg_right (l1_extend_le K _) (by norm_num)

theorem tv_map_le (f : V → W) (μ ν : FinDist V) : tv (map f μ) (map f ν) ≤ tv μ ν :=
  tv_bind_le μ ν _

theorem tv_product_right (μ ν : FinDist V) (ρ : FinDist W) :
    tv (product μ ρ) (product ν ρ) = tv μ ν := by
  apply le_antisymm (tv_bind_le μ ν _)
  simpa only [map_fst_product] using
    tv_map_le Prod.fst (product μ ρ) (product ν ρ)

@[simp] theorem map_const (μ : FinDist V) (w : W) : map (fun _ => w) μ = dirac w :=
  bind_const μ (dirac w)

/-- Apply a row kernel to the first wire, retaining the second wire. -/
def localLeft (K : V → FinDist X) (p : V × W) : FinDist (X × W) :=
  map (fun x => (x, p.2)) (K p.1)

/-- Apply a row kernel to the second wire, retaining the first wire. -/
def localRight (L : W → FinDist Y) (p : V × W) : FinDist (V × Y) :=
  map (fun y => (p.1, y)) (L p.2)

/-- The input joint distribution may be correlated. -/
theorem disjoint_local_commute (μ : FinDist (V × W))
    (K : V → FinDist X) (L : W → FinDist Y) :
    bind (bind μ (localLeft K)) (localRight L) =
      bind (bind μ (localRight L)) (localLeft K) := by
  rw [bind_bind, bind_bind]
  congr 1
  funext p
  simp only [localLeft, localRight, bind_map, Function.comp_def]
  simpa only [map, Function.comp_def] using
    bind_comm (K p.1) (L p.2) (fun x y => dirac (x, y))

theorem remote_marginal_left (μ : FinDist (V × W)) (K : V → FinDist X) :
    map Prod.snd (bind μ (localLeft K)) = map Prod.snd μ := by
  simp only [map_bind, localLeft, map_comp, Function.comp_def, map_const]
  rfl

theorem remote_marginal_right (μ : FinDist (V × W)) (L : W → FinDist Y) :
    map Prod.fst (bind μ (localRight L)) = map Prod.fst μ := by
  simp only [map_bind, localRight, map_comp, Function.comp_def, map_const]
  rfl

theorem bind_mixture (t : ℚ) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (μ ν : FinDist V) (K : V → FinDist W) :
    bind (mixture t ht ht' μ ν) K = mixture t ht ht' (bind μ K) (bind ν K) := by
  apply FinDist.ext
  exact (extend (fun v => (K v).coeff)).map_add _ _ |>.trans
    (congrArg₂ (· + ·) (map_smul _ _ _) (map_smul _ _ _))

theorem dirac_injective : Function.Injective (dirac : V → FinDist V) := by
  classical
  intro x y h
  by_contra hxy
  have hh := congrArg (fun μ : FinDist V => μ.coeff x) h
  simp [dirac, hxy] at hh

/-- A nontrivial classical mixture cannot equal a pure preparation. -/
theorem half_mixture_dirac (m x y : V)
    (h : dirac m = mixture (1 / 2) (by norm_num) (by norm_num) (dirac x) (dirac y)) :
    x = m ∧ y = m := by
  classical
  have endpoint (a b : V)
      (hh : dirac m = mixture (1 / 2) (by norm_num) (by norm_num) (dirac a) (dirac b)) :
      a = m := by
    by_contra ham
    have hc := congrArg (fun μ : FinDist V => μ.coeff a) hh
    simp only [dirac, mixture, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      Finsupp.single_eq_same, Finsupp.single_apply, if_neg (Ne.symm ham)] at hc
    norm_num at hc
    split_ifs at hc <;> norm_num at hc
  refine ⟨endpoint x y h, ?_⟩
  apply endpoint y x
  apply FinDist.ext
  have hc := congrArg FinDist.coeff h
  simpa only [mixture, show (1 - (1 / 2 : ℚ)) = 1 / 2 by norm_num,
    add_comm] using hc

end
end IDT.QMClosure.RationalFiniteDistribution
