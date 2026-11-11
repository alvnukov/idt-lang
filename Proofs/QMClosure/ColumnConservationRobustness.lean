import Proofs.QMClosure.ColumnConservationRobustnessCore

/-!
Source-local robustness bounds. The coefficient carrier is an
arbitrary commutative monoid. The sole coefficient relation is equality of
fourth histories. Real order and arbitrary forward serial depth are retained.
-/

namespace IDT.QMClosure.ColumnConservationRobustness

open ColumnConservationRobustnessCore

noncomputable section

variable {M : Type*} [CommMonoid M]

private def expand (a b : M) (W : M → ℝ) : ℕ → M → ℝ
  | 0, p => W p
  | n + 1, p => expand a b W n (a * p) + expand a b W n (b * p)

private theorem power_mem (S : Set M) (c : M)
    (hc : ∀ q ∈ S, c * q ∈ S) (n : ℕ) {p : M} (hp : p ∈ S) :
    c ^ n * p ∈ S := by
  induction n with
  | zero => simpa using hp
  | succ n ih =>
    simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hc _ ih

private theorem relative_expansion
    (a b : M) (W : M → ℝ) (S : Set M)
    (ha : ∀ q ∈ S, a * q ∈ S) (hb : ∀ q ∈ S, b * q ∈ S)
    (hpos : ∀ q ∈ S, 0 ≤ W q) {ε : ℝ} (hε : 0 ≤ ε)
    (hcolumn : ∀ q ∈ S, |W (a * q) + W (b * q) - W q| ≤ ε * W q)
    (n : ℕ) {p : M} (hp : p ∈ S) :
    |expand a b W n p - W p| ≤ ((1 + ε) ^ n - 1) * W p := by
  induction n generalizing p with
  | zero => simp [expand]
  | succ n ih =>
    obtain ⟨hal, hau⟩ := abs_le.mp (ih (ha p hp))
    obtain ⟨hbl, hbu⟩ := abs_le.mp (ih (hb p hp))
    obtain ⟨hcl, hcu⟩ := abs_le.mp (hcolumn p hp)
    have hfactor : 0 ≤ (1 + ε) ^ n - 1 := by
      have hpow (m : ℕ) : 1 ≤ (1 + ε) ^ m := by
        induction m with
        | zero => simp
        | succ m hm =>
          rw [pow_succ]
          nlinarith [mul_nonneg hε (by linarith : 0 ≤ (1 + ε) ^ m)]
      linarith [hpow n]
    have hsum := mul_le_mul_of_nonneg_left hcu hfactor
    rw [expand, pow_succ]
    apply abs_le.mpr
    constructor <;> nlinarith

private theorem absolute_expansion
    (a b : M) (W : M → ℝ) (S : Set M)
    (ha : ∀ q ∈ S, a * q ∈ S) (hb : ∀ q ∈ S, b * q ∈ S)
    {e : ℝ} (he : 0 ≤ e)
    (hcolumn : ∀ q ∈ S, |W (a * q) + W (b * q) - W q| ≤ e)
    (n : ℕ) {p : M} (hp : p ∈ S) :
    |expand a b W n p - W p| ≤ ((2 : ℝ) ^ n - 1) * e := by
  induction n generalizing p with
  | zero => simp [expand]
  | succ n ih =>
    obtain ⟨hal, hau⟩ := abs_le.mp (ih (ha p hp))
    obtain ⟨hbl, hbu⟩ := abs_le.mp (ih (hb p hp))
    obtain ⟨hcl, hcu⟩ := abs_le.mp (hcolumn p hp)
    rw [expand, pow_succ]
    apply abs_le.mpr
    constructor <;> nlinarith

private theorem shifted_row
    (a b : M) (W : M → ℝ) (u v w : M)
    (haa : a * a * u = (a * b) * v)
    (hbb : b * b * u = (a * b) * w) (n : ℕ) (p : M) :
    expand a b W 2 ((a * b) ^ n * u * p) =
      W ((a * b) ^ (n + 1) * v * p) +
      2 * W ((a * b) ^ (n + 1) * u * p) +
      W ((a * b) ^ (n + 1) * w * p) := by
  have eaa : a * (a * ((a * b) ^ n * u * p)) =
      (a * b) ^ (n + 1) * v * p := by
    calc
      _ = (a * b) ^ n * (a * a * u) * p := by ac_rfl
      _ = (a * b) ^ n * ((a * b) * v) * p := by rw [haa]
      _ = _ := by rw [pow_succ]; ac_rfl
  have eab : b * (a * ((a * b) ^ n * u * p)) =
      (a * b) ^ (n + 1) * u * p := by rw [pow_succ]; ac_rfl
  have eba : a * (b * ((a * b) ^ n * u * p)) =
      (a * b) ^ (n + 1) * u * p := by rw [pow_succ]; ac_rfl
  have ebb : b * (b * ((a * b) ^ n * u * p)) =
      (a * b) ^ (n + 1) * w * p := by
    calc
      _ = (a * b) ^ n * (b * b * u) * p := by ac_rfl
      _ = (a * b) ^ n * ((a * b) * w) * p := by rw [hbb]
      _ = _ := by rw [pow_succ]; ac_rfl
  simp only [expand, eaa, eab, eba, ebb]
  ring

/-- Construct the four forward slots once for either kind of error budget. -/
private theorem serial_cycle
    (a b : M) (W : M → ℝ) (S : Set M)
    (ha : ∀ q ∈ S, a * q ∈ S) (hb : ∀ q ∈ S, b * q ∈ S)
    (hfour : a ^ 4 = b ^ 4) (hpos : ∀ q ∈ S, 0 ≤ W q)
    (c d : ℝ)
    (hrow : ∀ q ∈ S, |W q - expand a b W 2 q| ≤ c * W q + d)
    {p : M} (hp : p ∈ S) :
    ∃ F : FourCycle c d,
      expand a b W 3 (a * p) = F.x 0 + 3 * F.y 0 + 3 * F.z 0 + F.t 0 ∧
      expand a b W 3 (b * p) = F.x 0 + F.y 0 + 3 * F.z 0 + 3 * F.t 0 := by
  let u : M := a ^ 4
  let v : M := a ^ 3 * b
  let w : M := a ^ 2 * b ^ 2
  let t : M := a * b ^ 3
  have hu : u * p ∈ S := power_mem S a ha 4 hp
  have hv : v * p ∈ S := by
    simpa only [v, mul_assoc] using power_mem S a ha 3 (hb p hp)
  have hw : w * p ∈ S := by
    simpa only [w, mul_assoc] using power_mem S a ha 2 (power_mem S b hb 2 hp)
  have ht : t * p ∈ S := by
    simpa only [t, mul_assoc] using ha _ (power_mem S b hb 3 hp)
  have hab : ∀ q ∈ S, (a * b) * q ∈ S := by
    intro q hq
    simpa only [mul_assoc] using ha _ (hb q hq)
  have mem (n : ℕ) {r : M} (hr : r * p ∈ S) : (a * b) ^ n * r * p ∈ S := by
    simpa only [mul_assoc] using power_mem S (a * b) hab n hr
  let x (n : ℕ) := W ((a * b) ^ n * u * p)
  let y (n : ℕ) := W ((a * b) ^ n * v * p)
  let z (n : ℕ) := W ((a * b) ^ n * w * p)
  let f (n : ℕ) := W ((a * b) ^ n * t * p)
  have aa0 : a * a * u = (a * b) * t := by
    dsimp [u, t]
    rw [hfour]
    simp only [pow_succ, pow_zero, one_mul, mul_one]
    ac_rfl
  have bb0 : b * b * u = (a * b) * v := by
    dsimp [u, v]
    simp only [pow_succ, pow_zero, one_mul, mul_one]
    ac_rfl
  have aa1 : a * a * v = (a * b) * u := by
    dsimp [v, u]
    simp only [pow_succ, pow_zero, one_mul, mul_one]
    ac_rfl
  have bb1 : b * b * v = (a * b) * w := by
    dsimp [v, w]
    simp only [pow_succ, pow_zero, one_mul, mul_one]
    ac_rfl
  have aa2 : a * a * w = (a * b) * v := by
    dsimp [w, v]
    simp only [pow_succ, pow_zero, one_mul, mul_one]
    ac_rfl
  have bb2 : b * b * w = (a * b) * t := by
    dsimp [w, t]
    simp only [pow_succ, pow_zero, one_mul, mul_one]
    ac_rfl
  have aa3 : a * a * t = (a * b) * w := by
    dsimp [t, w]
    simp only [pow_succ, pow_zero, one_mul, mul_one]
    ac_rfl
  have bb3 : b * b * t = (a * b) * u := by
    dsimp [t, u]
    rw [hfour]
    simp only [pow_succ, pow_zero, one_mul, mul_one]
    ac_rfl
  have row (r s t : M) (haa : a * a * r = (a * b) * s)
      (hbb : b * b * r = (a * b) * t) (n : ℕ) (hr : r * p ∈ S) :
      |W ((a * b) ^ n * r * p) -
        (2 * W ((a * b) ^ (n + 1) * r * p) +
          W ((a * b) ^ (n + 1) * s * p) + W ((a * b) ^ (n + 1) * t * p))| ≤
        c * W ((a * b) ^ n * r * p) + d := by
    have h := hrow _ (mem n hr)
    rw [shifted_row a b W r s t haa hbb n p] at h
    convert h using 1 <;> congr 1 <;> ring
  let F : FourCycle c d := {
    x := x, y := y, z := z, t := f
    nonneg := fun n => ⟨hpos _ (mem n hu), hpos _ (mem n hv),
      hpos _ (mem n hw), hpos _ (mem n ht)⟩
    row_x := by
      intro n
      have h := row u t v aa0 bb0 n hu
      change |x n - (2 * x (n + 1) + f (n + 1) + y (n + 1))| ≤ c * x n + d at h
      convert h using 1 <;> congr 1 <;> ring
    row_y := by
      intro n
      have h := row v u w aa1 bb1 n hv
      change |y n - (2 * y (n + 1) + x (n + 1) + z (n + 1))| ≤ c * y n + d at h
      convert h using 1 <;> congr 1 <;> ring
    row_z := by
      intro n
      have h := row w v t aa2 bb2 n hw
      change |z n - (2 * z (n + 1) + y (n + 1) + f (n + 1))| ≤ c * z n + d at h
      convert h using 1 <;> congr 1 <;> ring
    row_t := by
      intro n
      have h := row t w u aa3 bb3 n ht
      change |f n - (2 * f (n + 1) + z (n + 1) + x (n + 1))| ≤ c * f n + d at h
      convert h using 1 <;> congr 1 <;> ring }
  refine ⟨F, ?_, ?_⟩
  · dsimp [F, x, y, z, f, u, v, w, t]
    simp only [expand, pow_zero, one_mul, pow_succ, mul_one,
      mul_assoc, mul_left_comm, mul_comm]
    ring
  · have hlast : W (b ^ 4 * p) = W (a ^ 4 * p) := by rw [hfour]
    dsimp [F, x, y, z, f, u, v, w, t]
    simp only [expand, pow_zero, one_mul, pow_succ, mul_one,
      mul_assoc, mul_left_comm, mul_comm] at hlast ⊢
    linarith

/-- Relative column errors imply a quantitative branch imbalance bound on
every positive forward-closed preparation source. -/
theorem relative_branch_bound
    (a b : M) (W : M → ℝ) (S : Set M)
    (ha : ∀ q ∈ S, a * q ∈ S) (hb : ∀ q ∈ S, b * q ∈ S)
    (hfour : a ^ 4 = b ^ 4) (hpos : ∀ q ∈ S, 0 ≤ W q)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : 2 * ε + ε ^ 2 < 1)
    (hcolumn : ∀ q ∈ S, |W (a * q) + W (b * q) - W q| ≤ ε * W q)
    {p : M} (hp : p ∈ S) :
    |W (a * p) - W (b * p)| ≤ relativeConstant ε * W p := by
  let η := 2 * ε + ε ^ 2
  let R := 2 * η / (1 - η)
  let A := expand a b W 3 (a * p)
  let B := expand a b W 3 (b * p)
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η < 1 := hε1
  have hR0 : 0 ≤ R := by
    dsimp [R]
    exact div_nonneg (mul_nonneg (by norm_num) hη0) (by linarith)
  have hrow (q : M) (hq : q ∈ S) :
      |W q - expand a b W 2 q| ≤ η * W q + 0 := by
    have h := relative_expansion a b W S ha hb hpos hε0 hcolumn 2 hq
    rw [abs_sub_comm] at h
    dsimp [η]
    nlinarith
  obtain ⟨F, hA, hB⟩ := serial_cycle a b W S ha hb hfour hpos η 0 hrow hp
  have hop := relative_opposite_bound hη0 hε1 F
  have htotal : 2 * F.mass 0 ≤ A + B := by
    obtain ⟨hx, hy, hz, ht⟩ := F.nonneg 0
    dsimp [A, B] at *
    dsimp [FourCycle.mass]
    linarith
  have hleaf : |A - B| ≤ R * (A + B) := by
    obtain ⟨hl, hu⟩ := abs_le.mp hop
    have hm := mul_le_mul_of_nonneg_left htotal hR0
    dsimp [A, B, R, FourCycle.difference] at *
    apply abs_le.mpr
    constructor <;> nlinarith
  have hroot := relative_expansion a b W S ha hb hpos hε0 hcolumn 4 hp
  have hrootup : A + B ≤ (1 + ε) ^ 4 * W p := by
    have h := (abs_le.mp hroot).2
    change A + B - W p ≤ ((1 + ε) ^ 4 - 1) * W p at h
    nlinarith
  have hleafup := mul_le_mul_of_nonneg_left hrootup hR0
  have hEA := relative_expansion a b W S ha hb hpos hε0 hcolumn 3 (ha p hp)
  have hEB := relative_expansion a b W S ha hb hpos hε0 hcolumn 3 (hb p hp)
  have hsum := (abs_le.mp (hcolumn p hp)).2
  have hfactor : 0 ≤ (1 + ε) ^ 3 - 1 := by
    nlinarith [pow_nonneg hε0 3, sq_nonneg ε]
  have herr := mul_le_mul_of_nonneg_left hsum hfactor
  obtain ⟨hal, hau⟩ := abs_le.mp hEA
  obtain ⟨hbl, hbu⟩ := abs_le.mp hEB
  obtain ⟨hll, hlu⟩ := abs_le.mp hleaf
  dsimp [A, B] at *
  apply abs_le.mpr
  dsimp [relativeConstant]
  change -(((R * (1 + ε) ^ 4 + (1 + ε) ^ 4 - (1 + ε)) * W p)) ≤
      W (a * p) - W (b * p) ∧
    W (a * p) - W (b * p) ≤
      (R * (1 + ε) ^ 4 + (1 + ε) ^ 4 - (1 + ε)) * W p
  constructor <;> nlinarith

theorem relative_branch_bound_nine
    (a b : M) (W : M → ℝ) (S : Set M)
    (ha : ∀ q ∈ S, a * q ∈ S) (hb : ∀ q ∈ S, b * q ∈ S)
    (hfour : a ^ 4 = b ^ 4) (hpos : ∀ q ∈ S, 0 ≤ W q)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 20)
    (hcolumn : ∀ q ∈ S, |W (a * q) + W (b * q) - W q| ≤ ε * W q)
    {p : M} (hp : p ∈ S) :
    |W (a * p) - W (b * p)| ≤ 9 * ε * W p := by
  have hsmall : 2 * ε + ε ^ 2 < 1 := by
    have h := mul_le_mul_of_nonneg_left hε1 hε0
    nlinarith
  exact (relative_branch_bound a b W S ha hb hfour hpos hε0 hsmall hcolumn hp).trans
    (mul_le_mul_of_nonneg_right (relativeConstant_le_nine hε0 hε1) (hpos p hp))

/-- Absolute error retains its explicit depth parameter. -/
theorem absolute_branch_bound
    (a b : M) (W : M → ℝ) (S : Set M)
    (ha : ∀ q ∈ S, a * q ∈ S) (hb : ∀ q ∈ S, b * q ∈ S)
    (hfour : a ^ 4 = b ^ 4) (hpos : ∀ q ∈ S, 0 ≤ W q)
    {e : ℝ} (he : 0 ≤ e)
    (hcolumn : ∀ q ∈ S, |W (a * q) + W (b * q) - W q| ≤ e)
    {p : M} (hp : p ∈ S) (n : ℕ) :
    |W (a * p) - W (b * p)| ≤
      (W p + 7 * e) / (2 : ℝ) ^ n + 20 * e * (2 : ℝ) ^ n + 2 * e := by
  let A := expand a b W 3 (a * p)
  let B := expand a b W 3 (b * p)
  have hrow (q : M) (hq : q ∈ S) :
      |W q - expand a b W 2 q| ≤ 0 * W q + 3 * e := by
    have h := absolute_expansion a b W S ha hb he hcolumn 2 hq
    rw [abs_sub_comm] at h
    norm_num at h ⊢
    exact h
  obtain ⟨F, hA, hB⟩ := serial_cycle a b W S ha hb hfour hpos 0 (3 * e) hrow hp
  have hop := absolute_opposite_bound he F n
  have htotal : 2 * F.mass 0 ≤ A + B := by
    obtain ⟨hx, hy, hz, ht⟩ := F.nonneg 0
    dsimp [A, B] at *
    dsimp [FourCycle.mass]
    linarith
  have hroot := absolute_expansion a b W S ha hb he hcolumn 4 hp
  have hrootup : A + B ≤ W p + 15 * e := by
    have h := (abs_le.mp hroot).2
    change A + B - W p ≤ ((2 : ℝ) ^ 4 - 1) * e at h
    norm_num at h
    linarith
  have hEA := absolute_expansion a b W S ha hb he hcolumn 3 (ha p hp)
  have hEB := absolute_expansion a b W S ha hb he hcolumn 3 (hb p hp)
  obtain ⟨hal, hau⟩ := abs_le.mp hEA
  obtain ⟨hbl, hbu⟩ := abs_le.mp hEB
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  obtain ⟨hdlo, hdup⟩ := abs_le.mp (le_refl |F.difference 0|)
  have hbranch : |W (a * p) - W (b * p)| ≤ 2 * |F.difference 0| + 14 * e := by
    dsimp [FourCycle.difference] at hdlo hdup ⊢
    norm_num at hal hau hbl hbu
    apply abs_le.mpr
    constructor <;> linarith
  have hmass : (2 * F.mass 0 - 8 * e) / (2 : ℝ) ^ n ≤
      (W p + 7 * e) / (2 : ℝ) ^ n := by
    apply div_le_div_of_nonneg_right _ hpow.le
    linarith
  calc
    |W (a * p) - W (b * p)| ≤ 2 * |F.difference 0| + 14 * e := hbranch
    _ ≤ 2 * ((F.mass 0 - 4 * e) / (2 : ℝ) ^ n +
        10 * e * (2 : ℝ) ^ n - 6 * e) + 14 * e := by linarith
    _ = (2 * F.mass 0 - 8 * e) / (2 : ℝ) ^ n +
        20 * e * (2 : ℝ) ^ n + 2 * e := by ring
    _ ≤ (W p + 7 * e) / (2 : ℝ) ^ n + 20 * e * (2 : ℝ) ^ n + 2 * e := by linarith

end

end IDT.QMClosure.ColumnConservationRobustness
