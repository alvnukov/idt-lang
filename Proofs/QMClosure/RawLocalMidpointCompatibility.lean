import Proofs.QMClosure.RawDyadicMidpointGram

/-!
# Conditional local midpoint compatibility

Dyadic absorption of the three inputs makes local squared Jensen sufficient
for complete-row averaging. A second-order dyadic Jensen error also suffices
when its constant is uniform over the contraction index for each fixed triple.

No topology or arbitrary-real scaling operation on preparations is assumed.
The imported extension from integer Gram tests to real coefficients uses
coefficient-space topology. The unary maps below have only their stated row
laws and are independent of operations in any external native contract.
-/

namespace IDT.QMClosure.RawLocalMidpointCompatibility

open RawMidpointGramGeometry RawDyadicMidpointGram

noncomputable section

variable {V : Type*} {G : V → V → ℝ}

def DyadicallyAbsorbing (H : V → V) (U : V → Prop) : Prop :=
  ∀ x, ∃ M : ℕ, ∀ n : ℕ, M ≤ n → U (halfIterate H n x)

/-- Only the three inputs must belong to U. -/
def LocalSquaredMidpointConvex (G : V → V → ℝ) (mid : V → V → V)
    (U : V → Prop) : Prop :=
  ∀ z x y, U z → U x → U y → squaredDistance G z (mid x y) ≤
    (squaredDistance G z x + squaredDistance G z y) / 2

def DiagonalWeightBall (G : V → V → ℝ) (R : ℝ) (x : V) : Prop :=
  G x x ≤ R

/-- The error constant may depend on the fixed triple, but is uniform in n. -/
def SecondOrderJensenControl (G : V → V → ℝ) (H : V → V)
    (mid : V → V → V) : Prop :=
  ∀ x y z, ∃ K : ℝ, ∀ n : ℕ,
    squaredDistance G z (mid (halfIterate H n x) (halfIterate H n y)) ≤
      (squaredDistance G z (halfIterate H n x) +
        squaredDistance G z (halfIterate H n y)) / 2 +
          ((1 / 2 : ℝ) ^ n) ^ 2 * K

private def midpointSlack (G : V → V → ℝ) (mid : V → V → V)
    (z x y : V) : ℝ :=
  (G x x + G y y) / 2 - G (mid x y) (mid x y) +
    2 * G z (mid x y) - G z x - G z y

private theorem midpointSlack_add_error_nonnegative (mid : V → V → V)
    (z x y : V) (E : ℝ)
    (h : squaredDistance G z (mid x y) ≤
      (squaredDistance G z x + squaredDistance G z y) / 2 + E) :
    0 ≤ midpointSlack G mid z x y + E := by
  dsimp [midpointSlack, squaredDistance] at *
  linarith

private theorem midpointSlack_halfIterate (hsym : ∀ x y, G x y = G y x)
    (H : V → V) (hhalf : ∀ x z, G (H x) z = G x z / 2)
    (mid : V → V → V) (hcompat : HalfMidpointCompatible G H mid)
    (k n : ℕ) (z x y : V) :
    midpointSlack G mid (halfIterate H k z) (halfIterate H n x)
      (halfIterate H n y) =
      ((1 / 2 : ℝ) ^ n) ^ 2 *
        ((G x x + G y y) / 2 - G (mid x y) (mid x y)) +
      (1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ n *
        (2 * G z (mid x y) - G z x - G z y) := by
  have hright (w : V) : G z (halfIterate H n w) =
      (1 / 2 : ℝ) ^ n * G z w := by
    rw [hsym, halfIterate_row H hhalf, hsym w z]
  have hmright : G z (mid (halfIterate H n x) (halfIterate H n y)) =
      (1 / 2 : ℝ) ^ n * G z (mid x y) := by
    rw [hsym, midpoint_halfIterate_row H mid hcompat, hsym (mid x y) z]
  unfold midpointSlack
  rw [halfIterate_kernel hsym H hhalf, halfIterate_kernel hsym H hhalf,
    midpoint_halfIterate_diagonal hsym H mid hcompat]
  simp only [halfIterate_row H hhalf]
  rw [hmright, hright, hright]
  ring

theorem le_zero_of_eventually_le_dyadic_mul (M : ℕ) (C delta : ℝ)
    (h : ∀ n : ℕ, M ≤ n → delta ≤ (1 / 2 : ℝ) ^ n * C) : delta ≤ 0 := by
  apply le_zero_of_le_dyadic_mul ((1 / 2 : ℝ) ^ M * C) delta
  intro j
  calc
    delta ≤ (1 / 2 : ℝ) ^ (M + j) * C := h (M + j) (by omega)
    _ = (1 / 2 : ℝ) ^ j * ((1 / 2 : ℝ) ^ M * C) := by
      rw [pow_add]
      ring

/-- A fixed contracted reference and its contracted antiphase row suffice.
The endpoints may be contracted arbitrarily deeply inside the absorbing set. -/
theorem midpointRowAverage_of_localSquaredMidpointConvex
    (hsym : ∀ x y, G x y = G y x) (H N : V → V)
    (hhalf : ∀ x z, G (H x) z = G x z / 2)
    (hneg : ∀ x z, G (N x) z = -G x z)
    (mid : V → V → V) (hcompat : HalfMidpointCompatible G H mid)
    (U : V → Prop) (habsorb : DyadicallyAbsorbing H U)
    (hconv : LocalSquaredMidpointConvex G mid U) : MidpointRowAverage G mid := by
  intro x y z
  obtain ⟨kz, hkz⟩ := habsorb z
  obtain ⟨kn, hkn⟩ := habsorb (N z)
  obtain ⟨mx, hmx⟩ := habsorb x
  obtain ⟨my, hmy⟩ := habsorb y
  let k := max kz kn
  let M := max mx my
  let C := (G x x + G y y) / 2 - G (mid x y) (mid x y)
  let delta := 2 * G z (mid x y) - G z x - G z y
  have hz : U (halfIterate H k z) := hkz k (le_max_left _ _)
  have hnz : U (halfIterate H k (N z)) := hkn k (le_max_right _ _)
  have hx (n : ℕ) (hn : M ≤ n) : U (halfIterate H n x) :=
    hmx n (le_trans (le_max_left _ _) hn)
  have hy (n : ℕ) (hn : M ≤ n) : U (halfIterate H n y) :=
    hmy n (le_trans (le_max_right _ _) hn)
  have hplus (n : ℕ) (hn : M ≤ n) :
      0 ≤ ((1 / 2 : ℝ) ^ n) ^ 2 * C +
        (1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ n * delta := by
    have ht := midpointSlack_add_error_nonnegative mid
      (halfIterate H k z) (halfIterate H n x) (halfIterate H n y) 0
      (by simpa using hconv _ _ _ hz (hx n hn) (hy n hn))
    rw [midpointSlack_halfIterate hsym H hhalf mid hcompat] at ht
    simpa only [add_zero, C, delta] using ht
  have hminus (n : ℕ) (hn : M ≤ n) :
      0 ≤ ((1 / 2 : ℝ) ^ n) ^ 2 * C -
        (1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ n * delta := by
    have ht := midpointSlack_add_error_nonnegative mid
      (halfIterate H k (N z)) (halfIterate H n x) (halfIterate H n y) 0
      (by simpa using hconv _ _ _ hnz (hx n hn) (hy n hn))
    rw [midpointSlack_halfIterate hsym H hhalf mid hcompat] at ht
    simp only [hneg, add_zero] at ht
    dsimp [C, delta]
    nlinarith
  have hkpos : 0 < (1 / 2 : ℝ) ^ k := pow_pos (by norm_num) k
  have hup (n : ℕ) (hn : M ≤ n) :
      delta ≤ (1 / 2 : ℝ) ^ n * (C / (1 / 2 : ℝ) ^ k) := by
    have hstep : (1 / 2 : ℝ) ^ k * delta ≤ (1 / 2 : ℝ) ^ n * C := by
      apply le_of_mul_le_mul_left (a := (1 / 2 : ℝ) ^ n) ?_
        (pow_pos (by norm_num) n)
      nlinarith [hminus n hn]
    calc
      delta ≤ ((1 / 2 : ℝ) ^ n * C) / (1 / 2 : ℝ) ^ k :=
        (le_div_iff₀ hkpos).2 (by nlinarith [hstep])
      _ = (1 / 2 : ℝ) ^ n * (C / (1 / 2 : ℝ) ^ k) := by ring
  have hlo (n : ℕ) (hn : M ≤ n) :
      -delta ≤ (1 / 2 : ℝ) ^ n * (C / (1 / 2 : ℝ) ^ k) := by
    have hstep : (1 / 2 : ℝ) ^ k * (-delta) ≤ (1 / 2 : ℝ) ^ n * C := by
      apply le_of_mul_le_mul_left (a := (1 / 2 : ℝ) ^ n) ?_
        (pow_pos (by norm_num) n)
      nlinarith [hplus n hn]
    calc
      -delta ≤ ((1 / 2 : ℝ) ^ n * C) / (1 / 2 : ℝ) ^ k :=
        (le_div_iff₀ hkpos).2 (by nlinarith [hstep])
      _ = (1 / 2 : ℝ) ^ n * (C / (1 / 2 : ℝ) ^ k) := by ring
  have hd : delta = 0 := by
    have hu := le_zero_of_eventually_le_dyadic_mul M _ delta hup
    have hl := le_zero_of_eventually_le_dyadic_mul M _ (-delta) hlo
    linarith
  dsimp [delta] at hd
  rw [hsym z (mid x y), hsym z x, hsym z y] at hd
  linarith

theorem localSquaredMidpointConvex_iff_midpointRowAverage
    (hsym : ∀ x y, G x y = G y x) (H N : V → V)
    (hhalf : ∀ x z, G (H x) z = G x z / 2)
    (hneg : ∀ x z, G (N x) z = -G x z)
    (hnonneg : NonnegativeSquaredDistances G) (mid : V → V → V)
    (hcompat : HalfMidpointCompatible G H mid)
    (U : V → Prop) (habsorb : DyadicallyAbsorbing H U) :
    LocalSquaredMidpointConvex G mid U ↔ MidpointRowAverage G mid := by
  constructor
  · exact midpointRowAverage_of_localSquaredMidpointConvex hsym H N hhalf hneg
      mid hcompat U habsorb
  · intro hrow z x y _ _ _
    exact squaredMidpointConvex_of_midpointRowAverage hsym hnonneg mid hrow z x y

private theorem dyadic_pow_le_one (n : ℕ) : (1 / 2 : ℝ) ^ n ≤ 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]

/-- Every strictly positive diagonal-weight ball eventually contains each
dyadic ray. This is an Archimedean real-power argument. -/
theorem dyadicallyAbsorbing_diagonalWeightBall
    (hsym : ∀ x y, G x y = G y x) (H : V → V)
    (hhalf : ∀ x z, G (H x) z = G x z / 2)
    (hnonneg : NonnegativeSquaredDistances G) (R : ℝ) (hR : 0 < R) :
    DyadicallyAbsorbing H (DiagonalWeightBall G R) := by
  intro x
  have hd : 0 ≤ G x x := RawDyadicMidpointGram.diagonal_nonnegative hsym H hhalf
    hnonneg x
  have hdpos : 0 < G x x + 1 := by linarith
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (div_pos hR hdpos)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hbound : (1 / 2 : ℝ) ^ M * (G x x + 1) < R :=
    (lt_div_iff₀ hdpos).mp hM
  refine ⟨M, ?_⟩
  intro n hn
  have heq : n = M + (n - M) := by omega
  have hmono : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ M := by
    rw [heq, pow_add]
    have ht := mul_le_mul_of_nonneg_left (dyadic_pow_le_one (n - M))
      (le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) M))
    simpa only [mul_one] using ht
  have hnpos : 0 ≤ (1 / 2 : ℝ) ^ n := le_of_lt (pow_pos (by norm_num) n)
  have hsquare : ((1 / 2 : ℝ) ^ n) ^ 2 ≤ (1 / 2 : ℝ) ^ n := by
    nlinarith [dyadic_pow_le_one n]
  have hscaled := mul_le_mul_of_nonneg_right hsquare hd
  have hscaledmono := mul_le_mul_of_nonneg_right hmono hd
  unfold DiagonalWeightBall
  rw [halfIterate_kernel hsym H hhalf]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) M]

theorem midpointRowAverage_of_weightBallSquaredMidpointConvex
    (hsym : ∀ x y, G x y = G y x) (H N : V → V)
    (hhalf : ∀ x z, G (H x) z = G x z / 2)
    (hneg : ∀ x z, G (N x) z = -G x z)
    (hnonneg : NonnegativeSquaredDistances G) (mid : V → V → V)
    (hcompat : HalfMidpointCompatible G H mid) (R : ℝ) (hR : 0 < R)
    (hconv : LocalSquaredMidpointConvex G mid (DiagonalWeightBall G R)) :
    MidpointRowAverage G mid :=
  midpointRowAverage_of_localSquaredMidpointConvex hsym H N hhalf hneg mid hcompat
    (DiagonalWeightBall G R)
    (dyadicallyAbsorbing_diagonalWeightBall hsym H hhalf hnonneg R hR) hconv

theorem midpointRowAverage_of_secondOrderJensenControl
    (hsym : ∀ x y, G x y = G y x) (H N : V → V)
    (hhalf : ∀ x z, G (H x) z = G x z / 2)
    (hneg : ∀ x z, G (N x) z = -G x z)
    (mid : V → V → V) (hcompat : HalfMidpointCompatible G H mid)
    (hcontrol : SecondOrderJensenControl G H mid) : MidpointRowAverage G mid := by
  intro x y z
  obtain ⟨Kplus, hplus⟩ := hcontrol x y z
  obtain ⟨Kminus, hminus⟩ := hcontrol x y (N z)
  let C := (G x x + G y y) / 2 - G (mid x y) (mid x y)
  let delta := 2 * G z (mid x y) - G z x - G z y
  have hp (n : ℕ) : 0 ≤ ((1 / 2 : ℝ) ^ n) ^ 2 * (C + Kplus) +
      (1 / 2 : ℝ) ^ n * delta := by
    have ht := midpointSlack_add_error_nonnegative mid z
      (halfIterate H n x) (halfIterate H n y)
      (((1 / 2 : ℝ) ^ n) ^ 2 * Kplus) (hplus n)
    have he := midpointSlack_halfIterate hsym H hhalf mid hcompat 0 n z x y
    simp only [halfIterate, pow_zero, one_mul] at he
    rw [he] at ht
    dsimp [C, delta]
    nlinarith
  have hm (n : ℕ) : 0 ≤ ((1 / 2 : ℝ) ^ n) ^ 2 * (C + Kminus) -
      (1 / 2 : ℝ) ^ n * delta := by
    have ht := midpointSlack_add_error_nonnegative mid (N z)
      (halfIterate H n x) (halfIterate H n y)
      (((1 / 2 : ℝ) ^ n) ^ 2 * Kminus) (hminus n)
    have he := midpointSlack_halfIterate hsym H hhalf mid hcompat 0 n (N z) x y
    simp only [halfIterate, pow_zero, one_mul, hneg] at he
    rw [he] at ht
    dsimp [C, delta]
    nlinarith
  have hup (n : ℕ) : delta ≤ (1 / 2 : ℝ) ^ n * (C + Kminus) := by
    apply le_of_mul_le_mul_left (a := (1 / 2 : ℝ) ^ n) ?_
      (pow_pos (by norm_num) n)
    nlinarith [hm n]
  have hlo (n : ℕ) : -delta ≤ (1 / 2 : ℝ) ^ n * (C + Kplus) := by
    apply le_of_mul_le_mul_left (a := (1 / 2 : ℝ) ^ n) ?_
      (pow_pos (by norm_num) n)
    nlinarith [hp n]
  have hd : delta = 0 := by
    have hu := le_zero_of_le_dyadic_mul (C + Kminus) delta hup
    have hl := le_zero_of_le_dyadic_mul (C + Kplus) (-delta) hlo
    linarith
  dsimp [delta] at hd
  rw [hsym z (mid x y), hsym z x, hsym z y] at hd
  linarith

theorem secondOrderJensenControl_iff_midpointRowAverage
    (hsym : ∀ x y, G x y = G y x) (H N : V → V)
    (hhalf : ∀ x z, G (H x) z = G x z / 2)
    (hneg : ∀ x z, G (N x) z = -G x z)
    (hnonneg : NonnegativeSquaredDistances G) (mid : V → V → V)
    (hcompat : HalfMidpointCompatible G H mid) :
    SecondOrderJensenControl G H mid ↔ MidpointRowAverage G mid := by
  constructor
  · exact midpointRowAverage_of_secondOrderJensenControl hsym H N hhalf hneg mid
      hcompat
  · intro hrow x y z
    refine ⟨0, ?_⟩
    intro n
    simpa only [mul_zero, add_zero] using
      squaredMidpointConvex_of_midpointRowAverage hsym hnonneg mid hrow z
        (halfIterate H n x) (halfIterate H n y)

theorem gramNonnegative_of_localSquaredMidpointConvex
    (hsym : ∀ x y, G x y = G y x) (H N : V → V)
    (hhalf : ∀ x z, G (H x) z = G x z / 2)
    (hneg : ∀ x z, G (N x) z = -G x z)
    (hnonneg : NonnegativeSquaredDistances G) (mid : V → V → V)
    (hcompat : HalfMidpointCompatible G H mid)
    (U : V → Prop) (habsorb : DyadicallyAbsorbing H U)
    (hconv : LocalSquaredMidpointConvex G mid U) :
    ∀ n, RawGramGeometry.GramNonnegative G n :=
  RawDyadicMidpointGram.gramNonnegative_of_midpointRowAverage hsym H N hhalf hneg
    hnonneg mid (midpointRowAverage_of_localSquaredMidpointConvex hsym H N hhalf hneg
      mid hcompat U habsorb hconv)

theorem gramNonnegative_of_weightBallSquaredMidpointConvex
    (hsym : ∀ x y, G x y = G y x) (H N : V → V)
    (hhalf : ∀ x z, G (H x) z = G x z / 2)
    (hneg : ∀ x z, G (N x) z = -G x z)
    (hnonneg : NonnegativeSquaredDistances G) (mid : V → V → V)
    (hcompat : HalfMidpointCompatible G H mid) (R : ℝ) (hR : 0 < R)
    (hconv : LocalSquaredMidpointConvex G mid (DiagonalWeightBall G R)) :
    ∀ n, RawGramGeometry.GramNonnegative G n :=
  RawDyadicMidpointGram.gramNonnegative_of_midpointRowAverage hsym H N hhalf hneg
    hnonneg mid (midpointRowAverage_of_weightBallSquaredMidpointConvex hsym H N hhalf
      hneg hnonneg mid hcompat R hR hconv)

theorem gramNonnegative_of_secondOrderJensenControl
    (hsym : ∀ x y, G x y = G y x) (H N : V → V)
    (hhalf : ∀ x z, G (H x) z = G x z / 2)
    (hneg : ∀ x z, G (N x) z = -G x z)
    (hnonneg : NonnegativeSquaredDistances G) (mid : V → V → V)
    (hcompat : HalfMidpointCompatible G H mid)
    (hcontrol : SecondOrderJensenControl G H mid) :
    ∀ n, RawGramGeometry.GramNonnegative G n :=
  RawDyadicMidpointGram.gramNonnegative_of_midpointRowAverage hsym H N hhalf hneg
    hnonneg mid (midpointRowAverage_of_secondOrderJensenControl hsym H N hhalf hneg
      mid hcompat hcontrol)

open RawSparseConservationSelection RawFourPointGramBridge

theorem conclusions_of_localSquaredMidpointConvex (D : Contract V) (G : V → V → ℝ)
    (hk : LocalKernel D G) (H N : V → V)
    (hhalf : ∀ x z, G (H x) z = G x z / 2)
    (hneg : ∀ x z, G (N x) z = -G x z)
    (hnonneg : NonnegativeSquaredDistances G) (mid : V → V → V)
    (hcompat : HalfMidpointCompatible G H mid)
    (U : V → Prop) (habsorb : DyadicallyAbsorbing H U)
    (hconv : LocalSquaredMidpointConvex G mid U) :
    (∀ n, RawGramGeometry.GramNonnegative G n) ∧
      (∀ x, 0 ≤ D.weight x) ∧ PairConserved D ∧ ObservedMedial D ∧
      SparseMarginalLaw D ∧ RawSparseConservationTests.Tests D := by
  have hgram := gramNonnegative_of_localSquaredMidpointConvex hk.symmetric H N
    hhalf hneg hnonneg mid hcompat U habsorb hconv
  exact ⟨hgram, conclusions_of_fourPointPositive D G hk (hgram 4)⟩

theorem conclusions_of_secondOrderJensenControl (D : Contract V) (G : V → V → ℝ)
    (hk : LocalKernel D G) (H N : V → V)
    (hhalf : ∀ x z, G (H x) z = G x z / 2)
    (hneg : ∀ x z, G (N x) z = -G x z)
    (hnonneg : NonnegativeSquaredDistances G) (mid : V → V → V)
    (hcompat : HalfMidpointCompatible G H mid)
    (hcontrol : SecondOrderJensenControl G H mid) :
    (∀ n, RawGramGeometry.GramNonnegative G n) ∧
      (∀ x, 0 ≤ D.weight x) ∧ PairConserved D ∧ ObservedMedial D ∧
      SparseMarginalLaw D ∧ RawSparseConservationTests.Tests D := by
  have hgram := gramNonnegative_of_secondOrderJensenControl hk.symmetric H N
    hhalf hneg hnonneg mid hcompat hcontrol
  exact ⟨hgram, conclusions_of_fourPointPositive D G hk (hgram 4)⟩

end

end IDT.QMClosure.RawLocalMidpointCompatibility
