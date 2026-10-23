import Mathlib

namespace IDT.QMClosure.QuarticContextTransport

noncomputable section

/-!
Separable quartic coordinates obtained by transporting supplied real quadratic
geometry. This is a coordinate countermodel, not an inequivalent physical theory
and not a derivation of the carrier, accessible operations, or coherent merge.
-/

def phi (x : ℝ) : ℝ := x * |x|
def psi (y : ℝ) : ℝ := Real.sqrt y - Real.sqrt (-y)

@[simp] theorem psi_phi (x : ℝ) : psi (phi x) = x := by
  by_cases hx : 0 ≤ x
  · have h : phi x = x ^ 2 := by simp [phi, abs_of_nonneg hx, pow_two]
    rw [h, psi, Real.sqrt_sq hx, Real.sqrt_eq_zero_of_nonpos (neg_nonpos.mpr (sq_nonneg x))]
    ring
  · have hn : x ≤ 0 := le_of_not_ge hx
    have h : phi x = -(x ^ 2) := by simp [phi, abs_of_nonpos hn]; ring
    rw [h, psi, Real.sqrt_eq_zero_of_nonpos (neg_nonpos.mpr (sq_nonneg x)), neg_neg,
      Real.sqrt_sq_eq_abs, abs_of_nonpos hn]
    ring

@[simp] theorem phi_psi (y : ℝ) : phi (psi y) = y := by
  by_cases hy : 0 ≤ y
  · simp only [psi, Real.sqrt_eq_zero_of_nonpos (neg_nonpos.mpr hy), sub_zero]
    rw [phi, abs_of_nonneg (Real.sqrt_nonneg _), ← pow_two, Real.sq_sqrt hy]
  · have hn : 0 ≤ -y := by linarith
    simp only [psi, Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hy), zero_sub]
    rw [phi, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sq_sqrt hn]

theorem phi_mul (x y : ℝ) : phi (x * y) = phi x * phi y := by
  simp only [phi, abs_mul]
  ring

theorem psi_mul (x y : ℝ) : psi (x * y) = psi x * psi y := by
  calc
    psi (x * y) = psi (phi (psi x) * phi (psi y)) := by simp
    _ = psi (phi (psi x * psi y)) := by rw [phi_mul]
    _ = _ := psi_phi _

theorem phi_sq (x : ℝ) : phi x ^ 2 = x ^ 4 := by
  unfold phi
  rw [mul_pow, sq_abs]
  ring

theorem continuous_phi : Continuous phi := by unfold phi; fun_prop
theorem continuous_psi : Continuous psi := by unfold psi; fun_prop

def encode {ι : Type*} (x : ι → ℝ) : ι → ℝ := fun i => phi (x i)
def decode {ι : Type*} (x : ι → ℝ) : ι → ℝ := fun i => psi (x i)

@[simp] theorem encode_decode {ι : Type*} (x : ι → ℝ) : encode (decode x) = x := by
  funext i; exact phi_psi (x i)
@[simp] theorem decode_encode {ι : Type*} (x : ι → ℝ) : decode (encode x) = x := by
  funext i; exact psi_phi (x i)

def q4 {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := ∑ i, x i ^ 4
def q2 {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := ∑ i, x i ^ 2

theorem q2_encode {ι : Type*} [Fintype ι] (x : ι → ℝ) : q2 (encode x) = q4 x := by
  simp only [q2, q4, encode, phi_sq]

def transport {ι : Type*} (U : (ι → ℝ) → (ι → ℝ)) (x : ι → ℝ) : ι → ℝ :=
  decode (U (encode x))

theorem transport_preserves_q4 {ι : Type*} [Fintype ι]
    (U : (ι → ℝ) → (ι → ℝ)) (hU : ∀ x, q2 (U x) = q2 x) (x : ι → ℝ) :
    q4 (transport U x) = q4 x := by
  rw [← q2_encode, transport, encode_decode, hU, q2_encode]

theorem transport_inverse {ι : Type*} (U V : (ι → ℝ) → (ι → ℝ))
    (h : ∀ x, V (U x) = x) (x : ι → ℝ) : transport V (transport U x) = x := by
  simp [transport, h]

theorem transport_continuous {ι : Type*} (U : (ι → ℝ) → (ι → ℝ))
    (hU : Continuous U) : Continuous (transport U) := by
  have he : Continuous (encode : (ι → ℝ) → (ι → ℝ)) :=
    continuous_pi fun i => continuous_phi.comp (continuous_apply i)
  have hd : Continuous (decode : (ι → ℝ) → (ι → ℝ)) :=
    continuous_pi fun i => continuous_psi.comp (continuous_apply i)
  exact hd.comp (hU.comp he)

def coherentMerge {ι : Type*} (x y : ι → ℝ) : ι → ℝ := decode (encode x + encode y)

theorem transport_preserves_transported_merge {ι : Type*}
    (U : (ι → ℝ) → (ι → ℝ)) (hU : ∀ x y, U (x + y) = U x + U y)
    (x y : ι → ℝ) :
    transport U (coherentMerge x y) = coherentMerge (transport U x) (transport U y) := by
  simp [transport, coherentMerge, hU]

/-! Finite joint tables. Right action is rowwise; left action is columnwise.
The coefficients below are supplied real matrices, not reconstructed dynamics. -/

def rightAction {ι κ : Type*} [Fintype κ] (R : κ → κ → ℝ)
    (T : ι → κ → ℝ) : ι → κ → ℝ :=
  fun i j => psi (∑ k, R j k * phi (T i k))

def leftAction {ι κ : Type*} [Fintype ι] (L : ι → ι → ℝ)
    (T : ι → κ → ℝ) : ι → κ → ℝ :=
  fun i j => psi (∑ k, L i k * phi (T k j))

def PreservesSquares {ι : Type*} [Fintype ι] (U : ι → ι → ℝ) : Prop :=
  ∀ x : ι → ℝ, (∑ i, (∑ k, U i k * x k) ^ 2) = ∑ i, x i ^ 2

theorem right_action_continuous {ι κ : Type*} [Fintype κ] (R : κ → κ → ℝ) :
    Continuous (rightAction (ι := ι) R) := by
  have hp := continuous_phi
  have hs := continuous_psi
  unfold rightAction
  fun_prop

theorem left_action_continuous {ι κ : Type*} [Fintype ι] (L : ι → ι → ℝ) :
    Continuous (leftAction (κ := κ) L) := by
  have hp := continuous_phi
  have hs := continuous_psi
  unfold leftAction
  fun_prop

theorem right_action_inverse {ι κ : Type*} [Fintype κ]
    (R S : κ → κ → ℝ)
    (hRS : ∀ (v : κ → ℝ) j, (∑ k, S j k * (∑ l, R k l * v l)) = v j)
    (T : ι → κ → ℝ) : rightAction S (rightAction R T) = T := by
  funext i j
  simp only [rightAction, phi_psi]
  rw [hRS, psi_phi]

theorem left_action_inverse {ι κ : Type*} [Fintype ι]
    (L M : ι → ι → ℝ)
    (hLM : ∀ (v : ι → ℝ) i, (∑ k, M i k * (∑ l, L k l * v l)) = v i)
    (T : ι → κ → ℝ) : leftAction M (leftAction L T) = T := by
  funext i j
  simp only [leftAction, phi_psi]
  rw [hLM, psi_phi]

theorem right_preserves_row_q4 {ι κ : Type*} [Fintype κ]
    (R : κ → κ → ℝ) (hR : PreservesSquares R) (T : ι → κ → ℝ) (i : ι) :
    (∑ j, rightAction R T i j ^ 4) = ∑ j, T i j ^ 4 := by
  have h := hR (fun j => phi (T i j))
  simpa only [← phi_sq, rightAction, phi_psi] using h

theorem left_preserves_column_q4 {ι κ : Type*} [Fintype ι]
    (L : ι → ι → ℝ) (hL : PreservesSquares L) (T : ι → κ → ℝ) (j : κ) :
    (∑ i, leftAction L T i j ^ 4) = ∑ i, T i j ^ 4 := by
  have h := hL (fun i => phi (T i j))
  simpa only [← phi_sq, leftAction, phi_psi] using h

theorem right_action_rank_one {ι κ : Type*} [Fintype κ]
    (R : κ → κ → ℝ) (a : ι → ℝ) (b : κ → ℝ) :
    rightAction R (fun i j => a i * b j) =
      fun i j => a i * transport (fun v j => ∑ k, R j k * v k) b j := by
  funext i j
  simp only [rightAction, phi_mul, transport, decode, encode]
  have h : (∑ k, R j k * (phi (a i) * phi (b k))) =
      phi (a i) * ∑ k, R j k * phi (b k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [h, psi_mul, psi_phi]

theorem left_action_rank_one {ι κ : Type*} [Fintype ι]
    (L : ι → ι → ℝ) (a : ι → ℝ) (b : κ → ℝ) :
    leftAction L (fun i j => a i * b j) =
      fun i j => transport (fun v i => ∑ k, L i k * v k) a i * b j := by
  funext i j
  simp only [leftAction, phi_mul, transport, decode, encode]
  have h : (∑ k, L i k * (phi (a k) * phi (b j))) =
      (∑ k, L i k * phi (a k)) * phi (b j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [h, psi_mul, psi_phi]

theorem independent_product_actions {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : ι → ι → ℝ) (R : κ → κ → ℝ) (a : ι → ℝ) (b : κ → ℝ) :
    leftAction L (rightAction R (fun i j => a i * b j)) =
      fun i j => transport (fun v i => ∑ k, L i k * v k) a i *
        transport (fun v j => ∑ k, R j k * v k) b j := by
  rw [right_action_rank_one, left_action_rank_one]

theorem local_actions_commute {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : ι → ι → ℝ) (R : κ → κ → ℝ) (T : ι → κ → ℝ) :
    leftAction L (rightAction R T) = rightAction R (leftAction L T) := by
  funext i j
  simp only [leftAction, rightAction, phi_psi]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

def totalQ4 {ι κ : Type*} [Fintype ι] [Fintype κ] (T : ι → κ → ℝ) : ℝ :=
  ∑ i, ∑ j, T i j ^ 4

def jointProbability {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : ι → κ → ℝ) (i : ι) (j : κ) : ℝ := T i j ^ 4 / totalQ4 T

theorem right_preserves_total {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : κ → κ → ℝ) (hR : PreservesSquares R) (T : ι → κ → ℝ) :
    totalQ4 (rightAction R T) = totalQ4 T := by
  unfold totalQ4
  exact Finset.sum_congr rfl (fun i _ => right_preserves_row_q4 R hR T i)

theorem right_preserves_normalized_row {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : κ → κ → ℝ) (hR : PreservesSquares R) (T : ι → κ → ℝ) (i : ι) :
    (∑ j, jointProbability (rightAction R T) i j) = ∑ j, jointProbability T i j := by
  simp only [jointProbability, ← Finset.sum_div, right_preserves_total R hR,
    right_preserves_row_q4 R hR]

theorem left_preserves_total {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : ι → ι → ℝ) (hL : PreservesSquares L) (T : ι → κ → ℝ) :
    totalQ4 (leftAction L T) = totalQ4 T := by
  unfold totalQ4
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => T i j ^ 4)]
  exact Finset.sum_congr rfl (fun j _ => left_preserves_column_q4 L hL T j)

theorem left_preserves_normalized_column {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : ι → ι → ℝ) (hL : PreservesSquares L) (T : ι → κ → ℝ) (j : κ) :
    (∑ i, jointProbability (leftAction L T) i j) = ∑ i, jointProbability T i j := by
  simp only [jointProbability, ← Finset.sum_div, left_preserves_total L hL,
    left_preserves_column_q4 L hL]

theorem joint_probability_normalized {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : ι → κ → ℝ) (hT : totalQ4 T ≠ 0) :
    (∑ i, ∑ j, jointProbability T i j) = 1 := by
  simp only [jointProbability, ← Finset.sum_div]
  exact div_self hT

theorem joint_probability_nonnegative {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : ι → κ → ℝ) (i : ι) (j : κ) : 0 ≤ jointProbability T i j := by
  unfold jointProbability totalQ4
  positivity

/-- No-signalling for this declared operation/readout family at a nonzero state.
This does not quantify over arbitrary enlarged operation families. -/
theorem declared_family_no_signalling {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : ι → ι → ℝ) (R : κ → κ → ℝ)
    (hL : PreservesSquares L) (hR : PreservesSquares R)
    (T : ι → κ → ℝ) (hT : 0 < totalQ4 T) :
    (∑ i, ∑ j, jointProbability T i j) = 1 ∧
    (∀ i, (∑ j, jointProbability (rightAction R T) i j) = ∑ j, jointProbability T i j) ∧
    (∀ j, (∑ i, jointProbability (leftAction L T) i j) = ∑ i, jointProbability T i j) := by
  exact ⟨joint_probability_normalized T (ne_of_gt hT),
    right_preserves_normalized_row R hR T, left_preserves_normalized_column L hL T⟩

theorem rank_one_total {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (b : κ → ℝ) : totalQ4 (fun i j => a i * b j) = q4 a * q4 b := by
  unfold totalQ4 q4
  simp_rw [mul_pow, ← Finset.mul_sum]
  rw [← Finset.sum_mul]

theorem rank_one_probability {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (b : κ → ℝ) (i : ι) (j : κ) :
    jointProbability (fun i j => a i * b j) i j =
      (a i ^ 4 / q4 a) * (b j ^ 4 / q4 b) := by
  rw [jointProbability, rank_one_total, mul_pow, mul_div_mul_comm]

/-! A genuine two-dimensional mixing family, not just abstract hypotheses. -/

abbrev Plane := ℝ × ℝ
def planeEncode (v : Plane) : Plane := (phi v.1, phi v.2)
def planeDecode (v : Plane) : Plane := (psi v.1, psi v.2)
def planeQ4 (v : Plane) : ℝ := v.1 ^ 4 + v.2 ^ 4
def rotate (a b : ℝ) (v : Plane) : Plane := (a * v.1 - b * v.2, b * v.1 + a * v.2)
def quarticRotate (a b : ℝ) (v : Plane) : Plane := planeDecode (rotate a b (planeEncode v))

@[simp] theorem plane_encode_decode (v : Plane) : planeEncode (planeDecode v) = v := by
  apply Prod.ext <;> simp [planeEncode, planeDecode]
@[simp] theorem plane_decode_encode (v : Plane) : planeDecode (planeEncode v) = v := by
  apply Prod.ext <;> simp [planeEncode, planeDecode]

theorem psi_phi_mul (t z : ℝ) : psi (phi t * z) = t * psi z := by
  rw [psi_mul, psi_phi]

/-- Homogeneity is for all real scalars, not merely positive ones. -/
theorem quartic_rotation_homogeneous (a b t : ℝ) (v : Plane) :
    quarticRotate a b (t • v) = t • quarticRotate a b v := by
  apply Prod.ext
  · change psi (a * phi (t * v.1) - b * phi (t * v.2)) =
      t * psi (a * phi v.1 - b * phi v.2)
    rw [phi_mul, phi_mul]
    have h : a * (phi t * phi v.1) - b * (phi t * phi v.2) =
        phi t * (a * phi v.1 - b * phi v.2) := by ring
    rw [h, psi_phi_mul]
  · change psi (b * phi (t * v.1) + a * phi (t * v.2)) =
      t * psi (b * phi v.1 + a * phi v.2)
    rw [phi_mul, phi_mul]
    have h : b * (phi t * phi v.1) + a * (phi t * phi v.2) =
        phi t * (b * phi v.1 + a * phi v.2) := by ring
    rw [h, psi_phi_mul]

theorem quartic_rotation_preserves_q4 (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (v : Plane) :
    planeQ4 (quarticRotate a b v) = planeQ4 v := by
  have h : ∀ z : ℝ, psi z ^ 4 = z ^ 2 := fun z => by rw [← phi_sq, phi_psi]
  simp only [planeQ4, quarticRotate, planeDecode, rotate, planeEncode, h]
  calc
    _ = (a ^ 2 + b ^ 2) * (phi v.1 ^ 2 + phi v.2 ^ 2) := by ring
    _ = _ := by rw [hab, one_mul, phi_sq, phi_sq]

theorem quartic_rotation_inverse (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (v : Plane) :
    quarticRotate a (-b) (quarticRotate a b v) = v := by
  have hx := congrArg (fun z : ℝ => z * phi v.1) hab
  have hy := congrArg (fun z : ℝ => z * phi v.2) hab
  have h : rotate a (-b) (rotate a b (planeEncode v)) = planeEncode v := by
    apply Prod.ext <;> simp [rotate, planeEncode] <;> nlinarith [hx, hy]
  simp only [quarticRotate, plane_encode_decode, h, plane_decode_encode]

theorem quartic_rotation_jointly_continuous :
    Continuous (fun z : ℝ × ℝ × Plane => quarticRotate z.1 z.2.1 z.2.2) := by
  unfold quarticRotate planeDecode rotate planeEncode
  have hp := continuous_phi
  have hs := continuous_psi
  fun_prop

theorem continuous_reversible_rotation_family :
    Continuous (fun z : ℝ × Plane => quarticRotate (Real.cos z.1) (Real.sin z.1) z.2) ∧
    (∀ t v, quarticRotate (Real.cos t) (-Real.sin t)
      (quarticRotate (Real.cos t) (Real.sin t) v) = v) := by
  constructor
  · have hmap : Continuous (fun z : ℝ × Plane => (Real.cos z.1, Real.sin z.1, z.2)) := by
      fun_prop
    exact quartic_rotation_jointly_continuous.comp hmap
  · intro t v
    apply quartic_rotation_inverse
    nlinarith [Real.sin_sq_add_cos_sq t]

def rationalRotation : Fin 2 → Fin 2 → ℝ :=
  !![(3 / 5 : ℝ), -(4 / 5 : ℝ); (4 / 5 : ℝ), (3 / 5 : ℝ)]

theorem rational_rotation_preserves_squares : PreservesSquares rationalRotation := by
  intro x
  simp [rationalRotation, Fin.sum_univ_two]
  ring

def rationalInverse : Fin 2 → Fin 2 → ℝ :=
  !![(3 / 5 : ℝ), (4 / 5 : ℝ); -(4 / 5 : ℝ), (3 / 5 : ℝ)]

theorem rational_rotation_inverse (v : Fin 2 → ℝ) (j : Fin 2) :
    (∑ k, rationalInverse j k * (∑ l, rationalRotation k l * v l)) = v j := by
  fin_cases j <;> simp [rationalInverse, rationalRotation, Fin.sum_univ_two] <;> ring

theorem rational_inverse_rotation (v : Fin 2 → ℝ) (j : Fin 2) :
    (∑ k, rationalRotation j k * (∑ l, rationalInverse k l * v l)) = v j := by
  fin_cases j <;> simp [rationalInverse, rationalRotation, Fin.sum_univ_two] <;> ring

theorem rational_inverse_preserves_squares : PreservesSquares rationalInverse := by
  intro x
  simp [rationalInverse, Fin.sum_univ_two]
  ring

theorem concrete_right_action_reversible {ι : Type*} (T : ι → Fin 2 → ℝ) :
    rightAction rationalInverse (rightAction rationalRotation T) = T :=
  right_action_inverse rationalRotation rationalInverse rational_rotation_inverse T

theorem concrete_left_action_reversible {κ : Type*} (T : Fin 2 → κ → ℝ) :
    leftAction rationalInverse (leftAction rationalRotation T) = T :=
  left_action_inverse rationalRotation rationalInverse rational_rotation_inverse T

theorem concrete_right_inverse_action_reversible {ι : Type*} (T : ι → Fin 2 → ℝ) :
    rightAction rationalRotation (rightAction rationalInverse T) = T :=
  right_action_inverse rationalInverse rationalRotation rational_inverse_rotation T

theorem concrete_left_inverse_action_reversible {κ : Type*} (T : Fin 2 → κ → ℝ) :
    leftAction rationalRotation (leftAction rationalInverse T) = T :=
  left_action_inverse rationalInverse rationalRotation rational_inverse_rotation T

theorem concrete_mixing_sum_q4 :
    planeQ4 (quarticRotate (3 / 5) (4 / 5) (1, 0) +
      quarticRotate (3 / 5) (4 / 5) (0, 1)) = (194 / 25 : ℝ) := by
  have h1 : quarticRotate (3 / 5) (4 / 5) (1, 0) =
      (Real.sqrt (3 / 5), Real.sqrt (4 / 5)) := by
    norm_num [quarticRotate, planeDecode, rotate, planeEncode, phi, psi]
  have h2 : quarticRotate (3 / 5) (4 / 5) (0, 1) =
      (-Real.sqrt (4 / 5), Real.sqrt (3 / 5)) := by
    norm_num [quarticRotate, planeDecode, rotate, planeEncode, phi, psi]
  rw [h1, h2]
  simp only [planeQ4, Prod.mk_add_mk]
  calc
    _ = 2 * (Real.sqrt (3 / 5) ^ 2) ^ 2 +
        12 * (Real.sqrt (3 / 5) ^ 2) * (Real.sqrt (4 / 5) ^ 2) +
        2 * (Real.sqrt (4 / 5) ^ 2) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 5),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4 / 5)]; norm_num

theorem concrete_mixing_not_additive :
    quarticRotate (3 / 5) (4 / 5) ((1, 0) + (0, 1)) ≠
      quarticRotate (3 / 5) (4 / 5) (1, 0) + quarticRotate (3 / 5) (4 / 5) (0, 1) := by
  intro h
  have hh := congrArg planeQ4 h
  rw [quartic_rotation_preserves_q4 (3 / 5) (4 / 5) (by norm_num),
    concrete_mixing_sum_q4] at hh
  norm_num [planeQ4, Prod.mk_add_mk] at hh

/-- Keeping ordinary history addition gives a third-order residual, whereas
transporting addition gives the quadratic representation back. -/
theorem ordinary_scalar_merge_i3 :
    (3 : ℝ) ^ 4 - 3 * (2 : ℝ) ^ 4 + 3 * (1 : ℝ) ^ 4 = 36 := by norm_num

/-! Machine-visible scope ledger. Entries record work states, not proof upgrades. -/

inductive OpenBridge where
  | deriveRealCarrierAndAccessibleOrthogonalOperations
  | specifyIndependentlyOperationalCoherentHistoryUnion
  | deriveHistoryUnionCompatibilityWithRemoteContextAction
  | deriveComplexCompositeGeometryFromPrimitives
  | comparePhysicalEquivalenceWithTransportedObservables
  deriving DecidableEq, Repr

def openBridges : List OpenBridge :=
  [.deriveRealCarrierAndAccessibleOrthogonalOperations,
   .specifyIndependentlyOperationalCoherentHistoryUnion,
   .deriveHistoryUnionCompatibilityWithRemoteContextAction,
   .deriveComplexCompositeGeometryFromPrimitives,
   .comparePhysicalEquivalenceWithTransportedObservables]

/-- These claims are NOT proved by this module. The first is a mathematical
extension awaiting formalization; the others require an operational bridge. -/
inductive PendingResult where
  | continuousAdditiveMapsAreRealLinear
  | allVectorsRealizedByIndependentlyOperationalDisjointHistoryMerges
  | ordinaryHistoryUnionCommutesWithRemoteContextAction
  deriving DecidableEq, Repr

def paperOnlyOrOpen : List PendingResult :=
  [.continuousAdditiveMapsAreRealLinear,
   .allVectorsRealizedByIndependentlyOperationalDisjointHistoryMerges,
   .ordinaryHistoryUnionCommutesWithRemoteContextAction]

end
end IDT.QMClosure.QuarticContextTransport
