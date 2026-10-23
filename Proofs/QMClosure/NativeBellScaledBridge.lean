import Proofs.QMClosure.PairHistoryMeasureProbe

namespace IDT.QMClosure.NativeBellScaledBridge

/-!
# A supplied native integer-amplitude Bell protocol

The joint amplitude table, local coefficient action `A C Bᵀ`, setting
assignment, and normalization of positive native weights are supplied operational
bridges. None is derived from the primitive base. Amplitudes remain integers;
only normalized readouts are rational. The coherent table is not factorized.

Scaled-isometry and common-scale identities are universal algebraic statements.
The Bell numbers and uniform marginals are exact finite witness computations.
Readout-projective reversibility below concerns only this homogeneous supplied
protocol, not an integer-lattice inverse or a global observational quotient:
the fixed-reference countercontrol explicitly rules out that latter inference.
The real-axis embedding preserves the native operations and weight; this witness
therefore does not select between the scalar and Gaussian carriers or prove QM.
-/

abbrev W : ℤ → ℤ := signedScalarPairHistoryGate.weight

def realEmbed (x : ℤ) : GaussianHistoryAmplitude := ⟨x, 0⟩

theorem real_embedding_preserves_native_operations (x y : ℤ) :
    realEmbed (signedScalarPairHistoryGate.add x y) =
        gaussianPairHistoryGate.add (realEmbed x) (realEmbed y) ∧
      realEmbed (signedScalarPairHistoryGate.mul x y) =
        gaussianPairHistoryGate.mul (realEmbed x) (realEmbed y) ∧
      gaussianPairHistoryGate.weight (realEmbed x) = W x := by
  simp [realEmbed, W, signedScalarPairHistoryGate, gaussianPairHistoryGate,
    gaussianHistoryAdd, gaussianHistoryMul, gaussianHistoryWeight,
    pairHistoryQuadraticWeight]

theorem real_embedding_preserves_weight (x : ℤ) :
    gaussianPairHistoryGate.weight (realEmbed x) = W x :=
  (real_embedding_preserves_native_operations x 0).2.2

def gaussianScale (k : ℤ) (x : GaussianHistoryAmplitude) : GaussianHistoryAmplitude :=
  gaussianHistoryMul (realEmbed k) x

theorem native_weight_common_scale (k x : ℤ) : W (k * x) = k ^ 2 * W x := by
  simp only [W, signedScalarPairHistoryGate, pairHistoryQuadraticWeight]
  ring

theorem gaussian_weight_common_scale (k : ℤ) (x : GaussianHistoryAmplitude) :
    gaussianPairHistoryGate.weight (gaussianScale k x) =
      k ^ 2 * gaussianPairHistoryGate.weight x := by
  simp only [gaussianPairHistoryGate, gaussianScale, gaussianHistoryMul,
    realEmbed, gaussianHistoryWeight]
  ring

theorem native_two_coordinate_scaled_isometry
    (a b c d s x y : ℤ)
    (first : a ^ 2 + c ^ 2 = s) (second : b ^ 2 + d ^ 2 = s)
    (orthogonal : a * b + c * d = 0) :
    W (a * x + b * y) + W (c * x + d * y) = s * (W x + W y) := by
  simp only [W, signedScalarPairHistoryGate, pairHistoryQuadraticWeight]
  calc
    _ = (a ^ 2 + c ^ 2) * x ^ 2 + (b ^ 2 + d ^ 2) * y ^ 2 +
        2 * (a * b + c * d) * x * y := by ring
    _ = _ := by rw [first, second, orthogonal]; ring

def gaussianCombination (a b : ℤ) (x y : GaussianHistoryAmplitude) :
    GaussianHistoryAmplitude :=
  gaussianHistoryAdd (gaussianScale a x) (gaussianScale b y)

theorem gaussian_two_coordinate_scaled_isometry
    (a b c d s : ℤ) (x y : GaussianHistoryAmplitude)
    (first : a ^ 2 + c ^ 2 = s) (second : b ^ 2 + d ^ 2 = s)
    (orthogonal : a * b + c * d = 0) :
    gaussianPairHistoryGate.weight (gaussianCombination a b x y) +
      gaussianPairHistoryGate.weight (gaussianCombination c d x y) =
      s * (gaussianPairHistoryGate.weight x + gaussianPairHistoryGate.weight y) := by
  have hr := native_two_coordinate_scaled_isometry a b c d s x.re y.re
    first second orthogonal
  have hi := native_two_coordinate_scaled_isometry a b c d s x.im y.im
    first second orthogonal
  simp only [W, signedScalarPairHistoryGate, pairHistoryQuadraticWeight] at hr hi
  simp only [gaussianPairHistoryGate, gaussianCombination, gaussianHistoryAdd,
    gaussianScale, gaussianHistoryMul, realEmbed, gaussianHistoryWeight]
  nlinarith

def normalizedWeight (weight total : ℤ) : ℚ := (weight : ℚ) / (total : ℚ)

/-- Positive totals are explicit: totalized division is not a probability model. -/
theorem normalized_common_factor (s weight total : ℤ)
    (scalePositive : 0 < s) (totalPositive : 0 < total) :
    normalizedWeight (s * weight) (s * total) = normalizedWeight weight total := by
  have hs : (s : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt scalePositive)
  have ht : (total : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt totalPositive)
  simp only [normalizedWeight, Int.cast_mul]
  field_simp

theorem normalized_native_common_nonzero_scale
    (k x total : ℤ) (nonzero : k ≠ 0) (totalPositive : 0 < total) :
    normalizedWeight (W (k * x)) (k ^ 2 * total) =
      normalizedWeight (W x) total := by
  rw [native_weight_common_scale]
  exact normalized_common_factor (k ^ 2) _ _ (sq_pos_of_ne_zero nonzero) totalPositive

theorem normalized_gaussian_common_nonzero_scale
    (k : ℤ) (x : GaussianHistoryAmplitude) (total : ℤ)
    (nonzero : k ≠ 0) (totalPositive : 0 < total) :
    normalizedWeight (gaussianPairHistoryGate.weight (gaussianScale k x))
        (k ^ 2 * total) =
      normalizedWeight (gaussianPairHistoryGate.weight x) total := by
  rw [gaussian_weight_common_scale]
  exact normalized_common_factor (k ^ 2) _ _ (sq_pos_of_ne_zero nonzero) totalPositive

structure NativeTable where
  aa : ℤ
  ab : ℤ
  ba : ℤ
  bb : ℤ
deriving DecidableEq, Repr

def identity : NativeTable := ⟨1, 0, 0, 1⟩
def hadamard : NativeTable := ⟨1, 1, 1, -1⟩
def bobZero : NativeTable := ⟨2, 1, -1, 2⟩
def bobOne : NativeTable := ⟨2, -1, 1, 2⟩

def transpose (t : NativeTable) : NativeTable := ⟨t.aa, t.ba, t.ab, t.bb⟩

def multiply (a b : NativeTable) : NativeTable :=
  ⟨a.aa * b.aa + a.ab * b.ba, a.aa * b.ab + a.ab * b.bb,
    a.ba * b.aa + a.bb * b.ba, a.ba * b.ab + a.bb * b.bb⟩

def tableScale (k : ℤ) (t : NativeTable) : NativeTable :=
  ⟨k * t.aa, k * t.ab, k * t.ba, k * t.bb⟩

def determinant (t : NativeTable) : ℤ := t.aa * t.bb - t.ab * t.ba

/-- This action is an operational bridge supplied to the probe. -/
def localAction (a c b : NativeTable) : NativeTable :=
  multiply (multiply a c) (transpose b)

def totalWeight (t : NativeTable) : ℤ := W t.aa + W t.ab + W t.ba + W t.bb

def amplitude (t : NativeTable) (left right : Bool) : ℤ :=
  if left then (if right then t.bb else t.ba) else (if right then t.ab else t.aa)

def probability (t : NativeTable) (left right : Bool) : ℚ :=
  normalizedWeight (W (amplitude t left right)) (totalWeight t)

def gaussianEmbeddedTotal (t : NativeTable) : ℤ :=
  gaussianPairHistoryGate.weight (realEmbed t.aa) +
    gaussianPairHistoryGate.weight (realEmbed t.ab) +
    gaussianPairHistoryGate.weight (realEmbed t.ba) +
    gaussianPairHistoryGate.weight (realEmbed t.bb)

def gaussianEmbeddedProbability (t : NativeTable) (left right : Bool) : ℚ :=
  normalizedWeight (gaussianPairHistoryGate.weight (realEmbed (amplitude t left right)))
    (gaussianEmbeddedTotal t)

theorem real_embedded_table_total (t : NativeTable) :
    gaussianEmbeddedTotal t = totalWeight t := by
  simp only [gaussianEmbeddedTotal, totalWeight, real_embedding_preserves_weight]

/-- This is readout equality for the real-axis embedding, not carrier selection. -/
theorem real_embedded_table_probability (t : NativeTable)
    (totalPositive : 0 < totalWeight t) (left right : Bool) :
    0 < gaussianEmbeddedTotal t ∧
      gaussianEmbeddedProbability t left right = probability t left right := by
  constructor
  · simpa only [real_embedded_table_total] using totalPositive
  · simp only [gaussianEmbeddedProbability, probability, real_embedded_table_total,
      real_embedding_preserves_weight]

def aliceMarginal (t : NativeTable) (left : Bool) : ℚ :=
  probability t left false + probability t left true

def bobMarginal (t : NativeTable) (right : Bool) : ℚ :=
  probability t false right + probability t true right

def correlation (t : NativeTable) : ℚ :=
  probability t false false + probability t true true -
    probability t false true - probability t true false

def chsh (tables : Bool → Bool → NativeTable) : ℚ :=
  correlation (tables false false) + correlation (tables false true) +
    correlation (tables true false) - correlation (tables true true)

/-- Uniform settings and the CHSH winning predicate are supplied here. -/
def uniformSettingWin (tables : Bool → Bool → NativeTable) : ℚ :=
  ((probability (tables false false) false false + probability (tables false false) true true) +
    (probability (tables false true) false false + probability (tables false true) true true) +
    (probability (tables true false) false false + probability (tables true false) true true) +
    (probability (tables true true) false true + probability (tables true true) true false)) / 4

theorem table_scale_total (k : ℤ) (t : NativeTable) :
    totalWeight (tableScale k t) = k ^ 2 * totalWeight t := by
  simp only [totalWeight, tableScale, native_weight_common_scale]
  ring

theorem table_scale_probability (k : ℤ) (t : NativeTable)
    (nonzero : k ≠ 0) (totalPositive : 0 < totalWeight t) (left right : Bool) :
    probability (tableScale k t) left right = probability t left right := by
  have amplitudes : amplitude (tableScale k t) left right = k * amplitude t left right := by
    cases left <;> cases right <;> rfl
  simp only [probability, amplitudes, table_scale_total]
  exact normalized_native_common_nonzero_scale k _ _ nonzero totalPositive

/-- Column norm and orthogonality assumptions are supplied, not inferred from
integer coefficients or reversibility. The positive scale excludes zero maps. -/
def ScaledIsometry (b : NativeTable) (s : ℤ) : Prop :=
  0 < s ∧ b.aa ^ 2 + b.ba ^ 2 = s ∧ b.ab ^ 2 + b.bb ^ 2 = s ∧
    b.aa * b.ab + b.ba * b.bb = 0

def rowWeight (t : NativeTable) (left : Bool) : ℤ :=
  if left then W t.ba + W t.bb else W t.aa + W t.ab

theorem right_action_row_weight (t b : NativeTable) (s : ℤ)
    (isometry : ScaledIsometry b s) (left : Bool) :
    rowWeight (multiply t (transpose b)) left = s * rowWeight t left := by
  rcases isometry with ⟨_, hfirst, hsecond, horth⟩
  cases left
  · simpa [rowWeight, multiply, transpose, mul_comm] using
      native_two_coordinate_scaled_isometry b.aa b.ab b.ba b.bb s t.aa t.ab
        hfirst hsecond horth
  · simpa [rowWeight, multiply, transpose, mul_comm] using
      native_two_coordinate_scaled_isometry b.aa b.ab b.ba b.bb s t.ba t.bb
        hfirst hsecond horth

theorem right_action_total_weight (t b : NativeTable) (s : ℤ)
    (isometry : ScaledIsometry b s) :
    totalWeight (multiply t (transpose b)) = s * totalWeight t := by
  have first := right_action_row_weight t b s isometry false
  have second := right_action_row_weight t b s isometry true
  simp only [rowWeight, Bool.false_eq_true, if_false, if_true] at first second
  unfold totalWeight
  linarith

theorem right_action_total_positive (t b : NativeTable) (s : ℤ)
    (isometry : ScaledIsometry b s) (totalPositive : 0 < totalWeight t) :
    0 < totalWeight (multiply t (transpose b)) := by
  rw [right_action_total_weight t b s isometry]
  exact mul_pos isometry.1 totalPositive

theorem alice_marginal_as_row_weight (t : NativeTable) (left : Bool) :
    aliceMarginal t left = normalizedWeight (rowWeight t left) (totalWeight t) := by
  cases left <;>
    simp [aliceMarginal, probability, amplitude, normalizedWeight, rowWeight,
      Int.cast_add, add_div]

/-- Conditional scalar-table no-signalling for this action/readout only.
The arbitrary source table and local map are mathematical inputs. -/
theorem scalar_table_alice_no_signalling (t b : NativeTable) (s : ℤ)
    (isometry : ScaledIsometry b s) (totalPositive : 0 < totalWeight t)
    (left : Bool) :
    aliceMarginal (multiply t (transpose b)) left = aliceMarginal t left := by
  rw [alice_marginal_as_row_weight, alice_marginal_as_row_weight,
    right_action_row_weight t b s isometry, right_action_total_weight t b s isometry]
  exact normalized_common_factor s _ _ isometry.1 totalPositive

theorem transpose_probability (t : NativeTable) (left right : Bool) :
    probability (transpose t) left right = probability t right left := by
  have total : totalWeight (transpose t) = totalWeight t := by
    simp only [totalWeight, transpose]
    ring
  unfold probability
  rw [total]
  cases left <;> cases right <;> rfl

theorem transpose_bob_marginal (t : NativeTable) (right : Bool) :
    aliceMarginal (transpose t) right = bobMarginal t right := by
  simp only [aliceMarginal, bobMarginal, transpose_probability]

theorem transpose_local_action (a t : NativeTable) :
    transpose (multiply a t) = multiply (transpose t) (transpose a) := by
  cases a
  cases t
  simp only [transpose, multiply, NativeTable.mk.injEq]
  exact ⟨by ring, by ring, by ring, by ring⟩

theorem scalar_table_bob_no_signalling (a t : NativeTable) (s : ℤ)
    (isometry : ScaledIsometry a s) (totalPositive : 0 < totalWeight t)
    (right : Bool) :
    bobMarginal (multiply a t) right = bobMarginal t right := by
  have transposePositive : 0 < totalWeight (transpose t) := by
    have total : totalWeight (transpose t) = totalWeight t := by
      simp only [totalWeight, transpose]
      ring
    rw [total]
    exact totalPositive
  rw [← transpose_bob_marginal, transpose_local_action]
  rw [scalar_table_alice_no_signalling (transpose t) a s isometry transposePositive]
  exact transpose_bob_marginal t right

theorem benchmark_maps_scaled_isometries :
    ScaledIsometry identity 1 ∧ ScaledIsometry hadamard 2 ∧
      ScaledIsometry bobZero 5 ∧ ScaledIsometry bobOne 5 := by
  norm_num [ScaledIsometry, identity, hadamard, bobZero, bobOne]

theorem scaled_inverse_and_determinant_facts :
    multiply hadamard hadamard = tableScale 2 identity ∧
      multiply bobZero bobOne = tableScale 5 identity ∧
      multiply bobOne bobZero = tableScale 5 identity ∧
      determinant hadamard = -2 ∧ determinant bobZero = 5 ∧ determinant bobOne = 5 := by
  decide

theorem hadamard_readout_projective_reversibility (t : NativeTable)
    (totalPositive : 0 < totalWeight t) (left right : Bool) :
    probability (multiply hadamard (multiply hadamard t)) left right =
      probability t left right := by
  have h : multiply hadamard (multiply hadamard t) = tableScale 2 t := by
    cases t
    simp only [multiply, hadamard, tableScale, NativeTable.mk.injEq]
    exact ⟨by ring, by ring, by ring, by ring⟩
  rw [h]
  exact table_scale_probability 2 t (by decide) totalPositive left right

theorem bob_readout_projective_reversibility (t : NativeTable)
    (totalPositive : 0 < totalWeight t) (left right : Bool) :
    probability (multiply bobZero (multiply bobOne t)) left right = probability t left right ∧
      probability (multiply bobOne (multiply bobZero t)) left right = probability t left right := by
  have hzero : multiply bobZero (multiply bobOne t) = tableScale 5 t := by
    cases t
    simp only [multiply, bobZero, bobOne, tableScale, NativeTable.mk.injEq]
    exact ⟨by ring, by ring, by ring, by ring⟩
  have hone : multiply bobOne (multiply bobZero t) = tableScale 5 t := by
    cases t
    simp only [multiply, bobZero, bobOne, tableScale, NativeTable.mk.injEq]
    exact ⟨by ring, by ring, by ring, by ring⟩
  rw [hzero, hone]
  exact ⟨table_scale_probability 5 t (by decide) totalPositive left right,
    table_scale_probability 5 t (by decide) totalPositive left right⟩

def coherentSource : NativeTable := identity

theorem coherent_source_not_factorizable :
    ¬ ∃ a b c d : ℤ, coherentSource = ⟨a * c, a * d, b * c, b * d⟩ := by
  rintro ⟨a, b, c, d, h⟩
  have hd := congrArg determinant h
  norm_num [determinant, coherentSource, identity] at hd
  nlinarith [hd]

def aliceSetting (setting : Bool) : NativeTable := if setting then hadamard else identity
def bobSetting (setting : Bool) : NativeTable := if setting then bobOne else bobZero
def witness (leftSetting rightSetting : Bool) : NativeTable :=
  localAction (aliceSetting leftSetting) coherentSource (bobSetting rightSetting)

theorem witness_amplitude_tables :
    witness false false = ⟨2, -1, 1, 2⟩ ∧
      witness false true = ⟨2, 1, -1, 2⟩ ∧
      witness true false = ⟨3, 1, 1, -3⟩ ∧
      witness true true = ⟨1, 3, 3, -1⟩ := by decide

theorem witness_totals :
    totalWeight (witness false false) = 10 ∧
      totalWeight (witness false true) = 10 ∧
      totalWeight (witness true false) = 20 ∧
      totalWeight (witness true true) = 20 := by decide

theorem witness_totals_positive (leftSetting rightSetting : Bool) :
    0 < totalWeight (witness leftSetting rightSetting) := by
  cases leftSetting <;> cases rightSetting <;> decide

theorem gaussian_embedded_witness_readout (leftSetting rightSetting left right : Bool) :
    0 < gaussianEmbeddedTotal (witness leftSetting rightSetting) ∧
      gaussianEmbeddedProbability (witness leftSetting rightSetting) left right =
        probability (witness leftSetting rightSetting) left right :=
  real_embedded_table_probability _ (witness_totals_positive _ _) _ _

theorem witness_probability_tables (left right : Bool) :
    probability (witness false false) left right = (if left = right then 2/5 else 1/10) ∧
      probability (witness false true) left right = (if left = right then 2/5 else 1/10) ∧
      probability (witness true false) left right = (if left = right then 9/20 else 1/20) ∧
      probability (witness true true) left right = (if left = right then 1/20 else 9/20) := by
  cases left <;> cases right <;>
    norm_num [probability, amplitude, normalizedWeight, totalWeight, witness,
      localAction, aliceSetting, bobSetting, coherentSource, identity, hadamard,
      bobZero, bobOne, multiply, transpose, W, signedScalarPairHistoryGate,
      pairHistoryQuadraticWeight]

theorem witness_all_marginals (leftSetting rightSetting outcome : Bool) :
    aliceMarginal (witness leftSetting rightSetting) outcome = 1/2 ∧
      bobMarginal (witness leftSetting rightSetting) outcome = 1/2 := by
  cases leftSetting <;> cases rightSetting <;> cases outcome <;>
    norm_num [aliceMarginal, bobMarginal, witness_probability_tables]

theorem witness_correlations :
    correlation (witness false false) = 3/5 ∧
      correlation (witness false true) = 3/5 ∧
      correlation (witness true false) = 4/5 ∧
      correlation (witness true true) = -4/5 := by
  norm_num [correlation, witness_probability_tables]

theorem witness_chsh_and_win :
    chsh witness = 14/5 ∧ (2 : ℚ) < chsh witness ∧
      uniformSettingWin witness = 17/20 := by
  norm_num [chsh, witness_correlations, uniformSettingWin, witness_probability_tables]

def identityCompletion (_ _ : Bool) : NativeTable :=
  localAction identity coherentSource identity

theorem identity_completion_same_source :
    (∀ left right, identityCompletion left right = coherentSource) ∧
      chsh identityCompletion = 2 ∧ uniformSettingWin identityCompletion = 3/4 := by
  constructor
  · intro left right
    rfl
  · norm_num [chsh, uniformSettingWin, correlation, probability, normalizedWeight,
      amplitude, totalWeight, identityCompletion, localAction, coherentSource,
      identity, multiply, transpose, W, signedScalarPairHistoryGate, pairHistoryQuadraticWeight]

/-- Here `(1,0)`, `(2,0)`, and the fixed reference `(0,1)` are two-mode
vectors of scalar integer amplitudes, not single Gaussian amplitudes.
Direct readout identifies the scales, but adding the same reference does not. -/
theorem fixed_reference_breaks_global_scale_quotient :
    normalizedWeight (W 1) (W 1 + W 0) =
        normalizedWeight (W 2) (W 2 + W 0) ∧
      normalizedWeight (W (1 + 0)) (W (1 + 0) + W (0 + 1)) = 1/2 ∧
      normalizedWeight (W (2 + 0)) (W (2 + 0) + W (0 + 1)) = 4/5 ∧
      (1/2 : ℚ) ≠ 4/5 := by
  norm_num [normalizedWeight, W, signedScalarPairHistoryGate, pairHistoryQuadraticWeight]

theorem fixed_reference_totals_positive :
    0 < W 1 + W 0 ∧ 0 < W 2 + W 0 ∧
      0 < W (1 + 0) + W (0 + 1) ∧ 0 < W (2 + 0) + W (0 + 1) := by
  norm_num [W, signedScalarPairHistoryGate, pairHistoryQuadraticWeight]

end IDT.QMClosure.NativeBellScaledBridge
