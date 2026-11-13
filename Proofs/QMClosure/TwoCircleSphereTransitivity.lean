import Mathlib

/-!
# Sphere transitivity from two full rotation circles

This coordinate geometry bridge assumes invariance under every circle parameter
about both axes. It supplies neither finite-gate circle closure nor physical
continuum availability. No closedness of the invariant subset is assumed.
-/

noncomputable section

namespace IDT.QMClosure.TwoCircleSphere

open Set

@[ext] structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ

def sqnorm (p : Vec3) : ℝ := p.x ^ 2 + p.y ^ 2 + p.z ^ 2

def sphere (r : ℝ) : Set Vec3 := {p | sqnorm p = r ^ 2}

def rotZ (k l : ℝ) (p : Vec3) : Vec3 :=
  ⟨k * p.x - l * p.y, l * p.x + k * p.y, p.z⟩

def rotTilt (s c k l : ℝ) (p : Vec3) : Vec3 :=
  ⟨k * p.x - l * c * p.y + (1 - k) * (s * p.x + c * p.z) * s,
   k * p.y + l * (c * p.x - s * p.z),
   k * p.z + l * s * p.y + (1 - k) * (s * p.x + c * p.z) * c⟩

private def tiltFrame (s c : ℝ) (p : Vec3) : Vec3 :=
  ⟨c * p.x - s * p.z, p.y, s * p.x + c * p.z⟩

private def untiltFrame (s c : ℝ) (p : Vec3) : Vec3 :=
  ⟨c * p.x + s * p.z, p.y, -s * p.x + c * p.z⟩

private theorem frame_norm (s c : ℝ) (haxis : s ^ 2 + c ^ 2 = 1) (p : Vec3) :
    sqnorm (tiltFrame s c p) = sqnorm p := by
  dsimp [sqnorm, tiltFrame]
  linear_combination (p.x ^ 2 + p.z ^ 2) * haxis

private theorem unframe_norm (s c : ℝ) (haxis : s ^ 2 + c ^ 2 = 1) (p : Vec3) :
    sqnorm (untiltFrame s c p) = sqnorm p := by
  dsimp [sqnorm, untiltFrame]
  linear_combination (p.x ^ 2 + p.z ^ 2) * haxis

private theorem frame_unframe (s c : ℝ) (haxis : s ^ 2 + c ^ 2 = 1) (p : Vec3) :
    tiltFrame s c (untiltFrame s c p) = p := by
  ext <;> dsimp [tiltFrame, untiltFrame]
  · linear_combination p.x * haxis
  · linear_combination p.z * haxis

private theorem unframe_frame (s c : ℝ) (haxis : s ^ 2 + c ^ 2 = 1) (p : Vec3) :
    untiltFrame s c (tiltFrame s c p) = p := by
  ext <;> dsimp [tiltFrame, untiltFrame]
  · linear_combination p.x * haxis
  · linear_combination p.z * haxis

private theorem rotTilt_eq_conjugate (s c k l : ℝ)
    (haxis : s ^ 2 + c ^ 2 = 1) (p : Vec3) :
    rotTilt s c k l p = untiltFrame s c (rotZ k l (tiltFrame s c p)) := by
  ext <;> dsimp [rotTilt, rotZ, tiltFrame, untiltFrame]
  · linear_combination -k * p.x * haxis
  · ring
  · linear_combination -k * p.z * haxis

theorem rotZ_norm (k l : ℝ) (hcircle : k ^ 2 + l ^ 2 = 1) (p : Vec3) :
    sqnorm (rotZ k l p) = sqnorm p := by
  dsimp [sqnorm, rotZ]
  linear_combination (p.x ^ 2 + p.y ^ 2) * hcircle

theorem rotZ_inverse (k l : ℝ) (hcircle : k ^ 2 + l ^ 2 = 1) (p : Vec3) :
    rotZ k (-l) (rotZ k l p) = p := by
  ext <;> dsimp [rotZ]
  · linear_combination p.x * hcircle
  · linear_combination p.y * hcircle

theorem rotTilt_norm (s c k l : ℝ) (haxis : s ^ 2 + c ^ 2 = 1)
    (hcircle : k ^ 2 + l ^ 2 = 1) (p : Vec3) :
    sqnorm (rotTilt s c k l p) = sqnorm p := by
  rw [rotTilt_eq_conjugate s c k l haxis, unframe_norm s c haxis,
    rotZ_norm k l hcircle, frame_norm s c haxis]

theorem rotTilt_inverse (s c k l : ℝ) (haxis : s ^ 2 + c ^ 2 = 1)
    (hcircle : k ^ 2 + l ^ 2 = 1) (p : Vec3) :
    rotTilt s c k (-l) (rotTilt s c k l p) = p := by
  rw [rotTilt_eq_conjugate s c k (-l) haxis,
    rotTilt_eq_conjugate s c k l haxis, frame_unframe s c haxis,
    rotZ_inverse k l hcircle, unframe_frame s c haxis]

/-- Both hypotheses quantify over the entire parameter circle. -/
structure FullCircleInvariant (C : Set Vec3) (s c : ℝ) : Prop where
  z : ∀ k l : ℝ, k ^ 2 + l ^ 2 = 1 → ∀ p ∈ C, rotZ k l p ∈ C
  tilt : ∀ k l : ℝ, k ^ 2 + l ^ 2 = 1 → ∀ p ∈ C, rotTilt s c k l p ∈ C

private theorem complement_invariant {C : Set Vec3} {s c r : ℝ}
    (haxis : s ^ 2 + c ^ 2 = 1) (hC : FullCircleInvariant C s c) :
    FullCircleInvariant (sphere r \ C) s c := by
  constructor
  · intro k l hk p hp
    refine ⟨?_, ?_⟩
    · change sqnorm (rotZ k l p) = r ^ 2
      rw [rotZ_norm k l hk]
      exact hp.1
    · intro hmem
      have hinv := hC.z k (-l) (by nlinarith [hk]) _ hmem
      rw [rotZ_inverse k l hk] at hinv
      exact hp.2 hinv
  · intro k l hk p hp
    refine ⟨?_, ?_⟩
    · change sqnorm (rotTilt s c k l p) = r ^ 2
      rw [rotTilt_norm s c k l haxis hk]
      exact hp.1
    · intro hmem
      have hinv := hC.tilt k (-l) (by nlinarith [hk]) _ hmem
      rw [rotTilt_inverse s c k l haxis hk] at hinv
      exact hp.2 hinv

private def amplitude (r t : ℝ) : ℝ := Real.sqrt (r ^ 2 - t ^ 2)
private def canonical (r t : ℝ) : Vec3 := ⟨0, amplitude r t, t⟩

private theorem amplitude_pos {r t : ℝ} (_hr : 0 < r) (ht : t ∈ Ioo (-r) r) :
    0 < amplitude r t := by
  apply Real.sqrt_pos.2
  nlinarith [mul_pos (by linarith [ht.2] : 0 < r - t) (by linarith [ht.1] : 0 < r + t)]

private theorem amplitude_sq {r t : ℝ} (_hr : 0 < r) (ht : t ∈ Ioo (-r) r) :
    amplitude r t ^ 2 = r ^ 2 - t ^ 2 := by
  apply Real.sq_sqrt
  nlinarith [mul_pos (by linarith [ht.2] : 0 < r - t) (by linarith [ht.1] : 0 < r + t)]

private theorem canonical_on_sphere {r t : ℝ} (hr : 0 < r)
    (ht : t ∈ Ioo (-r) r) : canonical r t ∈ sphere r := by
  change 0 ^ 2 + amplitude r t ^ 2 + t ^ 2 = r ^ 2
  rw [amplitude_sq hr ht]
  ring

private theorem latitude_mem_iff {C : Set Vec3} {s c r t : ℝ}
    (hr : 0 < r) (hC : FullCircleInvariant C s c) (ht : t ∈ Ioo (-r) r)
    {p : Vec3} (hp : p ∈ sphere r) (hpz : p.z = t) :
    p ∈ C ↔ canonical r t ∈ C := by
  let A := amplitude r t
  have hA : 0 < A := amplitude_pos hr ht
  have hAne : A ≠ 0 := ne_of_gt hA
  have hAsq : A ^ 2 = r ^ 2 - t ^ 2 := amplitude_sq hr ht
  have hxy : p.x ^ 2 + p.y ^ 2 = A ^ 2 := by
    change p.x ^ 2 + p.y ^ 2 + p.z ^ 2 = r ^ 2 at hp
    rw [hpz] at hp
    nlinarith
  let k := p.y / A
  let l := -p.x / A
  have hk : k ^ 2 + l ^ 2 = 1 := by
    dsimp [k, l]
    field_simp [hAne]
    nlinarith [hxy]
  have hrot : rotZ k l (canonical r t) = p := by
    apply Vec3.ext
    · change p.y / A * 0 - (-p.x / A) * A = p.x
      field_simp [hAne]
      ring
    · change (-p.x / A) * 0 + (p.y / A) * A = p.y
      field_simp [hAne]
      ring
    · exact hpz.symm
  constructor
  · intro hmem
    have hi := hC.z k (-l) (by nlinarith [hk]) p hmem
    rw [← hrot, rotZ_inverse k l hk] at hi
    exact hi
  · intro hmem
    rw [← hrot]
    exact hC.z k l hk _ hmem

/-- A rational latitude-crossing family with a strictly positive linear term. -/
def latitudeCurve (t D B q : ℝ) : ℝ :=
  t + (2 * D * q - 2 * B * q ^ 2) / (1 + q ^ 2)

/-- An explicit interval lies in the range. No monotonicity is required. -/
theorem latitudeCurve_local_surjective (t B D : ℝ) (hD : 0 < D) :
    ∃ δ > 0, ∀ y ∈ Ioo (t - δ) (t + δ), ∃ q, latitudeCurve t D B q = y := by
  let h := D / (2 * (1 + |B|))
  have hden : 0 < 2 * (1 + |B|) := by positivity
  have hh : 0 < h := div_pos hD hden
  have hrel : h * (2 * (1 + |B|)) = D := by
    dsimp [h]
    field_simp [ne_of_gt hden]
  have habs : 2 * |B| * h < D := by nlinarith
  have hBupper : 2 * B * h < D := by
    have := mul_le_mul_of_nonneg_right (le_abs_self B) (le_of_lt hh)
    nlinarith
  have hBlower : -D < 2 * B * h := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le B) (le_of_lt hh)
    nlinarith
  have hd : 0 < 1 + h ^ 2 := by positivity
  let δ := h * D / (1 + h ^ 2)
  have hδ : 0 < δ := div_pos (mul_pos hh hD) hd
  have hhi : t + δ < latitudeCurve t D B h := by
    dsimp [latitudeCurve, δ]
    have hdiv : h * D / (1 + h ^ 2) <
        (2 * D * h - 2 * B * h ^ 2) / (1 + h ^ 2) := by
      apply (div_lt_div_iff_of_pos_right hd).2
      nlinarith [mul_pos hh (by linarith : 0 < D - 2 * B * h)]
    linarith
  have hneg : latitudeCurve t D B (-h) =
      t - (2 * D * h + 2 * B * h ^ 2) / (1 + h ^ 2) := by
    dsimp [latitudeCurve]
    ring
  have hlo : latitudeCurve t D B (-h) < t - δ := by
    rw [hneg]
    have hb : δ < (2 * D * h + 2 * B * h ^ 2) / (1 + h ^ 2) := by
      dsimp [δ]
      apply (div_lt_div_iff_of_pos_right hd).2
      nlinarith [mul_pos hh (by linarith : 0 < D + 2 * B * h)]
    linarith
  have hcont : Continuous (latitudeCurve t D B) := by
    unfold latitudeCurve
    fun_prop (disch := intro q; positivity)
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  have hy' : y ∈ Icc (latitudeCurve t D B (-h)) (latitudeCurve t D B h) := by
    constructor <;> linarith [hy.1, hy.2]
  obtain ⟨q, _, hq⟩ := intermediate_value_Icc (by linarith : -h ≤ h)
    hcont.continuousOn hy'
  exact ⟨q, hq⟩

private def cayleyK (q : ℝ) : ℝ := (1 - q ^ 2) / (1 + q ^ 2)
private def cayleyL (q : ℝ) : ℝ := 2 * q / (1 + q ^ 2)

private theorem cayley_circle (q : ℝ) : cayleyK q ^ 2 + cayleyL q ^ 2 = 1 := by
  have hd : 1 + q ^ 2 ≠ 0 := by positivity
  dsimp [cayleyK, cayleyL]
  field_simp [hd]
  ring

private theorem cayley_latitude (s c r t q : ℝ) (haxis : s ^ 2 + c ^ 2 = 1) :
    (rotTilt s c (cayleyK q) (cayleyL q) (canonical r t)).z =
      latitudeCurve t (s * amplitude r t) (t * s ^ 2) q := by
  have hd : 1 + q ^ 2 ≠ 0 := by positivity
  dsimp [rotTilt, canonical, cayleyK, cayleyL, latitudeCurve]
  field_simp [hd]
  linear_combination 2 * t * q ^ 2 * haxis

private def latitudes (C : Set Vec3) (r : ℝ) : Set ℝ :=
  {t | t ∈ Ioo (-r) r ∧ canonical r t ∈ C}

private theorem latitudes_open {C : Set Vec3} {s c r : ℝ}
    (hr : 0 < r) (hs : 0 < s) (haxis : s ^ 2 + c ^ 2 = 1)
    (hC : FullCircleInvariant C s c) : IsOpen (latitudes C r) := by
  apply isOpen_iff_mem_nhds.2
  intro t ht
  obtain ⟨δ, hδ, hsurj⟩ := latitudeCurve_local_surjective t (t * s ^ 2)
    (s * amplitude r t) (mul_pos hs (amplitude_pos hr ht.1))
  have hn : Ioo (t - δ) (t + δ) ∩ Ioo (-r) r ∈ nhds t :=
    Filter.inter_mem
      (isOpen_Ioo.mem_nhds (show t ∈ Ioo (t - δ) (t + δ) from
        ⟨by linarith, by linarith⟩))
      (isOpen_Ioo.mem_nhds ht.1)
  apply Filter.mem_of_superset hn
  intro y hy
  refine ⟨hy.2, ?_⟩
  obtain ⟨q, hq⟩ := hsurj y hy.1
  let p := rotTilt s c (cayleyK q) (cayleyL q) (canonical r t)
  have hpC : p ∈ C := hC.tilt _ _ (cayley_circle q) _ ht.2
  have hpS : p ∈ sphere r := by
    change sqnorm p = r ^ 2
    dsimp [p]
    rw [rotTilt_norm s c _ _ haxis (cayley_circle q)]
    exact canonical_on_sphere hr ht.1
  have hpz : p.z = y := (cayley_latitude s c r t q haxis).trans hq
  exact (latitude_mem_iff hr hC hy.2 hpS hpz).1 hpC

private theorem sphere_latitude_bounds {r : ℝ} (hr : 0 < r) {p : Vec3}
    (hp : p ∈ sphere r) : -r ≤ p.z ∧ p.z ≤ r := by
  change p.x ^ 2 + p.y ^ 2 + p.z ^ 2 = r ^ 2 at hp
  constructor <;> nlinarith [sq_nonneg p.x, sq_nonneg p.y]

/-- Every sphere point can be moved to an interior latitude by one tilted
circle element, taking either the identity or a quarter-turn. -/
private theorem interior_escape {r s c : ℝ} (hr : 0 < r) (hs : 0 < s)
    (haxis : s ^ 2 + c ^ 2 = 1) {p : Vec3} (hp : p ∈ sphere r) :
    ∃ k l : ℝ, k ^ 2 + l ^ 2 = 1 ∧ (rotTilt s c k l p).z ∈ Ioo (-r) r := by
  by_cases hi : p.z ∈ Ioo (-r) r
  · refine ⟨1, 0, by norm_num, ?_⟩
    simpa [rotTilt] using hi
  · have hb := sphere_latitude_bounds hr hp
    have hpole : p.z = -r ∨ p.z = r := by
      have : ¬ (-r < p.z ∧ p.z < r) := hi
      rcases le_or_gt p.z (-r) with h | h
      · exact Or.inl (le_antisymm h hb.1)
      · exact Or.inr (le_antisymm hb.2 (by by_contra hn; exact this ⟨h, lt_of_not_ge hn⟩))
    have hxy : p.x = 0 ∧ p.y = 0 := by
      change p.x ^ 2 + p.y ^ 2 + p.z ^ 2 = r ^ 2 at hp
      rcases hpole with hz | hz <;> rw [hz] at hp <;>
        constructor <;> nlinarith [sq_nonneg p.x, sq_nonneg p.y]
    have hc : c ^ 2 < 1 := by nlinarith [sq_pos_of_pos hs]
    have hc0 : 0 ≤ c ^ 2 := sq_nonneg c
    have hrc : r * c ^ 2 < r := by nlinarith [mul_pos hr (by linarith : 0 < 1 - c ^ 2)]
    refine ⟨0, 1, by norm_num, ?_⟩
    change -r < (rotTilt s c 0 1 p).z ∧ (rotTilt s c 0 1 p).z < r
    have hz : (rotTilt s c 0 1 p).z = p.z * c ^ 2 := by
      dsimp [rotTilt]
      rw [hxy.1, hxy.2]
      ring
    rw [hz]
    have hu := mul_le_mul_of_nonneg_right hb.2 hc0
    have hl := mul_le_mul_of_nonneg_right hb.1 hc0
    constructor <;> nlinarith

/-- A nonempty subset of a positive-radius sphere invariant under the full
z-axis rotation circle and full tilted-axis circle equals that sphere.
The tilted axis is `(s,0,c)` with `s > 0` and `s²+c²=1`. -/
theorem eq_sphere_of_full_circle_invariance {C : Set Vec3} {r s c : ℝ}
    (hr : 0 < r) (hs : 0 < s) (haxis : s ^ 2 + c ^ 2 = 1)
    (hsubset : C ⊆ sphere r) (hne : C.Nonempty)
    (hz : ∀ k l : ℝ, k ^ 2 + l ^ 2 = 1 → ∀ p ∈ C, rotZ k l p ∈ C)
    (htilt : ∀ k l : ℝ, k ^ 2 + l ^ 2 = 1 → ∀ p ∈ C, rotTilt s c k l p ∈ C) :
    C = sphere r := by
  let hC : FullCircleInvariant C s c := ⟨hz, htilt⟩
  let C' := sphere r \ C
  have hC' : FullCircleInvariant C' s c := complement_invariant haxis hC
  have hdis : Disjoint (latitudes C r) (latitudes C' r) := by
    apply Set.disjoint_left.2
    intro t ht ht'
    exact ht'.2.2 ht.2
  have hcover : Ioo (-r) r ⊆ latitudes C r ∪ latitudes C' r := by
    intro t ht
    by_cases hm : canonical r t ∈ C
    · exact Or.inl ⟨ht, hm⟩
    · exact Or.inr ⟨ht, canonical_on_sphere hr ht, hm⟩
  have hsome : (Ioo (-r) r ∩ latitudes C r).Nonempty := by
    obtain ⟨p, hp⟩ := hne
    obtain ⟨k, l, hk, hi⟩ := interior_escape hr hs haxis (hsubset hp)
    let q := rotTilt s c k l p
    have hqC : q ∈ C := hC.tilt k l hk p hp
    have hqS : q ∈ sphere r := hsubset hqC
    exact ⟨q.z, hi, hi, (latitude_mem_iff hr hC hi hqS rfl).1 hqC⟩
  have hall : Ioo (-r) r ⊆ latitudes C r :=
    isPreconnected_Ioo.subset_left_of_subset_union
      (latitudes_open hr hs haxis hC) (latitudes_open hr hs haxis hC') hdis hcover hsome
  apply Set.Subset.antisymm hsubset
  intro p hp
  obtain ⟨k, l, hk, hi⟩ := interior_escape hr hs haxis hp
  let q := rotTilt s c k l p
  have hqS : q ∈ sphere r := by
    change sqnorm q = r ^ 2
    dsimp [q]
    rw [rotTilt_norm s c k l haxis hk]
    exact hp
  have hqC : q ∈ C := (latitude_mem_iff hr hC hi hqS rfl).2 (hall hi).2
  have hinv := hC.tilt k (-l) (by nlinarith [hk]) q hqC
  change rotTilt s c k (-l) (rotTilt s c k l p) ∈ C at hinv
  rw [rotTilt_inverse s c k l haxis hk] at hinv
  exact hinv

end IDT.QMClosure.TwoCircleSphere
