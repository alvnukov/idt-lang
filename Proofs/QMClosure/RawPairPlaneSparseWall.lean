import Proofs.QMClosure.RawPairPlaneCompletion
import Proofs.QMClosure.RawPairPlaneLocalOperations

/-!
# An actual sparse-law countermodel

The three-ray completion satisfies the raw contract, positive faithful weight,
pair conservation, six universal sparse test families, the self-reference family,
and joint complex homogeneity. Its stage-two geometry supplies a triple whose
sparse equality has left side 2 and right side 3.
-/

namespace IDT.QMClosure.RawPairPlaneSparseWall

noncomputable section
set_option maxHeartbeats 2000000
open Classical RawPairPlaneAtlas RawPairPlaneLocalOperations

private def sw (k : Bool) (v : ℂ × ℂ) : ℂ × ℂ :=
  if k then v.swap else v

private theorem edge_order {A : PartialAtlas} (e : Edge A) (r s : A.Ray)
    (hrs : r ≠ s) (he : e.val = {r,s}) :
    ∃ k : Bool, e.left = (if k then s else r) ∧
      e.right = (if k then r else s) := by
  have hr : r = e.left ∨ r = e.right := (e.mem_iff r).mp (by simp [he])
  have hs : s = e.left ∨ s = e.right := (e.mem_iff s).mp (by simp [he])
  rcases hr with hr | hr <;> rcases hs with hs | hs
  · exact (hrs (hr.trans hs.symm)).elim
  · exact ⟨false, hr.symm, hs.symm⟩
  · exact ⟨true, hs.symm, hr.symm⟩
  · exact (hrs (hr.trans hs.symm)).elim

private theorem chart_interior (A : PartialAtlas) (e : Edge A) (c d : ℂ)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    ∃ t : NonzeroC, chart (nextAtlas A) (Sum.inr e) (c,d) =
      point (Sum.inr (e,t)) c := by
  refine ⟨⟨d/c, div_ne_zero hd hc⟩, ?_⟩
  simp only [chart, hc, ↓reduceIte]
  exact congrArg (fun r => point r c)
    (next_coord_new_nonzero A e ⟨d/c, div_ne_zero hd hc⟩)

private theorem attached_mixed_weight (A : PartialAtlas) (D : CompleteAtlas)
    (E : Extension (nextAtlas A) D.toPartialAtlas) (r s : A.Ray)
    (hrs : r ≠ s) (h : ¬ Covered A r s) (c d : ℂ) :
    W D.toPartialAtlas
      (m D (point (E.ray (Sum.inl r)) c) (point (E.ray (Sum.inl s)) d)) =
      (A.weight r * Complex.normSq c + A.weight s * Complex.normSq d)/2 := by
  obtain ⟨e, he | he⟩ := new_plane_axis_pair A r s hrs h
  · have h0 := E.coord_map (Sum.inr e) (some 0)
    have h1 := E.coord_map (Sum.inr e) none
    rw [he.1] at h0
    rw [he.2] at h1
    rw [← h0, ← h1, axis_mixed_weight]
    rw [h0, h1, E.weight_map, E.weight_map, next_weight_old, next_weight_old]
  · have h0 := E.coord_map (Sum.inr e) (some 0)
    have h1 := E.coord_map (Sum.inr e) none
    rw [he.1] at h0
    rw [he.2] at h1
    rw [← h1, ← h0, axis_mixed_weight_reverse]
    rw [h0, h1, E.weight_map, E.weight_map, next_weight_old, next_weight_old]
    ring

private theorem seed_uncovered (r s : threeRaySeed.Ray) :
    ¬ Covered threeRaySeed r s := by
  rintro ⟨p, _, _, _, _⟩
  exact Empty.elim p

private theorem seed_zero_ne_one : (0 : Fin 3) ≠ (1 : Fin 3) := by
  intro h
  have hh := congrArg (fun r : Fin 3 => r.val) h
  norm_num at hh

private theorem seed_zero_ne_two : (0 : Fin 3) ≠ (2 : Fin 3) := by
  intro h
  have hh := congrArg (fun r : Fin 3 => r.val) h
  norm_num at hh

private def q : Edge threeRaySeed :=
  edgeOfUncovered threeRaySeed (0 : Fin 3) (1 : Fin 3) seed_zero_ne_one
    (seed_uncovered (0 : Fin 3) (1 : Fin 3))

private def p : Edge threeRaySeed :=
  edgeOfUncovered threeRaySeed (0 : Fin 3) (2 : Fin 3) seed_zero_ne_two
    (seed_uncovered (0 : Fin 3) (2 : Fin 3))

private theorem q_ne_p : q ≠ p := by
  letI : DecidableEq (Fin 3) := fun a b => Classical.propDecidable (a = b)
  intro h
  have he : ({(0 : Fin 3),(1 : Fin 3)} : Finset threeRaySeed.Ray) =
      {(0 : Fin 3),(2 : Fin 3)} := congrArg Subtype.val h
  have hmem : (1 : Fin 3) ∈ ({(0 : Fin 3),(1 : Fin 3)} : Finset threeRaySeed.Ray) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [he] at hmem
  rcases Finset.mem_insert.mp hmem with h0 | h2
  · exact seed_zero_ne_one h0.symm
  · have hh := congrArg (fun r : Fin 3 => r.val) (Finset.mem_singleton.mp h2)
    norm_num at hh

private theorem first_chart_weight (D : CompleteAtlas)
    (F : Extension (nextAtlas threeRaySeed) D.toPartialAtlas)
    (e : Edge threeRaySeed) (v : ℂ × ℂ) :
    W D.toPartialAtlas (chart D.toPartialAtlas (F.plane (Sum.inr e)) v) =
      Complex.normSq v.1 + Complex.normSq v.2 := by
  rw [← F.chart_map, F.W_rawMap, W_chart]
  rw [next_coord_new_zero, next_coord_new_none, next_weight_old, next_weight_old]
  simp only [threeRaySeed, one_mul]

/-- The finite stage-two certificate produces the explicit unequal readouts. -/
theorem stage_two_sparse_witness (D : CompleteAtlas)
    (E : Extension (nextAtlas (nextAtlas threeRaySeed)) D.toPartialAtlas) :
    ∃ x y z : Raw D.Ray,
      W D.toPartialAtlas (m D (m D x y)
        (RawSparseConservationSelection.A (contract D) z)) +
      W D.toPartialAtlas (m D (m D y x)
        (RawSparseConservationSelection.B (contract D) z)) = 2 ∧
      W D.toPartialAtlas (m D x z) +
        W D.toPartialAtlas (RawSparseConservationSelection.A (contract D) y) = 3 := by
  let F : Extension (nextAtlas threeRaySeed) D.toPartialAtlas :=
    (stepExtension (nextAtlas threeRaySeed)).trans E
  obtain ⟨k, hk0, hk1⟩ := edge_order q (0 : Fin 3) (1 : Fin 3)
    seed_zero_ne_one (by rfl)
  obtain ⟨l, hl0, hl1⟩ := edge_order p (0 : Fin 3) (2 : Fin 3)
    seed_zero_ne_two (by rfl)
  let Q := F.plane (Sum.inr q)
  let P := F.plane (Sum.inr p)
  let X := sw k (1,0)
  let Y := sw k (0,1)
  let T := sw l (1,0)
  let Z := sw l (Complex.I,1)
  let U := mix₂ X Y
  let V := mix₂ Y X
  let x := point (F.ray (Sum.inl (0 : Fin 3))) 1
  let y := point (F.ray (Sum.inl (1 : Fin 3))) 1
  let z := chart D.toPartialAtlas P Z
  have hx : chart D.toPartialAtlas Q X = x := by
    rw [← F.chart_map]
    change F.rawMap (chart (nextAtlas threeRaySeed) (Sum.inr q) (sw k (1,0))) = _
    cases k <;> simp [sw, chart, hk0, hk1, x]
  have hy : chart D.toPartialAtlas Q Y = y := by
    rw [← F.chart_map]
    change F.rawMap (chart (nextAtlas threeRaySeed) (Sum.inr q) (sw k (0,1))) = _
    cases k <;> simp [sw, chart, hk0, hk1, y]
  have ht : chart D.toPartialAtlas P T = x := by
    rw [← F.chart_map]
    change F.rawMap (chart (nextAtlas threeRaySeed) (Sum.inr p) (sw l (1,0))) = _
    cases l <;> simp [sw, chart, hl0, hl1, x]
  have hU0 : U.1 ≠ 0 := by
    cases k <;> norm_num [U,X,Y,sw,mix₂,a,b,Complex.ext_iff]
  have hU1 : U.2 ≠ 0 := by
    cases k <;> norm_num [U,X,Y,sw,mix₂,a,b,Complex.ext_iff]
  have hV0 : V.1 ≠ 0 := by
    cases k <;> norm_num [V,X,Y,sw,mix₂,a,b,Complex.ext_iff]
  have hV1 : V.2 ≠ 0 := by
    cases k <;> norm_num [V,X,Y,sw,mix₂,a,b,Complex.ext_iff]
  have hZ0 : Z.1 ≠ 0 := by cases l <;> norm_num [Z,sw]
  have hZ1 : Z.2 ≠ 0 := by cases l <;> norm_num [Z,sw]
  obtain ⟨tu, htu⟩ := chart_interior threeRaySeed q U.1 U.2 hU0 hU1
  obtain ⟨tv, htv⟩ := chart_interior threeRaySeed q V.1 V.2 hV0 hV1
  obtain ⟨tz, htz⟩ := chart_interior threeRaySeed p Z.1 Z.2 hZ0 hZ1
  have hu : m D x y = point (F.ray (Sum.inr (q,tu))) U.1 := by
    rw [← hx, ← hy, m_chart, ← F.chart_map]
    change F.rawMap (chart (nextAtlas threeRaySeed) (Sum.inr q) (U.1,U.2)) = _
    rw [htu]
    exact F.rawMap_point (Sum.inr (q,tu)) U.1
  have hv : m D y x = point (F.ray (Sum.inr (q,tv))) V.1 := by
    rw [← hy, ← hx, m_chart, ← F.chart_map]
    change F.rawMap (chart (nextAtlas threeRaySeed) (Sum.inr q) (V.1,V.2)) = _
    rw [htv]
    exact F.rawMap_point (Sum.inr (q,tv)) V.1
  have hz : z = point (F.ray (Sum.inr (p,tz))) Z.1 := by
    change chart D.toPartialAtlas (F.plane (Sum.inr p)) Z = _
    rw [← F.chart_map]
    change F.rawMap (chart (nextAtlas threeRaySeed) (Sum.inr p) (Z.1,Z.2)) = _
    rw [htz]
    exact F.rawMap_point (Sum.inr (p,tz)) Z.1
  have huz := different_fresh_edges_uncovered threeRaySeed q p q_ne_p tu tz
  have hvz := different_fresh_edges_uncovered threeRaySeed q p q_ne_p tv tz
  have hune : (Sum.inr (q,tu) : (nextAtlas threeRaySeed).Ray) ≠ Sum.inr (p,tz) := by
    intro h
    exact q_ne_p (congrArg Prod.fst (Sum.inr.inj h))
  have hvne : (Sum.inr (q,tv) : (nextAtlas threeRaySeed).Ray) ≠ Sum.inr (p,tz) := by
    intro h
    exact q_ne_p (congrArg Prod.fst (Sum.inr.inj h))
  have hwu : (nextAtlas threeRaySeed).weight (Sum.inr (q,tu)) * Complex.normSq U.1 = 1 := by
    have hh := first_chart_weight D F q U
    rw [← F.chart_map, F.W_rawMap] at hh
    change W (nextAtlas threeRaySeed) (chart _ (Sum.inr q) (U.1,U.2)) = _ at hh
    rw [htu] at hh
    erw [W_point] at hh
    rw [hh]
    cases k <;> norm_num [U,X,Y,sw,mix₂,a,b,Complex.normSq_apply,
      Complex.div_re,Complex.div_im,Complex.mul_re,Complex.mul_im]
  have hwv : (nextAtlas threeRaySeed).weight (Sum.inr (q,tv)) * Complex.normSq V.1 = 1 := by
    have hh := first_chart_weight D F q V
    rw [← F.chart_map, F.W_rawMap] at hh
    change W (nextAtlas threeRaySeed) (chart _ (Sum.inr q) (V.1,V.2)) = _ at hh
    rw [htv] at hh
    erw [W_point] at hh
    rw [hh]
    cases k <;> norm_num [V,X,Y,sw,mix₂,a,b,Complex.normSq_apply,
      Complex.div_re,Complex.div_im,Complex.mul_re,Complex.mul_im]
  have hwz : (nextAtlas threeRaySeed).weight (Sum.inr (p,tz)) * Complex.normSq Z.1 = 2 := by
    have hh := first_chart_weight D F p Z
    rw [← F.chart_map, F.W_rawMap] at hh
    change W (nextAtlas threeRaySeed) (chart _ (Sum.inr p) (Z.1,Z.2)) = _ at hh
    rw [htz] at hh
    erw [W_point] at hh
    rw [hh]
    cases l <;> norm_num [Z,sw]
  have hwaz : (nextAtlas threeRaySeed).weight (Sum.inr (p,tz)) *
      Complex.normSq (a * Z.1) = 1 := by
    rw [Complex.normSq_mul]
    have ha : Complex.normSq a = 1/2 := by
      norm_num [a,Complex.normSq_apply,Complex.div_re,Complex.div_im]
    rw [ha]
    nlinarith [hwz]
  have hwbz : (nextAtlas threeRaySeed).weight (Sum.inr (p,tz)) *
      Complex.normSq (b * Z.1) = 1 := by
    rw [Complex.normSq_mul]
    have hb : Complex.normSq b = 1/2 := by
      norm_num [b,Complex.normSq_apply,Complex.div_re,Complex.div_im]
    rw [hb]
    nlinarith [hwz]
  have hleft : W D.toPartialAtlas (m D (m D x y)
      (RawSparseConservationSelection.A (contract D) z)) = 1 := by
    rw [hu,hz,A_point]
    change W D.toPartialAtlas (m D (point (E.ray (Sum.inl (Sum.inr (q,tu)))) U.1)
      (point (E.ray (Sum.inl (Sum.inr (p,tz)))) (a * Z.1))) = 1
    rw [attached_mixed_weight _ D E _ _ hune huz, hwu, hwaz]
    norm_num
  have hright : W D.toPartialAtlas (m D (m D y x)
      (RawSparseConservationSelection.B (contract D) z)) = 1 := by
    rw [hv,hz,B_point]
    change W D.toPartialAtlas (m D (point (E.ray (Sum.inl (Sum.inr (q,tv)))) V.1)
      (point (E.ray (Sum.inl (Sum.inr (p,tz)))) (b * Z.1))) = 1
    rw [attached_mixed_weight _ D E _ _ hvne hvz, hwv, hwbz]
    norm_num
  have hxz : W D.toPartialAtlas (m D x z) = 5/2 := by
    rw [← ht]
    change W D.toPartialAtlas (m D (chart D.toPartialAtlas P T) (chart D.toPartialAtlas P Z)) = _
    rw [m_chart,first_chart_weight D F p]
    cases l <;> norm_num [T,Z,sw,mix₂,a,b,Complex.normSq_apply,
      Complex.div_re,Complex.div_im,Complex.mul_re,Complex.mul_im]
  have hay : W D.toPartialAtlas (RawSparseConservationSelection.A (contract D) y) = 1/2 := by
    rw [← hy,contract_A_chart,first_chart_weight D F q]
    cases k <;> norm_num [Y,sw,mix₂,a,b,Complex.normSq_apply,
      Complex.div_re,Complex.div_im,Complex.mul_re,Complex.mul_im]
  exact ⟨x,y,z,by rw [hleft,hright]; norm_num,by rw [hxz,hay]; norm_num⟩

/-- The displayed witness belongs to the actual constructed complete atlas. -/
theorem constructed_sparse_witness :
    ∃ x y z : Raw constructedCompleteAtlas.Ray,
      W constructedCompleteAtlas.toPartialAtlas
        (m constructedCompleteAtlas (m constructedCompleteAtlas x y)
          (RawSparseConservationSelection.A (contract constructedCompleteAtlas) z)) +
      W constructedCompleteAtlas.toPartialAtlas
        (m constructedCompleteAtlas (m constructedCompleteAtlas y x)
          (RawSparseConservationSelection.B (contract constructedCompleteAtlas) z)) = 2 ∧
      W constructedCompleteAtlas.toPartialAtlas (m constructedCompleteAtlas x z) +
        W constructedCompleteAtlas.toPartialAtlas
          (RawSparseConservationSelection.A (contract constructedCompleteAtlas) y) = 3 :=
  stage_two_sparse_witness constructedCompleteAtlas (completionInclusion 2)

/-- Six tests and self-reference do not force the full sparse marginal law. -/
theorem constructed_not_sparse :
    ¬ RawSparseConservationSelection.SparseMarginalLaw
      (contract constructedCompleteAtlas) := by
  intro h
  obtain ⟨x,y,z,hl,hr⟩ := constructed_sparse_witness
  have hh := h x y z
  change W _ (m _ (m _ x y) _) + W _ (m _ (m _ y x) _) =
    W _ (m _ x z) + W _ _ at hh
  rw [hl,hr] at hh
  norm_num at hh

/-- The constructed operation also fails the separate observed-medial premise. -/
theorem constructed_not_observed_medial :
    ¬ RawSparseConservationSelection.ObservedMedial (contract constructedCompleteAtlas) := by
  intro hm
  exact constructed_not_sparse
    (RawSparseConservationSelection.sparse_of_conserved_and_observed_medial _
      (pair_conserved _) hm)

/-- All positive universal properties and the sparse failure hold together. -/
theorem constructed_countermodel :
    RawSparseConservationTests.Tests (contract constructedCompleteAtlas) ∧
    (∀ x y, RawSparseConservationTests.SparseAt (contract constructedCompleteAtlas) x y
      (RawSparseConservationSelection.A (contract constructedCompleteAtlas) x)) ∧
    (∀ x, 0 ≤ (contract constructedCompleteAtlas).weight x) ∧
    (∀ x, (contract constructedCompleteAtlas).weight x = 0 ↔
      x = (contract constructedCompleteAtlas).chosenZero) ∧
    RawSparseConservationSelection.PairConserved (contract constructedCompleteAtlas) ∧
    (∀ c x y, m constructedCompleteAtlas (scale c x) (scale c y) =
      scale c (m constructedCompleteAtlas x y)) ∧
    ¬ RawSparseConservationSelection.SparseMarginalLaw (contract constructedCompleteAtlas) :=
  ⟨tests _, self_sparse _, weight_nonnegative _, weight_faithful _,
    pair_conserved _, m_scale _, constructed_not_sparse⟩

end
end IDT.QMClosure.RawPairPlaneSparseWall
