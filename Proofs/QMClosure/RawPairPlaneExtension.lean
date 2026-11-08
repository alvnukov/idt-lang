import Proofs.QMClosure.RawPairPlaneAtlas

/-!
# One pair-plane extension step

Every uncovered unordered pair of old rays receives a new complex plane. New
non-axis rays retain their edge tag, so distinct new planes share only old axes.
This construction supplies a single partial-atlas successor, without a global
addition or a completed-atlas existence claim.
-/

namespace IDT.QMClosure.RawPairPlaneAtlas

universe u

noncomputable section

open Classical

def Covered (A : PartialAtlas.{u}) (r s : A.Ray) : Prop :=
  ∃ p a b, A.coord p a = r ∧ A.coord p b = s

/-- An unordered pair of old rays contained in no old plane. -/
def Edge (A : PartialAtlas.{u}) :=
  {e : Finset A.Ray // e.card = 2 ∧
    ¬ ∃ p, ∀ r ∈ e, ∃ t, A.coord p t = r}

namespace Edge

variable {A : PartialAtlas.{u}}

private theorem endpoints_exist (e : Edge A) :
    ∃ r s, r ≠ s ∧ e.val = {r, s} := Finset.card_eq_two.mp e.property.1

def left (e : Edge A) : A.Ray := (endpoints_exist e).choose

def right (e : Edge A) : A.Ray := (endpoints_exist e).choose_spec.choose

theorem left_ne_right (e : Edge A) : e.left ≠ e.right :=
  (endpoints_exist e).choose_spec.choose_spec.1

theorem endpoints (e : Edge A) : e.val = {e.left, e.right} :=
  (endpoints_exist e).choose_spec.choose_spec.2

theorem mem_iff (e : Edge A) (r : A.Ray) :
    r ∈ e.val ↔ r = e.left ∨ r = e.right := by simp [e.endpoints]

theorem not_covered (e : Edge A) : ¬ Covered A e.left e.right := by
  rintro ⟨p, a, b, ha, hb⟩
  apply e.property.2
  refine ⟨p, ?_⟩
  intro r hr
  rcases (e.mem_iff r).mp hr with rfl | rfl
  · exact ⟨a, ha⟩
  · exact ⟨b, hb⟩

theorem eq_pair (e : Edge A) {r s : A.Ray} (hrs : r ≠ s)
    (hr : r ∈ e.val) (hs : s ∈ e.val) : e.val = {r, s} := by
  rcases (e.mem_iff r).mp hr with hr | hr <;>
    rcases (e.mem_iff s).mp hs with hs | hs
  · exact (hrs (hr.trans hs.symm)).elim
  · rw [hr, hs, e.endpoints]
  · rw [hr, hs, e.endpoints, Finset.pair_comm]
  · exact (hrs (hr.trans hs.symm)).elim

end Edge

abbrev Fresh (A : PartialAtlas.{u}) := Edge A × NonzeroC

private def newCoord (A : PartialAtlas.{u}) (e : Edge A) :
    Option ℂ → A.Ray ⊕ Fresh A
  | none => Sum.inl e.right
  | some t => if ht : t = 0 then Sum.inl e.left else Sum.inr (e, ⟨t, ht⟩)

@[simp] private theorem newCoord_none (A : PartialAtlas.{u}) (e : Edge A) :
    newCoord A e none = Sum.inl e.right := rfl

@[simp] private theorem newCoord_zero (A : PartialAtlas.{u}) (e : Edge A) :
    newCoord A e (some 0) = Sum.inl e.left := by simp [newCoord]

@[simp] private theorem newCoord_nonzero (A : PartialAtlas.{u}) (e : Edge A)
    (t : NonzeroC) : newCoord A e (some t.val) = Sum.inr (e, t) := by
  simp [newCoord, t.property]

private theorem newCoord_injective (A : PartialAtlas.{u}) (e : Edge A) :
    Function.Injective (newCoord A e) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some t =>
      by_cases ht : t = 0
      · subst t
        have he : e.right = e.left := by simpa [newCoord] using h
        exact (e.left_ne_right he.symm).elim
      · simp [newCoord, ht] at h
  | some s =>
    cases b with
    | none =>
      by_cases hs : s = 0
      · subst s
        have he : e.left = e.right := by simpa [newCoord] using h
        exact (e.left_ne_right he).elim
      · simp [newCoord, hs] at h
    | some t =>
      by_cases hs : s = 0 <;> by_cases ht : t = 0
      · simp [hs, ht]
      · simp [newCoord, hs, ht] at h
      · simp [newCoord, hs, ht] at h
      · have he : s = t := by simpa [newCoord, hs, ht] using h
        exact congrArg some he

private theorem newCoord_old_mem (A : PartialAtlas.{u}) (e : Edge A)
    {t : Option ℂ} {r : A.Ray} (h : newCoord A e t = Sum.inl r) : r ∈ e.val := by
  cases t with
  | none => exact (e.mem_iff r).mpr (Or.inr (Sum.inl.inj h).symm)
  | some t =>
    by_cases ht : t = 0
    · subst t
      have he : e.left = r := by simpa [newCoord] using h
      exact (e.mem_iff r).mpr (Or.inl he.symm)
    · simp [newCoord, ht] at h

private theorem newCoord_fresh (A : PartialAtlas.{u}) (e f : Edge A)
    (t : Option ℂ) (z : NonzeroC)
    (h : newCoord A e t = Sum.inr (f, z)) : e = f := by
  cases t with
  | none => cases h
  | some t =>
    by_cases ht : t = 0
    · simp [newCoord, ht] at h
    · have hp : (e, (⟨t, ht⟩ : NonzeroC)) = (f, z) := by
        simpa only [newCoord, dif_neg ht, Sum.inr.injEq] using h
      exact congrArg Prod.fst hp

private def stepCoord (A : PartialAtlas.{u}) :
    A.Plane ⊕ Edge A → (Option ℂ ↪ A.Ray ⊕ Fresh A)
  | Sum.inl p =>
      { toFun := fun t => Sum.inl (A.coord p t)
        inj' := fun _ _ h => (A.coord p).injective (Sum.inl.inj h) }
  | Sum.inr e => ⟨newCoord A e, newCoord_injective A e⟩

private theorem old_new_impossible (A : PartialAtlas.{u}) (p : A.Plane)
    (e : Edge A) (s t a b : Option ℂ) (hst : s ≠ t)
    (hs : Sum.inl (A.coord p s) = newCoord A e a)
    (ht : Sum.inl (A.coord p t) = newCoord A e b) : False := by
  have hrs : A.coord p s ≠ A.coord p t := fun h => hst ((A.coord p).injective h)
  have he := e.eq_pair hrs (newCoord_old_mem A e hs.symm)
    (newCoord_old_mem A e ht.symm)
  apply e.property.2
  refine ⟨p, ?_⟩
  intro r hr
  rw [he] at hr
  have hr' : r = A.coord p s ∨ r = A.coord p t := by simpa using hr
  rcases hr' with rfl | rfl
  · exact ⟨s, rfl⟩
  · exact ⟨t, rfl⟩

private theorem stepCoord_two_points (A : PartialAtlas.{u})
    (p q : A.Plane ⊕ Edge A) (s t a b : Option ℂ) (hst : s ≠ t)
    (hs : stepCoord A p s = stepCoord A q a)
    (ht : stepCoord A p t = stepCoord A q b) : p = q := by
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      exact congrArg Sum.inl
        (A.two_points p q s t a b hst (Sum.inl.inj hs) (Sum.inl.inj ht))
    | inr e => exact (old_new_impossible A p e s t a b hst hs ht).elim
  | inr e =>
    cases q with
    | inl p =>
      have hab : a ≠ b := by
        intro h
        exact hst ((stepCoord A (Sum.inr e)).injective
          (hs.trans ((congrArg (fun x => stepCoord A (Sum.inl p) x) h).trans ht.symm)))
      exact (old_new_impossible A p e a b s t hab hs.symm ht.symm).elim
    | inr f =>
      apply congrArg Sum.inr
      by_cases hef : e = f
      · exact hef
      have old : ∀ x y, newCoord A e x = newCoord A f y →
          ∃ r, newCoord A e x = Sum.inl r ∧ newCoord A f y = Sum.inl r := by
        intro x y h
        cases hx : newCoord A e x with
        | inl r => exact ⟨r, rfl, h.symm.trans hx⟩
        | inr z =>
          exact (hef ((newCoord_fresh A e z.1 x z.2 hx).trans
            (newCoord_fresh A f z.1 y z.2 (h.symm.trans hx)).symm)).elim
      obtain ⟨r, her, hfr⟩ := old s a hs
      obtain ⟨v, hev, hfv⟩ := old t b ht
      have hrv : r ≠ v := by
        intro h
        exact hst ((newCoord_injective A e)
          (her.trans ((congrArg Sum.inl h).trans hev.symm)))
      apply Subtype.ext
      exact (e.eq_pair hrv (newCoord_old_mem A e her)
        (newCoord_old_mem A e hev)).trans
        (f.eq_pair hrv (newCoord_old_mem A f hfr)
          (newCoord_old_mem A f hfv)).symm

/-- Attach one plane to each currently uncovered unordered old pair. -/
def nextAtlas (A : PartialAtlas.{u}) : PartialAtlas.{u} where
  Ray := A.Ray ⊕ Fresh A
  Plane := A.Plane ⊕ Edge A
  weight := Sum.elim A.weight (fun z =>
    A.weight z.1.left + A.weight z.1.right * Complex.normSq z.2.val)
  weight_pos := by
    intro r
    cases r with
    | inl r => exact A.weight_pos r
    | inr z =>
      exact add_pos_of_pos_of_nonneg (A.weight_pos z.1.left)
        (mul_nonneg (A.weight_pos z.1.right).le (Complex.normSq_nonneg z.2.val))
  coord := stepCoord A
  weight_coord := by
    intro p t
    cases p with
    | inl p => exact A.weight_coord p t
    | inr e =>
      by_cases ht : t = 0
      · subst t
        simp [stepCoord, newCoord]
      · simp [stepCoord, newCoord, ht]
  two_points := stepCoord_two_points A

def stepExtension (A : PartialAtlas.{u}) : Extension A (nextAtlas A) where
  ray := ⟨Sum.inl, Sum.inl_injective⟩
  plane := ⟨Sum.inl, Sum.inl_injective⟩
  weight_map _ := rfl
  coord_map _ _ := rfl

@[simp] theorem next_coord_old (A : PartialAtlas.{u}) (p : A.Plane) (t : Option ℂ) :
    (nextAtlas A).coord (Sum.inl p) t = Sum.inl (A.coord p t) := rfl

@[simp] theorem next_coord_new_none (A : PartialAtlas.{u}) (e : Edge A) :
    (nextAtlas A).coord (Sum.inr e) none = Sum.inl e.right := rfl

@[simp] theorem next_coord_new_zero (A : PartialAtlas.{u}) (e : Edge A) :
    (nextAtlas A).coord (Sum.inr e) (some 0) = Sum.inl e.left :=
  newCoord_zero A e

@[simp] theorem next_coord_new_nonzero (A : PartialAtlas.{u}) (e : Edge A)
    (t : NonzeroC) :
    (nextAtlas A).coord (Sum.inr e) (some t.val) = Sum.inr (e, t) :=
  newCoord_nonzero A e t

@[simp] theorem next_weight_old (A : PartialAtlas.{u}) (r : A.Ray) :
    (nextAtlas A).weight (Sum.inl r) = A.weight r := rfl

@[simp] theorem next_weight_fresh (A : PartialAtlas.{u}) (e : Edge A)
    (t : NonzeroC) : (nextAtlas A).weight (Sum.inr (e, t)) =
      A.weight e.left + A.weight e.right * Complex.normSq t.val := rfl

def edgeOfUncovered (A : PartialAtlas.{u}) (r s : A.Ray) (hrs : r ≠ s)
    (h : ¬ Covered A r s) : Edge A :=
  ⟨{r, s}, by simp [hrs], by
    rintro ⟨p, hp⟩
    obtain ⟨a, ha⟩ := hp r (by simp)
    obtain ⟨b, hb⟩ := hp s (by simp)
    exact h ⟨p, a, b, ha, hb⟩⟩

/-- The two chart axes recover the chosen pair in either possible order. -/
theorem new_plane_axis_pair (A : PartialAtlas.{u}) (r s : A.Ray) (hrs : r ≠ s)
    (h : ¬ Covered A r s) : ∃ e : Edge A,
    ((nextAtlas A).coord (Sum.inr e) (some 0) = Sum.inl r ∧
      (nextAtlas A).coord (Sum.inr e) none = Sum.inl s) ∨
    ((nextAtlas A).coord (Sum.inr e) (some 0) = Sum.inl s ∧
      (nextAtlas A).coord (Sum.inr e) none = Sum.inl r) := by
  let e := edgeOfUncovered A r s hrs h
  have hr : r = e.left ∨ r = e.right := (e.mem_iff r).mp (by simp [e, edgeOfUncovered])
  have hs : s = e.left ∨ s = e.right := (e.mem_iff s).mp (by simp [e, edgeOfUncovered])
  refine ⟨e, ?_⟩
  rcases hr with hr | hr <;> rcases hs with hs | hs
  · exact (hrs (hr.trans hs.symm)).elim
  · exact Or.inl (by simp [hr, hs])
  · exact Or.inr (by simp [hr, hs])
  · exact (hrs (hr.trans hs.symm)).elim

theorem pair_covered_next (A : PartialAtlas.{u}) (r s : A.Ray) (hrs : r ≠ s) :
    Covered (nextAtlas A) (Sum.inl r) (Sum.inl s) := by
  by_cases h : Covered A r s
  · obtain ⟨p, a, b, ha, hb⟩ := h
    exact ⟨Sum.inl p, a, b, congrArg Sum.inl ha, congrArg Sum.inl hb⟩
  · obtain ⟨e, he | he⟩ := new_plane_axis_pair A r s hrs h
    · exact ⟨Sum.inr e, some 0, none, he⟩
    · exact ⟨Sum.inr e, none, some 0, he.2, he.1⟩

theorem fresh_on_plane_iff (A : PartialAtlas.{u}) (e : Edge A) (z : NonzeroC)
    (p : (nextAtlas A).Plane) :
    (∃ t, (nextAtlas A).coord p t = Sum.inr (e, z)) ↔ p = Sum.inr e := by
  constructor
  · rintro ⟨t, ht⟩
    cases p with
    | inl p => cases ht
    | inr f => exact congrArg Sum.inr (newCoord_fresh A f e t z ht)
  · rintro rfl
    exact ⟨some z.val, newCoord_nonzero A e z⟩

theorem different_fresh_edges_uncovered (A : PartialAtlas.{u}) (e f : Edge A)
    (hef : e ≠ f) (z w : NonzeroC) :
    ¬ Covered (nextAtlas A) (Sum.inr (e, z)) (Sum.inr (f, w)) := by
  rintro ⟨p, a, b, ha, hb⟩
  have he := (fresh_on_plane_iff A e z p).mp ⟨a, ha⟩
  have hf := (fresh_on_plane_iff A f w p).mp ⟨b, hb⟩
  exact hef (Sum.inr.inj (he.symm.trans hf))

end

end IDT.QMClosure.RawPairPlaneAtlas
