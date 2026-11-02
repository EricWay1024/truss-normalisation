/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Geometry.OpenCoord

/-!
# Non-trivially labelled singular elements, and the descent criterion (§5.3)

This module formalises the part of §"Open 1-trusses" of the draft normalisation chapter
`transfer/ch03-normalisation-draft.typ` that identifies *which arrows a coarsening of open
1-trusses collapses*, and turns the descent criterion of §5.1 into the chapter's combinatorial
criterion: the definitions `Non-trivially labelled singular element` and `The labelled
retained-set poset`, and the proof of
`prop:Outgoing labelled coarsenings as retained sets`.

Throughout, `T S : OpenTruss`, `k := T.numSing`, and `C` is an **arbitrary** category: no
gauntness, thinness, skeletality or `Prop`-valuedness is assumed of the label category.

## Main definitions

* `OpenTruss.singEl`, `OpenTruss.regLow`, `OpenTruss.regHigh` — the `i`-th singular element
  (frame index `2i+1`) and its two regular frame neighbours (frame indices `2i` and `2i+2`).
* `OpenTruss.incomingArr` — the incoming non-identity arrow at `singEl i` on a given side.
* `IsIdLabelled` — an arrow of the face order is *labelled by an identity*.  Per the draft's
  own convention this includes the equality of the two endpoint object labels.
* `NonTriv` — the finset of non-trivially labelled singular indices.

## Main results

* `OpenTruss.faceLt_iff_incoming` — the face order of an open 1-truss in coordinates.
* `OpenTruss.incoming_of_singEl`, `OpenTruss.exists_unique_incomingArr` — a non-identity arrow
  of `T` is exactly a pair (singular index, side).
* `OpenTruss.collapses_iff_target_isRegular` — a coarsening collapses an arrow with regular
  source exactly when the image of the target is regular; hence
  `OpenTruss.collapses_incomingArr_iff_isRegular` and
  `OpenTruss.not_collapses_incomingArr_of_isSingular`: the arrows collapsed by a coarsening
  are exactly the two incoming arrows of each *discarded* singular element, and no others.
* `sendsCollapsedToId_iff_nonTriv_retained` and `descendsAlong_iff_nonTriv_retained` — the
  chapter's criterion: a label descends along a coarsening exactly when every non-trivially
  labelled singular element is retained.

The retained set `ret q` itself is *not* named here; the right-hand side of the criterion is
spelled out as "the image of the `i`-th singular element is singular".
-/

universe u₂ v₂

namespace Truss.Transfer

open CategoryTheory Geometry Geometry.OneTruss TrussLike

namespace OpenTruss

variable {T : OpenTruss}

/-! ### Part 1: the face order of an open 1-truss, in coordinates -/

/-- **The face order of a 1-truss in coordinates.**  A strict face comparison `x < y` holds
exactly when `y` is singular, `x` is regular, and their frame indices differ by one.  This is
`OneTruss.lt_iff` spelled with `IsRegular`/`IsSingular`. -/
theorem faceLt_iff_incoming {x y : T.toOneTruss.El} :
    x < y ↔ T.toOneTruss.IsRegular x ∧ T.toOneTruss.IsSingular y ∧
      ((idx x).val = (idx y).val + 1 ∨ (idx y).val = (idx x).val + 1) :=
  OneTruss.lt_iff

variable {k : ℕ}

/-- The `i`-th singular element of `T`, as a carrier element; its frame index is `2i+1`. -/
def singEl (T : OpenTruss) (hk : T.numSing = k) (i : Fin k) : T.toOneTruss.El :=
  (T.singAt hk i).el

/-- The lower regular frame neighbour of the `i`-th singular element; its frame index is
`2i`. -/
def regLow (T : OpenTruss) (hk : T.numSing = k) (i : Fin k) : T.toOneTruss.El :=
  (T.regAt hk i.castSucc).el

/-- The upper regular frame neighbour of the `i`-th singular element; its frame index is
`2i+2`. -/
def regHigh (T : OpenTruss) (hk : T.numSing = k) (i : Fin k) : T.toOneTruss.El :=
  (T.regAt hk i.succ).el

@[simp] theorem idx_singEl (hk : T.numSing = k) (i : Fin k) :
    (idx (T.singEl hk i)).val = 2 * i.val + 1 := rfl

@[simp] theorem idx_regLow (hk : T.numSing = k) (i : Fin k) :
    (idx (T.regLow hk i)).val = 2 * i.val := rfl

@[simp] theorem idx_regHigh (hk : T.numSing = k) (i : Fin k) :
    (idx (T.regHigh hk i)).val = 2 * i.val + 2 := by
  change 2 * (i.val + 1) = 2 * i.val + 2
  omega

theorem isSingular_singEl (hk : T.numSing = k) (i : Fin k) :
    T.toOneTruss.IsSingular (T.singEl hk i) := (T.singAt hk i).isSingular

theorem isRegular_regLow (hk : T.numSing = k) (i : Fin k) :
    T.toOneTruss.IsRegular (T.regLow hk i) := (T.regAt hk i.castSucc).isRegular

theorem isRegular_regHigh (hk : T.numSing = k) (i : Fin k) :
    T.toOneTruss.IsRegular (T.regHigh hk i) := (T.regAt hk i.succ).isRegular

/-- **The first incoming arrow of the `i`-th singular element**, from the regular element at
frame index `2i`. -/
theorem regLow_le_singEl (hk : T.numSing = k) (i : Fin k) :
    T.regLow hk i ≤ T.singEl hk i :=
  Or.inr ⟨T.isRegular_regLow hk i, T.isSingular_singEl hk i, Or.inr (by simp)⟩

/-- **The second incoming arrow of the `i`-th singular element**, from the regular element at
frame index `2i+2`. -/
theorem regHigh_le_singEl (hk : T.numSing = k) (i : Fin k) :
    T.regHigh hk i ≤ T.singEl hk i :=
  Or.inr ⟨T.isRegular_regHigh hk i, T.isSingular_singEl hk i, Or.inl (by simp)⟩

/-- The two regular neighbours of a singular element are distinct. -/
theorem regLow_ne_regHigh (hk : T.numSing = k) (i : Fin k) :
    T.regLow hk i ≠ T.regHigh hk i := by
  intro h
  have := congrArg (fun z => (idx z).val) h
  simp only [idx_regLow, idx_regHigh] at this
  omega

/-- **There are no other incoming arrows.**  A strict face predecessor of the `i`-th singular
element is one of its two regular frame neighbours. -/
theorem incoming_of_singEl (hk : T.numSing = k) {x : T.toOneTruss.El} {i : Fin k}
    (h : x < T.singEl hk i) : x = T.regLow hk i ∨ x = T.regHigh hk i := by
  obtain ⟨-, -, hadj⟩ := faceLt_iff_incoming.1 h
  simp only [idx_singEl] at hadj
  rcases hadj with hadj | hadj
  · exact Or.inr (idx_injective (Fin.ext (by simp only [idx_regHigh]; omega)))
  · exact Or.inl (idx_injective (Fin.ext (by simp only [idx_regLow]; omega)))

/-- **Every non-identity arrow has a singular target, with a singular index.**  A strict face
comparison of `T` runs into the `i`-th singular element for a (unique) `i`. -/
theorem exists_singEl_of_lt (hk : T.numSing = k) {x y : T.toOneTruss.El} (h : x < y) :
    ∃ i : Fin k, y = T.singEl hk i ∧ (x = T.regLow hk i ∨ x = T.regHigh hk i) := by
  obtain ⟨-, hy, -⟩ := faceLt_iff_incoming.1 h
  refine ⟨T.singIdx hk ⟨y, hy⟩, ?_, ?_⟩
  · exact congrArg Sing.el (T.singAt_singIdx hk ⟨y, hy⟩).symm
  · refine incoming_of_singEl hk ?_
    show x < T.singEl hk (T.singIdx hk ⟨y, hy⟩)
    rwa [show T.singEl hk (T.singIdx hk ⟨y, hy⟩) = y from
      congrArg Sing.el (T.singAt_singIdx hk ⟨y, hy⟩)]

/-- The singular index of a non-identity arrow is determined by the arrow. -/
theorem singEl_injective (hk : T.numSing = k) : Function.Injective (T.singEl hk) := by
  intro i j h
  have := congrArg (fun z => (idx z).val) h
  simp only [idx_singEl] at this
  exact Fin.ext (by omega)

/-- **Source: §5.3, the two incoming arrows.**  The incoming non-identity arrow at the `i`-th
singular element on the side selected by `b`: `false` is the lower neighbour (frame index
`2i`), `true` the upper one (frame index `2i+2`). -/
def incomingArr (T : OpenTruss) (hk : T.numSing = k) (i : Fin k) (b : Bool) :
    Arr T.toOneTruss.El where
  src := if b then T.regHigh hk i else T.regLow hk i
  tgt := T.singEl hk i
  le := by cases b with
    | false => exact T.regLow_le_singEl hk i
    | true => exact T.regHigh_le_singEl hk i

@[simp] theorem incomingArr_tgt (hk : T.numSing = k) (i : Fin k) (b : Bool) :
    (T.incomingArr hk i b).tgt = T.singEl hk i := rfl

@[simp] theorem incomingArr_src_false (hk : T.numSing = k) (i : Fin k) :
    (T.incomingArr hk i false).src = T.regLow hk i := rfl

@[simp] theorem incomingArr_src_true (hk : T.numSing = k) (i : Fin k) :
    (T.incomingArr hk i true).src = T.regHigh hk i := rfl

/-- An incoming arrow is a non-identity arrow. -/
theorem incomingArr_src_ne_tgt (hk : T.numSing = k) (i : Fin k) (b : Bool) :
    (T.incomingArr hk i b).src ≠ (T.incomingArr hk i b).tgt := by
  cases b <;>
    · intro h
      have := congrArg (fun z => (idx z).val) h
      simp only [incomingArr_src_false, incomingArr_src_true, incomingArr_tgt, idx_regLow,
        idx_regHigh, idx_singEl] at this
      omega

/-- The side of an incoming arrow, read off from its source by a decidable test. -/
theorem eq_incomingArr_src (hk : T.numSing = k) {x : T.toOneTruss.El} {i : Fin k}
    (h : x = T.regLow hk i ∨ x = T.regHigh hk i) :
    x = (T.incomingArr hk i (decide (x = T.regHigh hk i))).src := by
  rcases h with hs | hs
  · rw [decide_eq_false (by rw [hs]; exact T.regLow_ne_regHigh hk i)]
    exact hs
  · rw [decide_eq_true hs]
    exact hs

/-- **Source: §5.3, "a non-identity arrow is a pair (singular index, side)".**  Every
non-identity arrow of an open 1-truss is `incomingArr` for exactly one pair `(i, b)`. -/
theorem exists_unique_incomingArr (hk : T.numSing = k) (a : Arr T.toOneTruss.El)
    (h : a.src ≠ a.tgt) : ∃! p : Fin k × Bool, a = T.incomingArr hk p.1 p.2 := by
  obtain ⟨i, htgt, hsrc⟩ := exists_singEl_of_lt hk (lt_of_le_of_ne a.le h)
  refine ⟨⟨i, decide (a.src = T.regHigh hk i)⟩, Arr.ext (eq_incomingArr_src hk hsrc) htgt, ?_⟩
  rintro ⟨j, c⟩ hj
  have htj : T.singEl hk i = T.singEl hk j := by rw [← htgt, hj]; rfl
  have hij : j = i := (singEl_injective hk htj).symm
  subst hij
  have hsrc' : a.src = (T.incomingArr hk j c).src := by rw [hj]
  refine Prod.ext rfl ?_
  cases c with
  | false =>
      rw [incomingArr_src_false] at hsrc'
      exact (decide_eq_false (by rw [hsrc']; exact T.regLow_ne_regHigh hk j)).symm
  | true =>
      rw [incomingArr_src_true] at hsrc'
      exact (decide_eq_true hsrc').symm

/-! ### Part 2: the arrows collapsed by a coarsening -/

variable {S : OpenTruss}

/-- **The substantive direction.**  If the image of the target of a face comparison is
regular, the comparison is collapsed: face monotonicity sends the comparison to a face
comparison of `S`, and a non-identity face comparison of `S` has singular target. -/
theorem collapses_of_target_isRegular (q : T ⟶ S) {x y : T.toOneTruss.El} (hxy : x ≤ y)
    (hy : S.toOneTruss.IsRegular (q.toFun y)) : q.toFun x = q.toFun y := by
  rcases OneTruss.le_iff_faceLE.1 (q.face_monotone hxy) with h | ⟨-, h0, -⟩
  · exact h
  · exact absurd (h0.symm.trans hy) (by decide)

/-- The converse direction, for an arrow with regular source: a coarsening preserves
regularity, so a collapsed arrow has regular image. -/
theorem isRegular_of_collapses (q : T ⟶ S)
    (hreg : ∀ i, T.toOneTruss.IsRegular i → S.toOneTruss.IsRegular (q.toFun i))
    {x y : T.toOneTruss.El} (hx : T.toOneTruss.IsRegular x) (h : q.toFun x = q.toFun y) :
    S.toOneTruss.IsRegular (q.toFun y) := h ▸ hreg x hx

/-- **Source: §5.3.**  A coarsening collapses a face comparison with regular source exactly
when it sends the target to a regular element. -/
theorem collapses_iff_target_isRegular (q : T ⟶ S)
    (hreg : ∀ i, T.toOneTruss.IsRegular i → S.toOneTruss.IsRegular (q.toFun i))
    {x y : T.toOneTruss.El} (hxy : x ≤ y) (hx : T.toOneTruss.IsRegular x) :
    q.toFun x = q.toFun y ↔ S.toOneTruss.IsRegular (q.toFun y) :=
  ⟨isRegular_of_collapses q hreg hx, collapses_of_target_isRegular q hxy⟩

/-- **Source: §5.3, `collapses_iff_target_regular`.**  A coarsening collapses an incoming
arrow at the `i`-th singular element exactly when it sends that singular element to a regular
element of `S` — and then it collapses *both* incoming arrows. -/
theorem collapses_incomingArr_iff_isRegular (q : T ⟶ S) (hq : IsCoarsening q)
    (hk : T.numSing = k) (i : Fin k) (b : Bool) :
    q.toFun (T.incomingArr hk i b).src = q.toFun (T.incomingArr hk i b).tgt ↔
      S.toOneTruss.IsRegular (q.toFun (T.singEl hk i)) := by
  have hreg := ((isCoarsening_iff_surjective_regular q).1 hq).2
  cases b with
  | false =>
      exact collapses_iff_target_isRegular q hreg (T.regLow_le_singEl hk i)
        (T.isRegular_regLow hk i)
  | true =>
      exact collapses_iff_target_isRegular q hreg (T.regHigh_le_singEl hk i)
        (T.isRegular_regHigh hk i)

/-- **Source: §5.3, `not_collapses_of_target_singular`.**  If a coarsening retains the `i`-th
singular element, then neither of its two incoming arrows is collapsed. -/
theorem not_collapses_incomingArr_of_isSingular (q : T ⟶ S) (hq : IsCoarsening q)
    (hk : T.numSing = k) (i : Fin k) (b : Bool)
    (hs : S.toOneTruss.IsSingular (q.toFun (T.singEl hk i))) :
    q.toFun (T.incomingArr hk i b).src ≠ q.toFun (T.incomingArr hk i b).tgt := by
  intro h
  have hr := (collapses_incomingArr_iff_isRegular q hq hk i b).1 h
  exact absurd (hs.symm.trans hr) (by decide)

/-- **The collapsed non-identity arrows of a coarsening, all of them.**  A collapsed face
comparison is either an identity or an incoming arrow of a *discarded* singular element. -/
theorem collapsed_cases (q : T ⟶ S) (hq : IsCoarsening q) (hk : T.numSing = k)
    {x y : T.toOneTruss.El} (hxy : x ≤ y) (hcol : q.toFun x = q.toFun y) :
    x = y ∨ ∃ (i : Fin k) (b : Bool), x = (T.incomingArr hk i b).src ∧
      y = T.singEl hk i ∧ S.toOneTruss.IsRegular (q.toFun (T.singEl hk i)) := by
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact Or.inl rfl
  · obtain ⟨i, htgt, hsrc⟩ := exists_singEl_of_lt hk hlt
    refine Or.inr ⟨i, decide (x = T.regHigh hk i), eq_incomingArr_src hk hsrc, htgt, ?_⟩
    · have hxreg : T.toOneTruss.IsRegular x := (faceLt_iff_incoming.1 hlt).1
      have hreg := ((isCoarsening_iff_surjective_regular q).1 hq).2
      rw [← htgt]
      exact isRegular_of_collapses q hreg hxreg hcol

end OpenTruss

/-! ### Part 3: non-trivially labelled singular elements -/

variable {C : Type u₂} [Category.{v₂} C]

/-- **Source: §5.3, the draft's convention.**  An arrow of the face order is *labelled by an
identity* when its two endpoint object labels are equal and its arrow label is the
corresponding object bridge.  No thinness or gauntness of `C` is assumed, so the equality of
object labels is genuine extra data and must be part of the definition. -/
def IsIdLabelled {T : OpenTruss} (L : Tot T ⥤ C) {x y : T.toOneTruss.El} (h : x ≤ y) : Prop :=
  ∃ e : L.obj x = L.obj y, L.map (homOfLE h) = eqToHom e

/-- An identity arrow is always labelled by an identity. -/
theorem isIdLabelled_refl {T : OpenTruss} (L : Tot T ⥤ C) (x : T.toOneTruss.El) :
    IsIdLabelled L (le_refl x) := by
  refine ⟨rfl, ?_⟩
  rw [show homOfLE (le_refl (x : Tot T)) = 𝟙 x from Subsingleton.elim _ _]
  simp

/-- The predicate "the `i`-th singular element is non-trivially labelled": its two incoming
arrows are *not* both labelled by identities. -/
def IsNonTriv (T : OpenTruss) (L : Tot T ⥤ C) (i : Fin T.numSing) : Prop :=
  ¬ (IsIdLabelled L (T.regLow_le_singEl rfl i) ∧ IsIdLabelled L (T.regHigh_le_singEl rfl i))

open Classical in
/-- **Source: `Non-trivially labelled singular element` (§5.3).**  `NonTriv(X, L)`: the set of
singular elements whose two incoming arrows are not both labelled by identities, indexed by
the frame-order enumeration of the singular elements. -/
noncomputable def NonTriv (T : OpenTruss) (L : Tot T ⥤ C) : Finset (Fin T.numSing) :=
  Finset.univ.filter (IsNonTriv T L)

open Classical in
@[simp] theorem mem_nonTriv {T : OpenTruss} {L : Tot T ⥤ C} {i : Fin T.numSing} :
    i ∈ NonTriv T L ↔ IsNonTriv T L i := by
  simp [NonTriv]

/-- Being outside `NonTriv` says exactly that both incoming arrows are identity labelled. -/
theorem isIdLabelled_of_not_mem_nonTriv {T : OpenTruss} {L : Tot T ⥤ C} {i : Fin T.numSing}
    (h : i ∉ NonTriv T L) :
    IsIdLabelled L (T.regLow_le_singEl rfl i) ∧ IsIdLabelled L (T.regHigh_le_singEl rfl i) :=
  not_not.1 (mem_nonTriv.not.1 h)

/-! ### Part 4: the descent criterion -/

/-- The descent criterion of §5.1, spelled in the coordinates of §5.3. -/
theorem sendsCollapsedToId_iff_isIdLabelled {T S : OpenTruss} (q : T ⟶ S) (L : Tot T ⥤ C) :
    SendsCollapsedToId (TrussLike.totMap q) L ↔
      ∀ (x y : T.toOneTruss.El) (h : x ≤ y), q.toFun x = q.toFun y → IsIdLabelled L h :=
  Iff.rfl

/-- **Source: `prop:Outgoing labelled coarsenings as retained sets` (§5.3), the proof's
criterion.**  A `C`-valued label of an open 1-truss descends along a coarsening `q` exactly
when every non-trivially labelled singular element is retained by `q`, i.e. is sent to a
singular element of the target.

The right-hand side is what §5.3 writes as `NonTriv(X, L) ⊆ ret(q)`. -/
theorem sendsCollapsedToId_iff_nonTriv_retained {T S : OpenTruss} (q : T ⟶ S)
    (hq : IsCoarsening q) (L : Tot T ⥤ C) :
    SendsCollapsedToId (TrussLike.totMap q) L ↔
      ∀ i ∈ NonTriv T L, S.toOneTruss.IsSingular (q.toFun (T.singEl rfl i)) := by
  constructor
  · -- Forward: a discarded singular element has both incoming arrows collapsed, hence
    -- identity labelled, hence is not in `NonTriv`.
    intro hSC i hi
    rcases OneTruss.isSingular_or_isRegular S.toOneTruss (q.toFun (T.singEl rfl i)) with h | h
    · exact h
    · exfalso
      refine mem_nonTriv.1 hi ⟨?_, ?_⟩
      · exact hSC _ _ (T.regLow_le_singEl rfl i)
          (OpenTruss.collapses_of_target_isRegular q (T.regLow_le_singEl rfl i) h)
      · exact hSC _ _ (T.regHigh_le_singEl rfl i)
          (OpenTruss.collapses_of_target_isRegular q (T.regHigh_le_singEl rfl i) h)
  · -- Backward: the only collapsed non-identity arrows are the incoming arrows of the
    -- discarded singular elements, which lie outside `NonTriv`.
    intro hret x y hxy hcol
    have hcol' : q.toFun x = q.toFun y := hcol
    rcases OpenTruss.collapsed_cases q hq rfl hxy hcol' with rfl | ⟨i, b, hsrc, htgt, hregim⟩
    · exact isIdLabelled_refl L x
    · have hnot : i ∉ NonTriv T L := fun hi =>
        absurd ((hret i hi).symm.trans hregim) (by decide)
      obtain ⟨hlow, hhigh⟩ := isIdLabelled_of_not_mem_nonTriv hnot
      subst htgt
      cases b with
      | false =>
          rw [OpenTruss.incomingArr_src_false] at hsrc
          subst hsrc
          exact hlow
      | true =>
          rw [OpenTruss.incomingArr_src_true] at hsrc
          subst hsrc
          exact hhigh

/-- **Source: `prop:Outgoing labelled coarsenings as retained sets` (§5.3).**  Combining the
criterion with `prop:draft-label-descent` (`label_descent`, §5.1): a coarsening of open
1-trusses is label preserving exactly when it retains every non-trivially labelled singular
element. -/
theorem descendsAlong_iff_nonTriv_retained {T S : OpenTruss} (q : T ⟶ S) (hq : IsCoarsening q)
    (L : Tot T ⥤ C) :
    DescendsAlong q L ↔
      ∀ i ∈ NonTriv T L, S.toOneTruss.IsSingular (q.toFun (T.singEl rfl i)) :=
  sendsCollapsedToId_iff_nonTriv_retained q hq L

/-- **Source: `prop:Outgoing labelled coarsenings as retained sets` (§5.3), existence form.**
A descended labelling of the target exists exactly when every non-trivially labelled singular
element is retained. -/
theorem exists_descend_iff_nonTriv_retained {T S : OpenTruss} (q : T ⟶ S)
    (hq : IsCoarsening q) (L : Tot T ⥤ C) :
    (∃ M : Tot S ⥤ C, posetFunctor (TrussLike.totMap q) ⋙ M = L) ↔
      ∀ i ∈ NonTriv T L, S.toOneTruss.IsSingular (q.toFun (T.singEl rfl i)) :=
  (label_descent hq.tot L).trans (sendsCollapsedToId_iff_nonTriv_retained q hq L)

end Truss.Transfer
