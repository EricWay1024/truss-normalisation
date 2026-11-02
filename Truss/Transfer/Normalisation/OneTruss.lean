/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.Terminality
import Truss.Transfer.Geometry.OneTruss

/-!
# Open 1-trusses as a 1-truss-like category (§5.3)

This module formalises the opening of §5.3 of the draft normalisation chapter
`transfer/ch03-normalisation-draft.typ`, rows `T01` and `T02` of
[`plan/DraftNormalisationVerification.md`](../../../plan/DraftNormalisationVerification.md):

> Let `K` be the category of open 1-trusses and truss maps.  Then `K` is 1-truss-like, with
> `Tot` the face-poset functor, which is easily seen to be faithful, and `dimsig = dim`.

> **Characterisation of open 1-truss coarsenings.**  A coarsening in `K` is exactly a truss
> map that sends regular elements to regular elements and is surjective on elements.

## Main definitions

* `OpenTruss` — an open 1-truss in Chapter 2's coordinate model, with the truss-map category.
* `OpenTruss.totFunctor` — the face-poset functor `Tot : K ⥤ FinPos`.
* `OpenTruss.instTrussLike` — `T01`: the `TrussLike 1 OpenTruss` instance, with `dimsig = dim`.

## Main results

* `OpenTruss.totMap_apply` — `Tot` of a truss map is its underlying function.
* `isCoarsening_iff_surjective_regular` — `T02`,
  `prop:characterisation-of-open-1-truss-coarsenings`.

## Auxiliary geometry proved here

The lemmas `frameSucc`, `framePred`, `OpenTruss.idx_lt_of_isSingular`,
`OpenTruss.exists_neighbour_succ` and `OpenTruss.exists_neighbour_pred` are facts about
Chapter 2's coordinate model that `Truss/Transfer/Geometry/OneTruss.lean` does not yet
provide; they are proved here rather than upstream because that file is frozen.
-/

namespace Truss.Transfer

open CategoryTheory Geometry

/-! ### Arithmetic in the two-element dimension interval `[2]` -/

/-- `0` is least in `[2]`. -/
private theorem fin2_zero_le (a : Fin 2) : (0 : Fin 2) ≤ a := by revert a; decide

/-- Anything above `1` in `[2]` is `1`. -/
private theorem fin2_eq_one_of_le {a b : Fin 2} (ha : a = 1) (hab : a ≤ b) : b = 1 := by
  subst ha; revert hab; revert b; decide

/-- A comparison in `[2]` is exactly the implication "`1` forces `1`". -/
private theorem fin2_le_of_imp {a b : Fin 2} (h : a = 1 → b = 1) : a ≤ b := by
  revert h; revert b; revert a; decide

/-! ### Frame neighbours in the coordinate model -/

/-- The frame successor of a carrier element strictly below the upper endpoint. -/
def frameSucc {T : OneTruss} (i : T.El) (h : (OneTruss.idx i).val < T.len) : T.El :=
  OneTruss.ofIdx ⟨(OneTruss.idx i).val + 1, by omega⟩

/-- The frame coordinate of the frame successor. -/
@[simp] theorem idx_frameSucc {T : OneTruss} (i : T.El) (h : (OneTruss.idx i).val < T.len) :
    (OneTruss.idx (frameSucc i h)).val = (OneTruss.idx i).val + 1 := rfl

/-- The frame predecessor of a carrier element strictly above the lower endpoint. -/
def framePred {T : OneTruss} (i : T.El) (h : 0 < (OneTruss.idx i).val) : T.El :=
  OneTruss.ofIdx ⟨(OneTruss.idx i).val - 1, by have := (OneTruss.idx i).isLt; omega⟩

/-- The frame coordinate of the frame predecessor. -/
@[simp] theorem idx_framePred {T : OneTruss} (i : T.El) (h : 0 < (OneTruss.idx i).val) :
    (OneTruss.idx (framePred i h)).val = (OneTruss.idx i).val - 1 := rfl

/-! ### T01: the structural category of open 1-trusses -/

/-- **Source: §5.3 opening.**  An *open* 1-truss: a 1-truss in Chapter 2's coordinate model
whose two frame endpoints are regular. -/
structure OpenTruss where
  /-- The underlying 1-truss. -/
  toOneTruss : OneTruss
  /-- Both endpoints are regular. -/
  isOpen : toOneTruss.IsOpen

namespace OpenTruss

/-- **Source: §5.3 opening.**  `K`: open 1-trusses and truss maps.  Lean's `≫` is
"first `f`, then `g`", which is the opposite order to `TrussMap.comp`. -/
instance instCategory : Category OpenTruss where
  Hom T S := TrussMap T.toOneTruss S.toOneTruss
  id T := TrussMap.id T.toOneTruss
  comp f g := g.comp f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The underlying function of the identity of `K`. -/
@[simp] theorem id_toFun (T : OpenTruss) : (𝟙 T : T ⟶ T).toFun = _root_.id := rfl

/-- The underlying function of a composite of `K`. -/
@[simp] theorem comp_toFun {T S R : OpenTruss} (f : T ⟶ S) (g : S ⟶ R) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl

/-- The face-poset map underlying a truss map. -/
def totHom {T S : OpenTruss} (q : T ⟶ S) : T.toOneTruss.El →o S.toOneTruss.El where
  toFun := q.toFun
  monotone' _ _ h := q.face_monotone h

/-- **Source: §5.3 opening.**  The face-poset functor `Tot : K ⥤ FinPos`. -/
def totFunctor : OpenTruss ⥤ FinPartOrd.{0} where
  obj T := FinPartOrd.of T.toOneTruss.El
  map q := FinPartOrd.ofHom (totHom q)
  map_id _ := FinPartOrd.hom_ext rfl
  map_comp _ _ := FinPartOrd.hom_ext rfl

/-- **Source: §5.3 opening, `dimsig = dim`.**  The dimension signature of an open 1-truss,
as a point of the one-dimensional numerical cube `[2]^1`. -/
def dimsigOf (T : OpenTruss) (x : T.toOneTruss.El) : DimCube 1 := fun _ => T.toOneTruss.dim x

/-- The dimension signature is antitone for the face order: a nonidentity face comparison
runs from dimension `1` to dimension `0`. -/
theorem dimsigOf_antitone (T : OpenTruss) : Antitone (dimsigOf T) := by
  intro x y hxy i
  rcases OneTruss.le_iff_faceLE.1 hxy with rfl | ⟨hx, hy, -⟩
  · exact le_rfl
  · change T.toOneTruss.dim y ≤ T.toOneTruss.dim x
    rw [hx, hy]
    exact fin2_zero_le _

/-- **Source: §5.3 opening, `T01`.**  `K` is 1-truss-like: the face-poset functor is
faithful (a truss map is its underlying function) and `dimsig = dim`. -/
instance instTrussLike : TrussLike.{0, 0, 0} 1 OpenTruss where
  tot := totFunctor
  tot_faithful := by
    constructor
    intro T S f g h
    refine TrussMap.ext fun i => ?_
    have h' : totHom f = totHom g :=
      congrArg (fun m : totFunctor.obj T ⟶ totFunctor.obj S => m.hom.hom) h
    exact congrFun (congrArg (fun m : T.toOneTruss.El →o S.toOneTruss.El => m.toFun) h') i
  dimsig := dimsigOf
  dimsig_antitone := dimsigOf_antitone

/-- **Source: §5.3 opening, `T01`.**  In `K` the total map of a morphism is the face-poset
form of its underlying function. -/
theorem totMap_eq {T S : OpenTruss} (q : T ⟶ S) : TrussLike.totMap q = totHom q := rfl

/-- The total map of a morphism of `K`, applied to an element. -/
@[simp] theorem totMap_apply {T S : OpenTruss} (q : T ⟶ S) (x : T.toOneTruss.El) :
    TrussLike.totMap q x = q.toFun x := rfl

/-- The dimension signature of `K` is the Chapter 2 dimension. -/
theorem dimsig_apply (T : OpenTruss) (x : T.toOneTruss.El) (i : Fin 1) :
    TrussLike.dimsig T x i = T.toOneTruss.dim x := rfl

/-! ### Geometry of open 1-trusses used by `T02` -/

/-- **Openness in coordinates.**  A singular element of an open 1-truss is not an endpoint,
so both of its frame neighbours exist. -/
theorem idx_lt_of_isSingular (T : OpenTruss) {y : T.toOneTruss.El}
    (hy : T.toOneTruss.IsSingular y) :
    0 < (OneTruss.idx y).val ∧ (OneTruss.idx y).val < T.toOneTruss.len := by
  have hy0 : T.toOneTruss.dim y = 0 := hy
  constructor
  · by_contra hc
    push_neg at hc
    have hyl : y = T.toOneTruss.lower :=
      OneTruss.idx_injective
        (Fin.ext ((Nat.le_zero.1 hc).trans (OneTruss.idx_lower T.toOneTruss).symm))
    have hreg : T.toOneTruss.dim T.toOneTruss.lower = 1 := T.isOpen.1
    rw [← hyl, hy0] at hreg
    exact absurd hreg (by decide)
  · rcases Nat.lt_or_ge (OneTruss.idx y).val T.toOneTruss.len with h | h
    · exact h
    · exfalso
      have hle : (OneTruss.idx y).val ≤ T.toOneTruss.len := by
        simpa using OneTruss.idx_le_upper y
      have hyu : y = T.toOneTruss.upper :=
        OneTruss.idx_injective
          (Fin.ext ((le_antisymm hle h).trans (OneTruss.idx_upper T.toOneTruss).symm))
      have hreg : T.toOneTruss.dim T.toOneTruss.upper = 1 := T.isOpen.2
      rw [← hyu, hy0] at hreg
      exact absurd hreg (by decide)

/-- The upper frame neighbour of a singular element of an open 1-truss: it exists, it is
regular, and it is a face of the singular element. -/
theorem exists_neighbour_succ (T : OpenTruss) {y : T.toOneTruss.El}
    (hy : T.toOneTruss.IsSingular y) :
    ∃ x : T.toOneTruss.El, (OneTruss.idx x).val = (OneTruss.idx y).val + 1 ∧
      T.toOneTruss.IsRegular x ∧ x ≤ y := by
  obtain ⟨-, hhi⟩ := T.idx_lt_of_isSingular hy
  refine ⟨frameSucc y hhi, idx_frameSucc y hhi, ?_, ?_⟩
  · exact (OneTruss.dim_succ _ y _ (idx_frameSucc y hhi)).trans (OneTruss.flip_eq_one.2 hy)
  · exact Or.inr ⟨(OneTruss.dim_succ _ y _ (idx_frameSucc y hhi)).trans
      (OneTruss.flip_eq_one.2 hy), hy, Or.inl (idx_frameSucc y hhi)⟩

/-- The lower frame neighbour of a singular element of an open 1-truss. -/
theorem exists_neighbour_pred (T : OpenTruss) {y : T.toOneTruss.El}
    (hy : T.toOneTruss.IsSingular y) :
    ∃ x : T.toOneTruss.El, (OneTruss.idx y).val = (OneTruss.idx x).val + 1 ∧
      T.toOneTruss.IsRegular x ∧ x ≤ y := by
  obtain ⟨hlo, -⟩ := T.idx_lt_of_isSingular hy
  have hidx : (OneTruss.idx y).val = (OneTruss.idx (framePred y hlo)).val + 1 := by
    rw [idx_framePred]; omega
  have hreg : T.toOneTruss.IsRegular (framePred y hlo) := by
    have hd : T.toOneTruss.dim y = OneTruss.flip (T.toOneTruss.dim (framePred y hlo)) :=
      OneTruss.dim_succ _ _ y hidx
    exact OneTruss.flip_eq_zero.1 (hd ▸ hy)
  exact ⟨framePred y hlo, hidx, hreg, Or.inr ⟨hreg, hy, Or.inr hidx⟩⟩

/-- **Source: §5.3 proof note.**  Face monotonicity makes the image of a regular face of a
singular element a regular face of its image; frame monotonicity then selects the side. -/
theorem map_idx_side {T S : OpenTruss} (q : T ⟶ S)
    (hreg : ∀ i, T.toOneTruss.IsRegular i → S.toOneTruss.IsRegular (q.toFun i))
    {x y : T.toOneTruss.El} (hx : T.toOneTruss.IsRegular x)
    (hqy : S.toOneTruss.IsSingular (q.toFun y)) (hxy : x ≤ y) :
    ((OneTruss.idx x).val = (OneTruss.idx y).val + 1 →
        (OneTruss.idx (q.toFun x)).val = (OneTruss.idx (q.toFun y)).val + 1) ∧
      ((OneTruss.idx y).val = (OneTruss.idx x).val + 1 →
        (OneTruss.idx (q.toFun y)).val = (OneTruss.idx (q.toFun x)).val + 1) := by
  have hqx : S.toOneTruss.dim (q.toFun x) = 1 := hreg x hx
  have hqy0 : S.toOneTruss.dim (q.toFun y) = 0 := hqy
  have hne : q.toFun x ≠ q.toFun y := by
    intro hc
    rw [hc, hqy0] at hqx
    exact absurd hqx (by decide)
  have hlt : q.toFun x < q.toFun y := lt_of_le_of_ne (q.face_monotone hxy) hne
  have hadj := OneTruss.idx_adjacent_of_lt hlt
  constructor
  · intro h
    have hm : (OneTruss.idx (q.toFun y)).val ≤ (OneTruss.idx (q.toFun x)).val :=
      q.idx_mono (by omega)
    omega
  · intro h
    have hm : (OneTruss.idx (q.toFun x)).val ≤ (OneTruss.idx (q.toFun y)).val :=
      q.idx_mono (by omega)
    omega

/-- **Source: §5.3 proof, "`fib_q (y)` is a frame interval".**  A point fibre of a truss map
is closed under passing to an intermediate frame coordinate. -/
theorem pointFibre_interval {T S : OpenTruss} (q : T ⟶ S) {i j k : T.toOneTruss.El}
    (hij : (OneTruss.idx i).val ≤ (OneTruss.idx j).val)
    (hjk : (OneTruss.idx j).val ≤ (OneTruss.idx k).val) (h : q.toFun i = q.toFun k) :
    q.toFun j = q.toFun i := by
  have h1 := q.idx_mono hij
  have h2 := q.idx_mono hjk
  have h3 : (OneTruss.idx (q.toFun k)).val = (OneTruss.idx (q.toFun i)).val := by rw [h]
  exact OneTruss.idx_injective (Fin.ext (by omega))

/-- Frame-monotone induction along a point fibre: consecutive frame coordinates inside a
point fibre are face-comparable, so the fibre is a face zigzag. -/
theorem pointFibre_zigzag_aux {T S : OpenTruss} (q : T ⟶ S) (y : S.toOneTruss.El) :
    ∀ (k : ℕ) (a b : T.toOneTruss.El), (OneTruss.idx b).val = (OneTruss.idx a).val + k →
      q.toFun a = y → q.toFun b = y →
      ZigzagIn (pointFibre (TrussLike.totMap q) y) a b := by
  intro k
  induction k with
  | zero =>
      intro a b hab _ _
      have : a = b := OneTruss.idx_injective (Fin.ext (by omega))
      subst this
      exact ZigzagIn.refl _
  | succ k ih =>
      intro a b hab ha hb
      have hbl := (OneTruss.idx b).isLt
      have hlt : (OneTruss.idx a).val < T.toOneTruss.len := by omega
      have hidx : (OneTruss.idx (frameSucc a hlt)).val = (OneTruss.idx a).val + 1 :=
        idx_frameSucc a hlt
      have hmem : q.toFun (frameSucc a hlt) = y := by
        have hint := pointFibre_interval q (i := a) (j := frameSucc a hlt) (k := b)
          (by omega) (by omega) (ha.trans hb.symm)
        rw [hint, ha]
      have hcomp : a ≤ frameSucc a hlt ∨ frameSucc a hlt ≤ a :=
        OneTruss.faceComparable_of_succ _ hidx
      have hstep : ZigzagStep (pointFibre (TrussLike.totMap q) y) a (frameSucc a hlt) :=
        ⟨ha, hmem, hcomp⟩
      exact (ZigzagIn.single hstep).trans (ih (frameSucc a hlt) b (by omega) hmem hb)

/-- **Source: §5.3 proof.**  Every point fibre of a truss map is a face-zigzag-connected
frame interval. -/
theorem pointFibre_zigzag {T S : OpenTruss} (q : T ⟶ S) (y : S.toOneTruss.El)
    {a b : T.toOneTruss.El} (ha : q.toFun a = y) (hb : q.toFun b = y) :
    ZigzagIn (pointFibre (TrussLike.totMap q) y) a b := by
  rcases Nat.le_total (OneTruss.idx a).val (OneTruss.idx b).val with h | h
  · exact pointFibre_zigzag_aux q y ((OneTruss.idx b).val - (OneTruss.idx a).val) a b
      (by omega) ha hb
  · exact (pointFibre_zigzag_aux q y ((OneTruss.idx a).val - (OneTruss.idx b).val) b a
      (by omega) hb ha).symm

/-- A zigzag inside a point fibre lifts to a zigzag of identity arrows. -/
theorem zigzagIn_diag {T S : OpenTruss} (q : T ⟶ S) (y : S.toOneTruss.El)
    {a b : T.toOneTruss.El} (h : ZigzagIn (pointFibre (TrussLike.totMap q) y) a b) :
    ZigzagIn (arrowFibre (TrussLike.totMap q) y y)
      (Arr.mk a a le_rfl) (Arr.mk b b le_rfl) := by
  induction h with
  | refl => exact ZigzagIn.refl _
  | tail _ hstep ih =>
      refine ih.tail ⟨⟨hstep.1, hstep.1⟩, ⟨hstep.2.1, hstep.2.1⟩, ?_⟩
      exact hstep.2.2.imp (fun hc => ⟨hc, hc⟩) (fun hc => ⟨hc, hc⟩)

/-- **Source: §5.3 proof, identity-arrow clause.**  The arrow fibre over an identity arrow
is connected: every arrow of the fibre lies below the identity arrow on its target, and the
identity arrows of the fibre are connected by the point-fibre zigzag. -/
theorem arrowFibre_self_connected {T S : OpenTruss} (q : T ⟶ S) (y : S.toOneTruss.El) :
    IsZigzagConnected (arrowFibre (TrussLike.totMap q) y y) := by
  intro A hA B hB
  have hAd : Arr.mk A.tgt A.tgt le_rfl ∈ arrowFibre (TrussLike.totMap q) y y := ⟨hA.2, hA.2⟩
  have hBd : Arr.mk B.tgt B.tgt le_rfl ∈ arrowFibre (TrussLike.totMap q) y y := ⟨hB.2, hB.2⟩
  have s1 : ZigzagIn (arrowFibre (TrussLike.totMap q) y y) A (Arr.mk A.tgt A.tgt le_rfl) :=
    ZigzagIn.of_le hA hAd ⟨A.le, le_rfl⟩
  have s3 : ZigzagIn (arrowFibre (TrussLike.totMap q) y y) (Arr.mk B.tgt B.tgt le_rfl) B :=
    ZigzagIn.of_ge hBd hB ⟨B.le, le_rfl⟩
  exact s1.trans ((zigzagIn_diag q y (pointFibre_zigzag q y hA.2 hB.2)).trans s3)

/-- **Source: §5.3 proof, "`q⁻¹(y')` contains a unique singular element".**  A point fibre
over a singular element consists of singular elements only, and a frame interval of a
1-truss contains at most one singular element without containing a regular one between
them, so the fibre is a subsingleton. -/
theorem pointFibre_singular_subsingleton {T S : OpenTruss} (q : T ⟶ S)
    (hreg : ∀ i, T.toOneTruss.IsRegular i → S.toOneTruss.IsRegular (q.toFun i))
    {y' : S.toOneTruss.El} (hy' : S.toOneTruss.IsSingular y') {z₁ z₂ : T.toOneTruss.El}
    (h₁ : q.toFun z₁ = y') (h₂ : q.toFun z₂ = y') : z₁ = z₂ := by
  have hy0 : S.toOneTruss.dim y' = 0 := hy'
  have hsing : ∀ z : T.toOneTruss.El, q.toFun z = y' → T.toOneTruss.dim z = 0 := by
    intro z hz
    rcases OneTruss.isSingular_or_isRegular T.toOneTruss z with h | h
    · exact h
    · exfalso
      have hq : S.toOneTruss.dim (q.toFun z) = 1 := hreg z h
      rw [hz, hy0] at hq
      exact absurd hq (by decide)
  have key : ∀ a b : T.toOneTruss.El, q.toFun a = y' → q.toFun b = y' →
      (OneTruss.idx a).val ≤ (OneTruss.idx b).val → a = b := by
    intro a b ha hb hab
    rcases Nat.eq_or_lt_of_le hab with h | h
    · exact OneTruss.idx_injective (Fin.ext h)
    · exfalso
      have hbl := (OneTruss.idx b).isLt
      have hlt : (OneTruss.idx a).val < T.toOneTruss.len := by omega
      have hidx : (OneTruss.idx (frameSucc a hlt)).val = (OneTruss.idx a).val + 1 :=
        idx_frameSucc a hlt
      have hmem : q.toFun (frameSucc a hlt) = y' := by
        have hint := pointFibre_interval q (i := a) (j := frameSucc a hlt) (k := b)
          (by omega) (by omega) (ha.trans hb.symm)
        rw [hint, ha]
      have hd : T.toOneTruss.dim (frameSucc a hlt) = OneTruss.flip (T.toOneTruss.dim a) :=
        OneTruss.dim_succ _ a _ hidx
      rw [hsing a ha] at hd
      rw [hsing _ hmem] at hd
      exact absurd hd.symm (by decide)
  rcases Nat.le_total (OneTruss.idx z₁).val (OneTruss.idx z₂).val with h | h
  · exact key z₁ z₂ h₁ h₂ h
  · exact (key z₂ z₁ h₂ h₁ h).symm

/-- **Source: §5.3 proof, nonidentity-arrow clause.**  An arrow fibre over a nonidentity
arrow of `S` is a subsingleton: its target is the unique element of the singular point
fibre, and frame monotonicity pins down which neighbour of that target is its source. -/
theorem arrowFibre_lt_subsingleton {T S : OpenTruss} (q : T ⟶ S)
    (hreg : ∀ i, T.toOneTruss.IsRegular i → S.toOneTruss.IsRegular (q.toFun i))
    {y y' : S.toOneTruss.El} (hyy' : y < y') {A B : Arr T.toOneTruss.El}
    (hA : A ∈ arrowFibre (TrussLike.totMap q) y y')
    (hB : B ∈ arrowFibre (TrussLike.totMap q) y y') : A = B := by
  obtain ⟨-, hy'0, -⟩ := OneTruss.lt_iff.1 hyy'
  have hy'sing : S.toOneTruss.IsSingular y' := hy'0
  have hyne : y ≠ y' := hyy'.ne
  have key : ∀ C : Arr T.toOneTruss.El, C ∈ arrowFibre (TrussLike.totMap q) y y' →
      (OneTruss.idx C.src).val + (OneTruss.idx y').val
        = (OneTruss.idx C.tgt).val + (OneTruss.idx y).val := by
    intro C hC
    have hsrc : q.toFun C.src = y := hC.1
    have htgt : q.toFun C.tgt = y' := hC.2
    have hne : C.src ≠ C.tgt := by
      intro hc
      rw [hc, htgt] at hsrc
      exact hyne hsrc.symm
    obtain ⟨hdsrc, -, hadj⟩ := OneTruss.lt_iff.1 (lt_of_le_of_ne C.le hne)
    have hside := map_idx_side q hreg (x := C.src) (y := C.tgt) hdsrc
      (by rw [htgt]; exact hy'sing) C.le
    rw [hsrc, htgt] at hside
    rcases hadj with h | h
    · have := hside.1 h; omega
    · have := hside.2 h; omega
  have htgt : A.tgt = B.tgt :=
    pointFibre_singular_subsingleton q hreg hy'sing hA.2 hB.2
  have hA' := key A hA
  have hB' := key B hB
  have hidx : (OneTruss.idx A.src).val = (OneTruss.idx B.src).val := by
    rw [htgt] at hA'; omega
  exact Arr.ext (OneTruss.idx_injective (Fin.ext hidx)) htgt

end OpenTruss

/-! ### T02: the characterisation of open 1-truss coarsenings -/

/-- **Source: `prop:characterisation-of-open-1-truss-coarsenings` (§5.3), row `T02`.**
A coarsening in the category of open 1-trusses is exactly a truss map that is surjective on
elements and sends regular elements to regular elements. -/
theorem isCoarsening_iff_surjective_regular {T S : OpenTruss} (q : T ⟶ S) :
    IsCoarsening q ↔ Function.Surjective q.toFun ∧
      ∀ i, T.toOneTruss.IsRegular i → S.toOneTruss.IsRegular (q.toFun i) := by
  constructor
  · rintro ⟨htot, hdim⟩
    refine ⟨htot.surjective, fun i hi => ?_⟩
    exact fin2_eq_one_of_le hi (hdim i ⟨0, by omega⟩)
  · rintro ⟨hsurj, hreg⟩
    refine ⟨⟨hsurj, ?_, ?_⟩, ?_⟩
    · -- openness: exact target lifting
      rw [isOpenPosetMap_iff_exists_le (TrussLike.totMap q).monotone]
      intro y w hw
      have hw' : w ≤ q.toFun y := hw
      by_cases hwe : w = q.toFun y
      · exact ⟨y, le_rfl, hwe.symm⟩
      · obtain ⟨-, hqy0, hadj⟩ := OneTruss.lt_iff.1 (lt_of_le_of_ne hw' hwe)
        have hqysing : S.toOneTruss.IsSingular (q.toFun y) := hqy0
        have hysing : T.toOneTruss.IsSingular y := by
          rcases OneTruss.isSingular_or_isRegular T.toOneTruss y with h | h
          · exact h
          · exfalso
            have hq : S.toOneTruss.dim (q.toFun y) = 1 := hreg y h
            rw [hqy0] at hq
            exact absurd hq (by decide)
        rcases hadj with hA | hA
        · obtain ⟨x, hxidx, hxreg, hxle⟩ := T.exists_neighbour_succ hysing
          refine ⟨x, hxle, ?_⟩
          have h1 := (OpenTruss.map_idx_side q hreg hxreg hqysing hxle).1 hxidx
          change q.toFun x = w
          exact OneTruss.idx_injective (Fin.ext (by omega))
        · obtain ⟨x, hxidx, hxreg, hxle⟩ := T.exists_neighbour_pred hysing
          refine ⟨x, hxle, ?_⟩
          have h1 := (OpenTruss.map_idx_side q hreg hxreg hqysing hxle).2 hxidx
          change q.toFun x = w
          exact OneTruss.idx_injective (Fin.ext (by omega))
    · -- arrow-fibre connectivity
      intro y y' hyy'
      rcases eq_or_lt_of_le hyy' with rfl | hlt
      · exact OpenTruss.arrowFibre_self_connected q y
      · intro A hA B hB
        have : A = B := OpenTruss.arrowFibre_lt_subsingleton q hreg hlt hA hB
        subst this
        exact ZigzagIn.refl _
    · -- the dimension inequality
      intro x i
      change T.toOneTruss.dim x ≤ S.toOneTruss.dim (q.toFun x)
      exact fin2_le_of_imp (fun h => hreg x h)

end Truss.Transfer
