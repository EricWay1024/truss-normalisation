/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.BundleFibre
import Truss.Transfer.Geometry.OpenBordism
import Truss.Transfer.Geometry.BordismRel

/-!
# The category `B(C)` of `C`-labelled 1-trusses, and classification at `n = 1`

This module formalises, for `n = 1`, the labelling layer of Chapter 2 of
`dphil-notes-typst/transfer/ch02-trusses.typ`: the total poset of a bordism
(`Total poset of a bordism`), `def:labelled-bundle` and `def:labelled-bundle-bordism` over
the point, the category `B(C)` of `C`-labelled 1-trusses, and the classification
`thm:classification` together with its strict-representative corollary
(`def:labelled-bundle-reindexing`).

## Main definitions

* `Geometry.Bord1.Tot` — the total poset of a 1-truss bordism, with the chapter's displayed
  order; `Geometry.Bord1.inlEmb`, `inrEmb` — the two layer inclusions, as order embeddings.
* `LabOneTruss C` — a `C`-labelled open 1-truss (`def:labelled-bundle` at `n = 1` over the
  point).
* `LabBord X Y` — a `C`-labelled 1-truss bordism (`def:labelled-bundle-bordism`): a bordism
  plus a labelling of its whole total poset restricting to the two endpoint labels.
* `LabBord.cross` — the *cross-arrow label*, the label of an arrow `(0,x) ⊴ (1,y)`
  normalised into a map `X.label.obj x ⟶ Y.label.obj y` by the two restrictions.
* `LabBord.crossMk` — the converse: a labelled bordism built from a bordism and a family of
  cross labels satisfying the two naturality laws.
* `LabBord.idLab`, `LabBord.compLab`, `LabBord.instCategory` — `B(C)`.
* `OpenBundle.classify`, `totalise` — the classifying functor `χ` and the totalisation `π`
  of `thm:classification` at `n = 1`.

## Main results

* `LabBord.cross_comp_witness_indep` — **witness-independent cross-arrow composition.**  The
  composite `R.cross ≫ Q.cross` of two cross labels at a witness `y` does not depend on the
  witness.  The proof is the one the chapter sketches: the witness set is the intersection
  of the frame interval `R(x,−)` with the frame interval `Q⁻¹(z)` (`Bord1.image_frameConvex`
  and `Bord1.preimage_frameConvex`), hence a frame interval; two witnesses at adjacent frame
  indices are face comparable (`OneTruss.faceComparable_of_succ`), and there the two
  composites agree by right naturality in `R` and left naturality in `Q`
  (`LabBord.cross_comp_face`); induction along the interval finishes.
* `LabBord.ext_cross` — a labelled bordism is determined by its bordism and its cross labels.
* `classify_totalise`, `totalise_classify` — the two round trips, **on the nose**: strict
  equalities, not isomorphisms.
* `totalise_comp` — `π(F ∘ f) = f^* π(F)`, by `rfl`.  The chapter *postulates* strict
  representatives with this property; in the functorial presentation it is a theorem,
  because `f^*` is precomposition.

## A point where the source's phrasing has to be sharpened

`OpenBundle.arrTotHom h : (A.arr h).Tot →o A.Tot` (`(0,x) ↦ (b,x)`, `(1,y) ↦ (c,y)`) is
always **monotone**, which is all the labelling uses, but it is an **order embedding only
for `b < c`** (`OpenBundle.arrTotEmb`).  For `b = c` it glues the two layers onto the single
fibre `A_b`, so it is neither injective nor order reflecting.
-/

universe u v

namespace Truss.Transfer

open CategoryTheory Geometry Geometry.OneTruss

/-! ### A builder for functors out of a poset -/

/-- Build a functor out of a poset from object data and arrow data. -/
def posetMk {P : Type u} [Preorder P] {C : Type v} [Category.{v} C] (obj : P → C)
    (map : ∀ {x y : P}, x ≤ y → (obj x ⟶ obj y))
    (hid : ∀ x : P, map (le_refl x) = 𝟙 (obj x))
    (hcomp : ∀ {x y z : P} (h₁ : x ≤ y) (h₂ : y ≤ z),
      map (h₁.trans h₂) = map h₁ ≫ map h₂) : P ⥤ C where
  obj := obj
  map f := map (leOfHom f)
  map_id x := hid x
  map_comp _ _ := hcomp _ _

@[simp] theorem posetMk_obj {P : Type u} [Preorder P] {C : Type v} [Category.{v} C]
    (obj : P → C) (map : ∀ {x y : P}, x ≤ y → (obj x ⟶ obj y)) (hid) (hcomp) (x : P) :
    (posetMk obj map hid hcomp).obj x = obj x := rfl

@[simp] theorem posetMk_map {P : Type u} [Preorder P] {C : Type v} [Category.{v} C]
    (obj : P → C) (map : ∀ {x y : P}, x ≤ y → (obj x ⟶ obj y)) (hid) (hcomp) {x y : P}
    (h : x ≤ y) : (posetMk obj map hid hcomp).map (homOfLE h) = map h := rfl


/-- Two functors out of a poset agree as soon as they agree on objects and on the arrows
given by `homOfLE`. -/
theorem posetFunctor_ext {P : Type u} [PartialOrder P] {C : Type v} [Category.{v} C]
    {F G : P ⥤ C} (hobj : ∀ p, F.obj p = G.obj p)
    (hmap : ∀ {p q : P} (h : p ≤ q),
      F.map (homOfLE h) = eqToHom (hobj p) ≫ G.map (homOfLE h) ≫ eqToHom (hobj q).symm) :
    F = G :=
  CategoryTheory.Functor.ext hobj fun _ _ f => hmap (leOfHom f)

/-! ### §1  The total poset of a 1-truss bordism -/

namespace Geometry.Bord1

variable {T S : OneTruss}

/-- **Source: `Total poset of a bordism` (Chapter 2).**  The carrier of the total poset of a
bordism: the disjoint union of the two carriers. -/
def Tot (_R : Bord1 T S) : Type := T.El ⊕ S.El

/-- **Source: `Total poset of a bordism`, order.**  The displayed order. -/
protected def Le (R : Bord1 T S) : R.Tot → R.Tot → Prop
  | Sum.inl x, Sum.inl x' => x ≤ x'
  | Sum.inr y, Sum.inr y' => y ≤ y'
  | Sum.inl x, Sum.inr y => R.rel x y
  | Sum.inr _, Sum.inl _ => False

instance instPartialOrder (R : Bord1 T S) : PartialOrder R.Tot where
  le := R.Le
  le_refl p := by
    match p with
    | Sum.inl _ => exact le_rfl
    | Sum.inr _ => exact le_rfl
  le_trans p q r := by
    match p, q, r with
    | Sum.inl _, Sum.inl _, Sum.inl _ => exact fun h₁ h₂ => le_trans h₁ h₂
    | Sum.inl _, Sum.inl _, Sum.inr _ => exact fun h₁ h₂ => R.preimage_downClosed h₁ h₂
    | Sum.inl _, Sum.inr _, Sum.inr _ => exact fun h₁ h₂ => R.image_upClosed h₁ h₂
    | Sum.inr _, Sum.inr _, Sum.inr _ => exact fun h₁ h₂ => le_trans h₁ h₂
    | Sum.inl _, Sum.inr _, Sum.inl _ => exact fun _ h₂ => h₂.elim
    | Sum.inr _, Sum.inl _, _ => exact fun h₁ _ => h₁.elim
    | Sum.inr _, Sum.inr _, Sum.inl _ => exact fun _ h₂ => h₂.elim
  le_antisymm p q := by
    match p, q with
    | Sum.inl _, Sum.inl _ => exact fun h₁ h₂ => congrArg Sum.inl (le_antisymm h₁ h₂)
    | Sum.inr _, Sum.inr _ => exact fun h₁ h₂ => congrArg Sum.inr (le_antisymm h₁ h₂)
    | Sum.inl _, Sum.inr _ => exact fun _ h₂ => h₂.elim
    | Sum.inr _, Sum.inl _ => exact fun h₁ _ => h₁.elim

variable (R : Bord1 T S)

/-- The inclusion of the source layer into the total poset. -/
def inlHom : T.El →o R.Tot where
  toFun := Sum.inl
  monotone' _ _ h := h

/-- The inclusion of the target layer into the total poset. -/
def inrHom : S.El →o R.Tot where
  toFun := Sum.inr
  monotone' _ _ h := h

@[simp] theorem inlHom_apply (x : T.El) : R.inlHom x = Sum.inl x := rfl

@[simp] theorem inrHom_apply (y : S.El) : R.inrHom y = Sum.inr y := rfl

@[simp] theorem inl_le_inl_iff (x x' : T.El) : R.inlHom x ≤ R.inlHom x' ↔ x ≤ x' := Iff.rfl

@[simp] theorem inr_le_inr_iff (y y' : S.El) : R.inrHom y ≤ R.inrHom y' ↔ y ≤ y' := Iff.rfl

@[simp] theorem inl_le_inr_iff (x : T.El) (y : S.El) :
    R.inlHom x ≤ R.inrHom y ↔ R.rel x y := Iff.rfl

@[simp] theorem not_inr_le_inl (y : S.El) (x : T.El) : ¬ (R.inrHom y ≤ R.inlHom x) := id

/-- The source-layer inclusion is an order embedding. -/
def inlEmb : T.El ↪o R.Tot where
  toFun := Sum.inl
  inj' _ _ h := Sum.inl.inj h
  map_rel_iff' := Iff.rfl

/-- The target-layer inclusion is an order embedding. -/
def inrEmb : S.El ↪o R.Tot where
  toFun := Sum.inr
  inj' _ _ h := Sum.inr.inj h
  map_rel_iff' := Iff.rfl

end Geometry.Bord1

/-! ### §2  Labelled 1-trusses and labelled bordisms -/

variable {C : Type v} [Category.{v} C]

/-- **Source: `def:labelled-bundle` at `n = 1` over the point.**  A `C`-labelled open
1-truss: an open 1-truss together with a functor from its face poset to `C`. -/
structure LabOneTruss (C : Type v) [Category.{v} C] where
  /-- The underlying open 1-truss. -/
  truss : OpenTruss
  /-- The labelling functor on the face poset. -/
  label : truss.toOneTruss.El ⥤ C

/-- **Source: `def:labelled-bundle-bordism` at `n = 1` over the point.**  A `C`-labelled
1-truss bordism: a bordism of the underlying 1-trusses together with a labelling of its
whole total poset restricting to the two endpoint labels. -/
structure LabBord (X Y : LabOneTruss C) where
  /-- The underlying 1-truss bordism. -/
  bord : Geometry.Bord1 X.truss.toOneTruss Y.truss.toOneTruss
  /-- The labelling of the total poset. -/
  lbl : bord.Tot ⥤ C
  /-- Source restriction. -/
  src : posetFunctor bord.inlHom ⋙ lbl = X.label
  /-- Target restriction. -/
  tgt : posetFunctor bord.inrHom ⋙ lbl = Y.label

namespace LabBord

variable {X Y Z : LabOneTruss C}

/-- The source restriction, on objects. -/
theorem srcObj (R : LabBord X Y) (x : X.truss.toOneTruss.El) :
    R.lbl.obj (R.bord.inlHom x) = X.label.obj x := Functor.congr_obj R.src x

/-- The target restriction, on objects. -/
theorem tgtObj (R : LabBord X Y) (y : Y.truss.toOneTruss.El) :
    R.lbl.obj (R.bord.inrHom y) = Y.label.obj y := Functor.congr_obj R.tgt y

/-- The source restriction, on arrows. -/
theorem lbl_map_inl (R : LabBord X Y) {x x' : X.truss.toOneTruss.El} (h : x ≤ x') :
    R.lbl.map (homOfLE ((R.bord.inl_le_inl_iff x x').2 h))
      = eqToHom (R.srcObj x) ≫ X.label.map (homOfLE h) ≫ eqToHom (R.srcObj x').symm :=
  Functor.congr_hom R.src (homOfLE h)

/-- The target restriction, on arrows. -/
theorem lbl_map_inr (R : LabBord X Y) {y y' : Y.truss.toOneTruss.El} (h : y ≤ y') :
    R.lbl.map (homOfLE ((R.bord.inr_le_inr_iff y y').2 h))
      = eqToHom (R.tgtObj y) ≫ Y.label.map (homOfLE h) ≫ eqToHom (R.tgtObj y').symm :=
  Functor.congr_hom R.tgt (homOfLE h)

/-- **The cross-arrow label.**  The label of the arrow `(0,x) ⊴ (1,y)` of the total poset,
normalised to a map between the *endpoint* object labels using the two restrictions. -/
def cross (R : LabBord X Y) {x : X.truss.toOneTruss.El} {y : Y.truss.toOneTruss.El}
    (h : R.bord.rel x y) : X.label.obj x ⟶ Y.label.obj y :=
  eqToHom (R.srcObj x).symm
    ≫ R.lbl.map (homOfLE ((R.bord.inl_le_inr_iff x y).2 h))
    ≫ eqToHom (R.tgtObj y)

/-- **Left naturality of the cross label.** -/
theorem cross_left (R : LabBord X Y) {x x' : X.truss.toOneTruss.El}
    {y : Y.truss.toOneTruss.El} (hxx' : x ≤ x') (h : R.bord.rel x' y) :
    X.label.map (homOfLE hxx') ≫ R.cross h = R.cross (R.bord.preimage_downClosed hxx' h) := by
  have hsplit : R.lbl.map (homOfLE ((R.bord.inl_le_inr_iff x y).2
        (R.bord.preimage_downClosed hxx' h)))
      = R.lbl.map (homOfLE ((R.bord.inl_le_inl_iff x x').2 hxx'))
        ≫ R.lbl.map (homOfLE ((R.bord.inl_le_inr_iff x' y).2 h)) := by
    rw [← Functor.map_comp]
    rfl
  rw [cross, cross, hsplit, R.lbl_map_inl hxx']
  simp

/-- **Right naturality of the cross label.** -/
theorem cross_right (R : LabBord X Y) {x : X.truss.toOneTruss.El}
    {y y' : Y.truss.toOneTruss.El} (h : R.bord.rel x y) (hyy' : y ≤ y') :
    R.cross h ≫ Y.label.map (homOfLE hyy') = R.cross (R.bord.image_upClosed h hyy') := by
  have hsplit : R.lbl.map (homOfLE ((R.bord.inl_le_inr_iff x y').2
        (R.bord.image_upClosed h hyy')))
      = R.lbl.map (homOfLE ((R.bord.inl_le_inr_iff x y).2 h))
        ≫ R.lbl.map (homOfLE ((R.bord.inr_le_inr_iff y y').2 hyy')) := by
    rw [← Functor.map_comp]
    rfl
  rw [cross, cross, hsplit, R.lbl_map_inr hyy']
  simp

/-! ### §2b  Building a labelled bordism from its cross-arrow labels -/

/-- **The cross-arrow presentation of a labelled bordism.**  A labelled bordism is exactly a
bordism together with a family of cross-arrow labels satisfying the two naturality laws. -/
def crossMk (R : Geometry.Bord1 X.truss.toOneTruss Y.truss.toOneTruss)
    (cr : ∀ {x : X.truss.toOneTruss.El} {y : Y.truss.toOneTruss.El},
      R.rel x y → (X.label.obj x ⟶ Y.label.obj y))
    (hleft : ∀ {x x' : X.truss.toOneTruss.El} {y : Y.truss.toOneTruss.El} (hxx' : x ≤ x')
      (h : R.rel x' y), X.label.map (homOfLE hxx') ≫ cr h = cr (R.preimage_downClosed hxx' h))
    (hright : ∀ {x : X.truss.toOneTruss.El} {y y' : Y.truss.toOneTruss.El} (h : R.rel x y)
      (hyy' : y ≤ y'), cr h ≫ Y.label.map (homOfLE hyy') = cr (R.image_upClosed h hyy')) :
    LabBord X Y where
  bord := R
  lbl := posetMk
    (fun p => match p with
      | Sum.inl x => X.label.obj x
      | Sum.inr y => Y.label.obj y)
    (fun {p q} => match p, q with
      | Sum.inl _, Sum.inl _ => fun h => X.label.map (homOfLE h)
      | Sum.inl _, Sum.inr _ => fun h => cr h
      | Sum.inr _, Sum.inr _ => fun h => Y.label.map (homOfLE h)
      | Sum.inr _, Sum.inl _ => fun h => h.elim)
    (by
      intro p
      match p with
      | Sum.inl x => exact X.label.map_id x
      | Sum.inr y => exact Y.label.map_id y)
    (by
      intro p q r h₁ h₂
      match p, q, r, h₁, h₂ with
      | Sum.inl _, Sum.inl _, Sum.inl _, h₁, h₂ => exact X.label.map_comp _ _
      | Sum.inl _, Sum.inl _, Sum.inr _, h₁, h₂ => exact (hleft h₁ h₂).symm
      | Sum.inl _, Sum.inr _, Sum.inr _, h₁, h₂ => exact (hright h₁ h₂).symm
      | Sum.inr _, Sum.inr _, Sum.inr _, h₁, h₂ => exact Y.label.map_comp _ _
      | Sum.inl _, Sum.inr _, Sum.inl _, _, h₂ => exact h₂.elim
      | Sum.inr _, Sum.inl _, _, h₁, _ => exact h₁.elim
      | Sum.inr _, Sum.inr _, Sum.inl _, _, h₂ => exact h₂.elim)
  src := rfl
  tgt := rfl

@[simp] theorem crossMk_bord (R : Geometry.Bord1 X.truss.toOneTruss Y.truss.toOneTruss)
    (cr) (hleft) (hright) : (crossMk (X := X) (Y := Y) R cr hleft hright).bord = R := rfl

@[simp] theorem crossMk_cross (R : Geometry.Bord1 X.truss.toOneTruss Y.truss.toOneTruss)
    (cr) (hleft) (hright) {x : X.truss.toOneTruss.El} {y : Y.truss.toOneTruss.El}
    (h : R.rel x y) : (crossMk (X := X) (Y := Y) R cr hleft hright).cross h = cr h := by
  rw [cross]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-! ### §2c  Extensionality -/

/-- **A labelled bordism is determined by its bordism and its cross-arrow labels.**  The
two layers of the label are fixed by the source and target restrictions, and there is
nothing else in the total poset. -/
theorem ext_cross {R R' : LabBord X Y} (hb : R.bord = R'.bord)
    (hc : ∀ (x : X.truss.toOneTruss.El) (y : Y.truss.toOneTruss.El)
      (h : R.bord.rel x y) (h' : R'.bord.rel x y), R.cross h = R'.cross h') : R = R' := by
  obtain ⟨b, l, hs, ht⟩ := R
  obtain ⟨b', l', hs', ht'⟩ := R'
  subst hb
  have hobj : ∀ p : b.Tot, l.obj p = l'.obj p := by
    intro p
    match p with
    | Sum.inl x => exact (Functor.congr_obj hs x).trans (Functor.congr_obj hs' x).symm
    | Sum.inr y => exact (Functor.congr_obj ht y).trans (Functor.congr_obj ht' y).symm
  have hl : l = l' := by
    refine posetFunctor_ext hobj ?_
    intro p q h
    match p, q, h with
    | Sum.inl x, Sum.inl x', h =>
      have e₁ : l.map (homOfLE h) = eqToHom (Functor.congr_obj hs x)
          ≫ X.label.map (homOfLE (show x ≤ x' from h))
          ≫ eqToHom (Functor.congr_obj hs x').symm :=
        Functor.congr_hom hs (homOfLE (show x ≤ x' from h))
      have e₂ : l'.map (homOfLE h) = eqToHom (Functor.congr_obj hs' x)
          ≫ X.label.map (homOfLE (show x ≤ x' from h))
          ≫ eqToHom (Functor.congr_obj hs' x').symm :=
        Functor.congr_hom hs' (homOfLE (show x ≤ x' from h))
      rw [e₁, e₂]
      simp
    | Sum.inr y, Sum.inr y', h =>
      have e₁ : l.map (homOfLE h) = eqToHom (Functor.congr_obj ht y)
          ≫ Y.label.map (homOfLE (show y ≤ y' from h))
          ≫ eqToHom (Functor.congr_obj ht y').symm :=
        Functor.congr_hom ht (homOfLE (show y ≤ y' from h))
      have e₂ : l'.map (homOfLE h) = eqToHom (Functor.congr_obj ht' y)
          ≫ Y.label.map (homOfLE (show y ≤ y' from h))
          ≫ eqToHom (Functor.congr_obj ht' y').symm :=
        Functor.congr_hom ht' (homOfLE (show y ≤ y' from h))
      rw [e₁, e₂]
      simp
    | Sum.inl x, Sum.inr y, h =>
      have hcx := hc x y h h
      simp only [cross] at hcx
      rw [← Category.assoc, ← Category.assoc] at hcx
      have := congrArg (fun g => eqToHom (Functor.congr_obj hs x) ≫ g
        ≫ eqToHom (Functor.congr_obj ht y).symm) hcx
      simpa using this
    | Sum.inr _, Sum.inl _, h => exact h.elim
  subst hl
  rfl

/-- **The cross-arrow presentation is faithful.**  Every labelled bordism is `crossMk` of
its own bordism and its own cross labels. -/
theorem crossMk_self (R : LabBord X Y) :
    crossMk R.bord (fun h => R.cross h) (fun hxx' h => R.cross_left hxx' h)
      (fun h hyy' => R.cross_right h hyy') = R :=
  ext_cross rfl fun _ _ _ _ => by rw [crossMk_cross]

end LabBord

/-! ### §3  The category `B(C)` of `C`-labelled 1-trusses -/

namespace LabBord

variable {X Y Z : LabOneTruss C}

/-- **Source: `Identity 1-bordism` (Chapter 2), labelled.**  The identity labelled bordism.
The total poset of `id_T` is two copies of `T` glued along the face order, so the label is
determined by `X.label`: the cross arrow `(0,x) ⊴ (1,y)` is the face arrow `x ⊴ y`. -/
def idLab (X : LabOneTruss C) : LabBord X X :=
  crossMk (idBord X.truss.toOneTruss) (fun {_ _} h => X.label.map (homOfLE h))
    (fun hxx' h => by rw [← Functor.map_comp]; rfl)
    (fun h hyy' => by rw [← Functor.map_comp]; rfl)

@[simp] theorem idLab_bord (X : LabOneTruss C) : (idLab X).bord = idBord X.truss.toOneTruss :=
  rfl

@[simp] theorem idLab_cross (X : LabOneTruss C) {x y : X.truss.toOneTruss.El}
    (h : (idLab X).bord.rel x y) :
    (idLab X).cross h = X.label.map (homOfLE (show x ≤ y from h)) :=
  crossMk_cross _ _ _ _ h

/-! #### Witness-independent cross-arrow composition -/

/-- **One step of witness independence.**  If two witnesses are *face comparable*, the two
composite cross labels agree, by right naturality in `R` and left naturality in `Q`. -/
theorem cross_comp_face (R : LabBord X Y) (Q : LabBord Y Z)
    {x : X.truss.toOneTruss.El} {y y' : Y.truss.toOneTruss.El} {z : Z.truss.toOneTruss.El}
    (hyy' : y ≤ y') (h₁ : R.bord.rel x y) (h₂ : Q.bord.rel y' z) :
    R.cross h₁ ≫ Q.cross (Q.bord.preimage_downClosed hyy' h₂)
      = R.cross (R.bord.image_upClosed h₁ hyy') ≫ Q.cross h₂ := by
  rw [← Q.cross_left hyy' h₂, ← R.cross_right h₁ hyy', Category.assoc]

/-- The induction along the frame interval of witnesses. -/
theorem cross_comp_indep_aux (R : LabBord X Y) (Q : LabBord Y Z)
    {x : X.truss.toOneTruss.El} {z : Z.truss.toOneTruss.El} :
    ∀ (n : ℕ) (y y' : Y.truss.toOneTruss.El), (idx y').val = (idx y).val + n →
      ∀ (h₁ : R.bord.rel x y) (h₂ : Q.bord.rel y z)
        (h₁' : R.bord.rel x y') (h₂' : Q.bord.rel y' z),
        R.cross h₁ ≫ Q.cross h₂ = R.cross h₁' ≫ Q.cross h₂' := by
  intro n
  induction n with
  | zero =>
    intro y y' hn h₁ h₂ h₁' h₂'
    obtain rfl : y' = y := Y.truss.el_eq_of_idx_eq (by omega)
    rfl
  | succ n ih =>
    intro y y' hn h₁ h₂ h₁' h₂'
    have hb : (idx y).val + 1 ≤ 2 * Y.truss.numSing := by
      have := Y.truss.idx_le y'; omega
    obtain ⟨w, hwidx⟩ : ∃ w : Y.truss.toOneTruss.El, (idx w).val = (idx y).val + 1 :=
      ⟨Y.truss.elAt hb, rfl⟩
    have hRw : R.bord.rel x w := by
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact (Y.truss.el_eq_of_idx_eq (show (idx w).val = (idx y').val by omega)) ▸ h₁'
      · exact R.bord.image_frameConvex Y.truss.isOpen (by omega) (by omega) h₁ h₁'
    have hQw : Q.bord.rel w z := by
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact (Y.truss.el_eq_of_idx_eq (show (idx w).val = (idx y').val by omega)) ▸ h₂'
      · exact Q.bord.preimage_frameConvex (by omega) (by omega) h₂ h₂'
    have step : R.cross h₁ ≫ Q.cross h₂ = R.cross hRw ≫ Q.cross hQw := by
      rcases Y.truss.toOneTruss.faceComparable_of_succ hwidx with hle | hle
      · exact cross_comp_face R Q hle h₁ hQw
      · exact (cross_comp_face R Q hle hRw h₂).symm
    rw [step]
    exact ih w y' (by omega) hRw hQw h₁' h₂'

/-- **Witness-independent cross-arrow composition.**  The composite cross label of a
composable pair does not depend on the chosen witness.

The witness set `W(x,z) = {y | R(x,y) and Q(y,z)}` is the intersection of the frame interval
`R(x,-)` with the frame interval `Q⁻¹(z)` (`Bord1.image_frameConvex`,
`Bord1.preimage_frameConvex`), hence is itself a frame interval.  Two witnesses at adjacent
frame indices are face comparable (`OneTruss.faceComparable_of_succ`), and for those the two
composites agree by `cross_comp_face`; induction along the interval finishes. -/
theorem cross_comp_witness_indep (R : LabBord X Y) (Q : LabBord Y Z)
    {x : X.truss.toOneTruss.El} {z : Z.truss.toOneTruss.El}
    {y y' : Y.truss.toOneTruss.El} (h₁ : R.bord.rel x y) (h₂ : Q.bord.rel y z)
    (h₁' : R.bord.rel x y') (h₂' : Q.bord.rel y' z) :
    R.cross h₁ ≫ Q.cross h₂ = R.cross h₁' ≫ Q.cross h₂' := by
  rcases le_total (idx y).val (idx y').val with hle | hle
  · exact cross_comp_indep_aux R Q ((idx y').val - (idx y).val) y y' (by omega) h₁ h₂ h₁' h₂'
  · exact (cross_comp_indep_aux R Q ((idx y).val - (idx y').val) y' y (by omega)
      h₁' h₂' h₁ h₂).symm

/-! #### Composition -/

/-- The cross label of the composite bordism, at a chosen witness. -/
noncomputable def crossComp (R : LabBord X Y) (Q : LabBord Y Z)
    {x : X.truss.toOneTruss.El} {z : Z.truss.toOneTruss.El}
    (h : (compBord R.bord Q.bord).rel x z) : X.label.obj x ⟶ Z.label.obj z :=
  R.cross h.choose_spec.1 ≫ Q.cross h.choose_spec.2

/-- The composite cross label computed at *any* witness. -/
theorem crossComp_eq (R : LabBord X Y) (Q : LabBord Y Z)
    {x : X.truss.toOneTruss.El} {y : Y.truss.toOneTruss.El} {z : Z.truss.toOneTruss.El}
    (h : (compBord R.bord Q.bord).rel x z) (h₁ : R.bord.rel x y) (h₂ : Q.bord.rel y z) :
    crossComp R Q h = R.cross h₁ ≫ Q.cross h₂ :=
  cross_comp_witness_indep R Q _ _ h₁ h₂

/-- **Source: `def:bordism-composition` (Chapter 2), labelled.**  Composition of labelled
1-truss bordisms. -/
noncomputable def compLab (R : LabBord X Y) (Q : LabBord Y Z) : LabBord X Z :=
  crossMk (compBord R.bord Q.bord) (fun {_ _} h => crossComp R Q h)
    (by
      intro x x' _z hxx' h
      obtain ⟨y, h₁, h₂⟩ := id h
      change X.label.map (homOfLE hxx') ≫ crossComp R Q h
        = crossComp R Q ((compBord R.bord Q.bord).preimage_downClosed hxx' h)
      rw [crossComp_eq R Q h h₁ h₂,
        crossComp_eq R Q ((compBord R.bord Q.bord).preimage_downClosed hxx' h)
          (R.bord.preimage_downClosed hxx' h₁) h₂, ← Category.assoc, R.cross_left hxx' h₁])
    (by
      intro _x z z' h hzz'
      obtain ⟨y, h₁, h₂⟩ := id h
      change crossComp R Q h ≫ Z.label.map (homOfLE hzz')
        = crossComp R Q ((compBord R.bord Q.bord).image_upClosed h hzz')
      rw [crossComp_eq R Q h h₁ h₂,
        crossComp_eq R Q ((compBord R.bord Q.bord).image_upClosed h hzz') h₁
          (Q.bord.image_upClosed h₂ hzz'), Category.assoc, Q.cross_right h₂ hzz'])

@[simp] theorem compLab_bord (R : LabBord X Y) (Q : LabBord Y Z) :
    (compLab R Q).bord = compBord R.bord Q.bord := rfl

@[simp] theorem compLab_cross (R : LabBord X Y) (Q : LabBord Y Z)
    {x : X.truss.toOneTruss.El} {z : Z.truss.toOneTruss.El}
    (h : (compLab R Q).bord.rel x z) : (compLab R Q).cross h = crossComp R Q h :=
  crossMk_cross _ _ _ _ h

end LabBord

/-! #### The underlying bordism laws -/

namespace Geometry.Bord1

variable {T S U V : OpenTruss}

/-- The identity bordism is a left unit for composition. -/
theorem compBord_idBord_left (R : Bord1 T.toOneTruss S.toOneTruss) :
    compBord (idBord T.toOneTruss) R = R :=
  Bord1.ext' (funext fun x => funext fun _ => propext
    ⟨fun ⟨_, hxy, hyz⟩ => R.preimage_downClosed hxy hyz, fun h => ⟨x, le_rfl, h⟩⟩)

/-- The identity bordism is a right unit for composition. -/
theorem compBord_idBord_right (R : Bord1 T.toOneTruss S.toOneTruss) :
    compBord R (idBord S.toOneTruss) = R :=
  Bord1.ext' (funext fun _ => funext fun z => propext
    ⟨fun ⟨_, hxy, hyz⟩ => R.image_upClosed hxy hyz, fun h => ⟨z, h, le_rfl⟩⟩)

/-- Relational composition of bordisms is associative. -/
theorem compBord_assoc (R : Bord1 T.toOneTruss S.toOneTruss)
    (Q : Bord1 S.toOneTruss U.toOneTruss) (P : Bord1 U.toOneTruss V.toOneTruss) :
    compBord (compBord R Q) P = compBord R (compBord Q P) :=
  Bord1.ext' (funext fun _ => funext fun _ => propext
    ⟨fun ⟨z, ⟨y, h₁, h₂⟩, h₃⟩ => ⟨y, h₁, z, h₂, h₃⟩,
     fun ⟨y, h₁, z, h₂, h₃⟩ => ⟨z, ⟨y, h₁, h₂⟩, h₃⟩⟩)

end Geometry.Bord1

namespace LabBord

variable {X Y Z W : LabOneTruss C}

/-- **Source: `Category of labelled `n`-truss bundles` (Chapter 2) at `n = 1` over the
point.**  `B(C)`: `C`-labelled open 1-trusses and labelled 1-truss bordisms. -/
noncomputable instance instCategory : Category (LabOneTruss C) where
  Hom X Y := LabBord X Y
  id X := idLab X
  comp R Q := compLab R Q
  id_comp := by
    intro X Y R
    refine ext_cross (Bord1.compBord_idBord_left R.bord) ?_
    intro x y h h'
    rw [compLab_cross, crossComp_eq _ _ h (show (idLab X).bord.rel x x from le_rfl) h']
    simp
  comp_id := by
    intro X Y R
    refine ext_cross (Bord1.compBord_idBord_right R.bord) ?_
    intro x y h h'
    rw [compLab_cross, crossComp_eq _ _ h h' (show (idLab Y).bord.rel y y from le_rfl)]
    simp
  assoc := by
    intro X Y Z W R Q P
    refine ext_cross (Bord1.compBord_assoc R.bord Q.bord P.bord) ?_
    intro x w h h'
    obtain ⟨u, ⟨y, hR, hQ⟩, hP⟩ := id h
    rw [compLab_cross, compLab_cross,
      crossComp_eq _ _ h (show (compBord R.bord Q.bord).rel x u from ⟨y, hR, hQ⟩) hP,
      crossComp_eq _ _ h' hR (show (compBord Q.bord P.bord).rel y w from ⟨u, hQ, hP⟩),
      compLab_cross, compLab_cross, crossComp_eq _ _ _ hR hQ, crossComp_eq _ _ _ hQ hP,
      Category.assoc]

@[simp] theorem id_bord (X : LabOneTruss C) : (𝟙 X : LabBord X X).bord =
    idBord X.truss.toOneTruss := rfl

@[simp] theorem comp_bord (R : X ⟶ Y) (Q : Y ⟶ Z) :
    ((R ≫ Q : X ⟶ Z)).bord = compBord R.bord Q.bord := rfl

@[simp] theorem id_cross (X : LabOneTruss C) {x y : X.truss.toOneTruss.El}
    (h : (𝟙 X : LabBord X X).bord.rel x y) :
    (𝟙 X : LabBord X X).cross h = X.label.map (homOfLE (show x ≤ y from h)) :=
  idLab_cross X h

@[simp] theorem comp_cross (R : X ⟶ Y) (Q : Y ⟶ Z) {x : X.truss.toOneTruss.El}
    {z : Z.truss.toOneTruss.El} (h : (R ≫ Q : X ⟶ Z).bord.rel x z) :
    (R ≫ Q : X ⟶ Z).cross h = crossComp R Q h := compLab_cross R Q h

end LabBord

/-! ### §4  Classification at `n = 1` -/

namespace OpenBundle

variable {P : Type u} [PartialOrder P]

/-- The arrow fibre over `b ≤ b` is the identity bordism. -/
theorem arr_le_refl (A : OpenBundle P) (b : P) :
    A.arr (le_refl b) = idBord (A.fib b).toOneTruss :=
  Bord1.ext' (funext fun x => funext fun y => propext (A.arr_id b x y))

/-- The arrow fibre over a composite is the composite bordism. -/
theorem arr_trans (A : OpenBundle P) {b c d : P} (h₁ : b ≤ c) (h₂ : c ≤ d) :
    A.arr (h₁.trans h₂) = compBord (A.arr h₁) (A.arr h₂) :=
  Bord1.ext' (funext fun x => funext fun z => propext (A.arr_comp h₁ h₂ x z))

/-- **The total poset of an arrow fibre maps to the total poset of the bundle**, by
`(0,x) ↦ (b,x)` and `(1,y) ↦ (c,y)`.  Monotonicity *is* the definition of the order on
`Tot A`. -/
def arrTotHom (A : OpenBundle P) {b c : P} (h : b ≤ c) : (A.arr h).Tot →o A.Tot where
  toFun p := match p with
    | Sum.inl x => ⟨b, x⟩
    | Sum.inr y => ⟨c, y⟩
  monotone' := by
    intro p q hpq
    match p, q, hpq with
    | Sum.inl x, Sum.inl x', hpq => exact ⟨le_rfl, (A.arr_id b x x').2 hpq⟩
    | Sum.inl _, Sum.inr _, hpq => exact ⟨h, hpq⟩
    | Sum.inr y, Sum.inr y', hpq => exact ⟨le_rfl, (A.arr_id c y y').2 hpq⟩
    | Sum.inr _, Sum.inl _, hpq => exact hpq.elim

@[simp] theorem arrTotHom_inl (A : OpenBundle P) {b c : P} (h : b ≤ c)
    (x : (A.fib b).toOneTruss.El) : A.arrTotHom h ((A.arr h).inlHom x) = ⟨b, x⟩ := rfl

@[simp] theorem arrTotHom_inr (A : OpenBundle P) {b c : P} (h : b ≤ c)
    (y : (A.fib c).toOneTruss.El) : A.arrTotHom h ((A.arr h).inrHom y) = ⟨c, y⟩ := rfl

/-- **`arrTotHom` is an order embedding when the base arrow is not an identity.**

This is the place where the source's phrasing has to be sharpened: for `b = c` the map is
*not* injective (it glues the two layers of `(A.arr h).Tot` onto the single fibre `A_b`) and
it is *not* order reflecting (`(1,y) ⊴ (0,x)` is false upstairs but can hold downstairs).
For `b < c` it is an order embedding, and for arbitrary `h` it is monotone, which is all the
labelling needs. -/
def arrTotEmb (A : OpenBundle P) {b c : P} (h : b < c) : (A.arr h.le).Tot ↪o A.Tot where
  toFun := A.arrTotHom h.le
  inj' := by
    intro p q hpq
    match p, q with
    | Sum.inl _, Sum.inl _ => exact congrArg Sum.inl (eq_of_heq (Sigma.mk.inj hpq).2)
    | Sum.inr _, Sum.inr _ => exact congrArg Sum.inr (eq_of_heq (Sigma.mk.inj hpq).2)
    | Sum.inl _, Sum.inr _ => exact absurd (Sigma.mk.inj hpq).1 h.ne
    | Sum.inr _, Sum.inl _ => exact absurd (Sigma.mk.inj hpq).1 h.ne'
  map_rel_iff' := by
    intro p q
    refine ⟨?_, fun hpq => (A.arrTotHom h.le).monotone hpq⟩
    match p, q with
    | Sum.inl x, Sum.inl x' =>
      rintro ⟨_, hr⟩
      exact (A.arr_id b x x').1 hr
    | Sum.inl _, Sum.inr _ =>
      rintro ⟨_, hr⟩
      exact hr
    | Sum.inr y, Sum.inr y' =>
      rintro ⟨_, hr⟩
      exact (A.arr_id c y y').1 hr
    | Sum.inr _, Sum.inl _ =>
      rintro ⟨hcb, _⟩
      exact absurd (le_antisymm h.le hcb) h.ne

variable {C : Type v} [Category.{v} C]

/-- **Source: `thm:classification` at `n = 1`, the classifying functor on objects.** -/
def classifyObj (A : OpenBundle P) (L : A.Tot ⥤ C) (b : P) : LabOneTruss C :=
  ⟨A.fib b, A.restrictLabel L b⟩

/-- **Source: `thm:classification` at `n = 1`, the classifying functor on arrows.** -/
def classifyMap (A : OpenBundle P) (L : A.Tot ⥤ C) {b c : P} (h : b ≤ c) :
    LabBord (classifyObj A L b) (classifyObj A L c) where
  bord := A.arr h
  lbl := posetFunctor (A.arrTotHom h) ⋙ L
  src := rfl
  tgt := rfl

@[simp] theorem classifyMap_bord (A : OpenBundle P) (L : A.Tot ⥤ C) {b c : P} (h : b ≤ c) :
    (classifyMap A L h).bord = A.arr h := rfl

/-- The cross label of a classifying bordism is the label of the corresponding arrow of the
total poset. -/
theorem classifyMap_cross (A : OpenBundle P) (L : A.Tot ⥤ C) {b c : P} (hbc : b ≤ c)
    {x : (A.fib b).toOneTruss.El} {y : (A.fib c).toOneTruss.El}
    (h : (classifyMap A L hbc).bord.rel x y) :
    (classifyMap A L hbc).cross h
      = L.map (homOfLE (show A.fibreIncl b x ≤ A.fibreIncl c y from ⟨hbc, h⟩)) := by
  rw [LabBord.cross]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- **Source: `thm:classification` at `n = 1`.**  The classifying functor `χ` of a labelled
1-truss bundle. -/
noncomputable def classify (A : OpenBundle P) (L : A.Tot ⥤ C) : P ⥤ LabOneTruss C where
  obj := classifyObj A L
  map f := classifyMap A L (leOfHom f)
  map_id b := by
    refine LabBord.ext_cross (A.arr_le_refl b) ?_
    intro x y h h'
    rw [classifyMap_cross, LabBord.id_cross]
    rfl
  map_comp f g := by
    refine LabBord.ext_cross (A.arr_trans (leOfHom f) (leOfHom g)) ?_
    intro x z h h'
    obtain ⟨y, hR, hQ⟩ := (A.arr_comp (leOfHom f) (leOfHom g) x z).1 h
    rw [classifyMap_cross, LabBord.comp_cross,
      LabBord.crossComp_eq _ _ h' (show (A.arr (leOfHom f)).rel x y from hR)
        (show (A.arr (leOfHom g)).rel y z from hQ),
      classifyMap_cross, classifyMap_cross, ← Functor.map_comp]
    rfl

end OpenBundle

/-! #### Totalisation -/

namespace OpenBundle

variable {P : Type u} [PartialOrder P]

/-- The base comparison underlying an arrow of a total poset. -/
theorem tot_base {A : OpenBundle P} {p q : A.Tot} (h : p ≤ q) : p.1 ≤ q.1 :=
  A.proj.monotone h

/-- The fibre comparison underlying an arrow of a total poset. -/
theorem tot_rel {A : OpenBundle P} {p q : A.Tot} (h : p ≤ q) (hb : p.1 ≤ q.1) :
    (A.arr hb).rel p.2 q.2 := by
  obtain ⟨_, hr⟩ := h
  exact hr

end OpenBundle

namespace LabBord

variable {C : Type v} [Category.{v} C]

/-- Transporting a cross label along an equality of labelled bordisms. -/
theorem cross_congr {X Y : LabOneTruss C} {R R' : LabBord X Y} (e : R = R')
    {x : X.truss.toOneTruss.El} {y : Y.truss.toOneTruss.El}
    (h : R.bord.rel x y) (h' : R'.bord.rel x y) : R.cross h = R'.cross h' := by
  subst e; rfl

end LabBord

variable {P : Type u} [PartialOrder P] {C : Type v} [Category.{v} C]

/-- **Source: `thm:classification` at `n = 1`, totalisation: the underlying bundle.** -/
def totaliseBundle (F : P ⥤ LabOneTruss C) : OpenBundle P where
  fib b := (F.obj b).truss
  arr h := (F.map (homOfLE h)).bord
  arr_id b x y := by
    show (F.map (homOfLE (le_refl b))).bord.rel x y ↔ x ≤ y
    have e : (F.map (homOfLE (le_refl b))).bord = idBord (F.obj b).truss.toOneTruss := by
      rw [show homOfLE (le_refl b) = 𝟙 b from rfl, F.map_id]
      rfl
    rw [e]
    exact Iff.rfl
  arr_comp h₁ h₂ x z := by
    show (F.map (homOfLE (h₁.trans h₂))).bord.rel x z ↔
      ∃ y, (F.map (homOfLE h₁)).bord.rel x y ∧ (F.map (homOfLE h₂)).bord.rel y z
    have e : (F.map (homOfLE (h₁.trans h₂))).bord
        = compBord (F.map (homOfLE h₁)).bord (F.map (homOfLE h₂)).bord := by
      rw [show homOfLE (h₁.trans h₂) = homOfLE h₁ ≫ homOfLE h₂ from rfl, F.map_comp]
      rfl
    rw [e]
    exact Iff.rfl

@[simp] theorem totaliseBundle_fib (F : P ⥤ LabOneTruss C) (b : P) :
    (totaliseBundle F).fib b = (F.obj b).truss := rfl

@[simp] theorem totaliseBundle_arr (F : P ⥤ LabOneTruss C) {b c : P} (h : b ≤ c) :
    (totaliseBundle F).arr h = (F.map (homOfLE h)).bord := rfl

/-- **Source: `thm:classification` at `n = 1`, totalisation: the label on the total poset.**
The object labels come from the point labels, the arrow labels from the cross labels. -/
noncomputable def totaliseLabel (F : P ⥤ LabOneTruss C) : (totaliseBundle F).Tot ⥤ C :=
  posetMk (fun p => (F.obj p.1).label.obj p.2)
    (fun {_ _} hpq => (F.map (homOfLE (OpenBundle.tot_base hpq))).cross
      (OpenBundle.tot_rel hpq (OpenBundle.tot_base hpq)))
    (fun p => by
      refine (LabBord.cross_congr (F.map_id p.1) _
        (show (𝟙 (F.obj p.1) : LabBord _ _).bord.rel p.2 p.2 from le_rfl)).trans ?_
      rw [LabBord.id_cross]
      exact (F.obj p.1).label.map_id p.2)
    (fun {p q r} h₁ h₂ => by
      refine (LabBord.cross_congr
        (F.map_comp (homOfLE (OpenBundle.tot_base h₁)) (homOfLE (OpenBundle.tot_base h₂))) _
        (show (F.map (homOfLE (OpenBundle.tot_base h₁))
            ≫ F.map (homOfLE (OpenBundle.tot_base h₂))).bord.rel p.2 r.2 from
          ⟨q.2, OpenBundle.tot_rel h₁ _, OpenBundle.tot_rel h₂ _⟩)).trans ?_
      rw [LabBord.comp_cross, LabBord.crossComp_eq _ _ _ (OpenBundle.tot_rel h₁ _)
        (OpenBundle.tot_rel h₂ _)])

/-- **Source: `thm:classification` at `n = 1`.**  Totalisation `π`. -/
noncomputable def totalise (F : P ⥤ LabOneTruss C) : Σ A : OpenBundle P, A.Tot ⥤ C :=
  ⟨totaliseBundle F, totaliseLabel F⟩

/-! #### The round trips -/

/-- Totalising a classification returns the original bundle, **literally**: the fibres and
the arrow fibres of `totaliseBundle (classify A L)` are those of `A` by definition. -/
theorem totaliseBundle_classify (A : OpenBundle P) (L : A.Tot ⥤ C) :
    totaliseBundle (OpenBundle.classify A L) = A := rfl

/-- Totalising a classification returns the original label. -/
theorem totaliseLabel_classify (A : OpenBundle P) (L : A.Tot ⥤ C) :
    totaliseLabel (OpenBundle.classify A L) = L := by
  refine posetFunctor_ext (fun _ => rfl) ?_
  intro p q h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (OpenBundle.classifyMap A L (OpenBundle.tot_base h)).cross
      (OpenBundle.tot_rel h (OpenBundle.tot_base h)) = L.map (homOfLE h)
  rw [OpenBundle.classifyMap_cross]

/-- **`π ∘ χ = id` on the nose.** -/
theorem totalise_classify (A : OpenBundle P) (L : A.Tot ⥤ C) :
    totalise (OpenBundle.classify A L) = ⟨A, L⟩ :=
  congrArg (fun M : A.Tot ⥤ C => (⟨A, M⟩ : Σ A' : OpenBundle P, A'.Tot ⥤ C))
    (totaliseLabel_classify A L)

/-- Restricting the totalised label to a point fibre returns the point label. -/
theorem restrictLabel_totaliseLabel (F : P ⥤ LabOneTruss C) (b : P) :
    (totaliseBundle F).restrictLabel (totaliseLabel F) b = (F.obj b).label := by
  refine posetFunctor_ext (fun _ => rfl) ?_
  intro x y h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  have hr : (F.map (homOfLE (le_refl b))).bord.rel x y :=
    ((totaliseBundle F).arr_id b x y).2 h
  have key : ((totaliseBundle F).restrictLabel (totaliseLabel F) b).map (homOfLE h)
      = (F.map (homOfLE (le_refl b))).cross hr := rfl
  rw [key]
  refine (LabBord.cross_congr (F.map_id b) hr
    (show (𝟙 (F.obj b) : LabBord (F.obj b) (F.obj b)).bord.rel x y from h)).trans ?_
  rw [LabBord.id_cross]

namespace LabBord

variable {C : Type v} [Category.{v} C]

/-- **Conjugation by `eqToHom` in `B(C)`.**  Comparing a labelled bordism with a
relabelling of another one: the shape that `CategoryTheory.Functor.ext` produces. -/
theorem eq_conj_eqToHom {T T' : OpenTruss} {L₁ L₂ : T.toOneTruss.El ⥤ C}
    {M₁ M₂ : T'.toOneTruss.El ⥤ C} (hL : L₁ = L₂) (hM : M₁ = M₂)
    (R : LabBord ⟨T, L₂⟩ ⟨T', M₂⟩) (R' : LabBord ⟨T, L₁⟩ ⟨T', M₁⟩)
    (hb : R'.bord = R.bord)
    (hc : ∀ (x : T.toOneTruss.El) (y : T'.toOneTruss.El) (h : R'.bord.rel x y)
      (h' : R.bord.rel x y), R'.cross h
        = eqToHom (Functor.congr_obj hL x) ≫ R.cross h'
          ≫ eqToHom (Functor.congr_obj hM y).symm) :
    R' = eqToHom (congrArg (LabOneTruss.mk T) hL) ≫ R
      ≫ eqToHom (congrArg (LabOneTruss.mk T') hM).symm := by
  subst hL
  subst hM
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  refine ext_cross hb ?_
  intro x y h h'
  simpa using hc x y h h'

end LabBord

/-- **`χ ∘ π = id` on the nose.** -/
theorem classify_totalise (F : P ⥤ LabOneTruss C) :
    OpenBundle.classify (totalise F).1 (totalise F).2 = F := by
  have hl : ∀ b : P, (totaliseBundle F).restrictLabel (totaliseLabel F) b = (F.obj b).label :=
    restrictLabel_totaliseLabel F
  refine CategoryTheory.Functor.ext
    (fun b => congrArg (LabOneTruss.mk (F.obj b).truss) (hl b)) ?_
  intro b c f
  refine LabBord.eq_conj_eqToHom (hl b) (hl c) (F.map f) _ rfl ?_
  intro x y h h'
  -- both `eqToHom`s are identities, because the two labels agree *definitionally* on
  -- objects; only their arrow parts need `F.map_id`
  have key : eqToHom (Functor.congr_obj (hl b) x) ≫ (F.map f).cross h'
      ≫ eqToHom (Functor.congr_obj (hl c) y).symm = (F.map f).cross h' :=
    (congrArg (fun g => eqToHom (Functor.congr_obj (hl b) x) ≫ g)
      (Category.comp_id ((F.map f).cross h'))).trans (Category.id_comp _)
  change (OpenBundle.classifyMap (totaliseBundle F) (totaliseLabel F) (leOfHom f)).cross h
      = eqToHom (Functor.congr_obj (hl b) x) ≫ (F.map f).cross h'
        ≫ eqToHom (Functor.congr_obj (hl c) y).symm
  rw [OpenBundle.classifyMap_cross, key]
  rfl

/-! #### Strict representatives: totalisation commutes with reindexing on the nose -/

section Reindex

variable {P' : Type u} [PartialOrder P']

/-- Reindexing of a fibrewise-open 1-truss bundle along a monotone base map.

This repeats `OpenBundle.reindex` of `Truss/Transfer/Normalisation/Tower.lean` verbatim;
that module is not among this file's imports, so the definition is restated here rather
than imported.  The two are literally the same term. -/
def reindexBundle (f : P' →o P) (A : OpenBundle P) : OpenBundle P' where
  fib b := A.fib (f b)
  arr h := A.arr (f.monotone h)
  arr_id b x y := A.arr_id (f b) x y
  arr_comp h₁ h₂ x z := A.arr_comp (f.monotone h₁) (f.monotone h₂) x z

/-- The canonical map `f̃ : Tot(f^* A) → Tot(A)`, `(p, x) ↦ (f p, x)` (a restatement of
`OpenBundle.tildeHom`, for the same reason as `reindexBundle`). -/
def reindexTilde (f : P' →o P) (A : OpenBundle P) : (reindexBundle f A).Tot →o A.Tot where
  toFun p := ⟨f p.1, p.2⟩
  monotone' := by
    rintro p q ⟨h, hrel⟩
    exact ⟨f.monotone h, hrel⟩

/-- **The draft chapter's standing convention `π(F ∘ f) = f^* π(F)` is a theorem here, and
holds on the nose** (indeed by `rfl`): in the functorial presentation `f^*` *is*
precomposition, and both the bundle and the label of `totalise (f^*F)` are literally those
of the reindexed totalisation of `F`. -/
theorem totalise_comp (f : P' →o P) (F : P ⥤ LabOneTruss C) :
    totalise (posetFunctor f ⋙ F)
      = ⟨reindexBundle f (totalise F).1,
         posetFunctor (reindexTilde f (totalise F).1) ⋙ (totalise F).2⟩ := rfl

/-- The bundle half of `totalise_comp`, separately. -/
theorem totaliseBundle_comp (f : P' →o P) (F : P ⥤ LabOneTruss C) :
    totaliseBundle (posetFunctor f ⋙ F) = reindexBundle f (totaliseBundle F) := rfl

/-- The label half of `totalise_comp`, separately. -/
theorem totaliseLabel_comp (f : P' →o P) (F : P ⥤ LabOneTruss C) :
    totaliseLabel (posetFunctor f ⋙ F)
      = posetFunctor (reindexTilde f (totaliseBundle F)) ⋙ totaliseLabel F := rfl

end Reindex

end Truss.Transfer
