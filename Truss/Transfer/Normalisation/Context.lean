/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.Descent

/-!
# Coarsenings in truss-like categories (§5.2)

This module formalises the common interface of the draft normalisation chapter's
§"Coarsenings in truss-like categories", rows `C01`–`C05` of
[`plan/DraftNormalisationVerification.md`](../../../plan/DraftNormalisationVerification.md).

## Main definitions

* `DimCube n` — the numerical cube `[2]^n`.  The chapter's brackets count elements, so `[2]`
  is the two-element interval and `[2]^n` is `Fin n → Fin 2` with the product order.
* `TrussLike n K` — an `n`-truss-like category: a faithful total-poset functor
  `Tot : K ⥤ FinPos` and, for every object, a dimension signature
  `dimsig_X : Tot X ⥤ ([2]^n)^op`.  The signatures are objectwise data, exactly as the
  chapter's remark insists; no naturality in `K` is assumed.
* `IsCoarsening` — `def:draft-coarsening`.
* `OutCoarse X` — the category of outgoing unlabelled coarsenings.
* `LabObj n K C` — the `C`-labelled `n`-truss-like category `G`.
* `LabOutCoarse A` — the category `OutCoarse(X, L)` of outgoing labelled coarsenings.
* `DescendsAlong`, `descendedLabel` — `\overline{L}_q`.

## Main results

* `isCoarsening_iff_exists_dimsigNatTrans` — the definition's two displayed forms agree.
* `IsCoarsening.epi`, `IsCoarsening.id`, `IsCoarsening.comp` — `Properties of coarsenings`.
* `OutCoarse.thin` — `Thinness of outgoing coarsenings`.
* `LabObj.epi_of_isCoarsening` — `prop:draft-labelled-coarsenings-epi`.
* `descendedLabel_comp`, `LabOutCoarse.full` — `lem:draft-labelled-outcoarse-full`.

## Zero-dimensional extension

The source opens §5.2 with "Let `n` be a positive integer", while the recursion of §5.5 uses
`n = 0`.  Nothing in the section's arguments needs positivity, so `TrussLike` is stated for
every `n : ℕ`; at `n = 0` the cube `[2]^0` is a one-point poset and the signature condition
of `def:draft-coarsening` is vacuous.  This is the reviewed zero-dimensional extension asked
for by the plan (row `C01`) and by the saved chapter review; it is a strict generalisation of
the printed statement, and the positive-`n` case is the specialisation.
-/

universe u v w u₂ v₂

namespace Truss.Transfer

open CategoryTheory

/-! ### The numerical dimension cube -/

/-- **Source: `def:n-truss-like category` (§5.2).**  The numerical cube `[2]^n`, with the
product order.  The chapter's brackets count elements, so `[2] = {0 < 1}`. -/
def DimCube (n : ℕ) : Type := Fin n → Fin 2

/-- The coordinatewise order on `[2]^n`. -/
instance (n : ℕ) : PartialOrder (DimCube n) := Pi.partialOrder

/-- Membership in `[2]^n` is given coordinatewise. -/
theorem DimCube.le_def {n : ℕ} {a b : DimCube n} : a ≤ b ↔ ∀ i, a i ≤ b i := Iff.rfl

/-- An antitone map into a preorder, packaged as a functor into the opposite category.
This is the shape in which the chapter states a dimension signature,
`dimsig_X : Tot(X) → ([2]^n)^op`. -/
def Antitone.opFunctor {P : Type u} {Q : Type v} [Preorder P] [Preorder Q] {f : P → Q}
    (hf : Antitone f) : P ⥤ Qᵒᵖ where
  obj x := Opposite.op (f x)
  map h := (homOfLE (hf (leOfHom h))).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-! ### C01: `n`-truss-like categories -/

/-- **Source: `def:n-truss-like category` (§5.2).**  An `n`-truss-like category: a faithful
total-poset functor to finite posets, and an objectwise dimension signature into
`([2]^n)^op`.  See the module docstring for the zero-dimensional extension. -/
class TrussLike (n : outParam ℕ) (K : Type u) [Category.{v} K] where
  /-- The total-poset functor `Tot : K ⥤ FinPos`. -/
  tot : K ⥤ FinPartOrd.{w}
  /-- `Tot` is faithful. -/
  tot_faithful : tot.Faithful
  /-- The dimension signature of each object, as a map into the numerical cube `[2]^n`. -/
  dimsig : ∀ X : K, ↥(tot.obj X) → DimCube n
  /-- Each dimension signature is a functor into `([2]^n)^op`, i.e. an antitone map. -/
  dimsig_antitone : ∀ X : K, Antitone (dimsig X)

namespace TrussLike

variable {n : ℕ} {K : Type u} [Category.{v} K] [inst : TrussLike.{u, v, w} n K]

/-- The total poset of an object of an `n`-truss-like category. -/
abbrev Tot (X : K) : Type w := ↥(inst.tot.obj X)

/-- The underlying monotone map of `Tot q`. -/
def totMap {X Y : K} (q : X ⟶ Y) : Tot X →o Tot Y := (inst.tot.map q).hom.hom

@[simp] theorem totMap_id (X : K) : totMap (𝟙 X) = OrderHom.id := by
  simp only [totMap, CategoryTheory.Functor.map_id]; rfl

@[simp] theorem totMap_comp {X Y Z : K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    totMap (f ≫ g) = (totMap g).comp (totMap f) := by
  simp only [totMap, CategoryTheory.Functor.map_comp]; rfl

/-- `Tot` is faithful: a morphism of `K` is determined by its total map. -/
theorem totMap_injective {X Y : K} {f g : X ⟶ Y} (h : totMap f = totMap g) : f = g := by
  have : inst.tot.map f = inst.tot.map g := FinPartOrd.hom_ext h
  exact inst.tot_faithful.map_injective this

/-- The dimension signature as a functor into `([2]^n)^op`, the chapter's displayed form. -/
def dimsigFunctor (X : K) : Tot X ⥤ (DimCube n)ᵒᵖ :=
  Antitone.opFunctor (inst.dimsig_antitone X)

end TrussLike

/-! ### C02: coarsenings -/

open TrussLike

section Coarsening

variable {n : ℕ} {K : Type u} [Category.{v} K] [inst : TrussLike.{u, v, w} n K]

/-- **Source: `def:draft-coarsening` (§5.2).**  A morphism of an `n`-truss-like category is a
*coarsening* when its total map is a poset coarsening and its dimension signature does not
decrease.  The second clause is the chapter's displayed equivalent form of the lax
comparison `dimsig_Y ∘ Tot(q) ⟹ dimsig_X`; see `isCoarsening_iff_exists_dimsigNatTrans`. -/
structure IsCoarsening {X Y : K} (q : X ⟶ Y) : Prop where
  /-- The total map is a poset coarsening. -/
  tot : IsPosetCoarsening (totMap q)
  /-- The dimension signature does not decrease. -/
  dimsig_le : ∀ x : Tot X, inst.dimsig X x ≤ inst.dimsig Y (totMap q x)

/-- **Source: `def:draft-coarsening` (§5.2), the two displayed forms of the second clause.**
A lax comparison `dimsig_Y ∘ Tot(q) ⟹ dimsig_X` exists exactly when the numerical signature
does not decrease.  The target `([2]^n)^op` is a poset category, so naturality is automatic
and a natural transformation is precisely a family of pointwise comparisons. -/
theorem isCoarsening_iff_exists_dimsigNatTrans {X Y : K} (q : X ⟶ Y) :
    (IsPosetCoarsening (totMap q) ∧
        Nonempty ((totMap q).monotone.functor ⋙ dimsigFunctor Y ⟶ dimsigFunctor X)) ↔
      IsCoarsening q := by
  constructor
  · rintro ⟨htot, ⟨η⟩⟩
    refine ⟨htot, fun x => ?_⟩
    have hx : (Opposite.unop ((dimsigFunctor X).obj x) : DimCube n) ⟶
        Opposite.unop (((totMap q).monotone.functor ⋙ dimsigFunctor Y).obj x) := (η.app x).unop
    exact leOfHom hx
  · rintro ⟨htot, hdim⟩
    exact ⟨htot, ⟨⟨fun x => (homOfLE (hdim x)).op, fun _ _ _ => Subsingleton.elim _ _⟩⟩⟩

namespace IsCoarsening

/-- **Source: `Properties of coarsenings`, clause 1 (§5.2).**  Every coarsening is an
epimorphism: its total map is right-cancellable and `Tot` is faithful. -/
theorem cancel_right {X Y Z : K} {q : X ⟶ Y} (hq : IsCoarsening q) {f g : Y ⟶ Z}
    (h : q ≫ f = q ≫ g) : f = g := by
  refine totMap_injective (hq.tot.cancel_right ?_)
  have h' := congrArg (fun k : X ⟶ Z => totMap k) h
  simpa using h'

theorem epi {X Y : K} {q : X ⟶ Y} (hq : IsCoarsening q) : Epi q :=
  ⟨fun _ _ h => hq.cancel_right h⟩

/-- **Source: `Properties of coarsenings`, clause 2 (§5.2), identities.** -/
theorem id (X : K) : IsCoarsening (𝟙 X) where
  tot := by rw [totMap_id]; exact IsPosetCoarsening.id
  dimsig_le x := by rw [totMap_id]; exact le_rfl

/-- **Source: `Properties of coarsenings`, clause 2 (§5.2), composition.** -/
theorem comp {X Y Z : K} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsCoarsening f) (hg : IsCoarsening g) :
    IsCoarsening (f ≫ g) where
  tot := by rw [totMap_comp]; exact hf.tot.comp hg.tot
  dimsig_le x := by
    rw [totMap_comp]
    exact (hf.dimsig_le x).trans (hg.dimsig_le (totMap f x))

end IsCoarsening

/-! ### C03: outgoing unlabelled coarsenings -/

/-- **Source: `def:Outgoing unlabelled coarsenings` (§5.2).**  An object of `OutCoarse(X)`:
a coarsening out of `X`. -/
structure OutCoarse (X : K) where
  /-- The target object. -/
  tgt : K
  /-- The coarsening. -/
  map : X ⟶ tgt
  /-- The witness that `map` is a coarsening. -/
  isCoarsening : IsCoarsening map

namespace OutCoarse

variable {X : K}

/-- Morphisms of `OutCoarse(X)`: coarsenings `h` under `X`. -/
instance : Category (OutCoarse X) where
  Hom r q := {h : r.tgt ⟶ q.tgt // IsCoarsening h ∧ q.map = r.map ≫ h}
  id r := ⟨𝟙 _, IsCoarsening.id _, by simp⟩
  comp {r q s} a b :=
    ⟨a.1 ≫ b.1, a.2.1.comp b.2.1, b.2.2.trans (by rw [← Category.assoc, ← a.2.2])⟩
  id_comp _ := Subtype.ext (Category.id_comp _)
  comp_id _ := Subtype.ext (Category.comp_id _)
  assoc _ _ _ := Subtype.ext (Category.assoc _ _ _)

/-- **Source: `Thinness of outgoing coarsenings` (§5.2).**  `OutCoarse(X)` is thin: any two
parallel mediators agree, because the source coarsening is an epimorphism. -/
instance thin (r q : OutCoarse X) : Subsingleton (r ⟶ q) :=
  ⟨fun h k => Subtype.ext (r.isCoarsening.cancel_right (by rw [← h.2.2, ← k.2.2]))⟩

end OutCoarse

end Coarsening

/-! ### C04: the labelled `n`-truss-like category -/

section Labelled

variable {n : ℕ} {K : Type u} [Category.{v} K] [inst : TrussLike.{u, v, w} n K]
variable {C : Type u₂} [Category.{v₂} C]

/-- **Source: `def:Labelled n-truss-like category` (§5.2).**  An object of the `C`-labelled
`n`-truss-like category `G`: an object of `K` together with a full `C`-valued label functor
on its total poset. -/
structure LabObj (n : ℕ) (K : Type u) [Category.{v} K] [TrussLike.{u, v, w} n K]
    (C : Type u₂) [Category.{v₂} C] where
  /-- The underlying object of `K`. -/
  obj : K
  /-- The label functor on the total poset. -/
  label : Tot obj ⥤ C

namespace LabObj

/-- Morphisms of `G`: morphisms of `K` that pull the target label back to the source label. -/
instance : Category (LabObj.{u, v, w, u₂, v₂} n K C) where
  Hom A B := {q : A.obj ⟶ B.obj // A.label = posetFunctor (totMap q) ⋙ B.label}
  id A := ⟨𝟙 _, by rw [totMap_id]; rfl⟩
  comp {A B D} f g := ⟨f.1 ≫ g.1, by
    have hsplit : posetFunctor (totMap (f.1 ≫ g.1)) ⋙ D.label
        = posetFunctor (totMap f.1) ⋙ posetFunctor (totMap g.1) ⋙ D.label := by
      rw [totMap_comp]; rfl
    rw [hsplit, ← g.2, ← f.2]⟩
  id_comp _ := Subtype.ext (Category.id_comp _)
  comp_id _ := Subtype.ext (Category.comp_id _)
  assoc _ _ _ := Subtype.ext (Category.assoc _ _ _)

@[simp] theorem comp_coe {A B D : LabObj.{u, v, w, u₂, v₂} n K C} (f : A ⟶ B) (g : B ⟶ D) :
    (f ≫ g).1 = f.1 ≫ g.1 := rfl

@[simp] theorem id_coe (A : LabObj.{u, v, w, u₂, v₂} n K C) : (𝟙 A : A ⟶ A).1 = 𝟙 A.obj := rfl

/-- The label equation carried by a morphism of `G`. -/
theorem label_eq {A B : LabObj.{u, v, w, u₂, v₂} n K C} (f : A ⟶ B) :
    A.label = posetFunctor (totMap f.1) ⋙ B.label := f.2

/-- **Source: `prop:draft-labelled-coarsenings-epi` (§5.2).**  A labelled coarsening is an
epimorphism in `G`: labelled morphisms are determined by their underlying morphisms, and the
underlying coarsening is epi in `K`. -/
theorem epi_of_isCoarsening {A B : LabObj.{u, v, w, u₂, v₂} n K C} {q : A ⟶ B}
    (hq : IsCoarsening q.1) : Epi q := by
  refine ⟨fun {D} f g h => Subtype.ext (hq.cancel_right ?_)⟩
  exact congrArg Subtype.val h

end LabObj

/-! ### C05: label-preserving coarsenings and the full-subcategory description -/

/-- **Source: `def:Label-preserving coarsening` (§5.2).**  `q` is label preserving for `L`
when `L` descends along `Tot(q)`.  By `prop:draft-label-descent` this happens exactly when
`L` sends every arrow collapsed by `Tot(q)` to an identity. -/
def DescendsAlong {X Y : K} (q : X ⟶ Y) (L : Tot X ⥤ C) : Prop :=
  SendsCollapsedToId (totMap q) L

/-- The descended label `\overline{L}_q`. -/
noncomputable def descendedLabel {X Y : K} {q : X ⟶ Y} (hq : IsCoarsening q) {L : Tot X ⥤ C}
    (hL : DescendsAlong q L) : Tot Y ⥤ C := descend hq.tot hL

theorem descendedLabel_spec {X Y : K} {q : X ⟶ Y} (hq : IsCoarsening q) {L : Tot X ⥤ C}
    (hL : DescendsAlong q L) : posetFunctor (totMap q) ⋙ descendedLabel hq hL = L :=
  descend_spec hq.tot hL

/-- Uniqueness of the descended label. -/
theorem descendedLabel_unique {X Y : K} {q : X ⟶ Y} (hq : IsCoarsening q) {L : Tot X ⥤ C}
    {M M' : Tot Y ⥤ C} (hM : posetFunctor (totMap q) ⋙ M = L)
    (hM' : posetFunctor (totMap q) ⋙ M' = L) : M = M' :=
  label_descent_unique hq.tot (hM.trans hM'.symm)

/-- **Source: `def:Label-preserving coarsening` (§5.2), existence criterion.** -/
theorem descendsAlong_iff {X Y : K} {q : X ⟶ Y} (hq : IsCoarsening q) (L : Tot X ⥤ C) :
    DescendsAlong q L ↔ ∃ M : Tot Y ⥤ C, posetFunctor (totMap q) ⋙ M = L :=
  (label_descent hq.tot L).symm

/-- **Source: `lem:draft-labelled-outcoarse-full` (§5.2), fullness.**  Every *structural*
mediator between two label-preserving coarsenings out of `(X, L)` is automatically a labelled
morphism: uniqueness of descent along `Tot(r)` forces `M = N ∘ Tot(h)`. -/
theorem descendedLabel_comp {X Y Z : K} {L : Tot X ⥤ C} {r : X ⟶ Y} {q : X ⟶ Z} {h : Y ⟶ Z}
    (hr : IsCoarsening r) (hcomp : q = r ≫ h) {M : Tot Y ⥤ C} {N : Tot Z ⥤ C}
    (hM : posetFunctor (totMap r) ⋙ M = L) (hN : posetFunctor (totMap q) ⋙ N = L) :
    posetFunctor (totMap h) ⋙ N = M := by
  refine label_descent_unique hr.tot ?_
  rw [hM]
  subst hcomp
  rw [totMap_comp] at hN
  rw [← hN]
  rfl

/-! ### C05: the category of outgoing labelled coarsenings -/

/-- **Source: `def:Outgoing coarsenings` (§5.2).**  An object of `OutCoarse(X, L)`: a labelled
coarsening out of `(X, L)`. -/
structure LabOutCoarse (A : LabObj.{u, v, w, u₂, v₂} n K C) where
  /-- The target labelled object. -/
  tgt : LabObj.{u, v, w, u₂, v₂} n K C
  /-- The labelled coarsening. -/
  map : A ⟶ tgt
  /-- The witness that the underlying morphism is a coarsening. -/
  isCoarsening : IsCoarsening map.1

namespace LabOutCoarse

variable {A : LabObj.{u, v, w, u₂, v₂} n K C}

instance : Category (LabOutCoarse A) where
  Hom r q := {h : r.tgt ⟶ q.tgt // IsCoarsening h.1 ∧ q.map = r.map ≫ h}
  id r := ⟨𝟙 _, IsCoarsening.id _, by simp⟩
  comp {r q s} a b :=
    ⟨a.1 ≫ b.1, a.2.1.comp b.2.1, b.2.2.trans (by rw [← Category.assoc, ← a.2.2])⟩
  id_comp _ := Subtype.ext (Category.id_comp _)
  comp_id _ := Subtype.ext (Category.comp_id _)
  assoc _ _ _ := Subtype.ext (Category.assoc _ _ _)

/-- `OutCoarse(X, L)` is thin: its source coarsening is an epimorphism of `G`. -/
instance thin (r q : LabOutCoarse A) : Subsingleton (r ⟶ q) := by
  refine ⟨fun h k => Subtype.ext ?_⟩
  haveI := LabObj.epi_of_isCoarsening r.isCoarsening
  exact (cancel_epi r.map).1 (by rw [← h.2.2, ← k.2.2])

/-- The identity coarsening, as the canonical object of `OutCoarse(X, L)`. -/
def idObj (A : LabObj.{u, v, w, u₂, v₂} n K C) : LabOutCoarse A :=
  ⟨A, 𝟙 A, IsCoarsening.id _⟩

/-- **Source: `Characterisation of normality` (§5.2), first step.**  The identity coarsening
is initial in `OutCoarse(X, L)`: every object `r` receives the canonical triangle. -/
def fromIdObj (r : LabOutCoarse A) : idObj A ⟶ r :=
  ⟨r.map, r.isCoarsening, by simp [idObj]⟩

/-- **Source: `lem:draft-labelled-outcoarse-full` (§5.2), fullness.**  Every *structural*
mediator between objects of `OutCoarse(X, L)` is already a labelled mediator, so
`OutCoarse(X, L)` really is a full subcategory of `OutCoarse(X)`. -/
theorem full (r q : LabOutCoarse A) (h : r.tgt.obj ⟶ q.tgt.obj) (hh : IsCoarsening h)
    (hcomp : q.map.1 = r.map.1 ≫ h) : ∃ H : r ⟶ q, H.1.1 = h := by
  have hlab : posetFunctor (totMap h) ⋙ q.tgt.label = r.tgt.label :=
    descendedLabel_comp r.isCoarsening hcomp (r.map.2).symm (q.map.2).symm
  exact ⟨⟨⟨h, hlab.symm⟩, hh, Subtype.ext hcomp⟩, rfl⟩

end LabOutCoarse

end Labelled

end Truss.Transfer
