/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.Category.FinPartOrd
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Fin.Basic

/-!
# The poset preamble of the draft normalisation chapter (§5.1)

This module formalises the generic poset material of the author's draft
normalisation chapter, `dphil-notes-typst/transfer/ch03-normalisation-draft.typ`,
§"Poset preamble".  It is the bottom layer of the verification plan
[`plan/DraftNormalisationVerification.md`](../../../plan/DraftNormalisationVerification.md);
the coverage IDs referenced below are that plan's §6 D1 rows.

## Source coverage

* `P01` — `Open poset map`, `prop:draft-open-exact`:
  `IsOpenPosetMap`, `isOpenPosetMap_iff_exists_le`.
* `P02` — `Arrow-poset functor`, `Point fibres, arrow fibres, and collapsed arrows`,
  `lem:draft-identity-arrow-fibre`: `Arr`, `Arr.map`, `arrFunctor`, `pointFibre`,
  `arrowFibre`, `Collapses`, `arrowFibre_self_orderIso`.
* `P03` — `Poset coarsening` and the remark following it: `IsPosetCoarsening`,
  `IsPosetCoarsening.arrowFibre_nonempty`, `IsPosetCoarsening.pointFibre_connected`.
* `P04` — `prop:draft-poset-coarsening-properties`: `IsPosetCoarsening.epi_aux`,
  `IsPosetCoarsening.id`, `IsPosetCoarsening.comp`, `IsPosetCoarsening.pullbackSnd`.

`P05` (label descent) lives in `Truss.Transfer.Normalisation.Descent`.

## Deviation from the source's standing finiteness convention

The draft declares "All posets in this chapter are finite".  None of the results
below uses finiteness, so they are stated without it; the chapter's finite case is
the specialisation along `[Fintype _]`.  This is strictly stronger than the source
statement, never weaker.  The bundled arrow-poset functor `arrFunctor` is the one
place where the chapter's literal `FinPos → FinPos` typing is reproduced.

## Connectedness convention

The chapter's remark after `Poset coarsening` asserts that object-surjectivity and
openness *make every arrow fibre nonempty*.  That remark is only informative if
"connected" does not itself include nonemptiness, so `IsZigzagConnected` is the pure
zigzag-connectivity predicate and nonemptiness is derived
(`IsPosetCoarsening.arrowFibre_nonempty`).
-/

universe u v w

namespace Truss.Transfer

open CategoryTheory

/-! ### Comparability zigzags -/

section Zigzag

variable {α : Type u} [Preorder α]

/-- One comparability step of a zigzag confined to `S`: both endpoints lie in `S`
and they are comparable in the ambient order. -/
def ZigzagStep (S : Set α) (a b : α) : Prop := a ∈ S ∧ b ∈ S ∧ (a ≤ b ∨ b ≤ a)

/-- Zigzag reachability inside `S`: the reflexive-transitive closure of `ZigzagStep S`. -/
def ZigzagIn (S : Set α) : α → α → Prop := Relation.ReflTransGen (ZigzagStep S)

/-- A set is *zigzag connected* when any two of its elements are joined by a
comparability zigzag that stays inside the set.  Nonemptiness is deliberately not
part of this predicate; see the module docstring. -/
def IsZigzagConnected (S : Set α) : Prop := ∀ a ∈ S, ∀ b ∈ S, ZigzagIn S a b

theorem ZigzagIn.refl {S : Set α} (a : α) : ZigzagIn S a a := Relation.ReflTransGen.refl

theorem ZigzagIn.trans {S : Set α} {a b c : α} (h₁ : ZigzagIn S a b) (h₂ : ZigzagIn S b c) :
    ZigzagIn S a c := Relation.ReflTransGen.trans h₁ h₂

/-- A single comparability step is a zigzag. -/
theorem ZigzagIn.single {S : Set α} {a b : α} (h : ZigzagStep S a b) : ZigzagIn S a b :=
  Relation.ReflTransGen.single h

/-- A `≤`-comparison between two members of `S` is a zigzag step. -/
theorem ZigzagIn.of_le {S : Set α} {a b : α} (ha : a ∈ S) (hb : b ∈ S) (h : a ≤ b) :
    ZigzagIn S a b := Relation.ReflTransGen.single ⟨ha, hb, Or.inl h⟩

/-- A `≥`-comparison between two members of `S` is a zigzag step. -/
theorem ZigzagIn.of_ge {S : Set α} {a b : α} (ha : a ∈ S) (hb : b ∈ S) (h : b ≤ a) :
    ZigzagIn S a b := Relation.ReflTransGen.single ⟨ha, hb, Or.inr h⟩

/-- Zigzags may be transported along an inclusion of ambient sets. -/
theorem ZigzagIn.mono {S T : Set α} (hST : S ⊆ T) {a b : α} (h : ZigzagIn S a b) :
    ZigzagIn T a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail ⟨hST hstep.1, hST hstep.2.1, hstep.2.2⟩

/-- Comparability zigzags are symmetric: each step is a symmetric relation. -/
theorem ZigzagIn.symm {S : Set α} {a b : α} (h : ZigzagIn S a b) : ZigzagIn S b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact (Relation.ReflTransGen.single ⟨hstep.2.1, hstep.1, hstep.2.2.symm⟩).trans ih

/-- Every element reached by a zigzag out of a member of `S` again lies in `S`. -/
theorem ZigzagIn.mem_right {S : Set α} {a b : α} (ha : a ∈ S) (h : ZigzagIn S a b) : b ∈ S := by
  induction h with
  | refl => exact ha
  | tail _ hstep _ => exact hstep.2.1

end Zigzag

/-! ### P01: open poset maps -/

section Open

variable {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]

/-- **Source: `Open poset map` (§5.1).**  A monotone map `q` is *open* when the image
of every principal downset `↓y` is the principal downset `↓q y`. -/
def IsOpenPosetMap (q : P → Q) : Prop := ∀ y : P, q '' Set.Iic y = Set.Iic (q y)

/-- **Source: `prop:draft-open-exact` (§5.1).**  A monotone map is open if and only if
it admits *exact target lifting*: whenever `z ≤ q y` there is an `x ≤ y` with `q x = z`.

Monotonicity always supplies the inclusion `q '' ↓y ⊆ ↓q y`; the reverse inclusion is
exactly the lifting property. -/
theorem isOpenPosetMap_iff_exists_le {q : P → Q} (hq : Monotone q) :
    IsOpenPosetMap q ↔ ∀ (y : P) (z : Q), z ≤ q y → ∃ x ≤ y, q x = z := by
  constructor
  · intro h y z hz
    have : z ∈ q '' Set.Iic y := by rw [h y]; exact hz
    obtain ⟨x, hx, hxz⟩ := this
    exact ⟨x, hx, hxz⟩
  · intro h y
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hq hx
    · intro z hz
      obtain ⟨x, hx, hxz⟩ := h y z hz
      exact ⟨x, hx, hxz⟩

/-- The exact-target-lifting form of openness, for direct use. -/
theorem IsOpenPosetMap.exists_le {q : P →o Q} (h : IsOpenPosetMap q) {y : P} {z : Q}
    (hz : z ≤ q y) : ∃ x ≤ y, q x = z :=
  (isOpenPosetMap_iff_exists_le q.monotone).1 h y z hz

/-- **`lem:draft-poset-coarsening-basics` (3), using only openness.** A monotone
finite chain has a monotone lift with any prescribed last element over its last value.
Lift the penultimate value below the prescribed endpoint and induct on the prefix. -/
theorem IsOpenPosetMap.exists_monotone_lift {q : P →o Q} (hq : IsOpenPosetMap q)
    {n : ℕ} (y : Fin (n + 1) → Q) (hy : Monotone y) (last : P)
    (hlast : q last = y (Fin.last n)) :
    ∃ x : Fin (n + 1) → P, Monotone x ∧ x (Fin.last n) = last ∧ ∀ i, q (x i) = y i := by
  induction n generalizing last with
  | zero =>
    refine ⟨fun _ => last, fun _ _ _ => le_rfl, rfl, ?_⟩
    intro i
    simpa only [Fin.eq_zero i, Fin.last_zero] using hlast
  | succ n ih =>
    obtain ⟨prev, hprev, hqprev⟩ := hq.exists_le
      (y := last) (z := y (Fin.last n).castSucc)
      (by rw [hlast]; exact hy (Fin.le_last _))
    obtain ⟨x, hx, hxlast, hqx⟩ := ih (fun i => y i.castSucc)
      (fun i j hij => hy (Fin.castSucc_le_castSucc_iff.mpr hij)) prev hqprev
    refine ⟨Fin.snoc x last, ?_, Fin.snoc_last _ _, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · intro _
        refine Fin.lastCases ?_ (fun i => ?_) i
        · exact le_rfl
        · simpa only [Fin.snoc_castSucc, Fin.snoc_last] using
            (hx (Fin.le_last i)).trans (hxlast ▸ hprev)
      · refine Fin.lastCases ?_ (fun i => ?_) i
        · intro hij
          have := j.isLt
          simp only [Fin.le_def, Fin.val_last, Fin.val_castSucc] at hij
          omega
        · intro hij
          simpa only [Fin.snoc_castSucc] using hx (Fin.castSucc_le_castSucc_iff.mp hij)
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa only [Fin.snoc_last] using hlast
      · simpa only [Fin.snoc_castSucc] using hqx i

/-- Identity maps are open. -/
theorem isOpenPosetMap_id : IsOpenPosetMap (id : P → P) := by
  intro y; simp

end Open

/-! ### P02: the arrow poset -/

/-- **Source: `Arrow-poset functor` (§5.1).**  The arrow poset of `P`: pairs `(x, x')`
with `x ≤ x'`, ordered componentwise. -/
@[ext]
structure Arr (P : Type u) [Preorder P] where
  /-- The source of the arrow. -/
  src : P
  /-- The target of the arrow. -/
  tgt : P
  /-- Arrows point upwards. -/
  le : src ≤ tgt

namespace Arr

variable {P : Type u} {Q : Type v} {R : Type w}

section
variable [Preorder P]

instance instPreorder : Preorder (Arr P) where
  le a b := a.src ≤ b.src ∧ a.tgt ≤ b.tgt
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem le_def {a b : Arr P} : a ≤ b ↔ a.src ≤ b.src ∧ a.tgt ≤ b.tgt := Iff.rfl

end

instance instPartialOrder [PartialOrder P] : PartialOrder (Arr P) where
  __ := Arr.instPreorder
  le_antisymm _ _ h₁ h₂ :=
    Arr.ext (le_antisymm h₁.1 h₂.1) (le_antisymm h₁.2 h₂.2)

instance instFinite [PartialOrder P] [Finite P] : Finite (Arr P) :=
  Finite.of_injective (fun a => (a.src, a.tgt)) (by
    rintro ⟨s, t, _⟩ ⟨s', t', _⟩ h
    simp only [Prod.mk.injEq] at h
    exact Arr.ext h.1 h.2)

/-- A finite poset has a finite arrow poset.  The enumeration is produced classically,
so this instance is noncomputable. -/
noncomputable instance instFintype [PartialOrder P] [Fintype P] : Fintype (Arr P) :=
  @Fintype.ofFinite _ Arr.instFinite

/-- The action of a monotone map on arrow posets. -/
def map [Preorder P] [Preorder Q] (q : P →o Q) (a : Arr P) : Arr Q :=
  ⟨q a.src, q a.tgt, q.monotone a.le⟩

@[simp] theorem map_src [Preorder P] [Preorder Q] (q : P →o Q) (a : Arr P) :
    (map q a).src = q a.src := rfl

@[simp] theorem map_tgt [Preorder P] [Preorder Q] (q : P →o Q) (a : Arr P) :
    (map q a).tgt = q a.tgt := rfl

/-- `Arr.map` is monotone, so it is a map of arrow posets. -/
def hom [Preorder P] [Preorder Q] (q : P →o Q) : Arr P →o Arr Q where
  toFun := map q
  monotone' _ _ h := ⟨q.monotone h.1, q.monotone h.2⟩

@[simp] theorem hom_apply [Preorder P] [Preorder Q] (q : P →o Q) (a : Arr P) :
    hom q a = map q a := rfl

/-- Functoriality of `Arr`: identities. -/
@[simp] theorem map_id [Preorder P] (a : Arr P) : map (OrderHom.id : P →o P) a = a := rfl

/-- Functoriality of `Arr`: composition. -/
@[simp] theorem map_comp [Preorder P] [Preorder Q] [Preorder R] (r : Q →o R) (q : P →o Q)
    (a : Arr P) : map (r.comp q) a = map r (map q a) := rfl

end Arr

/-- **Source: `Arrow-poset functor` (§5.1), bundled form.**  The arrow-poset construction
as an endofunctor of the category of finite posets.  `Fintype` instances are produced
classically from `Finite`, so this functor is noncomputable. -/
noncomputable def arrFunctor : FinPartOrd.{u} ⥤ FinPartOrd.{u} where
  obj P := FinPartOrd.of (Arr P)
  map q := FinPartOrd.ofHom (Arr.hom q.hom.hom)
  map_id _ := FinPartOrd.hom_ext rfl
  map_comp _ _ := FinPartOrd.hom_ext rfl

/-! ### P02: fibres and collapsed arrows -/

section Fibres

variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]

/-- **Source: `Point fibres, arrow fibres, and collapsed arrows` (§5.1).**  The point
fibre of `q` over `y`. -/
def pointFibre (q : P →o Q) (y : Q) : Set P := {x | q x = y}

/-- **Source: same definition.**  The arrow fibre of `q` over the arrow `y ≤ y'`, as a
subset of the arrow poset of `P`.  It is the preimage of `(y, y')` under `Arr q`. -/
def arrowFibre (q : P →o Q) (y y' : Q) : Set (Arr P) := {a | q a.src = y ∧ q a.tgt = y'}

/-- **Source: same definition.**  An arrow of `P` is *collapsed* by `q` when its two
endpoints have the same image. -/
def Collapses (q : P →o Q) (a : Arr P) : Prop := q a.src = q a.tgt

@[simp] theorem mem_pointFibre {q : P →o Q} {y : Q} {x : P} : x ∈ pointFibre q y ↔ q x = y :=
  Iff.rfl

@[simp] theorem mem_arrowFibre {q : P →o Q} {y y' : Q} {a : Arr P} :
    a ∈ arrowFibre q y y' ↔ q a.src = y ∧ q a.tgt = y' := Iff.rfl

/-- The arrow fibre over an identity arrow consists of the arrows collapsed to `y`. -/
theorem arrowFibre_self (q : P →o Q) (y : Q) :
    arrowFibre q y y = {a : Arr P | a.src ∈ pointFibre q y ∧ a.tgt ∈ pointFibre q y} := rfl

/-- **Source: `lem:draft-identity-arrow-fibre` (§5.1).**  The arrow fibre over an identity
arrow `y ≤ y` is the arrow poset of the point fibre over `y`.

The subposet `arrowFibre q y y` of `Arr P` and the poset `Arr ↥(pointFibre q y)` are
identified by the evident order isomorphism. -/
def arrowFibre_self_orderIso (q : P →o Q) (y : Q) :
    ↥(arrowFibre q y y) ≃o Arr ↥(pointFibre q y) where
  toFun a := ⟨⟨a.1.src, a.2.1⟩, ⟨a.1.tgt, a.2.2⟩, a.1.le⟩
  invFun a := ⟨⟨a.src.1, a.tgt.1, a.le⟩, a.src.2, a.tgt.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by
    obtain ⟨⟨s, hs⟩, ⟨t, ht⟩, h⟩ := a; rfl
  map_rel_iff' := Iff.rfl

end Fibres

/-! ### P03: poset coarsenings -/

section Coarsening

variable {P : Type u} {Q : Type v} {R : Type w}
variable [PartialOrder P] [PartialOrder Q] [PartialOrder R]

/-- **Source: `Poset coarsening` (§5.1).**  A monotone map is a *poset coarsening* when it
is surjective on objects, open, and has connected arrow fibres over every arrow. -/
structure IsPosetCoarsening (q : P →o Q) : Prop where
  /-- Surjectivity on objects. -/
  surjective : Function.Surjective q
  /-- Openness in the sense of `IsOpenPosetMap`. -/
  isOpen : IsOpenPosetMap q
  /-- Every arrow fibre is zigzag connected. -/
  arrowFibre_connected : ∀ y y' : Q, y ≤ y' → IsZigzagConnected (arrowFibre q y y')

/-- **Source: the remark after `Poset coarsening` (§5.1), first clause.**
Object-surjectivity and openness make every arrow fibre nonempty: lift the target, then
lift the source below it by exact target lifting. -/
theorem IsPosetCoarsening.arrowFibre_nonempty {q : P →o Q} (hq : IsPosetCoarsening q)
    {y y' : Q} (h : y ≤ y') : (arrowFibre q y y').Nonempty := by
  obtain ⟨t, ht⟩ := hq.surjective y'
  obtain ⟨s, hst, hs⟩ := hq.isOpen.exists_le (y := t) (z := y) (by rw [ht]; exact h)
  exact ⟨⟨s, t, hst⟩, hs, ht⟩

/-- **`lem:draft-poset-coarsening-basics` (1), arrows.** Every arrow has a lift:
choose a preimage of its target and use openness to lift its source below it. -/
theorem IsPosetCoarsening.arr_surjective {q : P →o Q} (hq : IsPosetCoarsening q) :
    Function.Surjective (Arr.map q) := by
  intro a
  obtain ⟨b, hb⟩ := hq.arrowFibre_nonempty a.le
  exact ⟨b, Arr.ext hb.1 hb.2⟩

/-- **`lem:draft-poset-coarsening-basics` (3).** Lift every finite chain through a
poset coarsening, fixing its prescribed last element. No finiteness of the posets is needed. -/
theorem IsPosetCoarsening.exists_monotone_lift {q : P →o Q} (hq : IsPosetCoarsening q)
    {n : ℕ} (y : Fin (n + 1) → Q) (hy : Monotone y) (last : P)
    (hlast : q last = y (Fin.last n)) :
    ∃ x : Fin (n + 1) → P, Monotone x ∧ x (Fin.last n) = last ∧ ∀ i, q (x i) = y i :=
  hq.isOpen.exists_monotone_lift y hy last hlast

/-- Point fibres of a poset coarsening are nonempty. -/
theorem IsPosetCoarsening.pointFibre_nonempty {q : P →o Q} (hq : IsPosetCoarsening q) (y : Q) :
    (pointFibre q y).Nonempty := by
  obtain ⟨x, hx⟩ := hq.surjective y; exact ⟨x, hx⟩

/-- **Source: the remark after `Poset coarsening` (§5.1), second clause.**
Arrow-fibre connectivity implies point-fibre connectivity: a point of the fibre gives the
identity arrow on it, and a zigzag of identity arrows projects to a zigzag of points. -/
theorem IsPosetCoarsening.pointFibre_connected {q : P →o Q} (hq : IsPosetCoarsening q) (y : Q) :
    IsZigzagConnected (pointFibre q y) := by
  intro a ha b hb
  have hA : (⟨a, a, le_rfl⟩ : Arr P) ∈ arrowFibre q y y := ⟨ha, ha⟩
  have hB : (⟨b, b, le_rfl⟩ : Arr P) ∈ arrowFibre q y y := ⟨hb, hb⟩
  have hz := hq.arrowFibre_connected y y le_rfl _ hA _ hB
  -- project the zigzag of identity arrows to a zigzag of their sources
  have key : ∀ v : Arr P, ZigzagIn (arrowFibre q y y) ⟨a, a, le_rfl⟩ v →
      ZigzagIn (pointFibre q y) a v.src := by
    intro v h
    induction h with
    | refl => exact ZigzagIn.refl _
    | tail _ hstep ih =>
        exact ih.tail ⟨hstep.1.1, hstep.2.1.1, hstep.2.2.imp (fun h => h.1) (fun h => h.1)⟩
  exact key _ hz

/-! ### P04: elementary properties of poset coarsenings -/

/-- **Source: `prop:draft-poset-coarsening-properties`, clause 1 (§5.1).**
A poset coarsening is right-cancellable among monotone maps: it is surjective on objects,
and a monotone map is determined by its object function. -/
theorem IsPosetCoarsening.cancel_right {q : P →o Q} (hq : IsPosetCoarsening q)
    {g h : Q →o R} (hgh : g.comp q = h.comp q) : g = h := by
  ext y
  obtain ⟨x, rfl⟩ := hq.surjective y
  exact congrArg (fun k : P →o R => k x) hgh

/-- **Source: `prop:draft-poset-coarsening-properties`, clause 2 (§5.1), identities.**
Identity maps are poset coarsenings. -/
theorem IsPosetCoarsening.id : IsPosetCoarsening (OrderHom.id : P →o P) where
  surjective := Function.surjective_id
  isOpen := isOpenPosetMap_id
  arrowFibre_connected y y' _ := by
    intro a ha b hb
    obtain ⟨ha₁, ha₂⟩ := ha
    obtain ⟨hb₁, hb₂⟩ := hb
    have : a = b := Arr.ext (ha₁.trans hb₁.symm) (ha₂.trans hb₂.symm)
    subst this
    exact ZigzagIn.refl _

/-! #### The linking lemmas behind closure under composition

The draft's composition proof reads: *"project an arrow fibre of the composite to the
corresponding arrow fibre of the second map.  Its fibres are connected arrow fibres of the
first map, and exact target lifting supplies links over each comparison in the base arrow
fibre."*  The two lemmas below make those links explicit.  A comparison
`(u, u') ≤ (v, v')` in the arrow poset of `Q` is factored through the intermediate arrow
`(u, v')`, and each of the two resulting one-sided comparisons is bridged separately. -/

/-- Link over a target increase: for `u ≤ u' ≤ v'` there are comparable arrows in the
fibres of `q` over `(u, u')` and over `(u, v')`. -/
theorem exists_le_arrowFibre_tgt {q : P →o Q} (hsurj : Function.Surjective q)
    (hopen : IsOpenPosetMap q) {u u' v' : Q} (huu' : u ≤ u') (hu'v' : u' ≤ v') :
    ∃ A ∈ arrowFibre q u u', ∃ B ∈ arrowFibre q u v', A ≤ B := by
  obtain ⟨t', ht'⟩ := hsurj v'
  obtain ⟨t, htt', ht⟩ := hopen.exists_le (y := t') (z := u') (by rw [ht']; exact hu'v')
  obtain ⟨s, hst, hs⟩ := hopen.exists_le (y := t) (z := u) (by rw [ht]; exact huu')
  exact ⟨⟨s, t, hst⟩, ⟨hs, ht⟩, ⟨s, t', hst.trans htt'⟩, ⟨hs, ht'⟩, ⟨le_rfl, htt'⟩⟩

/-- Link over a source increase: for `u ≤ v ≤ v'` there are comparable arrows in the
fibres of `q` over `(u, v')` and over `(v, v')`. -/
theorem exists_le_arrowFibre_src {q : P →o Q} (hsurj : Function.Surjective q)
    (hopen : IsOpenPosetMap q) {u v v' : Q} (huv : u ≤ v) (hvv' : v ≤ v') :
    ∃ A ∈ arrowFibre q u v', ∃ B ∈ arrowFibre q v v', A ≤ B := by
  obtain ⟨t, ht⟩ := hsurj v'
  obtain ⟨y, hyt, hy⟩ := hopen.exists_le (y := t) (z := v) (by rw [ht]; exact hvv')
  obtain ⟨s, hsy, hs⟩ := hopen.exists_le (y := y) (z := u) (by rw [hy]; exact huv)
  exact ⟨⟨s, t, hsy.trans hyt⟩, ⟨hs, ht⟩, ⟨y, t, hyt⟩, ⟨hy, ht⟩, ⟨hsy, le_rfl⟩⟩

/-- The full link: arrow fibres of `q` over comparable arrows of `Q` are joined by a zigzag
inside any set `T` containing those two fibres and the intermediate fibre over `(u, v')`. -/
theorem zigzagIn_of_arrowFibre_le {q : P →o Q} (hq : IsPosetCoarsening q) {u u' v v' : Q}
    (huu' : u ≤ u') (hvv' : v ≤ v') (huv : u ≤ v) (hu'v' : u' ≤ v')
    {T : Set (Arr P)} (hTu : arrowFibre q u u' ⊆ T) (hTv : arrowFibre q v v' ⊆ T)
    (hTm : arrowFibre q u v' ⊆ T) {A B : Arr P} (hA : A ∈ arrowFibre q u u')
    (hB : B ∈ arrowFibre q v v') : ZigzagIn T A B := by
  obtain ⟨A₀, hA₀, B₀, hB₀, hle₀⟩ := exists_le_arrowFibre_tgt hq.surjective hq.isOpen huu' hu'v'
  obtain ⟨A₁, hA₁, B₁, hB₁, hle₁⟩ := exists_le_arrowFibre_src hq.surjective hq.isOpen huv hvv'
  have h1 : ZigzagIn T A A₀ := (hq.arrowFibre_connected u u' huu' A hA A₀ hA₀).mono hTu
  have h2 : ZigzagIn T A₀ B₀ := ZigzagIn.of_le (hTu hA₀) (hTm hB₀) hle₀
  have h3 : ZigzagIn T B₀ A₁ :=
    (hq.arrowFibre_connected u v' (huu'.trans hu'v') B₀ hB₀ A₁ hA₁).mono hTm
  have h4 : ZigzagIn T A₁ B₁ := ZigzagIn.of_le (hTm hA₁) (hTv hB₁) hle₁
  have h5 : ZigzagIn T B₁ B := (hq.arrowFibre_connected v v' hvv' B₁ hB₁ B hB).mono hTv
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

/-- **Source: `prop:draft-poset-coarsening-properties`, clause 2 (§5.1), composition.**
Poset coarsenings are closed under composition. -/
theorem IsPosetCoarsening.comp {q : P →o Q} {r : Q →o R} (hq : IsPosetCoarsening q)
    (hr : IsPosetCoarsening r) : IsPosetCoarsening (r.comp q) := by
  have hopen : IsOpenPosetMap (r.comp q) := by
    rw [isOpenPosetMap_iff_exists_le (r.comp q).monotone]
    intro y w hw
    obtain ⟨z, hzq, hz⟩ := hr.isOpen.exists_le (y := q y) (z := w) hw
    obtain ⟨x, hxy, hx⟩ := hq.isOpen.exists_le (y := y) (z := z) hzq
    exact ⟨x, hxy, by simp [OrderHom.comp, hx, hz]⟩
  refine ⟨hr.surjective.comp hq.surjective, hopen, ?_⟩
  intro w w' hw
  set T : Set (Arr P) := arrowFibre (r.comp q) w w' with hT
  -- fibres of `q` over an arrow of `arrowFibre r w w'` sit inside `T`
  have hsub : ∀ u u' : Q, r u = w → r u' = w' → arrowFibre q u u' ⊆ T := by
    intro u u' hu hu' a ha
    exact ⟨by simp [OrderHom.comp, ha.1, hu], by simp [OrderHom.comp, ha.2, hu']⟩
  -- one comparability step downstairs lifts to a zigzag upstairs
  have hstepLift : ∀ c d : Arr Q, ZigzagStep (arrowFibre r w w') c d →
      ∀ x ∈ arrowFibre q c.src c.tgt, ∀ y ∈ arrowFibre q d.src d.tgt, ZigzagIn T x y := by
    intro c d hcd x hx y hy
    have hc : r c.src = w ∧ r c.tgt = w' := hcd.1
    have hd : r d.src = w ∧ r d.tgt = w' := hcd.2.1
    rcases hcd.2.2 with h | h
    · exact zigzagIn_of_arrowFibre_le hq c.le d.le h.1 h.2
        (hsub _ _ hc.1 hc.2) (hsub _ _ hd.1 hd.2) (hsub _ _ hc.1 hd.2) hx hy
    · exact (zigzagIn_of_arrowFibre_le hq d.le c.le h.1 h.2
        (hsub _ _ hd.1 hd.2) (hsub _ _ hc.1 hc.2) (hsub _ _ hd.1 hc.2) hy hx).symm
  intro a ha b hb
  have haq : Arr.map q a ∈ arrowFibre r w w' := ⟨ha.1, ha.2⟩
  have hbq : Arr.map q b ∈ arrowFibre r w w' := ⟨hb.1, hb.2⟩
  have hz := hr.arrowFibre_connected w w' hw _ haq _ hbq
  have key : ∀ β : Arr Q, ZigzagIn (arrowFibre r w w') (Arr.map q a) β →
      ∀ y ∈ arrowFibre q β.src β.tgt, ZigzagIn T a y := by
    intro β h
    induction h with
    | refl =>
        intro y hy
        exact (hq.arrowFibre_connected _ _ (q.monotone a.le) a ⟨rfl, rfl⟩ y hy).mono
          (hsub _ _ ha.1 ha.2)
    | tail _ hstep ih =>
        rename_i c d _
        intro y hy
        obtain ⟨x, hx⟩ := hq.arrowFibre_nonempty (y := c.src) (y' := c.tgt) c.le
        exact (ih x hx).trans (hstepLift c d hstep x hx y hy)
  exact key _ hz b ⟨rfl, rfl⟩

end Coarsening

/-! ### P04, clause 3: pullbacks -/

section Pullback

variable {P : Type u} {Q : Type v} {Z : Type w}
variable [PartialOrder P] [PartialOrder Q] [PartialOrder Z]

/-- The pullback `X ×_Y Z` of `q : P →o Q` along `f : Z →o Q`, with the induced product
order. -/
@[ext]
structure Pullback (q : P →o Q) (f : Z →o Q) where
  /-- The `P`-coordinate. -/
  fst : P
  /-- The `Z`-coordinate. -/
  snd : Z
  /-- The two coordinates agree in `Q`. -/
  compat : q fst = f snd

namespace Pullback

variable {q : P →o Q} {f : Z →o Q}

instance instPartialOrder : PartialOrder (Pullback q f) where
  le a b := a.fst ≤ b.fst ∧ a.snd ≤ b.snd
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := Pullback.ext (le_antisymm h₁.1 h₂.1) (le_antisymm h₁.2 h₂.2)

theorem le_def {a b : Pullback q f} : a ≤ b ↔ a.fst ≤ b.fst ∧ a.snd ≤ b.snd := Iff.rfl

end Pullback

/-- The projection of the pullback to `P`. -/
def pullbackFst (q : P →o Q) (f : Z →o Q) : Pullback q f →o P where
  toFun a := a.fst
  monotone' _ _ h := h.1

/-- The pullback projection `f^*q : X ×_Y Z → Z`. -/
def pullbackSnd (q : P →o Q) (f : Z →o Q) : Pullback q f →o Z where
  toFun a := a.snd
  monotone' _ _ h := h.2

@[simp] theorem pullbackFst_apply (q : P →o Q) (f : Z →o Q) (a : Pullback q f) :
    pullbackFst q f a = a.fst := rfl

@[simp] theorem pullbackSnd_apply (q : P →o Q) (f : Z →o Q) (a : Pullback q f) :
    pullbackSnd q f a = a.snd := rfl

/-- Lift an arrow of `P` lying in the fibre of `q` over `f z₀ ≤ f z₁` to an arrow of the
pullback lying in the fibre of `f^*q` over `z₀ ≤ z₁`. -/
def arrPullbackLift (q : P →o Q) (f : Z →o Q) {z₀ z₁ : Z} (hz : z₀ ≤ z₁) (a : Arr P)
    (ha : a ∈ arrowFibre q (f z₀) (f z₁)) : Arr (Pullback q f) :=
  ⟨⟨a.src, z₀, ha.1⟩, ⟨a.tgt, z₁, ha.2⟩, ⟨a.le, hz⟩⟩

theorem arrPullbackLift_mem (q : P →o Q) (f : Z →o Q) {z₀ z₁ : Z} (hz : z₀ ≤ z₁) (a : Arr P)
    (ha : a ∈ arrowFibre q (f z₀) (f z₁)) :
    arrPullbackLift q f hz a ha ∈ arrowFibre (pullbackSnd q f) z₀ z₁ := ⟨rfl, rfl⟩

theorem arrPullbackLift_mono (q : P →o Q) (f : Z →o Q) {z₀ z₁ : Z} (hz : z₀ ≤ z₁) {a b : Arr P}
    (ha : a ∈ arrowFibre q (f z₀) (f z₁)) (hb : b ∈ arrowFibre q (f z₀) (f z₁)) (hab : a ≤ b) :
    arrPullbackLift q f hz a ha ≤ arrPullbackLift q f hz b hb :=
  ⟨⟨hab.1, le_rfl⟩, ⟨hab.2, le_rfl⟩⟩

/-- Every arrow of the pullback in the fibre over `z₀ ≤ z₁` is the lift of its
`P`-projection: the arrow fibres of `f^*q` and of `q` correspond exactly. -/
theorem arrPullbackLift_proj (q : P →o Q) (f : Z →o Q) {z₀ z₁ : Z} (hz : z₀ ≤ z₁)
    (A : Arr (Pullback q f)) (hA : A ∈ arrowFibre (pullbackSnd q f) z₀ z₁)
    (ha : Arr.map (pullbackFst q f) A ∈ arrowFibre q (f z₀) (f z₁)) :
    arrPullbackLift q f hz (Arr.map (pullbackFst q f) A) ha = A := by
  obtain ⟨⟨s, zs, hs⟩, ⟨t, zt, ht⟩, hle⟩ := A
  obtain ⟨h1, h2⟩ := hA
  simp only [pullbackSnd_apply] at h1 h2
  subst h1; subst h2
  rfl

/-- **Source: `prop:draft-poset-coarsening-properties`, clause 3 (§5.1).**
For a poset coarsening `q : P → Q` and an arbitrary monotone `f : Z → Q`, the pullback
projection `f^*q : P ×_Q Z → Z` is a poset coarsening. -/
theorem IsPosetCoarsening.pullback_proj {q : P →o Q} (hq : IsPosetCoarsening q)
    (f : Z →o Q) : IsPosetCoarsening (pullbackSnd q f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    obtain ⟨x, hx⟩ := hq.surjective (f z)
    exact ⟨⟨x, z, hx⟩, rfl⟩
  · rw [isOpenPosetMap_iff_exists_le (pullbackSnd q f).monotone]
    intro y z hz
    obtain ⟨x, hxy, hx⟩ :=
      hq.isOpen.exists_le (y := y.fst) (z := f z) (by rw [y.compat]; exact f.monotone hz)
    exact ⟨⟨x, z, hx⟩, ⟨hxy, hz⟩, rfl⟩
  · intro z₀ z₁ hz A hA B hB
    have hproj : ∀ C : Arr (Pullback q f), C ∈ arrowFibre (pullbackSnd q f) z₀ z₁ →
        Arr.map (pullbackFst q f) C ∈ arrowFibre q (f z₀) (f z₁) := by
      intro C hC
      refine ⟨?_, ?_⟩
      · change q C.src.fst = f z₀
        rw [C.src.compat]; exact congrArg f hC.1
      · change q C.tgt.fst = f z₁
        rw [C.tgt.compat]; exact congrArg f hC.2
    have ha := hproj A hA
    have hb := hproj B hB
    have hz' := hq.arrowFibre_connected (f z₀) (f z₁) (f.monotone hz) _ ha _ hb
    -- lift the downstairs zigzag arrow by arrow
    have key : ∀ c : Arr P, ZigzagIn (arrowFibre q (f z₀) (f z₁)) (Arr.map (pullbackFst q f) A) c →
        ∀ hc : c ∈ arrowFibre q (f z₀) (f z₁),
        ZigzagIn (arrowFibre (pullbackSnd q f) z₀ z₁) A (arrPullbackLift q f hz c hc) := by
      intro c h
      induction h with
      | refl =>
          intro hc
          rw [arrPullbackLift_proj q f hz A hA hc]
          exact ZigzagIn.refl _
      | tail _ hstep ih =>
          rename_i d e _
          intro hc
          refine (ih hstep.1).trans (ZigzagIn.single ?_)
          refine ⟨arrPullbackLift_mem q f hz d hstep.1, arrPullbackLift_mem q f hz e hc, ?_⟩
          exact hstep.2.2.imp (arrPullbackLift_mono q f hz hstep.1 hc)
            (arrPullbackLift_mono q f hz hc hstep.1)
    have := key _ hz' hb
    rwa [arrPullbackLift_proj q f hz B hB hb] at this

end Pullback

end Truss.Transfer
