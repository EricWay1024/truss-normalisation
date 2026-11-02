/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.Poset

/-!
# Descent of category-valued labels along a poset coarsening (§5.1)

This module formalises `prop:draft-label-descent`, row `P05` of
[`plan/DraftNormalisationVerification.md`](../../../plan/DraftNormalisationVerification.md),
from the draft normalisation chapter `transfer/ch03-normalisation-draft.typ`:

> Let `q : P → Q` be a poset coarsening and `L : Fun(P, C)`.  There is a factorisation
> `L = K ∘ q` with `K : Fun(Q, C)` if and only if `L` sends every arrow collapsed by `q`
> to an identity.  When it exists, `K` is unique.

## Main definitions

* `SendsCollapsedToId` — the descent criterion.  Following the draft's own convention
  ("saying that an incoming arrow is labelled by an identity includes the required equality
  of its endpoint object labels"), an arrow is *labelled by an identity* when its two
  endpoint object labels are equal and the arrow label is the corresponding object bridge.
  The label category `C` is an arbitrary category: no gauntness, thinness, skeletality or
  `Prop`-valuedness is assumed.
* `descend` — the descended label functor `K`.

## Main results

* `label_descent` — the stated equivalence.
* `descend_spec` — `q ⋙ descend = L`, the construction equation.
* `label_descent_unique` — uniqueness of the descended functor.

The proof follows the draft's own argument: connected identity-arrow fibres make the object
label constant on each point fibre (`SendsCollapsedToId.obj_eq`); comparable lifts of one
coarse arrow differ by collapsed endpoint arrows, so functoriality equates their labels
(`transportArrow_of_le`); connected arrow fibres remove the choice of lift
(`transportArrow_indep`); openness lifts a composable pair with a prescribed final target,
which is what makes the descended arrow labels compose (`descend`'s `map_comp`); and
object-surjectivity plus openness give arrow-surjectivity, hence uniqueness.
-/

universe u v w

namespace Truss.Transfer

open CategoryTheory

variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
variable {C : Type w} [Category C]

/-- A monotone map, viewed as a functor between the associated poset categories. -/
abbrev posetFunctor (q : P →o Q) : P ⥤ Q := q.monotone.functor

/-- **Source: `prop:draft-label-descent`, hypothesis (§5.1).**  The label `L` sends every
arrow collapsed by `q` to an identity.  Per the draft's convention this includes equality of
the two endpoint object labels. -/
def SendsCollapsedToId (q : P →o Q) (L : P ⥤ C) : Prop :=
  ∀ (x y : P) (h : x ≤ y), q x = q y → ∃ e : L.obj x = L.obj y, L.map (homOfLE h) = eqToHom e

/-- Restatement of the descent criterion in the draft's `Arr`/`Collapses` vocabulary. -/
theorem sendsCollapsedToId_iff (q : P →o Q) (L : P ⥤ C) :
    SendsCollapsedToId q L ↔
      ∀ a : Arr P, Collapses q a →
        ∃ e : L.obj a.src = L.obj a.tgt, L.map (homOfLE a.le) = eqToHom e := by
  constructor
  · intro h a ha; exact h a.src a.tgt a.le ha
  · intro h x y hxy hq; exact h ⟨x, y, hxy⟩ hq

namespace SendsCollapsedToId

variable {q : P →o Q} {L : P ⥤ C}

/-- Connected point fibres make the object label constant on each point fibre. -/
theorem obj_eq (hL : SendsCollapsedToId q L) (hq : IsPosetCoarsening q) {x y : P}
    (hxy : q x = q y) : L.obj x = L.obj y := by
  have hx : x ∈ pointFibre q (q x) := rfl
  have hy : y ∈ pointFibre q (q x) := hxy.symm
  have hz := hq.pointFibre_connected (q x) x hx y hy
  have key : ∀ z : P, ZigzagIn (pointFibre q (q x)) x z → L.obj x = L.obj z := by
    intro z h
    induction h with
    | refl => rfl
    | tail _ hstep ih =>
        refine ih.trans ?_
        rcases hstep.2.2 with hle | hle
        · exact (hL _ _ hle (hstep.1.trans hstep.2.1.symm)).choose
        · exact ((hL _ _ hle (hstep.2.1.trans hstep.1.symm)).choose).symm
  exact key y hz

end SendsCollapsedToId

/-! ### The descended functor -/

section Descend

variable {q : P →o Q} {L : P ⥤ C}

/-- A chosen preimage of a point of `Q`. -/
noncomputable def preimagePoint (hq : IsPosetCoarsening q) (y : Q) : P :=
  Function.surjInv hq.surjective y

@[simp] theorem preimagePoint_spec (hq : IsPosetCoarsening q) (y : Q) :
    q (preimagePoint hq y) = y := Function.surjInv_eq hq.surjective y

/-- A chosen lift of an arrow of `Q` to an arrow of `P`. -/
noncomputable def liftArrow (hq : IsPosetCoarsening q) {y y' : Q} (h : y ≤ y') : Arr P :=
  (hq.arrowFibre_nonempty h).choose

theorem liftArrow_mem (hq : IsPosetCoarsening q) {y y' : Q} (h : y ≤ y') :
    liftArrow hq h ∈ arrowFibre q y y' := (hq.arrowFibre_nonempty h).choose_spec

/-- The label of an arbitrary lift `a` of the arrow `y ≤ y'`, transported along the object
bridges to the chosen preimages of `y` and `y'`. -/
noncomputable def transportArrow (hq : IsPosetCoarsening q) (hL : SendsCollapsedToId q L)
    {y y' : Q} (a : Arr P) (ha : a ∈ arrowFibre q y y') :
    L.obj (preimagePoint hq y) ⟶ L.obj (preimagePoint hq y') :=
  eqToHom (hL.obj_eq hq (by rw [preimagePoint_spec hq y, ha.1])) ≫
    L.map (homOfLE a.le) ≫
    eqToHom (hL.obj_eq hq (by rw [ha.2, preimagePoint_spec hq y']))

/-- A bookkeeping lemma: two `eqToHom`-conjugates agree as soon as the inner square does.
Proof irrelevance identifies the outer bridges. -/
private theorem eqToHom_conj_eq {X Y X' Y' Z W : C} (α : X ⟶ Y) (β : X' ⟶ Y')
    (p₁ : Z = X) (p₂ : Y = W) (r₁ : Z = X') (r₂ : Y' = W) (e₁ : X = X') (e₂ : Y = Y')
    (hsq : α ≫ eqToHom e₂ = eqToHom e₁ ≫ β) :
    eqToHom p₁ ≫ α ≫ eqToHom p₂ = eqToHom r₁ ≫ β ≫ eqToHom r₂ := by
  subst e₁; subst e₂
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hsq
  subst hsq
  rfl

/-- Comparable lifts of a single coarse arrow carry the same transported label: the two
endpoint comparisons are collapsed arrows, and functoriality of `L` closes the square. -/
theorem transportArrow_of_le (hq : IsPosetCoarsening q) (hL : SendsCollapsedToId q L)
    {y y' : Q} {a b : Arr P} (ha : a ∈ arrowFibre q y y') (hb : b ∈ arrowFibre q y y')
    (hab : a ≤ b) : transportArrow hq hL a ha = transportArrow hq hL b hb := by
  obtain ⟨e₁, he₁⟩ := hL a.src b.src hab.1 (by rw [ha.1, hb.1])
  obtain ⟨e₂, he₂⟩ := hL a.tgt b.tgt hab.2 (by rw [ha.2, hb.2])
  have hsq : L.map (homOfLE a.le) ≫ eqToHom e₂ = eqToHom e₁ ≫ L.map (homOfLE b.le) := by
    have hpath : (homOfLE a.le ≫ homOfLE hab.2 : a.src ⟶ b.tgt) = homOfLE hab.1 ≫ homOfLE b.le :=
      Subsingleton.elim _ _
    rw [← he₁, ← he₂, ← L.map_comp, ← L.map_comp, hpath]
  exact eqToHom_conj_eq _ _ _ _ _ _ e₁ e₂ hsq

/-- The transported label does not depend on the chosen lift: arrow fibres are connected. -/
theorem transportArrow_indep (hq : IsPosetCoarsening q) (hL : SendsCollapsedToId q L)
    {y y' : Q} (h : y ≤ y') {a b : Arr P} (ha : a ∈ arrowFibre q y y')
    (hb : b ∈ arrowFibre q y y') :
    transportArrow hq hL a ha = transportArrow hq hL b hb := by
  have hz := hq.arrowFibre_connected y y' h a ha b hb
  have key : ∀ c : Arr P, ZigzagIn (arrowFibre q y y') a c →
      ∀ hc : c ∈ arrowFibre q y y', transportArrow hq hL a ha = transportArrow hq hL c hc := by
    intro c hzc
    induction hzc with
    | refl => intro hc; rfl
    | tail _ hstep ih =>
        rename_i d e _
        intro hc
        refine (ih hstep.1).trans ?_
        rcases hstep.2.2 with hle | hle
        · exact transportArrow_of_le hq hL hstep.1 hc hle
        · exact (transportArrow_of_le hq hL hc hstep.1 hle).symm
  exact key b hz hb

/-- **Source: `prop:draft-label-descent` (§5.1), the descended functor.**  The unique
labelling `K : Fun(Q, C)` with `L = K ∘ q`. -/
noncomputable def descend (hq : IsPosetCoarsening q) (hL : SendsCollapsedToId q L) : Q ⥤ C where
  obj y := L.obj (preimagePoint hq y)
  map {_ _} h := transportArrow hq hL (liftArrow hq (leOfHom h)) (liftArrow_mem hq (leOfHom h))
  map_id y := by
    have hid : (⟨preimagePoint hq y, preimagePoint hq y, le_rfl⟩ : Arr P) ∈ arrowFibre q y y :=
      ⟨preimagePoint_spec hq y, preimagePoint_spec hq y⟩
    rw [transportArrow_indep hq hL le_rfl (liftArrow_mem hq (le_refl y)) hid]
    change eqToHom _ ≫ L.map (homOfLE le_rfl) ≫ eqToHom _ = _
    rw [show homOfLE (le_refl (preimagePoint hq y)) = 𝟙 _ from Subsingleton.elim _ _]
    simp
  map_comp {y y' y''} f g := by
    -- lift the composable pair with a prescribed final target, using openness
    obtain ⟨t, ht⟩ := hq.surjective y''
    obtain ⟨s, hst, hs⟩ :=
      hq.isOpen.exists_le (y := t) (z := y') (by rw [ht]; exact leOfHom g)
    obtain ⟨r, hrs, hr⟩ :=
      hq.isOpen.exists_le (y := s) (z := y) (by rw [hs]; exact leOfHom f)
    have hA : (⟨r, s, hrs⟩ : Arr P) ∈ arrowFibre q y y' := ⟨hr, hs⟩
    have hB : (⟨s, t, hst⟩ : Arr P) ∈ arrowFibre q y' y'' := ⟨hs, ht⟩
    have hC : (⟨r, t, hrs.trans hst⟩ : Arr P) ∈ arrowFibre q y y'' := ⟨hr, ht⟩
    rw [transportArrow_indep hq hL (leOfHom f) (liftArrow_mem hq (leOfHom f)) hA,
      transportArrow_indep hq hL (leOfHom g) (liftArrow_mem hq (leOfHom g)) hB,
      transportArrow_indep hq hL (leOfHom (f ≫ g)) (liftArrow_mem hq (leOfHom (f ≫ g))) hC]
    change eqToHom _ ≫ L.map (homOfLE (hrs.trans hst)) ≫ eqToHom _ =
      (eqToHom _ ≫ L.map (homOfLE hrs) ≫ eqToHom _) ≫
        eqToHom _ ≫ L.map (homOfLE hst) ≫ eqToHom _
    rw [show homOfLE (hrs.trans hst) = homOfLE hrs ≫ homOfLE hst from Subsingleton.elim _ _,
      L.map_comp]
    simp

@[simp] theorem descend_obj (hq : IsPosetCoarsening q) (hL : SendsCollapsedToId q L) (y : Q) :
    (descend hq hL).obj y = L.obj (preimagePoint hq y) := rfl

/-- **Source: `prop:draft-label-descent` (§5.1), the construction equation.**
The descended labelling really does factor `L`. -/
theorem descend_spec (hq : IsPosetCoarsening q) (hL : SendsCollapsedToId q L) :
    posetFunctor q ⋙ descend hq hL = L := by
  have hobj : ∀ x : P, (posetFunctor q ⋙ descend hq hL).obj x = L.obj x := by
    intro x
    exact hL.obj_eq hq (by simp)
  refine CategoryTheory.Functor.ext hobj ?_
  intro x x' f
  have hmem : (⟨x, x', leOfHom f⟩ : Arr P) ∈ arrowFibre q (q x) (q x') := ⟨rfl, rfl⟩
  change transportArrow hq hL _ (liftArrow_mem hq (q.monotone (leOfHom f))) = _
  rw [transportArrow_indep hq hL (q.monotone (leOfHom f))
    (liftArrow_mem hq (q.monotone (leOfHom f))) hmem]
  change eqToHom _ ≫ L.map (homOfLE (leOfHom f)) ≫ eqToHom _ = eqToHom _ ≫ L.map f ≫ eqToHom _
  rw [show homOfLE (leOfHom f) = f from Subsingleton.elim _ _]

end Descend

/-! ### Uniqueness and the stated equivalence -/

section Uniqueness

variable {q : P →o Q}

/-- Object-surjectivity and openness give arrow-surjectivity, hence a descended labelling is
unique.  **Source: `prop:draft-label-descent` (§5.1), final clause.** -/
theorem label_descent_unique (hq : IsPosetCoarsening q) {K K' : Q ⥤ C}
    (h : posetFunctor q ⋙ K = posetFunctor q ⋙ K') : K = K' := by
  have hobj : ∀ y : Q, K.obj y = K'.obj y := by
    intro y
    have hx := Functor.congr_obj h (preimagePoint hq y)
    simpa using hx
  refine CategoryTheory.Functor.ext hobj ?_
  intro y y' f
  obtain ⟨a, ha⟩ := hq.arrowFibre_nonempty (leOfHom f)
  obtain ⟨h1, h2⟩ := ha
  subst h1; subst h2
  have hc := Functor.congr_hom h (homOfLE a.le)
  rw [show f = homOfLE (q.monotone a.le) from Subsingleton.elim _ _]
  simpa using hc

/-- **Source: `prop:draft-label-descent` (§5.1).**  A category-valued label descends along a
poset coarsening exactly when it sends every collapsed arrow to an identity. -/
theorem label_descent (hq : IsPosetCoarsening q) (L : P ⥤ C) :
    (∃ K : Q ⥤ C, posetFunctor q ⋙ K = L) ↔ SendsCollapsedToId q L := by
  constructor
  · rintro ⟨K, rfl⟩ x y hxy hq'
    refine ⟨congrArg K.obj hq', ?_⟩
    have hmap : (posetFunctor q).map (homOfLE hxy) = (eqToHom hq' : (q x : Q) ⟶ q y) :=
      Subsingleton.elim _ _
    rw [Functor.comp_map, hmap, eqToHom_map]
  · intro hL
    exact ⟨descend hq hL, descend_spec hq hL⟩

end Uniqueness

end Truss.Transfer
