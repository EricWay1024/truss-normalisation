/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.Context

/-!
# Normalising coarsenings and normal objects (§5.2)

This module formalises the terminality half of the draft normalisation chapter's §5.2, rows
`C06`–`C10` of
[`plan/DraftNormalisationVerification.md`](../../../plan/DraftNormalisationVerification.md).

## Main definitions

* `IsNormalising` — `def:draft-normalising`: terminality in `OutCoarse(X, L)`, written out as
  an explicit unique-mediator statement.  **No existence is presumed anywhere in this file.**
* `IsNormal` — the identity coarsening is normalising.

## Main results

* `IsNormalising.unique_iso` — `Structural uniqueness`: two normalising coarsenings out of one
  labelled object are related by a unique compatible isomorphism, whose inverse is again a
  coarsening.
* `isNormal_iff_isIso` — `Characterisation of normality`, both directions.
* `terminal_factors` — `prop:draft-terminal-factors`.
* `normalising_precomp` — `lem:draft-normalisation-precomposition`, with the source's
  existence hypothesis kept explicit.
* `IsNormalising.target_isNormal` — `The target of a normalising coarsening is normal`.
  Its converse is *not* asserted; see the module note.

## Note on the unasserted converse

The chapter's commented remark observes that normality of `(Y, M)` alone does not make a
chosen coarsening `(X, L) → (Y, M)` terminal.  Nothing here asserts that converse, in line
with plan row `C10`.
-/

universe u v w u₂ v₂

namespace Truss.Transfer

open CategoryTheory TrussLike

variable {n : ℕ} {K : Type u} [Category.{v} K] [inst : TrussLike.{u, v, w} n K]
variable {C : Type u₂} [Category.{v₂} C]

/-! ### C06: normalising coarsenings and normal objects -/

/-- **Source: `def:draft-normalising` (§5.2).**  A labelled coarsening is *normalising* when
it is terminal in `OutCoarse(X, L)`: it is itself a coarsening, and every labelled coarsening
out of the same source factors through it by a unique labelled coarsening. -/
def IsNormalising {A B : LabObj.{u, v, w, u₂, v₂} n K C} (q : A ⟶ B) : Prop :=
  IsCoarsening q.1 ∧ ∀ (D : LabObj.{u, v, w, u₂, v₂} n K C) (r : A ⟶ D), IsCoarsening r.1 →
    ∃! h : D ⟶ B, IsCoarsening h.1 ∧ q = r ≫ h

/-- **Source: `def:draft-normalising` (§5.2).**  A labelled object is *normal* when its
identity map is normalising. -/
def IsNormal (A : LabObj.{u, v, w, u₂, v₂} n K C) : Prop := IsNormalising (𝟙 A)

namespace IsNormalising

variable {A B D : LabObj.{u, v, w, u₂, v₂} n K C}

theorem isCoarsening {q : A ⟶ B} (h : IsNormalising q) : IsCoarsening q.1 := h.1

/-- The mediator supplied by terminality. -/
theorem exists_mediator {q : A ⟶ B} (h : IsNormalising q) {U : LabObj.{u, v, w, u₂, v₂} n K C}
    (r : A ⟶ U) (hr : IsCoarsening r.1) : ∃ m : U ⟶ B, IsCoarsening m.1 ∧ q = r ≫ m := by
  obtain ⟨m, hm, -⟩ := h.2 U r hr
  exact ⟨m, hm⟩

/-- Mediators out of a coarsening are unique, because a coarsening is an epimorphism. -/
theorem mediator_unique {U : LabObj.{u, v, w, u₂, v₂} n K C} {r : A ⟶ U}
    (hr : IsCoarsening r.1) {m m' : U ⟶ B} (h : r ≫ m = r ≫ m') : m = m' := by
  haveI := LabObj.epi_of_isCoarsening hr
  exact (cancel_epi r).1 h

/-- **Source: `Structural uniqueness` (§5.2).**  Two normalising coarsenings out of the same
labelled object are related by a compatible isomorphism, unique as a mediator, whose inverse
is again a labelled coarsening. -/
theorem unique_iso {q : A ⟶ B} {q' : A ⟶ D} (h : IsNormalising q) (h' : IsNormalising q') :
    ∃ e : B ⟶ D, ∃ e' : D ⟶ B, IsCoarsening e.1 ∧ IsCoarsening e'.1 ∧
      q' = q ≫ e ∧ q = q' ≫ e' ∧ e ≫ e' = 𝟙 B ∧ e' ≫ e = 𝟙 D := by
  obtain ⟨e, he, hqe⟩ := h'.exists_mediator q h.isCoarsening
  obtain ⟨e', he', hq'e⟩ := h.exists_mediator q' h'.isCoarsening
  refine ⟨e, e', he, he', hqe, hq'e, ?_, ?_⟩
  · refine mediator_unique h.isCoarsening (m := e ≫ e') (m' := 𝟙 B) ?_
    rw [← Category.assoc, ← hqe, ← hq'e, Category.comp_id]
  · refine mediator_unique h'.isCoarsening (m := e' ≫ e) (m' := 𝟙 D) ?_
    rw [← Category.assoc, ← hq'e, ← hqe, Category.comp_id]

end IsNormalising

/-! ### C07: characterisation of normality -/

/-- **Source: `Characterisation of normality` (§5.2).**  A labelled object is normal exactly
when every morphism of `OutCoarse(X, L)` is invertible.  "Invertible" is invertibility in
`OutCoarse(X, L)`, so the inverse mediator is itself a labelled coarsening. -/
theorem isNormal_iff_isIso (A : LabObj.{u, v, w, u₂, v₂} n K C) :
    IsNormal A ↔ ∀ (r q : LabOutCoarse A) (h : r ⟶ q), IsIso h := by
  constructor
  · -- The identity coarsening is initial; normality makes it terminal; thinness does the rest.
    intro hA r q h
    obtain ⟨uq, huq, hquq⟩ := hA.exists_mediator q.map q.isCoarsening
    have huqObj : q ⟶ LabOutCoarse.idObj A := ⟨uq, huq, by simpa [LabOutCoarse.idObj] using hquq⟩
    refine ⟨huqObj ≫ LabOutCoarse.fromIdObj r, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · intro hiso
    refine ⟨IsCoarsening.id _, fun D r hr => ?_⟩
    set robj : LabOutCoarse A := ⟨D, r, hr⟩ with hrobj
    haveI := hiso (LabOutCoarse.idObj A) robj (LabOutCoarse.fromIdObj robj)
    set k := inv (LabOutCoarse.fromIdObj robj) with hk
    refine ⟨k.1, ⟨k.2.1, ?_⟩, fun m hm => ?_⟩
    · have := k.2.2
      simpa [LabOutCoarse.idObj] using this
    · exact IsNormalising.mediator_unique hr (by rw [← hm.2, ← k.2.2]; simp [LabOutCoarse.idObj])

/-- A normalising coarsening out of a normal object is invertible in `G`; equivalently, every
labelled coarsening out of a normal object admits a coarsening inverse. -/
theorem IsNormal.isIso_of_isCoarsening {A B : LabObj.{u, v, w, u₂, v₂} n K C} (hA : IsNormal A)
    {q : A ⟶ B} (hq : IsCoarsening q.1) :
    ∃ p : B ⟶ A, IsCoarsening p.1 ∧ q ≫ p = 𝟙 A ∧ p ≫ q = 𝟙 B := by
  obtain ⟨p, hp, hqp⟩ := hA.exists_mediator q hq
  refine ⟨p, hp, hqp.symm, ?_⟩
  refine IsNormalising.mediator_unique hq (m := p ≫ q) (m' := 𝟙 B) ?_
  rw [← Category.assoc, ← hqp, Category.id_comp, Category.comp_id]

/-! ### C08: terminal factors -/

/-- **Source: `prop:draft-terminal-factors` (§5.2).**  If a composite of labelled coarsenings
is normalising, its final factor is normalising. -/
theorem terminal_factors {A B D : LabObj.{u, v, w, u₂, v₂} n K C} {c : A ⟶ B} {e : B ⟶ D}
    (hc : IsCoarsening c.1) (he : IsCoarsening e.1) (h : IsNormalising (c ≫ e)) :
    IsNormalising e := by
  refine ⟨he, fun W r hr => ?_⟩
  obtain ⟨h', hh', hfact⟩ := h.exists_mediator (c ≫ r) (hc.comp hr)
  refine ⟨h', ⟨hh', ?_⟩, fun k hk => ?_⟩
  · -- cancel the epimorphism `c`
    refine IsNormalising.mediator_unique hc (m := e) (m' := r ≫ h') ?_
    rw [← Category.assoc]
    exact hfact
  · -- cancel the epimorphism `r`
    refine IsNormalising.mediator_unique hr (m := k) (m' := h') ?_
    rw [← hk.2]
    refine IsNormalising.mediator_unique hc (m := e) (m' := r ≫ h') ?_
    rw [← Category.assoc]
    exact hfact

/-! ### C10: the target of a normalising coarsening is normal -/

/-- **Source: `The target of a normalising coarsening is normal` (§5.2).**  Factor `q` as
`q ≫ 𝟙`, and apply `terminal_factors`.  The converse is not asserted. -/
theorem IsNormalising.target_isNormal {A B : LabObj.{u, v, w, u₂, v₂} n K C} {q : A ⟶ B}
    (h : IsNormalising q) : IsNormal B := by
  refine terminal_factors h.isCoarsening (IsCoarsening.id _) ?_
  rwa [Category.comp_id]

/-! ### C09: normalisation after a coarsening -/

/-- **Source: `lem:draft-normalisation-precomposition` (§5.2).**  If the source admits *some*
normalisation, then `d ∘ a` is normalising exactly when `d` is.  The existence hypothesis is
kept explicit, as the source states it; this result does not depend on any later existence
theorem. -/
theorem normalising_precomp {A B D : LabObj.{u, v, w, u₂, v₂} n K C} {a : A ⟶ B} {d : B ⟶ D}
    (ha : IsCoarsening a.1) (hd : IsCoarsening d.1)
    (hex : ∃ (W : LabObj.{u, v, w, u₂, v₂} n K C) (q : A ⟶ W), IsNormalising q) :
    IsNormalising (a ≫ d) ↔ IsNormalising d := by
  constructor
  · exact terminal_factors ha hd
  · intro hdnorm
    obtain ⟨W, q, hq⟩ := hex
    -- terminality of `q` factors it through `a`
    obtain ⟨e, he, hqe⟩ := hq.exists_mediator a ha
    -- `e` is then normalising out of `B`, by C08
    have henorm : IsNormalising e := terminal_factors ha he (by rwa [← hqe])
    -- compare the two normalisations of `B`
    obtain ⟨h, h', hh, hh', hdh, heh', hhh', hh'h⟩ := hdnorm.unique_iso henorm
    refine ⟨ha.comp hd, fun U r hr => ?_⟩
    obtain ⟨k, hk, hqk⟩ := hq.exists_mediator r hr
    refine ⟨k ≫ h', ⟨hk.comp hh', ?_⟩, fun m hm => ?_⟩
    · -- `r ≫ (k ≫ h') = q ≫ h' = (a ≫ e) ≫ h' = a ≫ (d ≫ h) ≫ h' = a ≫ d`
      rw [← Category.assoc, ← hqk, hqe, Category.assoc, hdh, Category.assoc, hhh',
        Category.comp_id]
    · refine IsNormalising.mediator_unique hr (m := m) (m' := k ≫ h') ?_
      rw [← hm.2, ← Category.assoc, ← hqk, hqe, Category.assoc, hdh, Category.assoc, hhh',
        Category.comp_id]

end Truss.Transfer
