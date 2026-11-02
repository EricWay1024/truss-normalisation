/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.Terminality

/-!
# From a retained-invariant classification to the normalising criterion

Both §5.3 and §5.4 of the draft chapter run the same argument twice:

1. classify the outgoing labelled coarsenings of `(X,L)` by an invariant (the retained
   singular set, resp. the retained singular family), so that a mediator `r → q` exists
   exactly when `inv q ≤ inv r`;
2. observe that the invariant of any labelled coarsening is at least some least value
   (`NonTriv`, resp. its forward-stable closure);
3. exhibit one labelled coarsening attaining that least value;
4. conclude that a labelled coarsening is **normalising** exactly when its invariant is
   least, and that the object is **normal** exactly when the identity attains it.

Step 4 is pure order theory on top of §5.2 and is proved here once, so that the two concrete
sections need only supply steps 1–3.  `isNormalising_iff_inv_eq_least` is the statement.
-/

universe u v w u₂ v₂ r

namespace Truss.Transfer

open CategoryTheory TrussLike

variable {n : ℕ} {K : Type u} [Category.{v} K] [inst : TrussLike.{u, v, w} n K]
variable {C : Type u₂} [Category.{v₂} C]

/-- The data of a retained-invariant classification of the outgoing labelled coarsenings of
a fixed labelled object.  The two concrete instances are §5.3's retained set and §5.4's
retained family. -/
structure OutClassification (A : LabObj.{u, v, w, u₂, v₂} n K C) (R : Type r)
    [PartialOrder R] where
  /-- The invariant of a labelled coarsening out of `A`. -/
  inv : ∀ {D : LabObj.{u, v, w, u₂, v₂} n K C}, (A ⟶ D) → R
  /-- A mediator exists exactly when the invariants are reverse-ordered. -/
  mediator_iff : ∀ {D E : LabObj.{u, v, w, u₂, v₂} n K C} (r : A ⟶ D) (q : A ⟶ E),
    IsCoarsening r.1 → IsCoarsening q.1 →
      ((∃ h : D ⟶ E, IsCoarsening h.1 ∧ q = r ≫ h) ↔ inv q ≤ inv r)
  /-- The least attainable invariant. -/
  least : R
  /-- Every labelled coarsening attains at least the least value. -/
  least_le : ∀ {D : LabObj.{u, v, w, u₂, v₂} n K C} (r : A ⟶ D), IsCoarsening r.1 →
    least ≤ inv r
  /-- The least value is attained. -/
  exists_least : ∃ (D : LabObj.{u, v, w, u₂, v₂} n K C) (r : A ⟶ D),
    IsCoarsening r.1 ∧ inv r = least

namespace OutClassification

variable {A : LabObj.{u, v, w, u₂, v₂} n K C} {R : Type r} [PartialOrder R]
variable (cl : OutClassification A R)

/-- **The normalising criterion.**  Given a retained-invariant classification, a labelled
coarsening is normalising exactly when its invariant is least. -/
theorem isNormalising_iff_inv_eq_least {Bo : LabObj.{u, v, w, u₂, v₂} n K C} (q : A ⟶ Bo)
    (hq : IsCoarsening q.1) : IsNormalising q ↔ cl.inv q = cl.least := by
  constructor
  · intro hnorm
    obtain ⟨D, r, hr, hrleast⟩ := cl.exists_least
    obtain ⟨m, hm, heq⟩ := hnorm.exists_mediator r hr
    have hle : cl.inv q ≤ cl.inv r := (cl.mediator_iff r q hr hq).1 ⟨m, hm, heq⟩
    rw [hrleast] at hle
    exact le_antisymm hle (cl.least_le q hq)
  · intro hinv
    refine ⟨hq, fun D r hr => ?_⟩
    have hle : cl.inv q ≤ cl.inv r := by rw [hinv]; exact cl.least_le r hr
    obtain ⟨h, hh, hcomp⟩ := (cl.mediator_iff r q hr hq).2 hle
    refine ⟨h, ⟨hh, hcomp⟩, fun k hk => ?_⟩
    exact IsNormalising.mediator_unique hr (hk.2.symm.trans hcomp)

/-- **The normality criterion.**  The object is normal exactly when the identity coarsening
attains the least invariant. -/
theorem isNormal_iff_inv_id_eq_least : IsNormal A ↔ cl.inv (𝟙 A) = cl.least :=
  cl.isNormalising_iff_inv_eq_least (𝟙 A) (IsCoarsening.id _)

/-- **Existence.**  A classification with an attained least value produces a normalising
coarsening: the one attaining it. -/
theorem exists_isNormalising (cl : OutClassification A R) :
    ∃ (D : LabObj.{u, v, w, u₂, v₂} n K C) (r : A ⟶ D), IsNormalising r := by
  obtain ⟨D, r, hr, hrleast⟩ := cl.exists_least
  exact ⟨D, r, (cl.isNormalising_iff_inv_eq_least r hr).2 hrleast⟩

/-- Any two normalising coarsenings supplied by the classification have the same invariant. -/
theorem inv_eq_of_isNormalising {D E : LabObj.{u, v, w, u₂, v₂} n K C} {r : A ⟶ D} {q : A ⟶ E}
    (hr : IsNormalising r) (hq : IsNormalising q) : cl.inv r = cl.inv q :=
  ((cl.isNormalising_iff_inv_eq_least r hr.isCoarsening).1 hr).trans
    ((cl.isNormalising_iff_inv_eq_least q hq.isCoarsening).1 hq).symm

end OutClassification

end Truss.Transfer
