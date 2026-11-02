/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.Context

/-!
# Automorphism-free label categories and the uniqueness of label comparisons

Chapter 2's `NoAut` (`def:Automorphism-free categories`) and the clause of §5.2's
`Label comparisons` remark that says the invertible natural comparison
`L ≅ M ∘ Tot(q)` **is unique**.

That uniqueness is exactly what makes the chapter's strict convention legitimate: if the
comparison were not unique, displaying it as an equality would discard information.  It is
proved here from `NoAut` alone, for an arbitrary source category.

## Main results

* `NoAut.natIso_unique` — any two natural isomorphisms between the same pair of functors into
  an automorphism-free category are equal.
* `NoAut.natIso_subsingleton`, `NoAut.autEqIso` — packaged forms.
* `labelComparison_unique` — the `Label comparisons` remark for a labelled coarsening.

## What is *not* proved here

`prop:noaut-iteration` (automorphism-freeness is stable under iterating the labelled-truss
construction) and the chapter's standing choice of gaunt skeletal representatives are
separate obligations; neither is claimed.
-/

universe u v u' v'

namespace Truss.Transfer

open CategoryTheory

/-- **Source: `def:Automorphism-free categories` (Chapter 2).**  Every automorphism of every
object is the identity. -/
def NoAut (C : Type u) [Category.{v} C] : Prop := ∀ (X : C) (f : X ⟶ X), IsIso f → f = 𝟙 X

namespace NoAut

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- In an automorphism-free category, any two natural isomorphisms between the same pair of
functors agree.  The difference of two such isomorphisms is an automorphism of the source
functor, hence componentwise an identity. -/
theorem natIso_unique (hC : NoAut C) {F G : D ⥤ C} (α β : F ≅ G) : α = β := by
  refine Iso.ext (NatTrans.ext (funext fun X => ?_))
  -- `α.hom.app X ≫ β.inv.app X` is an automorphism of `F.obj X`
  have hiso : IsIso (α.hom.app X ≫ β.inv.app X) := by
    haveI : IsIso (α.hom.app X) := inferInstance
    haveI : IsIso (β.inv.app X) := inferInstance
    infer_instance
  have hid := hC _ (α.hom.app X ≫ β.inv.app X) hiso
  calc α.hom.app X = (α.hom.app X ≫ β.inv.app X) ≫ β.hom.app X := by
        rw [Category.assoc, ← NatTrans.comp_app, β.inv_hom_id, NatTrans.id_app,
          Category.comp_id]
    _ = 𝟙 _ ≫ β.hom.app X := by rw [hid]
    _ = β.hom.app X := Category.id_comp _

theorem natIso_subsingleton (hC : NoAut C) (F G : D ⥤ C) : Subsingleton (F ≅ G) :=
  ⟨fun α β => hC.natIso_unique α β⟩

/-- Two functors into an automorphism-free category that are isomorphic are isomorphic in
exactly one way. -/
theorem autEqIso (hC : NoAut C) {F : D ⥤ C} (α : F ≅ F) : α = Iso.refl F :=
  hC.natIso_unique α (Iso.refl F)

end NoAut

/-! ### The `Label comparisons` remark of §5.2 -/

variable {n : ℕ} {K : Type u} [Category.{v} K] [inst : TrussLike.{u, v, u'} n K]
variable {C : Type u'} [Category.{v'} C]

/-- **Source: the `Label comparisons` remark (§5.2).**  *"Label preservation intrinsically
consists of an invertible natural comparison `L ≅ M ∘ Tot(q)`.  Such a comparison is
unique."*  That uniqueness clause is proved here; it is what licenses the chapter's
convention of displaying the comparison as an equality. -/
theorem labelComparison_unique (hC : NoAut C) {X Y : K} (q : X ⟶ Y) (L : TrussLike.Tot X ⥤ C)
    (M : TrussLike.Tot Y ⥤ C) (α β : L ≅ posetFunctor (TrussLike.totMap q) ⋙ M) : α = β :=
  hC.natIso_unique α β

end Truss.Transfer
