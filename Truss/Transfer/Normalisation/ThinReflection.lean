/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Reflections between thin categories (`lem:draft-thin-reflection`)

The draft normalisation chapter's §5.5 reduces the successor step of normalisation to an
abstract statement about thin categories, printed without proof:

> Let `Φ : X → Y` and `Λ : Y → X` be functors between thin categories.  If `Φ ∘ Λ = id_Y`
> and `R → Λ(Φ(R))` for every `R ∈ X`, then `Φ ⊣ Λ` and `Λ` is fully faithful.  In
> particular, `Λ` preserves and reflects terminal objects.

This module proves it for genuine functors between genuine categories.  Mathematical
composition `Φ ∘ Λ` is Lean's `Λ ⋙ Φ`, so the hypothesis is the **functor equality**
`Λ ⋙ Φ = 𝟭 Y`, not an isomorphism.  The counit used internally is the canonical comparison
`eqToHom` of that equality; the equality itself is the hypothesis and is not weakened.

Thinness is `Quiver.IsThin`: every hom-type is a subsingleton.  Thinness is **not**
skeletality, and nothing here assumes the latter: two objects of `X` may be isomorphic
without being equal.

## Main definitions

* `ThinReflection.adjunction` — `Φ ⊣ Λ`, with unit the given family and counit the canonical
  comparison of `Φ (Λ Z) = Z`.
* `ThinReflection.fullyFaithful` — `Λ` is fully faithful.

## Main results

* `ThinReflection.isTerminalObj` — `Λ` preserves terminal objects.
* `ThinReflection.isTerminalOfObj` — `Λ` reflects terminal objects.
* `ThinReflection.nonempty_isTerminal_obj_iff` — both, as one equivalence.
* `nonempty_isTerminal_iff_of_isThin` — in a thin category, an object is terminal exactly
  when every object maps to it.
* `nonempty_isTerminal_iff_of_homs` — in a thin category, terminality transfers along a pair
  of opposite morphisms.
-/

universe v₁ v₂ u₁ u₂

namespace Truss.Transfer

open CategoryTheory Limits

/-- In a thin category an object is terminal exactly when every object admits a morphism to
it: uniqueness of that morphism is automatic. -/
theorem nonempty_isTerminal_iff_of_isThin {X : Type u₁} [Category.{v₁} X] [Quiver.IsThin X]
    (Z : X) : Nonempty (IsTerminal Z) ↔ ∀ R : X, Nonempty (R ⟶ Z) :=
  ⟨fun ⟨h⟩ R => ⟨h.from R⟩, fun h =>
    ⟨IsTerminal.ofUniqueHom (fun R => (h R).some) (fun _ _ => Subsingleton.elim _ _)⟩⟩

/-- In a thin category, objects with morphisms both ways are simultaneously terminal. -/
theorem nonempty_isTerminal_iff_of_homs {X : Type u₁} [Category.{v₁} X] [Quiver.IsThin X]
    {Z Z' : X} (f : Z ⟶ Z') (g : Z' ⟶ Z) :
    Nonempty (IsTerminal Z) ↔ Nonempty (IsTerminal Z') := by
  rw [nonempty_isTerminal_iff_of_isThin, nonempty_isTerminal_iff_of_isThin]
  exact ⟨fun h R => ⟨(h R).some ≫ f⟩, fun h R => ⟨(h R).some ≫ g⟩⟩

namespace ThinReflection

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]
variable [Quiver.IsThin X] [Quiver.IsThin Y]
variable (Φ : X ⥤ Y) (Λ : Y ⥤ X)

omit [Quiver.IsThin X] [Quiver.IsThin Y] in
/-- The object equation `Φ (Λ Z) = Z` extracted from the functor equation. -/
theorem obj_eq (hΦΛ : Λ ⋙ Φ = 𝟭 Y) (Z : Y) : Φ.obj (Λ.obj Z) = Z := Functor.congr_obj hΦΛ Z

/-- **Source: `lem:draft-thin-reflection`, the adjunction `Φ ⊣ Λ`.**  The unit is the given
family `R → Λ (Φ R)`; the counit is the canonical comparison of the equation
`Φ (Λ Z) = Z`.  Naturality and the triangle identities hold by thinness. -/
def adjunction (hΦΛ : Λ ⋙ Φ = 𝟭 Y) (η : ∀ R : X, R ⟶ Λ.obj (Φ.obj R)) : Φ ⊣ Λ :=
  Adjunction.mkOfUnitCounit
    { unit := { app := η, naturality := fun _ _ _ => Subsingleton.elim _ _ }
      counit :=
        { app := fun Z => eqToHom (obj_eq Φ Λ hΦΛ Z)
          naturality := fun _ _ _ => Subsingleton.elim _ _ }
      left_triangle := by ext; exact Subsingleton.elim _ _
      right_triangle := by ext; exact Subsingleton.elim _ _ }

/-- The unit of `adjunction` is the given family. -/
@[simp] theorem adjunction_unit_app (hΦΛ : Λ ⋙ Φ = 𝟭 Y)
    (η : ∀ R : X, R ⟶ Λ.obj (Φ.obj R)) (R : X) : (adjunction Φ Λ hΦΛ η).unit.app R = η R := rfl

/-- The preimage of a morphism `Λ Z ⟶ Λ Z'`: apply `Φ` and read the ends through
`Φ (Λ Z) = Z`. -/
def preimage (hΦΛ : Λ ⋙ Φ = 𝟭 Y) {Z Z' : Y} (f : Λ.obj Z ⟶ Λ.obj Z') : Z ⟶ Z' :=
  eqToHom (obj_eq Φ Λ hΦΛ Z).symm ≫ Φ.map f ≫ eqToHom (obj_eq Φ Λ hΦΛ Z')

/-- **Source: `lem:draft-thin-reflection`, full faithfulness of `Λ`.**  Faithfulness is
thinness of `Y`; fullness is `preimage`. -/
def fullyFaithful (hΦΛ : Λ ⋙ Φ = 𝟭 Y) : Λ.FullyFaithful where
  preimage f := preimage Φ Λ hΦΛ f
  map_preimage _ := Subsingleton.elim _ _
  preimage_map _ := Subsingleton.elim _ _

/-- **Source: `lem:draft-thin-reflection`, preservation of terminal objects.**  Every `R`
maps to `Λ Z` through the unit `R → Λ (Φ R)` followed by `Λ` of the map `Φ R → Z`. -/
noncomputable def isTerminalObj (η : ∀ R : X, R ⟶ Λ.obj (Φ.obj R)) {Z : Y}
    (hZ : IsTerminal Z) : IsTerminal (Λ.obj Z) :=
  IsTerminal.ofUniqueHom (fun R => η R ≫ Λ.map (hZ.from (Φ.obj R)))
    (fun _ _ => Subsingleton.elim _ _)

/-- **Source: `lem:draft-thin-reflection`, reflection of terminal objects.**  Every `Z'`
maps to `Z`: take the preimage of the map `Λ Z' → Λ Z`. -/
noncomputable def isTerminalOfObj (hΦΛ : Λ ⋙ Φ = 𝟭 Y) {Z : Y}
    (hZ : IsTerminal (Λ.obj Z)) : IsTerminal Z :=
  IsTerminal.ofUniqueHom (fun Z' => preimage Φ Λ hΦΛ (hZ.from (Λ.obj Z')))
    (fun _ _ => Subsingleton.elim _ _)

/-- `Λ` preserves **and** reflects terminal objects. -/
theorem nonempty_isTerminal_obj_iff (hΦΛ : Λ ⋙ Φ = 𝟭 Y)
    (η : ∀ R : X, R ⟶ Λ.obj (Φ.obj R)) (Z : Y) :
    Nonempty (IsTerminal (Λ.obj Z)) ↔ Nonempty (IsTerminal Z) :=
  ⟨fun ⟨h⟩ => ⟨isTerminalOfObj Φ Λ hΦΛ h⟩, fun ⟨h⟩ => ⟨isTerminalObj Φ Λ η h⟩⟩

end ThinReflection

end Truss.Transfer
