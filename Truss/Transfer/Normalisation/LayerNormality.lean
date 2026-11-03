/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.RecursiveNorm

/-!
# Normality of individual layers and classified lower prefixes

`isNormal_iff_hasNormalLayers` iterates `succ_isNormal_iff`, simultaneously in the label
category. `HasNormalLayers` records every individual 1-bundle layer and every lower prefix,
with the labels obtained by successively classifying the layers above it.

This recursive formulation concerns individual layers. The arbitrary middle `j`-tower
of `cor:draft-layer-normality`, with labels in the literal iterated categories, is
constructed and proved normal in `BlockNormality.lean`, using the tower-splitting and
iterated-classifier infrastructure. No extra mathematical hypothesis is imposed.
-/

universe u v
namespace Truss.Transfer
open CategoryTheory

/-- Each one-bundle layer is normal, with labels obtained by classifying all layers above.
The recursive clause also records the normality of the remaining classified lower tower. -/
def HasNormalLayers {P : FPoset.{u}} :
    ∀ (n : ℕ) {C : Type v} [Category.{v} C] (T : Tower P n),
      ((towerTot P n T).carrier ⥤ C) → Prop
  | 0, _, _, _, _ => True
  | n + 1, _, _, T, L =>
      IsNormal (⟨T.top, L⟩ : LabObj 1 (OpenBundle (towerTot P n T.lower).carrier) _) ∧
      IsNormal (⟨T.lower, OpenBundle.classify T.top L⟩ : LabObj n (Tower P n) _) ∧
      HasNormalLayers n T.lower (OpenBundle.classify T.top L)

/-- Iterating `succ_isNormal_iff` proves normality of every one-bundle layer and every
classified lower prefix. The converse holds too. -/
theorem isNormal_iff_hasNormalLayers {P : FPoset.{u}} :
    ∀ (n : ℕ) {C : Type v} [Category.{v} C] (T : Tower P n)
      (L : (towerTot P n T).carrier ⥤ C),
      IsNormal (⟨T, L⟩ : LabObj n (Tower P n) C) ↔ HasNormalLayers n T L
  | 0, _, _, T, L => ⟨fun _ => trivial, fun _ => isNormal_zero T L⟩
  | n + 1, _, _, T, L => by
      rw [succ_isNormal_iff]
      change (_ ∧ _) ↔ _ ∧ _ ∧ _
      have ih := isNormal_iff_hasNormalLayers n T.lower (OpenBundle.classify T.top L)
      exact ⟨fun h => ⟨h.2, h.1, ih.mp h.1⟩, fun h => ⟨h.2.1, h.1⟩⟩

/-- A normal tower has normal individual layers and normal classified lower prefixes. -/
theorem IsNormal.hasNormalLayers {P : FPoset.{u}} {n : ℕ} {C : Type v} [Category.{v} C]
    {T : Tower P n} {L : (towerTot P n T).carrier ⥤ C}
    (h : IsNormal (⟨T, L⟩ : LabObj n (Tower P n) C)) : HasNormalLayers n T L :=
  (isNormal_iff_hasNormalLayers n T L).mp h

end Truss.Transfer
