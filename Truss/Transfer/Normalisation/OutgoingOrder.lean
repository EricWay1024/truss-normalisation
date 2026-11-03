/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.Context

/-!
# Forgetting labels of outgoing coarsenings

The target label of an outgoing coarsening is unique by descent. Thus forgetting it is
injective on objects. The full-subcategory result identifies existence of labelled
mediators with existence of structural mediators. These facts let the retained-set and
retained-family order isomorphisms restrict to the labelled outgoing posets.
-/

universe u v w u₂ v₂
namespace Truss.Transfer
open CategoryTheory TrussLike

namespace LabOutCoarse
variable {n : ℕ} {K : Type u} [Category.{v} K] [TrussLike.{u, v, w} n K]
variable {C : Type u₂} [Category.{v₂} C] {A : LabObj n K C}

/-- Forget the uniquely descended target label of an outgoing labelled coarsening. -/
def forgetObj (r : LabOutCoarse A) : OutCoarse A.obj :=
  ⟨r.tgt.obj, r.map.1, r.isCoarsening⟩

/-- Descent uniqueness makes the forgetful map on outgoing coarsenings injective. -/
theorem forgetObj_injective : Function.Injective (forgetObj (A := A)) := by
  rintro ⟨⟨Y, M⟩, ⟨r, hrL⟩, hr⟩ ⟨⟨Z, N⟩, ⟨s, hsL⟩, hs⟩ h
  have e : Y = Z := congrArg OutCoarse.tgt h
  subst Z
  have e : r = s := by cases h; rfl
  subst s
  have e : M = N := descendedLabel_unique hr hrL.symm hsL.symm
  subst N
  rfl

/-- A structural mediator between labelled outgoing coarsenings has a unique label. -/
theorem nonempty_hom_iff (r q : LabOutCoarse A) :
    Nonempty (r ⟶ q) ↔
      ∃ h : r.tgt.obj ⟶ q.tgt.obj, IsCoarsening h ∧ q.map.1 = r.map.1 ≫ h := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.1.1, h.2.1, congrArg Subtype.val h.2.2⟩
  · rintro ⟨h, hh, he⟩
    obtain ⟨H, _⟩ := full r q h hh he
    exact ⟨H⟩

end LabOutCoarse

end Truss.Transfer
