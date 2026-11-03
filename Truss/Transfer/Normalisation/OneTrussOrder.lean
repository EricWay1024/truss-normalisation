/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.OneTrussNorm
import Truss.Transfer.Normalisation.OutgoingOrder

/-!
# The order isomorphism for labelled outgoing one-truss coarsenings

`OpenTruss.labelledRetOrderIso` is the literal order isomorphism of
`prop:draft-labelled-outcoarse-1-truss-poset-iso`. Its source consists of actual
`LabOutCoarse` objects, ordered by existence of a labelled mediating coarsening.
Its target consists of retained subsets containing every non-trivially labelled singular.
The target label in the inverse is the unique descent along the retained-set quotient.
-/

universe u₂ v₂
namespace Truss.Transfer
open CategoryTheory TrussLike

namespace OpenTruss
variable {C : Type u₂} [Category.{v₂} C]

/-- The retained sets containing every non-trivially labelled singular element. -/
def LabelledRetainedSet (A : LabObj 1 OpenTruss C) :=
  {U : Finset (Fin A.obj.numSing) // NonTriv A.obj A.label ⊆ U}

instance (A : LabObj 1 OpenTruss C) : PartialOrder (LabelledRetainedSet A) :=
  inferInstanceAs (PartialOrder {U : Finset (Fin A.obj.numSing) // NonTriv A.obj A.label ⊆ U})

/-- Outgoing labelled one-truss coarsenings with the factorisation order. -/
def LabOutCoarsePoset (A : LabObj 1 OpenTruss C) := LabOutCoarse A
namespace LabOutCoarsePoset
/-- The underlying outgoing labelled coarsening. -/
def out {A : LabObj 1 OpenTruss C} (r : LabOutCoarsePoset A) : LabOutCoarse A := r

instance (A : LabObj 1 OpenTruss C) : PartialOrder (LabOutCoarsePoset A) where
  le r q := Nonempty (r.out ⟶ q.out)
  le_refl r := ⟨𝟙 r.out⟩
  le_trans _ _ _ := fun ⟨h⟩ ⟨k⟩ => ⟨h ≫ k⟩
  le_antisymm r q hrq hqr := by
    apply LabOutCoarse.forgetObj_injective
    apply outCoarse_ext
    have hrq := (LabOutCoarse.nonempty_hom_iff r.out q.out).mp hrq
    have hqr := (LabOutCoarse.nonempty_hom_iff q.out r.out).mp hqr
    exact Finset.Subset.antisymm
      ((exists_mediator_iff_ret_subset rfl q.out.isCoarsening r.out.isCoarsening).mp hqr)
      ((exists_mediator_iff_ret_subset rfl r.out.isCoarsening q.out.isCoarsening).mp hrq)
/-- The labelled factorisation order is existence of a labelled mediator. -/
theorem le_iff {A : LabObj 1 OpenTruss C} (r q : LabOutCoarsePoset A) :
    r ≤ q ↔ Nonempty (r.out ⟶ q.out) := Iff.rfl

end LabOutCoarsePoset

/-- `prop:draft-labelled-outcoarse-1-truss-poset-iso`: the retained-set classification
restricts to the outgoing coarsenings preserving the full label functor. -/
noncomputable def labelledRetOrderIso (A : LabObj 1 OpenTruss C) :
    LabOutCoarsePoset A ≃o (LabelledRetainedSet A)ᵒᵈ where
  toFun r := OrderDual.toDual
    ⟨retOf rfl r.out.map.1, nonTriv_subset_ret_of_hom r.out.map r.out.isCoarsening⟩
  invFun U := by
    let q := qU A.obj (OrderDual.ofDual U).val
    have hq := qU_isCoarsening A.obj rfl (OrderDual.ofDual U).val
    have hL : DescendsAlong q A.label :=
      (descendsAlong_iff_nonTriv_subset q hq A.label).mpr
        (by simpa only [q, ret_qU] using (OrderDual.ofDual U).property)
    exact ⟨⟨_, descendedLabel hq hL⟩, ⟨q, (descendedLabel_spec hq hL).symm⟩, hq⟩
  left_inv r := by
    apply LabOutCoarse.forgetObj_injective
    apply outCoarse_ext
    change retOf rfl (qU A.obj (retOf rfl r.out.map.1)) = retOf rfl r.out.map.1
    exact ret_qU _ _ _
  right_inv U := by
    apply Subtype.ext
    change retOf rfl (qU A.obj (OrderDual.ofDual U).val) = (OrderDual.ofDual U).val
    exact ret_qU _ _ _
  map_rel_iff' := by
    intro r q
    change (retOf rfl q.out.map.1 ⊆ retOf rfl r.out.map.1) ↔ Nonempty (r.out ⟶ q.out)
    rw [LabOutCoarse.nonempty_hom_iff,
      exists_mediator_iff_ret_subset rfl r.out.isCoarsening q.out.isCoarsening]

/-- The labelled isomorphism is the restriction of the unlabelled classification. -/
theorem labelledRetOrderIso_forget (A : LabObj 1 OpenTruss C)
    (r : LabOutCoarsePoset A) :
    (OrderDual.ofDual (labelledRetOrderIso A r)).val =
      OrderDual.ofDual (retOrderIso A.obj (OutCoarsePoset.of r.out.forgetObj)) := rfl

end OpenTruss
end Truss.Transfer
