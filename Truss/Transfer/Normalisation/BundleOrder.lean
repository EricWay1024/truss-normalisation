/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.BundleRetract
import Truss.Transfer.Normalisation.OutgoingOrder

/-!
# Outgoing bundle coarsenings as the opposite poset of stable retained families

`OpenBundle.retOrderIso` assembles the quotient/retained-family inverse equations and the
mediator criterion into `prop:draft-outcoarse-1-bundle-poset-iso`, as an actual `≃o`.
`OpenBundle.labelledRetOrderIso` restricts this to stable families containing the
non-trivially labelled family (`prop:draft-labelled-outcoarse-1-bundle-poset-iso`).

Both outgoing posets have actual outgoing coarsenings as their elements, ordered by
existence of mediating coarsenings. Antisymmetry uses the proved equality of a coarsening
with the quotient at its retained family; thinness alone would not suffice.
-/

universe u v w
namespace Truss.Transfer
open CategoryTheory TrussLike
namespace OpenBundle
variable {B : Type u} [PartialOrder B] [Finite B]

/-- Forward-stable singular families, ordered by fibrewise inclusion. -/
def StableRetainedFamily (A : OpenBundle B) :=
  {U : ∀ b : B, Finset (Fin (A.fib b).numSing) // A.IsForwardStableFam U}

instance (A : OpenBundle B) : PartialOrder (StableRetainedFamily A) :=
  inferInstanceAs (PartialOrder {U : ∀ b : B, Finset (Fin (A.fib b).numSing) //
    A.IsForwardStableFam U})

/-- An outgoing coarsening is determined by its retained family. -/
theorem outCoarse_ext {A : OpenBundle B} {r s : OutCoarse A}
    (h : retFinset r.map = retFinset s.map) : r = s := by
  obtain ⟨Y, r, hr⟩ := r
  obtain ⟨Z, s, hs⟩ := s
  dsimp at h
  have e : Y = Z := by
    rw [← quotient_retFinset_eq hr, ← quotient_retFinset_eq hs]
    simp only [h]
  subst e
  have he : r = s := by
    refine BundleMap.ext fun b x => OpenTruss.el_eq_of_idx_eq _ ?_
    rw [coarsening_fib_idx hr, coarsening_fib_idx hs, h]
  subst he
  rfl

omit [Finite B] in
/-- Retained-family inclusion agrees in its finite-set and set presentations. -/
theorem retFinset_le_iff {A Y Z : OpenBundle B} (r : A ⟶ Y) (q : A ⟶ Z) :
    retFinset q ≤ retFinset r ↔ retFam q ≤ retFam r := by
  constructor <;> intro h b i hi
  · apply (show i ∈ (↑(retFinset r b) : Set _) ↔ i ∈ retFam r b by
      rw [coe_retFinset]).mp
    exact h b ((show i ∈ (↑(retFinset q b) : Set _) ↔ i ∈ retFam q b by
      rw [coe_retFinset]).mpr hi)
  · apply (show i ∈ (↑(retFinset r b) : Set _) ↔ i ∈ retFam r b by
      rw [coe_retFinset]).mpr
    exact h b ((show i ∈ (↑(retFinset q b) : Set _) ↔ i ∈ retFam q b by
      rw [coe_retFinset]).mp hi)

/-- Outgoing bundle coarsenings, ordered by existence of a mediating coarsening. -/
def OutCoarsePoset (A : OpenBundle B) := OutCoarse A
namespace OutCoarsePoset
/-- The outgoing coarsening underlying an element of the factorisation poset. -/
def out {A : OpenBundle B} (r : OutCoarsePoset A) : OutCoarse A := r
/-- Regard an outgoing coarsening as an element of the factorisation poset. -/
def of {A : OpenBundle B} (r : OutCoarse A) : OutCoarsePoset A := r

instance (A : OpenBundle B) : PartialOrder (OutCoarsePoset A) where
  le r q := ∃ h : r.out.tgt ⟶ q.out.tgt, IsCoarsening h ∧ q.out.map = r.out.map ≫ h
  le_refl _ := ⟨𝟙 _, IsCoarsening.id _, by simp⟩
  le_trans _ _ _ := by
    rintro ⟨h, hh, he⟩ ⟨h', hh', he'⟩
    exact ⟨h ≫ h', hh.comp hh', by rw [he', he, Category.assoc]⟩
  le_antisymm r q hrq hqr := by
    apply outCoarse_ext
    exact le_antisymm
      ((retFinset_le_iff q.out.map r.out.map).mpr
        ((exists_mediator_iff_retFam_le' q.out.isCoarsening r.out.isCoarsening).mp hqr))
      ((retFinset_le_iff r.out.map q.out.map).mpr
        ((exists_mediator_iff_retFam_le' r.out.isCoarsening q.out.isCoarsening).mp hrq))

/-- The order is precisely existence of a mediator. -/
theorem le_iff {A : OpenBundle B} (r q : OutCoarsePoset A) :
    r ≤ q ↔ ∃ h : r.out.tgt ⟶ q.out.tgt, IsCoarsening h ∧ q.out.map = r.out.map ≫ h :=
  Iff.rfl
end OutCoarsePoset

/-- `prop:draft-outcoarse-1-bundle-poset-iso`: retained families classify outgoing
coarsenings, reversing the factorisation order. -/
noncomputable def retOrderIso (A : OpenBundle B) :
    OutCoarsePoset A ≃o (StableRetainedFamily A)ᵒᵈ where
  toFun r := OrderDual.toDual ⟨retFinset r.out.map, retFinset_isForwardStableFam r.out.map⟩
  invFun U := OutCoarsePoset.of
    ⟨A.quotient (OrderDual.ofDual U).val (OrderDual.ofDual U).property,
      A.quotientMap (OrderDual.ofDual U).val (OrderDual.ofDual U).property,
      isCoarsening_quotientMap (fibrewiseThm B) _ _ _⟩
  left_inv r := outCoarse_ext (retFinset_quotientMap _ _ _)
  right_inv U := Subtype.ext (retFinset_quotientMap _ _ _)
  map_rel_iff' := by
    intro r q
    change retFinset q.out.map ≤ retFinset r.out.map ↔ r ≤ q
    rw [retFinset_le_iff, OutCoarsePoset.le_iff,
      exists_mediator_iff_retFam_le' r.out.isCoarsening q.out.isCoarsening]

/-- The forward map of the classification takes exactly the retained family. -/
@[simp] theorem retOrderIso_apply (A : OpenBundle B) (r : OutCoarsePoset A) :
    (OrderDual.ofDual (retOrderIso A r)).val = retFinset r.out.map := rfl

/-- The inverse classification is the canonical retained-family quotient map. -/
@[simp] theorem retOrderIso_symm_map (A : OpenBundle B) (U : (StableRetainedFamily A)ᵒᵈ) :
    ((retOrderIso A).symm U).out.map =
      A.quotientMap (OrderDual.ofDual U).val (OrderDual.ofDual U).property := rfl

end OpenBundle

namespace OpenBundle
variable {B : Type u} [PartialOrder B] [Finite B]
variable {C : Type v} [Category.{w} C]

/-- Stable retained families containing the non-trivially labelled family. -/
def LabelledRetainedFamily (A : LabObj 1 (OpenBundle B) C) :=
  {U : StableRetainedFamily A.obj //
    A.obj.nonTrivFam A.label ≤ fun b => (↑(U.val b) : Set (Fin (A.obj.fib b).numSing))}

instance (A : LabObj 1 (OpenBundle B) C) : PartialOrder (LabelledRetainedFamily A) :=
  inferInstanceAs (PartialOrder {U : StableRetainedFamily A.obj //
    A.obj.nonTrivFam A.label ≤ fun b => (↑(U.val b) : Set (Fin (A.obj.fib b).numSing))})

/-- Outgoing labelled bundle coarsenings with the factorisation order. -/
def LabOutCoarsePoset (A : LabObj 1 (OpenBundle B) C) := LabOutCoarse A
namespace LabOutCoarsePoset
/-- The underlying outgoing labelled coarsening. -/
def out {A : LabObj 1 (OpenBundle B) C} (r : LabOutCoarsePoset A) : LabOutCoarse A := r

instance (A : LabObj 1 (OpenBundle B) C) : PartialOrder (LabOutCoarsePoset A) where
  le r q := Nonempty (r.out ⟶ q.out)
  le_refl r := ⟨𝟙 r.out⟩
  le_trans _ _ _ := fun ⟨h⟩ ⟨k⟩ => ⟨h ≫ k⟩
  le_antisymm r q hrq hqr := by
    apply LabOutCoarse.forgetObj_injective
    apply outCoarse_ext
    have hrq := (LabOutCoarse.nonempty_hom_iff r.out q.out).mp hrq
    have hqr := (LabOutCoarse.nonempty_hom_iff q.out r.out).mp hqr
    exact le_antisymm
      ((retFinset_le_iff q.out.map.1 r.out.map.1).mpr
        ((exists_mediator_iff_retFam_le' q.out.isCoarsening r.out.isCoarsening).mp hqr))
      ((retFinset_le_iff r.out.map.1 q.out.map.1).mpr
        ((exists_mediator_iff_retFam_le' r.out.isCoarsening q.out.isCoarsening).mp hrq))
/-- The labelled factorisation order is existence of a labelled mediator. -/
theorem le_iff {A : LabObj 1 (OpenBundle B) C} (r q : LabOutCoarsePoset A) :
    r ≤ q ↔ Nonempty (r.out ⟶ q.out) := Iff.rfl

end LabOutCoarsePoset

/-- The retained family of a labelled coarsening contains all non-trivial labels. -/
theorem nonTrivFam_le_retFinset {A : LabObj 1 (OpenBundle B) C} (r : LabOutCoarse A) :
    A.obj.nonTrivFam A.label ≤ fun b => (↑(retFinset r.map.1 b) : Set _) := by
  have hL : DescendsAlong r.map.1 A.label :=
    (descendsAlong_iff r.isCoarsening A.label).mpr ⟨r.tgt.label, r.map.2.symm⟩
  simpa only [coe_retFinset] using
    (descendsAlong_iff_nonTrivFam_le r.map.1 r.isCoarsening A.label).mp hL

/-- `prop:draft-labelled-outcoarse-1-bundle-poset-iso`: the retained-family order
isomorphism restricts to coarsenings preserving the full category-valued labelling. -/
noncomputable def labelledRetOrderIso (A : LabObj 1 (OpenBundle B) C) :
    LabOutCoarsePoset A ≃o (LabelledRetainedFamily A)ᵒᵈ where
  toFun r := OrderDual.toDual
    ⟨⟨retFinset r.out.map.1, retFinset_isForwardStableFam r.out.map.1⟩,
      nonTrivFam_le_retFinset r.out⟩
  invFun U := by
    let V := (OrderDual.ofDual U).val
    let q := A.obj.quotientMap V.val V.property
    have hq := isCoarsening_quotientMap (fibrewiseThm B) A.obj V.val V.property
    have hL : DescendsAlong q A.label :=
      (descendsAlong_iff_nonTrivFam_le q hq A.label).mpr (by
        have he : retFam q = fun b => (↑(V.val b) : Set _) := by
          funext b
          rw [← coe_retFinset, retFinset_quotientMap]
        rw [he]
        exact (OrderDual.ofDual U).property)
    exact ⟨⟨_, descendedLabel hq hL⟩, ⟨q, (descendedLabel_spec hq hL).symm⟩, hq⟩
  left_inv r := by
    apply LabOutCoarse.forgetObj_injective
    apply outCoarse_ext
    change retFinset (A.obj.quotientMap _ _) = retFinset r.out.map.1
    exact retFinset_quotientMap _ _ _
  right_inv U := by
    apply Subtype.ext
    apply Subtype.ext
    change retFinset (A.obj.quotientMap _ _) = (OrderDual.ofDual U).val.val
    exact retFinset_quotientMap _ _ _
  map_rel_iff' := by
    intro r q
    change (retFinset q.out.map.1 ≤ retFinset r.out.map.1) ↔ Nonempty (r.out ⟶ q.out)
    rw [retFinset_le_iff, LabOutCoarse.nonempty_hom_iff,
      exists_mediator_iff_retFam_le' r.out.isCoarsening q.out.isCoarsening]

/-- The labelled isomorphism is the restriction of the unlabelled classification. -/
theorem labelledRetOrderIso_forget (A : LabObj 1 (OpenBundle B) C)
    (r : LabOutCoarsePoset A) :
    (OrderDual.ofDual (labelledRetOrderIso A r)).val =
      OrderDual.ofDual (retOrderIso A.obj (OutCoarsePoset.of r.out.forgetObj)) := rfl

end OpenBundle
end Truss.Transfer
