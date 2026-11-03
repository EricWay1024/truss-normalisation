/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.NoAut
import Truss.Transfer.Normalisation.LabBordism
import Mathlib.Order.Hom.Set

/-!
# Automorphism-freeness is stable under the labelled-truss construction

Chapter 2's `prop:noaut-iteration`, for the formal model `LabOneTruss C` of `C`-labelled open
1-trusses (`B(C)` at `n = 1`).

The proof follows the source.  An automorphism `R : X ⟶ X` in `B(C)` has an invertible
underlying bordism; its singular function (`singHom`) is then an order automorphism of the
finite linear order `Fin k` of singular indices, hence the identity, so by the
classification `openBordEquiv` the bordism is the identity bordism.  The *diagonal* labels,
i.e. the cross labels `R.cross (x ≤ x)` at the related pairs `(x, x)`, are automorphisms in
`C` (their inverses are the diagonal labels of the inverse), hence identities.  Right
naturality of cross labels then fixes every remaining cross label, and `LabBord.ext_cross`
concludes.

## Main results

* `Geometry.Bord1.eq_idBord_of_comp` — an invertible open 1-truss bordism `T ⇸ T` is the
  identity bordism.
* `noAut_labOneTruss` — `NoAut C → NoAut (LabOneTruss C)` (the inductive step).
* `iterLab`, `noAut_iterLab` — the iterates `B^r(C)` and the proposition for every `r`.
-/

universe v

namespace Truss.Transfer

open CategoryTheory Geometry Geometry.OneTruss

namespace Geometry.Bord1

variable {T : OpenTruss}

/-- **An invertible bordism is the identity.**  If `R ∘ Q` and `Q ∘ R` are both the identity
bordism of an open 1-truss `T`, then `R` is the identity bordism: its singular function is an
order automorphism of `Fin T.numSing`, hence the identity. -/
theorem eq_idBord_of_comp (R Q : Bord1 T.toOneTruss T.toOneTruss)
    (hRQ : compBord R Q = idBord T.toOneTruss) (hQR : compBord Q R = idBord T.toOneTruss) :
    R = idBord T.toOneTruss := by
  have h₁ : (singHom Q).comp (singHom R) = OrderHom.id := by
    rw [← singHom_compBord, hRQ, singHom_idBord]
  have h₂ : (singHom R).comp (singHom Q) = OrderHom.id := by
    rw [← singHom_compBord, hQR, singHom_idBord]
  let e : Fin T.numSing ≃o Fin T.numSing := OrderIso.ofHomInv (singHom R) (singHom Q) h₂ h₁
  have he : e = OrderIso.refl _ := Subsingleton.elim _ _
  have hf : singHom R = OrderHom.id := by
    refine OrderHom.ext _ _ (funext fun i => ?_)
    change e i = i
    rw [he]
    rfl
  rw [← induceOpen_singHom R, hf, induceOpen_id]

end Geometry.Bord1

/-- **Source: `prop:noaut-iteration` (Chapter 2), inductive step.**  If `C` is
automorphism-free, so is the category `B(C) = LabOneTruss C` of `C`-labelled open
1-trusses. -/
theorem noAut_labOneTruss {C : Type v} [Category.{v} C] (hC : NoAut C) :
    NoAut (LabOneTruss C) := by
  intro X R hR
  set Q : X ⟶ X := inv R with hQdef
  have hRQ : R ≫ Q = 𝟙 X := IsIso.hom_inv_id R
  have hQR : Q ≫ R = 𝟙 X := IsIso.inv_hom_id R
  -- the underlying bordism is the identity
  have hb : R.bord = idBord X.truss.toOneTruss :=
    Bord1.eq_idBord_of_comp R.bord Q.bord (by rw [← LabBord.comp_bord, hRQ]; rfl)
      (by rw [← LabBord.comp_bord, hQR]; rfl)
  have hQb : Q.bord = idBord X.truss.toOneTruss :=
    Bord1.eq_idBord_of_comp Q.bord R.bord (by rw [← LabBord.comp_bord, hQR]; rfl)
      (by rw [← LabBord.comp_bord, hRQ]; rfl)
  -- the diagonal labels are identities
  have hdiag : ∀ (x : X.truss.toOneTruss.El) (h : R.bord.rel x x), R.cross h = 𝟙 _ := by
    intro x h
    have hq : Q.bord.rel x x := by rw [hQb]; exact le_refl x
    have hid : ∀ (h' : (𝟙 X : LabBord X X).bord.rel x x),
        (𝟙 X : LabBord X X).cross h' = 𝟙 _ := by
      intro h'
      rw [LabBord.id_cross]
      exact X.label.map_id x
    have e₁ : R.cross h ≫ Q.cross hq = 𝟙 _ := by
      have := LabBord.cross_congr hRQ (show (R ≫ Q : X ⟶ X).bord.rel x x from ⟨x, h, hq⟩)
        (show (𝟙 X : LabBord X X).bord.rel x x from le_refl x)
      rw [LabBord.comp_cross, LabBord.crossComp_eq R Q _ h hq, hid] at this
      exact this
    have e₂ : Q.cross hq ≫ R.cross h = 𝟙 _ := by
      have := LabBord.cross_congr hQR (show (Q ≫ R : X ⟶ X).bord.rel x x from ⟨x, hq, h⟩)
        (show (𝟙 X : LabBord X X).bord.rel x x from le_refl x)
      rw [LabBord.comp_cross, LabBord.crossComp_eq Q R _ hq h, hid] at this
      exact this
    exact hC _ _ ⟨⟨Q.cross hq, e₁, e₂⟩⟩
  refine LabBord.ext_cross (hb.trans rfl) ?_
  intro x y h h'
  have hxx : R.bord.rel x x := by rw [hb]; exact le_refl x
  have hxy : x ≤ y := by rw [hb] at h; exact h
  rw [LabBord.id_cross, ← R.cross_right hxx hxy, hdiag x hxx, Category.id_comp]

/-- **The iterates `B^r(C)`.**  `B^0(C) = C` and `B^{r+1}(C) = B(B^r(C))`, bundled as a type
with a category structure. -/
noncomputable def iterLab (C : Type v) [Category.{v} C] : ℕ → Σ D : Type v, Category.{v} D
  | 0 => ⟨C, inferInstance⟩
  | r + 1 =>
    letI := (iterLab C r).2
    ⟨LabOneTruss (iterLab C r).1, inferInstance⟩

/-- **Source: `prop:noaut-iteration` (Chapter 2).**  If `C` is automorphism-free, then so is
every iterate `B^r(C)`. -/
theorem noAut_iterLab {C : Type v} [Category.{v} C] (hC : NoAut C) :
    ∀ r : ℕ, @NoAut (iterLab C r).1 (iterLab C r).2
  | 0 => hC
  | r + 1 => by
    letI := (iterLab C r).2
    exact noAut_labOneTruss (noAut_iterLab hC r)

end Truss.Transfer
