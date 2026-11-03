/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.NoAutIteration
import Truss.Transfer.Normalisation.Terminality
import Truss.Transfer.Normalisation.TowerBlocks

/-!
# Iterated classifiers and explicit transport of label categories

`towerClassify` classifies a labelled tower by repeatedly classifying its final bundle.
Its target is the literal bundled category `iterLab C n`. The equality `iterLab_add`
identifies iterating `j` times after `r` iterations with iterating `j + r` times.
`categoryTransport` makes the resulting change of label category explicit, including
the category structure, and preserves normality. `towerClassify_blocks` proves that
classification commutes with splitting a tower into consecutive blocks.
-/

universe u v w z

namespace Truss.Transfer

open CategoryTheory

/-- The bundled category obtained by applying the labelled 1-truss construction once. -/
noncomputable def labCategory (D : Σ C : Type v, Category.{v} C) :
    Σ C : Type v, Category.{v} C :=
  letI := D.2
  ⟨LabOneTruss D.1, inferInstance⟩

/-- Transport between equal bundled categories, including their category structures. -/
def categoryTransport {A B : Σ C : Type v, Category.{v} C} (h : A = B) :
    @Functor A.1 A.2 B.1 B.2 := by
  cases h
  letI := A.2
  exact 𝟭 A.1

/-- Transport along reflexivity is the identity functor. -/
@[simp] theorem categoryTransport_refl (A : Σ C : Type v, Category.{v} C) :
    categoryTransport (rfl : A = A) = @Functor.id A.1 A.2 := rfl

/-- Successive transports compose to transport along the composite equality. -/
theorem categoryTransport_trans {A B D : Σ C : Type v, Category.{v} C}
    (h : A = B) (h' : B = D) :
    @Functor.comp A.1 A.2 B.1 B.2 D.1 D.2
      (categoryTransport h) (categoryTransport h') = categoryTransport (h.trans h') := by
  cases h
  cases h'
  rfl

/-- Transport followed by the reverse transport is the identity. -/
@[simp] theorem categoryTransport_symm_comp {A B : Σ C : Type v, Category.{v} C}
    (h : A = B) :
    @Functor.comp A.1 A.2 B.1 B.2 A.1 A.2
      (categoryTransport h) (categoryTransport h.symm) = @Functor.id A.1 A.2 := by
  cases h
  rfl

/-- Changing labels along an equality of bundled categories preserves and reflects normality. -/
theorem isNormal_categoryTransport_iff {n : ℕ} {K : Type u} [Category.{w} K]
    [TrussLike.{u, w, z} n K] {A B : Σ C : Type v, Category.{v} C} (h : A = B)
    (X : K) (L : @Functor (TrussLike.Tot X) inferInstance A.1 A.2) :
    @IsNormal n K inferInstance inferInstance B.1 B.2
      (@LabObj.mk n K inferInstance inferInstance B.1 B.2 X
        (@Functor.comp _ inferInstance A.1 A.2 B.1 B.2 L (categoryTransport h))) ↔
      @IsNormal n K inferInstance inferInstance A.1 A.2
        (@LabObj.mk n K inferInstance inferInstance A.1 A.2 X L) := by
  cases h
  letI := A.2
  simp only [categoryTransport_refl, Functor.comp_id]

/-- The successor equation for the bundled iterate. -/
theorem iterLab_succ (C : Type v) [Category.{v} C] (r : ℕ) :
    iterLab C (r + 1) = labCategory (iterLab C r) := rfl

/-- Iterating `j` times after `r` iterations gives the bundled category `B^(j+r)(C)`. -/
theorem iterLab_add (C : Type v) [Category.{v} C] (r : ℕ) :
    ∀ j : ℕ, @iterLab (iterLab C r).1 (iterLab C r).2 j = iterLab C (j + r)
  | 0 => by
      rw [Nat.zero_add]
      rfl
  | j + 1 => by
      rw [Nat.succ_add]
      exact congrArg labCategory (iterLab_add C r j)

/-- Moving the initial labelled-truss construction across the iteration counter. -/
theorem iterLab_shift (C : Type v) [Category.{v} C] (n : ℕ) :
    iterLab (LabOneTruss C) n = iterLab C (n + 1) := iterLab_add C 1 n

/-- The classifier of a labelled tower, with its target the literal category `B^n(C)`. -/
noncomputable def towerClassify {P : FPoset.{u}} :
    ∀ {n : ℕ} {C : Type v} [Category.{v} C] (T : Tower P n),
      ((towerTot P n T).carrier ⥤ C) →
        @Functor P.carrier inferInstance (iterLab C n).1 (iterLab C n).2
  | 0, _, _, _, L => L
  | n + 1, C, _, T, L =>
      @Functor.comp P.carrier inferInstance
        (iterLab (LabOneTruss C) n).1 (iterLab (LabOneTruss C) n).2
        (iterLab C (n + 1)).1 (iterLab C (n + 1)).2
        (towerClassify T.lower (OpenBundle.classify T.top L))
        (categoryTransport (iterLab_shift C n))

/-- The classifier of a height-zero tower is its label functor. -/
@[simp] theorem towerClassify_zero {P : FPoset.{u}} {C : Type v} [Category.{v} C]
    (T : Tower P 0) (L : (towerTot P 0 T).carrier ⥤ C) : towerClassify T L = L := rfl

/-- Classifying a successor tower first classifies its final bundle, then its lower tower. -/
theorem towerClassify_succ {P : FPoset.{u}} {n : ℕ} {C : Type v} [Category.{v} C]
    (T : Tower P (n + 1)) (L : (towerTot P (n + 1) T).carrier ⥤ C) :
    towerClassify T L =
      @Functor.comp P.carrier inferInstance
        (iterLab (LabOneTruss C) n).1 (iterLab (LabOneTruss C) n).2
        (iterLab C (n + 1)).1 (iterLab C (n + 1)).2
        (towerClassify T.lower (OpenBundle.classify T.top L))
        (categoryTransport (iterLab_shift C n)) := rfl

/-- One-step classification commutes with transport of the label category. -/
theorem OpenBundle.classify_categoryTransport {P : Type u} [PartialOrder P]
    {A B : Σ C : Type v, Category.{v} C} (h : A = B) (T : OpenBundle P)
    (L : @Functor T.Tot inferInstance A.1 A.2) :
    @OpenBundle.classify P inferInstance B.1 B.2 T
      (@Functor.comp _ inferInstance A.1 A.2 B.1 B.2 L (categoryTransport h)) =
      @Functor.comp _ inferInstance (labCategory A).1 (labCategory A).2
        (labCategory B).1 (labCategory B).2
        (@OpenBundle.classify P inferInstance A.1 A.2 T L)
        (categoryTransport (congrArg labCategory h)) := by
  cases h
  letI := A.2
  simp only [categoryTransport_refl, Functor.comp_id]

/-- Iterated classification commutes with transport of the original label category. -/
theorem towerClassify_categoryTransport {P : FPoset.{u}} {n : ℕ}
    {A B : Σ C : Type v, Category.{v} C} (h : A = B) (T : Tower P n)
    (L : @Functor (towerTot P n T).carrier inferInstance A.1 A.2) :
    @towerClassify P n B.1 B.2 T
      (@Functor.comp _ inferInstance A.1 A.2 B.1 B.2 L (categoryTransport h)) =
      @Functor.comp _ inferInstance (@iterLab A.1 A.2 n).1 (@iterLab A.1 A.2 n).2
        (@iterLab B.1 B.2 n).1 (@iterLab B.1 B.2 n).2
        (@towerClassify P n A.1 A.2 T L)
        (categoryTransport (congrArg (fun D => @iterLab D.1 D.2 n) h)) := by
  cases h
  letI := A.2
  simp only [categoryTransport_refl, Functor.comp_id]

/-- One-step classification commutes with equality transport of the finite base poset. -/
private theorem classify_baseTransport {P Q : FPoset.{u}} (h : P = Q)
    (T : OpenBundle P.carrier) {C : Type v} [Category.{v} C] (L : T.Tot ⥤ C) :
    OpenBundle.classify (FPoset.transportBundle h T)
      (FPoset.pullLabel (FPoset.transportBundle_tot h T) L) =
        FPoset.pullLabel h.symm (OpenBundle.classify T L) := by
  cases h
  simp only [FPoset.transportBundle, FPoset.pullLabel_refl]

/-- Classifying the upper block and then the lower block agrees with classifying the whole
tower. The final functor explicitly identifies `B^k(B^j(C))` with `B^(k+j)(C)`. -/
theorem towerClassify_blocks {P : FPoset.{u}} (k : ℕ) :
    ∀ (j : ℕ) {C : Type v} [Category.{v} C] (T : Tower P (k + j))
      (L : (towerTot P (k + j) T).carrier ⥤ C),
      letI := (iterLab C j).2
      letI := (@iterLab (iterLab C j).1 (iterLab C j).2 k).2
      letI := (iterLab C (k + j)).2
      towerClassify T L =
        towerClassify (Tower.prefix k j T)
          (towerClassify (Tower.suffix k j T) (Tower.suffixLabel k j T L)) ⋙
          categoryTransport (iterLab_add C j k)
  | 0, C, _, T, L => by
      rfl
  | j + 1, C, _, T, L => by
      let A := iterLab (LabOneTruss C) j
      let B := iterLab C (j + 1)
      letI := A.2
      letI := B.2
      letI := (@iterLab A.1 A.2 k).2
      letI := (@iterLab B.1 B.2 k).2
      letI := (iterLab (LabOneTruss C) (k + j)).2
      letI := (iterLab C (k + (j + 1))).2
      letI := (iterLab C ((k + j) + 1)).2
      have htop :
          OpenBundle.classify (Tower.suffix k (j + 1) T).top
            (Tower.suffixLabel k (j + 1) T L) =
          Tower.suffixLabel k j T.lower (OpenBundle.classify T.top L) :=
        classify_baseTransport (Tower.suffix_tot k j T.lower).symm T.top L
      have ih := towerClassify_blocks k j T.lower (OpenBundle.classify T.top L)
      have htransport := towerClassify_categoryTransport (iterLab_shift C j)
        (Tower.prefix k j T.lower)
        (towerClassify (Tower.suffix k j T.lower)
          (Tower.suffixLabel k j T.lower (OpenBundle.classify T.top L)))
      rw [towerClassify_succ, ih]
      simp only [Tower.prefix_succ, towerClassify_succ, Tower.suffix_succ_lower, htop]
      rw [htransport]
      change _ ⋙ ((categoryTransport (iterLab_add (LabOneTruss C) j k)) ⋙
          categoryTransport (iterLab_shift C (k + j))) =
        _ ⋙ ((categoryTransport
            (congrArg (fun D => @iterLab D.1 D.2 k) (iterLab_shift C j))) ⋙
          categoryTransport (iterLab_add C (j + 1) k))
      rw [categoryTransport_trans, categoryTransport_trans]

end Truss.Transfer
