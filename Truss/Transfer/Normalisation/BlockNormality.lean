/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.TowerBlocks
import Truss.Transfer.Normalisation.IteratedClassifier
import Truss.Transfer.Normalisation.RecursiveNorm

/-!
# Normality of arbitrary consecutive tower blocks

`isNormal_iff_blocks` splits normality across any cut of a labelled tower. Its upper block
is a genuine tower over the total poset of the lower block, and the lower label is the
iterated classifier of that upper block. `normality_of_tower_layers` applies this twice to
obtain the arbitrary middle and lower blocks of `cor:draft-layer-normality`, including
zero-height blocks. The equality between the nested iterated label category and the
single iterate is transported explicitly.
-/

universe u v

namespace Truss.Transfer

open CategoryTheory

namespace FPoset

/-- Classifying a bundle commutes with transport between equal finite base posets. -/
theorem transportBundle_classify {P Q : FPoset.{u}} (h : P = Q)
    (A : OpenBundle P.carrier) {C : Type v} [Category.{v} C]
    (L : A.Tot ⥤ C) :
    OpenBundle.classify (transportBundle h A) (pullLabel (transportBundle_tot h A) L) =
      pullLabel h.symm (OpenBundle.classify A L) := by
  cases h
  simp only [transportBundle, pullLabel_refl]

/-- Normality of a labelled one-bundle is preserved by transport of its base poset. -/
theorem transportBundle_isNormal_iff {P Q : FPoset.{u}} (h : P = Q)
    (A : OpenBundle P.carrier) {C : Type v} [Category.{v} C]
    (L : A.Tot ⥤ C) :
    IsNormal (⟨transportBundle h A, pullLabel (transportBundle_tot h A) L⟩ :
      LabObj 1 (OpenBundle Q.carrier) C) ↔
    IsNormal (⟨A, L⟩ : LabObj 1 (OpenBundle P.carrier) C) := by
  cases h
  simp only [transportBundle, pullLabel_refl]

end FPoset

namespace Tower

/-- The successor classifier of a suffix is the original successor classifier pulled
back along the identification of the lower total posets. -/
theorem suffix_classify {P : FPoset.{u}} (k j : ℕ) (T : Tower P (k + (j + 1)))
    {C : Type v} [Category.{v} C] (L : (towerTot P (k + (j + 1)) T).carrier ⥤ C) :
    OpenBundle.classify (suffix k (j + 1) T).top (suffixLabel k (j + 1) T L) =
      suffixLabel k j T.lower (OpenBundle.classify T.top L) := by
  exact FPoset.transportBundle_classify (suffix_tot k j T.lower).symm T.top L

/-- The top one-bundle of a suffix has the normality of the original top one-bundle. -/
theorem suffix_top_isNormal_iff {P : FPoset.{u}} (k j : ℕ)
    (T : Tower P (k + (j + 1))) {C : Type v} [Category.{v} C]
    (L : (towerTot P (k + (j + 1)) T).carrier ⥤ C) :
    IsNormal (⟨(suffix k (j + 1) T).top, suffixLabel k (j + 1) T L⟩ :
      LabObj 1
        (OpenBundle (towerTot (towerTot P k (Tower.prefix k (j + 1) T)) j
          (suffix k (j + 1) T).lower).carrier) C) ↔
    IsNormal (⟨T.top, L⟩ :
      LabObj 1 (OpenBundle (towerTot P (k + j) T.lower).carrier) C) := by
  exact FPoset.transportBundle_isNormal_iff (suffix_tot k j T.lower).symm T.top L

end Tower

/-- Normality splits across any cut: both the upper block with the original labels and
its classified lower prefix are normal. Conversely, these two conditions imply normality. -/
theorem isNormal_iff_blocks {P : FPoset.{u}} (k : ℕ) :
    ∀ (j : ℕ) {C : Type v} [Category.{v} C] (T : Tower P (k + j))
      (L : (towerTot P (k + j) T).carrier ⥤ C),
      letI := (iterLab C j).2
      IsNormal (⟨T, L⟩ : LabObj (k + j) (Tower P (k + j)) C) ↔
        IsNormal (⟨Tower.suffix k j T, Tower.suffixLabel k j T L⟩ :
          LabObj j (Tower (towerTot P k (Tower.prefix k j T)) j) C) ∧
        IsNormal (⟨Tower.prefix k j T,
          towerClassify (Tower.suffix k j T) (Tower.suffixLabel k j T L)⟩ :
          LabObj k (Tower P k) (iterLab C j).1)
  | 0, C, _, T, L => by
      change IsNormal (⟨T, L⟩ : LabObj k (Tower P k) C) ↔ _
      simp only [Tower.prefix_zero, towerClassify_zero, Tower.suffixLabel,
        FPoset.pullLabel_refl]
      exact ⟨fun h => ⟨isNormal_zero _ _, h⟩, fun h => h.2⟩
  | j + 1, C, _, T, L => by
      letI := (iterLab C (j + 1)).2
      letI := (iterLab (LabOneTruss C) j).2
      have ih := isNormal_iff_blocks k j T.lower (OpenBundle.classify T.top L)
      have hs := succ_isNormal_iff (Tower.suffix k (j + 1) T)
        (Tower.suffixLabel k (j + 1) T L)
      have hclass := Tower.suffix_classify k j T L
      rw [hclass] at hs
      have ht := Tower.suffix_top_isNormal_iff k j T L
      have hc := isNormal_categoryTransport_iff (iterLab_shift C j)
        (Tower.prefix k j T.lower)
        (towerClassify (Tower.suffix k j T.lower)
          (Tower.suffixLabel k j T.lower (OpenBundle.classify T.top L)))
      constructor
      · intro h
        obtain ⟨hl, ht'⟩ := (succ_isNormal_iff T L).mp h
        obtain ⟨hu, hp⟩ := ih.mp hl
        constructor
        · apply hs.mpr
          constructor
          · simpa only [Tower.suffix_succ_lower] using hu
          · exact ht.mpr ht'
        · have hp' := hc.mpr hp
          rw [towerClassify_succ, hclass]
          simpa only [Tower.suffix_succ_lower, Tower.prefix_succ] using hp'
      · rintro ⟨hu, hp⟩
        obtain ⟨hl, ht'⟩ := hs.mp hu
        apply (succ_isNormal_iff T L).mpr
        constructor
        · apply ih.mpr
          constructor
          · simpa only [Tower.suffix_succ_lower] using hl
          · apply hc.mp
            rw [towerClassify_succ, hclass] at hp
            simpa only [Tower.suffix_succ_lower, Tower.prefix_succ] using hp
        · exact ht.mp ht'

namespace Tower

/-- Reindexing a tower's height and its label preserves and reflects normality. -/
theorem castHeight_isNormal_iff {P : FPoset.{u}} {a b : ℕ} (h : a = b)
    (T : Tower P a) {C : Type v} [Category.{v} C]
    (L : (towerTot P a T).carrier ⥤ C) :
    IsNormal (⟨castHeight h T, castHeightLabel h T L⟩ : LabObj b (Tower P b) C) ↔
      IsNormal (⟨T, L⟩ : LabObj a (Tower P a) C) := by
  cases h
  simp only [castHeight, castHeightLabel, FPoset.pullLabel_refl]

end Tower

/-- The height decomposition used to select the middle `j` layers after the lower `k`. -/
theorem tower_layers_height_eq {n j k : ℕ} (hjk : j + k ≤ n) :
    n = (k + j) + (n - j - k) := by omega

/-- The middle classifier's nested label category is the literal category `B^(n-k)(C)`.
The equality includes the category structure, so its transport is an explicit functor. -/
theorem tower_layers_iterLab_eq (C : Type v) [Category.{v} C] (n j k : ℕ)
    (hjk : j + k ≤ n) :
    @iterLab (iterLab C (n - j - k)).1 (iterLab C (n - j - k)).2 j =
      iterLab C (n - k) := by
  rw [iterLab_add]
  congr 1
  omega

/-- **`cor:draft-layer-normality`.** A normal labelled `n`-tower has a normal middle
`j`-tower, labelled by the classifier of the upper `r = n-j-k` layers, and a normal lower
`k`-tower labelled by the classifier of that middle tower. The lower label is transported
explicitly to the literal iterated category `B^(n-k)(C)`. All zero-height cases are included. -/
theorem normality_of_tower_layers {P : FPoset.{u}} {n : ℕ} {C : Type v}
    [Category.{v} C] (T : Tower P n) (L : (towerTot P n T).carrier ⥤ C)
    (j k : ℕ) (hjk : j + k ≤ n)
    (hN : IsNormal (⟨T, L⟩ : LabObj n (Tower P n) C)) :
    let r := n - j - k
    let hheight := tower_layers_height_eq hjk
    let T' := Tower.castHeight hheight T
    let L' := Tower.castHeightLabel hheight T L
    let S := Tower.prefix (k + j) r T'
    letI := (iterLab C r).2
    let U := towerClassify (Tower.suffix (k + j) r T')
      (Tower.suffixLabel (k + j) r T' L')
    let T_low := Tower.prefix k j S
    let M := Tower.suffix k j S
    let U_M := Tower.suffixLabel k j S U
    letI := (@iterLab (iterLab C r).1 (iterLab C r).2 j).2
    letI := (iterLab C (n - k)).2
    let V := (towerClassify M U_M).comp
      (categoryTransport (tower_layers_iterLab_eq C n j k hjk))
    IsNormal (⟨M, U_M⟩ : LabObj j (Tower (towerTot P k T_low) j) (iterLab C r).1) ∧
      IsNormal (⟨T_low, V⟩ : LabObj k (Tower P k) (iterLab C (n - k)).1) := by
  let r := n - j - k
  let hheight := tower_layers_height_eq hjk
  let T' := Tower.castHeight hheight T
  let L' := Tower.castHeightLabel hheight T L
  let S := Tower.prefix (k + j) r T'
  letI := (iterLab C r).2
  let U := towerClassify (Tower.suffix (k + j) r T')
    (Tower.suffixLabel (k + j) r T' L')
  have hT' : IsNormal (⟨T', L'⟩ : LabObj ((k + j) + r) (Tower P ((k + j) + r)) C) :=
    (Tower.castHeight_isNormal_iff hheight T L).mpr hN
  have hS : IsNormal (⟨S, U⟩ : LabObj (k + j) (Tower P (k + j)) (iterLab C r).1) :=
    ((isNormal_iff_blocks (k + j) r T' L').mp hT').2
  have hM := (isNormal_iff_blocks k j S U).mp hS
  exact ⟨hM.1, (isNormal_categoryTransport_iff (tower_layers_iterLab_eq C n j k hjk)
    (Tower.prefix k j S) (towerClassify (Tower.suffix k j S)
      (Tower.suffixLabel k j S U))).mpr hM.2⟩

end Truss.Transfer
