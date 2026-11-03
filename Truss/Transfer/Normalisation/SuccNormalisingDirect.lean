/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.SuccAssembly

/-!
# The superseded direct proof of `thm:draft-successor-normalising` (historical)

**Status: OBSOLETE PROOF ROUTE, kept as a record (2026-09-26).**  This module preserves,
under `_direct` names, the proof of the successor decomposition of normalising coarsenings
that the draft chapter printed *before* the reflection-based rewrite frozen at notes commit
`451d8ef`.  The public theorem `succ_isNormalising_iff` is now proved in
`SuccNormalising.lean` by the two-step reflection argument
([the reflection plan](../../../plan/ReflectionNormalisationVerification.md)
row `R6`), and **nothing in the reflection chain imports this file**; the audit
`Truss/Transfer/Audit/Reflection.lean` checks that.  The statements proved here are true
and axiom-clean; only their role as *the* proof of the chapter's theorem is retired.

The direct route normalised the top of an arbitrary competitor, pulled the normalisation
back along the open base map, and compared the two normalisations of the source by strict
uniqueness (`OpenBundle.normalising_target_eq`) to build the lower competitor by hand.
-/

universe u v w u₂ v₂

namespace Truss.Transfer

open CategoryTheory TrussLike

section Succ

variable {P : FPoset.{u}} {m : ℕ} {C : Type v} [Category.{v} C]

/-! ### The forward direction, upper component -/

/-- **`thm:draft-successor-normalising`, forward direction, upper component.**  Normalise the
final bundle over `T_m` with `B10`; comparing `Q` with `(id, c₀)`, which is a coarsening by
`N02 (3) → (1)`, exhibits `c` as `c₀` followed by a further coarsening, hence normalising. -/
theorem isNormalising_topLab_direct {T S : Tower P (m + 1)}
    {L : (towerTot P (m + 1) T).carrier ⥤ C} {M : (towerTot P (m + 1) S).carrier ⥤ C}
    (Q : (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨S, M⟩) (hQ : IsNormalising Q) :
    IsNormalising (topLab Q) := by
  obtain ⟨D₀, c₀, hc₀⟩ : ∃ (D₀ : LabObj 1 (OpenBundle (towerTot P m T.lower).carrier) C)
      (c₀ : (⟨T.top, L⟩ : LabObj 1 (OpenBundle (towerTot P m T.lower).carrier) C) ⟶ D₀),
      IsNormalising c₀ := ⟨_, _, OpenBundle.bundleNormaliseMap_isNormalising' T.top L⟩
  obtain ⟨A₀, L₀⟩ := D₀
  have hobj0 : (⟨OpenBundle.reindex (𝟙 T.lower : T.lower ⟶ T.lower).totHom A₀,
        OpenBundle.pullbackLabel (𝟙 T.lower : T.lower ⟶ T.lower).totHom A₀ L₀⟩ :
        LabObj 1 (OpenBundle (towerTot P m T.lower).carrier) C) = ⟨A₀, L₀⟩ := by
    rw [show (𝟙 T.lower : T.lower ⟶ T.lower).totHom = OrderHom.id from TowerMap.totHom_id _]
    rfl
  set c₀' := c₀ ≫ eqToHom hobj0.symm with hc₀'
  set R₀ := assemble (L := L) (𝟙 T.lower) c₀' with hR₀def
  have hR₀ : IsCoarsening R₀.1 :=
    isCoarsening_of_parts R₀.1 (IsCoarsening.id _) (hc₀.1.comp (isCoarsening_labEqToHom _))
  obtain ⟨e, he, hfact⟩ := hQ.exists_mediator R₀ hR₀
  rw [hfact, topLab_comp]
  exact (hc₀.comp_isCoarsening (isCoarsening_labEqToHom _)).comp_isCoarsening
    (isCoarsening_labReindex _ (isCoarsening_topMap he))

/-! ### The forward direction, lower component -/

/-- **`thm:draft-successor-normalising`, forward direction, lower component.**  A competing
labelled lower coarsening `J` is turned into a competing labelled coarsening of towers by
**totalising** its target label and appending the resulting 1-truss bundle; the label
equation of `J` identifies the pullback of that bundle with `f^*(S_(m+1),M)` — this is
`totalise_comp`, the strict-representative equation, and it holds by `rfl`.  Terminality of
`Q` then supplies the mediator; `C05` fullness makes it labelled and `C04` epi makes it
unique. -/
theorem isNormalising_lowLab_direct {T S : Tower P (m + 1)}
    {L : (towerTot P (m + 1) T).carrier ⥤ C} {M : (towerTot P (m + 1) S).carrier ⥤ C}
    (Q : (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨S, M⟩) (hQ : IsNormalising Q) :
    IsNormalising (lowLab Q) := by
  refine ⟨isCoarsening_lower hQ.1, ?_⟩
  rintro ⟨V, H⟩ J hJ
  have hobj : (⟨OpenBundle.reindex Q.1.base S.top,
        OpenBundle.pullbackLabel Q.1.base S.top M⟩ :
        LabObj 1 (OpenBundle (towerTot P m T.lower).carrier) C)
      = ⟨OpenBundle.reindex (J.1 : T.lower ⟶ V).totHom (totaliseBundle H),
         OpenBundle.pullbackLabel (J.1 : T.lower ⟶ V).totHom (totaliseBundle H)
           (totaliseLabel H)⟩ := by
    have hJ2 := congrArg labTotalise J.2
    rwa [labTotalise_comp_classify] at hJ2
  set a := topLab Q ≫ eqToHom hobj with ha
  set R := assemble (L := L) (N := totaliseLabel H) J.1 a with hR
  have hRc : IsCoarsening R.1 :=
    isCoarsening_of_parts R.1 hJ ((isCoarsening_topMap hQ.1).comp (isCoarsening_labEqToHom _))
  obtain ⟨k, hk, hfact⟩ := hQ.exists_mediator R hRc
  have hlow : Q.1.lower = J.1 ≫ k.1.lower :=
    congrArg (fun z : (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨S, M⟩ =>
      z.1.lower) hfact
  have hHG : posetFunctor (totMap k.1.lower) ⋙ (OpenBundle.classify S.top M :
      (towerTot P m S.lower).carrier ⥤ LabOneTruss C) = H :=
    descendedLabel_comp hJ hlow J.2.symm (lowLab Q).2.symm
  refine ⟨⟨k.1.lower, hHG.symm⟩, ⟨isCoarsening_lower hk, Subtype.ext hlow⟩, fun w hw => ?_⟩
  exact IsNormalising.mediator_unique hJ (hw.2.symm.trans (Subtype.ext hlow))

/-! ### The reverse direction -/

/-- **`thm:draft-successor-normalising`, reverse direction.**  Given an arbitrary competing
labelled coarsening `R = (J, a) : (T,L) → (U,N)`, normalise `R`'s final bundle over `U_m` by
`B10`, getting `d`.  By `N02` the base map `j` of `R` is a poset coarsening, hence **open**,
so `B11` makes `j^*d` normalising, and `C09` makes `a ≫ j^*d` normalising because `c`
normalises the source of `a`.  Strict uniqueness of normalisation
(`OpenBundle.normalising_target_eq`) then **equates** the two normalisations of `(T_(m+1),L)`,
which is what turns `J` into a labelled lower competitor with source label `G ∘ f`; lower
terminality supplies `V` with `F = V ∘ J`, `totalise_comp` identifies the normalised final
bundle with `v^*(S_(m+1),M)`, and `(V,d)` is the mediator, unique because `R` is epi. -/
theorem isNormalising_of_parts_direct {T S : Tower P (m + 1)}
    {L : (towerTot P (m + 1) T).carrier ⥤ C} {M : (towerTot P (m + 1) S).carrier ⥤ C}
    (Q : (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨S, M⟩)
    (hc : IsNormalising (topLab Q)) (hF : IsNormalising (lowLab Q)) : IsNormalising Q := by
  refine ⟨isCoarsening_of_parts Q.1 hF.1 hc.1, ?_⟩
  rintro ⟨U, N⟩ R hR
  have hRlow : IsCoarsening (K := Tower P m) R.1.lower := isCoarsening_lower hR
  have hRtop : IsCoarsening (K := OpenBundle (towerTot P m T.lower).carrier) R.1.topMap :=
    isCoarsening_topMap hR
  have hopen : IsOpenPosetMap R.1.base := by
    rw [← TowerMap.base_eq R.1]; exact hRlow.tot.isOpen
  obtain ⟨D₁, d, hd⟩ : ∃ (D₁ : LabObj 1 (OpenBundle (towerTot P m U.lower).carrier) C)
      (d : (⟨U.top, N⟩ : LabObj 1 (OpenBundle (towerTot P m U.lower).carrier) C) ⟶ D₁),
      IsNormalising d := ⟨_, _, OpenBundle.bundleNormaliseMap_isNormalising' U.top N⟩
  obtain ⟨A₁, N₁⟩ := D₁
  have hdj : IsNormalising (OpenBundle.labReindex R.1.base d) :=
    OpenBundle.isNormalising_reindex' R.1.base hopen d hd
  have hadj : IsNormalising (topLab R ≫ OpenBundle.labReindex R.1.base d) :=
    (normalising_precomp hRtop hdj.1 ⟨_, _, hc⟩).2 hdj
  obtain ⟨eo, heo⟩ := OpenBundle.normalising_target_eq hc hadj
  have hcls : posetFunctor Q.1.base ⋙ (OpenBundle.classify S.top M :
        (towerTot P m S.lower).carrier ⥤ LabOneTruss C)
      = posetFunctor R.1.base ⋙ (OpenBundle.classify A₁ N₁ :
        (towerTot P m U.lower).carrier ⥤ LabOneTruss C) := by
    have hz := congrArg (fun z : LabObj 1 (OpenBundle (towerTot P m T.lower).carrier) C =>
      OpenBundle.classify z.obj z.label) eo
    simpa only [classify_reindex] using hz
  set J' : (⟨T.lower, posetFunctor Q.1.base ⋙ OpenBundle.classify S.top M⟩ :
      LabObj m (Tower P m) (LabOneTruss C)) ⟶ ⟨U.lower, OpenBundle.classify A₁ N₁⟩ :=
    ⟨R.1.lower, hcls.trans (by rw [← TowerMap.base_eq R.1])⟩ with hJ'
  obtain ⟨w, hw, hwfac⟩ := hF.exists_mediator J' hRlow
  have hA₁ : (⟨A₁, N₁⟩ : LabObj 1 (OpenBundle (towerTot P m U.lower).carrier) C)
      = ⟨OpenBundle.reindex (w.1 : U.lower ⟶ S.lower).totHom S.top,
         OpenBundle.pullbackLabel (w.1 : U.lower ⟶ S.lower).totHom S.top M⟩ := by
    have hh := congrArg labTotalise w.2
    rwa [labTotalise_classify, labTotalise_comp_classify] at hh
  set med := assemble (L := N) w.1 (d ≫ eqToHom hA₁) with hmed
  have hmedc : IsCoarsening med.1 :=
    isCoarsening_of_parts med.1 hw (hd.1.comp (isCoarsening_labEqToHom _))
  have hlowfac : Q.1.lower = R.1.lower ≫ w.1 := congrArg (fun z => z.1) hwfac
  have hbase : Q.1.base = (R.1 ≫ med.1).base := by
    have h2 : (Q.1.lower).totHom = ((R.1.lower).comp w.1).totHom :=
      congrArg TowerMap.totHom hlowfac
    rw [TowerMap.totHom_comp, TowerMap.base_eq Q.1, TowerMap.base_eq R.1] at h2
    exact h2
  have hQfac : Q = R ≫ med := by
    refine Subtype.ext (TowerMap.ext_succ Q.1 (R.1 ≫ med.1) hbase ?_)
    have h1 := congrArg Subtype.val heo
    simp only [LabObj.comp_coe, topLab_coe, OpenBundle.labReindex_coe] at h1
    have h3 : TowerMap.topMap (R.1 ≫ med.1)
        = R.1.topMap ≫ (show OpenBundle.reindex R.1.base U.top ⟶
            OpenBundle.reindex R.1.base
              (OpenBundle.reindex (w.1 : U.lower ⟶ S.lower).totHom S.top) from
            BundleMap.reindex R.1.base ((d ≫ eqToHom hA₁).1)) := rfl
    rw [h3, LabObj.comp_coe, BundleMap.reindex_comp', ← Category.assoc, ← h1, Category.assoc,
      LabObj.eqToHom_coe, LabObj.eqToHom_coe, BundleMap.reindex_eqToHom, eqToHom_trans]
  exact ⟨med, ⟨hmedc, hQfac⟩, fun k hk => IsNormalising.mediator_unique hR
    (hk.2.symm.trans hQfac)⟩

/-! ### `thm:draft-successor-normalising` -/

/-- **`thm:draft-successor-normalising` (§5.5).**  Let
`Q = (F, c) : (T, L) → (S, M)` be a labelled morphism of levelwise-open `(m+1)`-truss
bundles over `P`, with `f := Tot(F)` its lower total map, and let
`G := χ_(S_(m+1),M) : S_m → B(C)` be the classifying functor of the final labelled bundle
of `(S, M)`.  Then `Q` is normalising if and only if both

1. `c : (T_(m+1), L) → f^*(S_(m+1), M)` is normalising over `T_m`, and
2. `F : (T_(≤m), G ∘ f) → (S_(≤m), G)` is normalising over `P`.

The lower tower is labelled in `B(C)`, not in `C`; that is what `G` is for. -/
theorem succ_isNormalising_iff_direct {T S : Tower P (m + 1)}
    {L : (towerTot P (m + 1) T).carrier ⥤ C} {M : (towerTot P (m + 1) S).carrier ⥤ C}
    (Q : (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨S, M⟩) :
    IsNormalising Q ↔ IsNormalising (topLab Q) ∧ IsNormalising (lowLab Q) :=
  ⟨fun hQ => ⟨isNormalising_topLab_direct Q hQ, isNormalising_lowLab_direct Q hQ⟩,
    fun h => isNormalising_of_parts_direct Q h.1 h.2⟩


end Succ

end Truss.Transfer
