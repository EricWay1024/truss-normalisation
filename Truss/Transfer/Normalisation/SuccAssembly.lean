/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.Section55
import Truss.Transfer.Normalisation.LabBordism
import Truss.Transfer.Normalisation.BundleRetract

/-!
# Successor assembly: the substrate of §5.5's normalisation arguments

This module collects the elementary, proof-route-independent substrate that both the
reflection-based proof of `thm:draft-successor-normalising` and the recursive construction
consume.  It was factored out of the former `SuccNormalising.lean` (2026-09-26,
[the reflection plan](../../../plan/ReflectionNormalisationVerification.md)
row `R0`) so that the new proof does not import the superseded direct proof.  Nothing here
mentions normalisation of *towers*; the only normalisation facts are about labelled
1-truss bundles.

## Main definitions

* `topLab` — the upper component `c : (T_(m+1), L) → f^*(S_(m+1), M)` of a labelled tower
  morphism, with the label equation read off from the tower morphism's own.
* `lowLab` — the lower component `F : (T_(≤m), G ∘ f) → (S_(≤m), G)`, labelled in
  `B(C) = LabOneTruss C`.
* `assemble` — the converse: a lower tower map together with a compatible labelled map of
  final bundles is a labelled map of `(m+1)`-towers (`def:bundle-over-structural-tower`,
  `prop:structural-successor-equivalence`).
* `labTotalise` — the totalisation `π` of `thm:classification`, packaged as a labelled
  1-truss bundle.

## Main results

* `OpenBundle.normalising_target_eq` — **strict uniqueness of normalisation** for labelled
  1-truss bundles: two normalising coarsenings out of one labelled bundle have *equal*
  targets, and agree after the canonical identification.  This is the retraction half of
  `prop:draft-labelled-outcoarse-1-bundle-poset-iso` (via `BundleRetract.lean`), not a
  consequence of thinness.
* `classify_reindex`, `labTotalise_comp_classify`, `labTotalise_comp` — the strict
  representative equations (`lem:recognising-reindexed-labelled-bundles` in the chosen
  representatives).
* `isCoarsening_bundleReindex`, `isCoarsening_labReindex` — reindexing preserves bundle
  coarsenings.
* `TowerMap.ext_succ` — extensionality for maps of `(m+1)`-towers.
* `isCoarsening_lower`, `isCoarsening_topMap`, `isCoarsening_of_parts` —
  `thm:draft-successor-coarsening`, `(1) ↔ (3)`, in split form.
-/

universe u v w u₂ v₂

namespace Truss.Transfer

open CategoryTheory TrussLike

/-! ### Strict uniqueness of normalisation for labelled 1-truss bundles -/

namespace OpenBundle

variable {B : Type u} [PartialOrder B] [Finite B]

omit [Finite B] in
/-- Quotients at **equal** forward-stable families are equal, compatibly with the quotient
maps.  The forward-stability witnesses are propositions, so they need no transport. -/
theorem quotient_transport {A : OpenBundle B} {U U' : ∀ b : B, Finset (Fin (A.fib b).numSing)}
    (hU : A.IsForwardStableFam U) (hU' : A.IsForwardStableFam U') (h : U = U')
    {A' : OpenBundle B} (e : A.quotient U' hU' = A') :
    ∃ e' : A.quotient U hU = A',
      A.quotientMap U hU ≫ eqToHom e' = A.quotientMap U' hU' ≫ eqToHom e := by
  subst h; exact ⟨e, rfl⟩

/-- **Bundle coarsenings with the same retained family have the same target.**  This is the
retraction half of `prop:draft-outcoarse-1-bundle-poset-iso`: both are the quotient map at
that family, so the target is *equal*, not merely isomorphic. -/
theorem eq_of_retFinset_eq {A A' A'' : OpenBundle B} {r : A ⟶ A'} {r' : A ⟶ A''}
    (hr : IsCoarsening r) (hr' : IsCoarsening r') (h : retFinset r = retFinset r') :
    ∃ e : A' = A'', r ≫ eqToHom e = r' := by
  obtain ⟨e', he'⟩ := quotient_transport (retFinset_isForwardStableFam r)
    (retFinset_isForwardStableFam r') h (quotient_retFinset_eq hr')
  refine ⟨(quotient_retFinset_eq hr).symm.trans e', ?_⟩
  calc r ≫ eqToHom ((quotient_retFinset_eq hr).symm.trans e')
      = (A.quotientMap (retFinset r) (retFinset_isForwardStableFam r)
            ≫ eqToHom (quotient_retFinset_eq hr))
          ≫ eqToHom ((quotient_retFinset_eq hr).symm.trans e') := by
        rw [quotientMap_retFinset_eq hr]
    _ = A.quotientMap (retFinset r) (retFinset_isForwardStableFam r) ≫ eqToHom e' := by
        rw [Category.assoc, eqToHom_trans]
    _ = r' := by rw [he', quotientMap_retFinset_eq hr']

variable {C : Type v} [Category.{w} C]

/-- **Strict uniqueness of normalisation for labelled 1-truss bundles.**  Two normalising
coarsenings out of one labelled fibrewise-open 1-truss bundle have **equal** targets, and
agree after the canonical identification.  This is what makes the chapter's "uniqueness of
normalisation" an equality rather than an isomorphism; it rests on skeletality of
`OpenTruss` through `BundleRetract.lean`. -/
theorem normalising_target_eq {A : OpenBundle B} {L : A.Tot ⥤ C}
    {D D' : LabObj 1 (OpenBundle B) C} {q : (⟨A, L⟩ : LabObj 1 (OpenBundle B) C) ⟶ D}
    {q' : (⟨A, L⟩ : LabObj 1 (OpenBundle B) C) ⟶ D'}
    (hq : IsNormalising q) (hq' : IsNormalising q') : ∃ e : D = D', q ≫ eqToHom e = q' := by
  have hret : retFam q.1 = retFam q'.1 :=
    ((isNormalising_iff_retFam_eq_closure' q hq.1).1 hq).trans
      ((isNormalising_iff_retFam_eq_closure' q' hq'.1).1 hq').symm
  have hfin : retFinset q.1 = retFinset q'.1 := by
    funext b
    exact Finset.coe_injective (by rw [coe_retFinset, coe_retFinset, hret])
  obtain ⟨Ad, Ld⟩ := D
  obtain ⟨Ad', Ld'⟩ := D'
  obtain ⟨eo, heo⟩ : ∃ e : Ad = Ad', q.1 ≫ eqToHom e = q'.1 :=
    eq_of_retFinset_eq hq.1 hq'.1 hfin
  subst eo
  have hq1 : q.1 = q'.1 := by simpa using heo
  have hlab : Ld = Ld' := by
    refine descendedLabel_unique hq.1 (M := Ld) (M' := Ld') q.2.symm ?_
    rw [hq1]; exact q'.2.symm
  subst hlab
  exact ⟨rfl, by simpa using Subtype.ext hq1⟩

end OpenBundle

/-! ### Totalisation as a labelled object -/

section Totalise

variable {W W' : Type u} [PartialOrder W] [PartialOrder W'] [Finite W] [Finite W']
variable {C : Type v} [Category.{v} C]

/-- The totalisation of a `B(C)`-valued functor, packaged as a labelled 1-truss bundle. -/
noncomputable def labTotalise (F : W ⥤ LabOneTruss C) : LabObj 1 (OpenBundle W) C :=
  ⟨totaliseBundle F, totaliseLabel F⟩

/-- Totalising a classification returns the labelled bundle one started from. -/
theorem labTotalise_classify (A : OpenBundle W) (N : A.Tot ⥤ C) :
    labTotalise (OpenBundle.classify A N) = ⟨A, N⟩ := by
  rw [labTotalise, totaliseLabel_classify]
  rfl

omit [Finite W] in
/-- Totalising a **reindexed** classification returns the reindexed labelled bundle, on the
nose.  This is `totalise_comp`, the strict-representative equation, in labelled form. -/
theorem labTotalise_comp_classify (f : W' →o W) (A : OpenBundle W) (N : A.Tot ⥤ C) :
    labTotalise (posetFunctor f ⋙ OpenBundle.classify A N)
      = ⟨OpenBundle.reindex f A, OpenBundle.pullbackLabel f A N⟩ := by
  rw [labTotalise, totaliseLabel_comp, totaliseLabel_classify]
  rfl

omit [Finite W] in
/-- Classification commutes with reindexing. -/
theorem classify_reindex (f : W' →o W) (A : OpenBundle W) (N : A.Tot ⥤ C) :
    OpenBundle.classify (OpenBundle.reindex f A) (OpenBundle.pullbackLabel f A N)
      = posetFunctor f ⋙ OpenBundle.classify A N := by
  have h2 : OpenBundle.classify (labTotalise (posetFunctor f ⋙ OpenBundle.classify A N)).obj
      (labTotalise (posetFunctor f ⋙ OpenBundle.classify A N)).label
        = posetFunctor f ⋙ OpenBundle.classify A N :=
    classify_totalise _
  rw [labTotalise_comp_classify] at h2
  exact h2

end Totalise

/-! ### Reindexing preserves bundle coarsenings -/

section Reindex

variable {B B' : Type u} [PartialOrder B] [PartialOrder B'] [Finite B] [Finite B']
variable {C : Type v} [Category.{v} C]

/-- Reindexing a bundle coarsening along **any** base map gives a coarsening: it is
fibrewise the very same coarsening. -/
theorem isCoarsening_bundleReindex (f : B' →o B) {A A' : OpenBundle B} {q : A ⟶ A'}
    (hq : IsCoarsening q) :
    IsCoarsening (show OpenBundle.reindex f A ⟶ OpenBundle.reindex f A' from
      BundleMap.reindex f q) :=
  fibrewiseThm B' _ fun p => OpenBundle.isCoarsening_fibHom hq (f p)

omit [Finite B] [Finite B'] in
/-- Reindexing of bundle maps preserves composition. -/
theorem BundleMap.reindex_comp' (f : B' →o B) {A A' A'' : OpenBundle B} (a : A ⟶ A')
    (b : A' ⟶ A'') :
    (show OpenBundle.reindex f A ⟶ OpenBundle.reindex f A'' from
        BundleMap.reindex f (a ≫ b))
      = (show OpenBundle.reindex f A ⟶ OpenBundle.reindex f A' from BundleMap.reindex f a)
        ≫ (show OpenBundle.reindex f A' ⟶ OpenBundle.reindex f A'' from
            BundleMap.reindex f b) := rfl

omit [Finite B] [Finite B'] in
/-- Reindexing of bundle maps preserves the canonical comparison of equal bundles. -/
theorem BundleMap.reindex_eqToHom (f : B' →o B) {A A' : OpenBundle B} (h : A = A') :
    (show OpenBundle.reindex f A ⟶ OpenBundle.reindex f A' from
        BundleMap.reindex f (eqToHom h))
      = eqToHom (congrArg (OpenBundle.reindex f) h) := by subst h; rfl

/-- The labelled form of `isCoarsening_bundleReindex`. -/
theorem isCoarsening_labReindex (f : B' →o B) {A A' : OpenBundle B} {L : A.Tot ⥤ C}
    {M : A'.Tot ⥤ C} {q : (⟨A, L⟩ : LabObj 1 (OpenBundle B) C) ⟶ ⟨A', M⟩}
    (hq : IsCoarsening q.1) : IsCoarsening (OpenBundle.labReindex f q).1 :=
  isCoarsening_bundleReindex f hq

end Reindex

/-! ### The successor decomposition of a labelled tower morphism -/

section Succ

variable {P : FPoset.{u}} {m : ℕ} {C : Type v} [Category.{v} C]

/-- **The upper component `c : (T_(m+1),L) → f^*(S_(m+1),M)`.**  The label equation of the
tower morphism *is* the label equation of its top bundle map against the pulled-back label. -/
def topLab {T S : Tower P (m + 1)} {L : (towerTot P (m + 1) T).carrier ⥤ C}
    {M : (towerTot P (m + 1) S).carrier ⥤ C}
    (Q : (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨S, M⟩) :
    (⟨T.top, L⟩ : LabObj 1 (OpenBundle (towerTot P m T.lower).carrier) C) ⟶
      ⟨OpenBundle.reindex Q.1.base S.top, OpenBundle.pullbackLabel Q.1.base S.top M⟩ :=
  ⟨Q.1.topMap, Q.2⟩

@[simp] theorem topLab_coe {T S : Tower P (m + 1)}
    {L : (towerTot P (m + 1) T).carrier ⥤ C} {M : (towerTot P (m + 1) S).carrier ⥤ C}
    (Q : (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨S, M⟩) :
    (topLab Q).1 = Q.1.topMap := rfl

/-- **The lower component `F : (T_(≤m), G∘f) → (S_(≤m), G)`.**  The lower tower is labelled
in `B(C)`, by the classifying functor `G` of the final labelled bundle of `(S,M)`. -/
noncomputable def lowLab {T S : Tower P (m + 1)} {L : (towerTot P (m + 1) T).carrier ⥤ C}
    {M : (towerTot P (m + 1) S).carrier ⥤ C}
    (Q : (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨S, M⟩) :
    (⟨T.lower, posetFunctor Q.1.base ⋙ OpenBundle.classify S.top M⟩ :
        LabObj m (Tower P m) (LabOneTruss C)) ⟶
      ⟨S.lower, OpenBundle.classify S.top M⟩ :=
  ⟨Q.1.lower, by rw [← TowerMap.base_eq Q.1]⟩

@[simp] theorem lowLab_coe {T S : Tower P (m + 1)}
    {L : (towerTot P (m + 1) T).carrier ⥤ C} {M : (towerTot P (m + 1) S).carrier ⥤ C}
    (Q : (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨S, M⟩) :
    (lowLab Q).1 = Q.1.lower := rfl

/-- The upper component of a composite is the composite of the upper components, the second
one reindexed along the first base map. -/
theorem topLab_comp {T S U : Tower P (m + 1)} {L : (towerTot P (m + 1) T).carrier ⥤ C}
    {M : (towerTot P (m + 1) S).carrier ⥤ C} {N : (towerTot P (m + 1) U).carrier ⥤ C}
    (q : (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨S, M⟩)
    (r : (⟨S, M⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨U, N⟩) :
    topLab (q ≫ r) = topLab q ≫ OpenBundle.labReindex q.1.base (topLab r) := rfl

/-- **Assembly**: a lower tower map together with a compatible labelled map of final bundles
is a labelled map of `(m+1)`-towers.  This is `prop:structural-successor-equivalence` in
labelled form. -/
def assemble {T : Tower P (m + 1)} {L : (towerTot P (m + 1) T).carrier ⥤ C} {V : Tower P m}
    {A : OpenBundle (towerTot P m V).carrier} {N : A.Tot ⥤ C} (J : T.lower ⟶ V)
    (a : (⟨T.top, L⟩ : LabObj 1 (OpenBundle (towerTot P m T.lower).carrier) C) ⟶
          ⟨OpenBundle.reindex J.totHom A, OpenBundle.pullbackLabel J.totHom A N⟩) :
    (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨V.succ A, N⟩ :=
  ⟨TowerMap.succ J a.1, a.2⟩

@[simp] theorem assemble_lower {T : Tower P (m + 1)}
    {L : (towerTot P (m + 1) T).carrier ⥤ C} {V : Tower P m}
    {A : OpenBundle (towerTot P m V).carrier} {N : A.Tot ⥤ C} (J : T.lower ⟶ V)
    (a : (⟨T.top, L⟩ : LabObj 1 (OpenBundle (towerTot P m T.lower).carrier) C) ⟶
          ⟨OpenBundle.reindex J.totHom A, OpenBundle.pullbackLabel J.totHom A N⟩) :
    (assemble (L := L) (N := N) J a).1.lower = J := rfl

@[simp] theorem assemble_topMap {T : Tower P (m + 1)}
    {L : (towerTot P (m + 1) T).carrier ⥤ C} {V : Tower P m}
    {A : OpenBundle (towerTot P m V).carrier} {N : A.Tot ⥤ C} (J : T.lower ⟶ V)
    (a : (⟨T.top, L⟩ : LabObj 1 (OpenBundle (towerTot P m T.lower).carrier) C) ⟶
          ⟨OpenBundle.reindex J.totHom A, OpenBundle.pullbackLabel J.totHom A N⟩) :
    (assemble (L := L) (N := N) J a).1.topMap = a.1 := rfl

/-- **Extensionality for maps of `(m+1)`-towers**, in components: two maps with the same
lower total map, and with final bundle maps agreeing after the induced identification of the
reindexed target bundles, are equal. -/
theorem TowerMap.ext_succ_aux {T S : Tower P (m + 1)} (F G : TowerMap P m T.lower S.lower)
    (f g : (towerTot P m T.lower).carrier →o (towerTot P m S.lower).carrier)
    (hf : F.totHom = f) (hg : G.totHom = g)
    (c : BundleMap T.top (OpenBundle.reindex f S.top))
    (d : BundleMap T.top (OpenBundle.reindex g S.top)) (hb : f = g)
    (ht : (c ≫ eqToHom (congrArg (fun k => OpenBundle.reindex k S.top) hb) :
        T.top ⟶ OpenBundle.reindex g S.top) = d) :
    (⟨F, f, hf, c⟩ : TowerMap P (m + 1) T S) = ⟨G, g, hg, d⟩ := by
  subst hb
  have hFG : F = G := TowerMap.totHom_injective m (hf.trans hg.symm)
  subst hFG
  simp only [eqToHom_refl, Category.comp_id] at ht
  subst ht
  rfl

/-- **Extensionality for maps of `(m+1)`-towers.** -/
theorem TowerMap.ext_succ {T S : Tower P (m + 1)} (X Y : TowerMap P (m + 1) T S)
    (hb : X.base = Y.base)
    (ht : (X.topMap ≫ eqToHom (congrArg (fun k => OpenBundle.reindex k S.top) hb) :
        T.top ⟶ OpenBundle.reindex Y.base S.top) = Y.topMap) : X = Y :=
  TowerMap.ext_succ_aux X.lower Y.lower X.base Y.base (TowerMap.base_eq X) (TowerMap.base_eq Y)
    X.topMap Y.topMap hb ht

/-! ### Splitting and assembling coarsenings (row `N02`) -/

/-- `N02`, `(1) → (3)`, lower half. -/
theorem isCoarsening_lower {T S : Tower P (m + 1)} {Q : T ⟶ S} (hQ : IsCoarsening Q) :
    IsCoarsening (K := Tower P m) Q.lower :=
  (tfae_two_to_three' Q (tfae_one_to_two' Q hQ).1 (tfae_one_to_two' Q hQ).2).1

/-- `N02`, `(1) → (3)`, upper half. -/
theorem isCoarsening_topMap {T S : Tower P (m + 1)} {Q : T ⟶ S} (hQ : IsCoarsening Q) :
    IsCoarsening (K := OpenBundle (towerTot P m T.lower).carrier) Q.topMap :=
  (tfae_two_to_three' Q (tfae_one_to_two' Q hQ).1 (tfae_one_to_two' Q hQ).2).2

/-- `N02`, `(3) → (1)`. -/
theorem isCoarsening_of_parts {T S : Tower P (m + 1)} (Q : T ⟶ S)
    (hF : IsCoarsening (K := Tower P m) Q.lower)
    (hc : IsCoarsening (K := OpenBundle (towerTot P m T.lower).carrier) Q.topMap) :
    IsCoarsening Q := tfae_three_to_one' Q hF hc


/-- `topLab (𝟙 _) = 𝟙 _`. -/
theorem topLab_id (T : Tower P (m + 1)) (L : (towerTot P (m + 1) T).carrier ⥤ C) :
    topLab (𝟙 (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C))
      = 𝟙 (⟨T.top, L⟩ : LabObj 1 (OpenBundle (towerTot P m T.lower).carrier) C) := rfl

/-- `lowLab (𝟙 _) = 𝟙 _`. -/
theorem lowLab_id (T : Tower P (m + 1)) (L : (towerTot P (m + 1) T).carrier ⥤ C) :
    lowLab (𝟙 (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C))
      = 𝟙 (⟨T.lower, OpenBundle.classify T.top L⟩ :
            LabObj m (Tower P m) (LabOneTruss C)) := rfl


end Succ

/-! ### Totalisation of an arbitrary reindexed functor -/

section Totalise

variable {W W' : Type u} [PartialOrder W] [PartialOrder W'] [Finite W] [Finite W']
variable {C : Type v} [Category.{v} C]

omit [Finite W] in
/-- `labTotalise (F ∘ f) = f^* labTotalise F`, on the nose. -/
theorem labTotalise_comp (f : W' →o W) (F : W ⥤ LabOneTruss C) :
    labTotalise (posetFunctor f ⋙ F)
      = ⟨OpenBundle.reindex f (totaliseBundle F),
         OpenBundle.pullbackLabel f (totaliseBundle F) (totaliseLabel F)⟩ := rfl

omit [Finite W] in
/-- `classify_totalise` in the split form `χ(π(F)) = F`, which is the form used below. -/
theorem classify_totaliseBundle (F : W ⥤ LabOneTruss C) :
    OpenBundle.classify (totaliseBundle F) (totaliseLabel F) = F := classify_totalise F

end Totalise

end Truss.Transfer
