/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.Section55
import Truss.Transfer.Normalisation.LabBordism
import Truss.Transfer.Normalisation.BundleRetract

/-!
# `thm:draft-successor-normalising` (§5.5)

This module proves the draft normalisation chapter's **successor decomposition of normalising
coarsenings**: a labelled coarsening of levelwise-open `(m+1)`-truss bundles is normalising
exactly when its final bundle map is normalising over `T_m` *and* its lower tower map is
normalising over `P`, the lower tower being labelled in the category `B(C)` of `C`-labelled
1-trusses by the classifying functor of the final labelled bundle of the target.

## Main definitions

* `topLab` — the upper component `c : (T_(m+1), L) → f^*(S_(m+1), M)` of a labelled tower
  morphism, with the label equation read off from the tower morphism's own.
* `lowLab` — the lower component `F : (T_(≤m), G ∘ f) → (S_(≤m), G)`, labelled in
  `B(C) = LabOneTruss C`.
* `assemble` — the converse: a lower tower map together with a compatible labelled map of
  final bundles is a labelled map of `(m+1)`-towers.
* `labTotalise` — the totalisation `π` of `thm:classification`, packaged as a labelled
  1-truss bundle.

## Main results

* `succ_isNormalising_iff` — **`thm:draft-successor-normalising`**.
* `isNormalising_topLab`, `isNormalising_lowLab` — the two forward components.
* `isNormalising_of_parts` — the reverse direction.
* `OpenBundle.normalising_target_eq` — **strict uniqueness of normalisation** for labelled
  1-truss bundles: two normalising coarsenings out of one labelled bundle have *equal*
  targets, and agree after the canonical identification.
* `TowerMap.ext_succ` — extensionality for maps of `(m+1)`-towers.
* `classify_reindex`, `labTotalise_comp_classify` — `totalise_comp`, the strict-representative
  equation, in the two forms the proof consumes.

## A point where the source's proof needs more than §5.2

The chapter's reverse direction says *"Uniqueness of normalisation therefore gives
`f^*(S_(m+1),M) = j^*(U'_(m+1),N')`, `c = (j^*d) ∘ a`, `G ∘ f = H' ∘ j`"* — three
**equalities**.  Section 5.2 alone (`IsNormalising.unique_iso`) gives only a compatible
*isomorphism* of the two normalisations, and an isomorphism is not enough: the lower
competitor built from `R` has to have source label *literally* `G ∘ f`, so that lower
terminality applies.  The equality is genuinely available, but it comes from §5.4's
retraction half (`BundleRetract.lean`, ultimately skeletality of `OpenTruss`): two normalising
coarsenings have the same retained family, hence are the *same* quotient map.  That is
`OpenBundle.normalising_target_eq`, proved here, and it is why this file imports
`BundleRetract` in addition to `Section55` and `LabBordism`.
-/

universe u v w u₂ v₂

namespace Truss.Transfer

open CategoryTheory TrussLike

/-! ### Generic §5.2 lemmas -/

section Generic

variable {n : ℕ} {K : Type u} [Category.{v} K] [inst : TrussLike.{u, v, w} n K]
variable {C : Type u₂} [Category.{v₂} C]

/-- The canonical comparison of equal objects is a coarsening. -/
theorem isCoarsening_eqToHom {X Y : K} (h : X = Y) : IsCoarsening (eqToHom h) := by
  subst h; simpa using IsCoarsening.id X

/-- The canonical comparison of equal **labelled** objects is a coarsening. -/
theorem isCoarsening_labEqToHom {A B : LabObj.{u, v, w, u₂, v₂} n K C} (h : A = B) :
    IsCoarsening (eqToHom h).1 := by
  subst h; simpa using IsCoarsening.id A.obj

/-- A normalising coarsening stays normalising after any further coarsening.  (The further
coarsening is then automatically invertible, by `C10` and `C07`; this is the packaged form
used to read off normality of a factor.) -/
theorem IsNormalising.comp_isCoarsening {A B D : LabObj.{u, v, w, u₂, v₂} n K C} {q : A ⟶ B}
    (hq : IsNormalising q) {e : B ⟶ D} (he : IsCoarsening e.1) : IsNormalising (q ≫ e) := by
  refine ⟨hq.1.comp he, fun U r hr => ?_⟩
  obtain ⟨k, hk, hqk⟩ := hq.exists_mediator r hr
  refine ⟨k ≫ e, ⟨hk.comp he, by rw [← Category.assoc, ← hqk]⟩, fun mm hmm => ?_⟩
  refine IsNormalising.mediator_unique hr (m := mm) (m' := k ≫ e) ?_
  rw [← hmm.2, ← Category.assoc, ← hqk]

/-- The underlying morphism of the canonical comparison of equal labelled objects. -/
@[simp] theorem LabObj.eqToHom_coe {A B : LabObj.{u, v, w, u₂, v₂} n K C} (h : A = B) :
    (eqToHom h : A ⟶ B).1 = eqToHom (congrArg LabObj.obj h) := by
  subst h; simp

end Generic

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

/-! ### The forward direction, upper component -/

/-- **`thm:draft-successor-normalising`, forward direction, upper component.**  Normalise the
final bundle over `T_m` with `B10`; comparing `Q` with `(id, c₀)`, which is a coarsening by
`N02 (3) → (1)`, exhibits `c` as `c₀` followed by a further coarsening, hence normalising. -/
theorem isNormalising_topLab {T S : Tower P (m + 1)}
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
theorem isNormalising_lowLab {T S : Tower P (m + 1)}
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
theorem isNormalising_of_parts {T S : Tower P (m + 1)}
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
theorem succ_isNormalising_iff {T S : Tower P (m + 1)}
    {L : (towerTot P (m + 1) T).carrier ⥤ C} {M : (towerTot P (m + 1) S).carrier ⥤ C}
    (Q : (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨S, M⟩) :
    IsNormalising Q ↔ IsNormalising (topLab Q) ∧ IsNormalising (lowLab Q) :=
  ⟨fun hQ => ⟨isNormalising_topLab Q hQ, isNormalising_lowLab Q hQ⟩,
    fun h => isNormalising_of_parts Q h.1 h.2⟩

end Succ

end Truss.Transfer
