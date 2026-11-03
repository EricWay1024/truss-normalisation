/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.TopReflection

/-!
# `thm:draft-successor-normalising` by reflection (§5.5)

This module proves the draft normalisation chapter's **inductive characterisation of
normalising coarsenings** by the two-step argument of the frozen chapter (notes commit
`451d8ef`), row `R6` of
[the reflection plan](../../../plan/ReflectionNormalisationVerification.md):

1. *Top factorisation.*  If `Q = (F, c)` is normalising, it factors through the competitor
   `τ_T = (id, ν_T)`; decomposition gives `c = e ∘ ν_T`, and postcomposing the normalising
   `ν_T` with a coarsening keeps it normalising (`prop:draft-terminal-factors` (2)).
2. *Reflection.*  If `c` is normalising, one-bundle uniqueness gives `c = ν_T` in the chosen
   representatives (`OpenBundle.normalising_target_eq`), hence `χ*L = χ_M ∘ f`; so `F` is an
   object of the lower outgoing category `Q = OutCoarse(T_(≤m), χ*L)` and `Q = Λ(F)` in the
   chosen representatives.  `Λ` preserves and reflects terminal objects
   (`lam_isNormalising_iff`), which finishes **both** directions.

The lower tower is labelled by the classifier `χ_M := χ_(S_(m+1), M)` of the **target**'s top
bundle, pulled back along `f`; in general this is *not* the classifier of the source.

## Main results

* `isNormalising_topLab` — step 1.
* `isNormalising_iff_lowLab_of_topLab` — step 2: when `c` is normalising, `Q` is normalising
  iff `F` is.
* `succ_isNormalising_iff_of_isCoarsening` — **`thm:draft-successor-normalising`** in the
  printed form, for a labelled coarsening `Q`.
* `succ_isNormalising_iff` — the same, for an arbitrary labelled map (the existing public
  statement, with a new proof).
* `isNormalising_lowLab`, `isNormalising_of_parts` — the two directions, as corollaries.

## Proof route

Nothing here calls the superseded direct proof (`SuccNormalisingDirect.lean`, not imported).
The reverse direction does not construct a mediator by hand: it is terminality transport
along `Λ`.
-/

universe u v

namespace Truss.Transfer

open CategoryTheory TrussLike Limits

section Succ

variable {P : FPoset.{u}} {m : ℕ} {C : Type v} [Category.{v} C]

/-- **`thm:draft-successor-normalising`, step 1 (top factorisation).**  If `Q = (F, c)` is
normalising then `c` is normalising: terminality factors `Q` through `τ_T = (id, ν_T)`, so
`c = e ∘ ν_T` with `e` a coarsening, and `prop:draft-terminal-factors` (2) applies. -/
theorem isNormalising_topLab {T S : Tower P (m + 1)}
    {L : (towerTot P (m + 1) T).carrier ⥤ C} {M : (towerTot P (m + 1) S).carrier ⥤ C}
    (Q : (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨S, M⟩) (hQ : IsNormalising Q) :
    IsNormalising (topLab Q) := by
  obtain ⟨e, he, hfact⟩ := hQ.exists_mediator (topNorm ⟨T, L⟩) (topNorm_isCoarsening _)
  rw [hfact, topLab_comp]
  exact (succTopMap_isNormalising T L).comp_isCoarsening
    (isCoarsening_labReindex _ (isCoarsening_topMap he))

/-- **`thm:draft-successor-normalising`, step 2 (reflection).**  Let `Q = (F, c)` be a
labelled coarsening whose top component `c` is normalising.  Then `Q` is normalising iff its
lower component `F : (T_(≤m), χ_M ∘ f) → (S_(≤m), χ_M)` is.

`c = ν_T` in the chosen representatives, so `χ*L = χ_M ∘ f` and `F` is an object of
`OutCoarse(T_(≤m), χ*L)`; `Q` and `Λ(F)` differ only by the representative identification
`(S, M) = π(χ(S_(m+1), M))`-extension, which gives morphisms both ways in the thin category
`OutCoarse(T, L)`; and `Λ` preserves and reflects terminal objects. -/
theorem isNormalising_iff_lowLab_of_topLab {T S : Tower P (m + 1)}
    {L : (towerTot P (m + 1) T).carrier ⥤ C} {M : (towerTot P (m + 1) S).carrier ⥤ C}
    (Q : (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨S, M⟩) (hQ : IsCoarsening Q.1)
    (hc : IsNormalising (topLab Q)) : IsNormalising Q ↔ IsNormalising (lowLab Q) := by
  let A : LabObj (m + 1) (Tower P (m + 1)) C := ⟨T, L⟩
  -- one-bundle uniqueness: `c = ν_T` in the chosen representatives
  obtain ⟨e, he⟩ := OpenBundle.normalising_target_eq (succTopMap_isNormalising T L) hc
  -- classifiers: `χ*L = χ_M ∘ f`
  have hcls : succClassifier T L
      = posetFunctor Q.1.base ⋙ OpenBundle.classify S.top M := by
    have hz := congrArg (fun z : LabObj 1 (OpenBundle (towerTot P m T.lower).carrier) C =>
      OpenBundle.classify z.obj z.label) e
    simpa only [classify_reindex] using hz
  -- `F` as an object of the lower outgoing category
  let F : LabOutCoarse (lowerObj A) :=
    ⟨⟨S.lower, OpenBundle.classify S.top M⟩,
      ⟨Q.1.lower, hcls.trans (by rw [← TowerMap.base_eq Q.1])⟩, isCoarsening_lower hQ⟩
  let Qo : LabOutCoarse A := ⟨⟨S, M⟩, Q, hQ⟩
  -- the representative identification `(S_(m+1), M) = π(χ(S_(m+1), M))`
  have hcl := (labTotalise_classify S.top M).symm
  let d : (⟨S.top, M⟩ : LabObj 1 (OpenBundle (towerTot P m S.lower).carrier) C) ⟶
      labTotalise (OpenBundle.classify S.top M) := eqToHom hcl
  let d' : labTotalise (OpenBundle.classify S.top M) ⟶
      (⟨S.top, M⟩ : LabObj 1 (OpenBundle (towerTot P m S.lower).carrier) C) := eqToHom hcl.symm
  -- `Λ(F) = Q` in the chosen representatives
  have hlift : ((lam A).obj F).map = Q ≫ appendTop ⟨S, M⟩ d := by
    refine lift_eq_comp_appendTop Q (succTopMap T L) F.map rfl d
      (e.trans (congrArg (fun Z : LabObj 1 (OpenBundle (towerTot P m S.lower).carrier) C =>
        (⟨OpenBundle.reindex Q.1.base Z.obj, OpenBundle.pullbackLabel Q.1.base Z.obj Z.label⟩ :
          LabObj 1 (OpenBundle (towerTot P m T.lower).carrier) C)) hcl)) ?_
    rw [labReindex_eqToHom, ← he, Category.assoc, eqToHom_trans]
  have hdd' : appendTop (⟨S, M⟩ : LabObj (m + 1) (Tower P (m + 1)) C) d
      ≫ appendTop (liftTarget F.tgt) d' = 𝟙 _ := by
    refine (appendTop_comp (⟨S, M⟩ : LabObj (m + 1) (Tower P (m + 1)) C) d d').trans ?_
    change appendTop _ (eqToHom hcl ≫ eqToHom hcl.symm) = _
    rw [eqToHom_trans, eqToHom_refl]
    rfl
  let fwd : Qo ⟶ (lam A).obj F :=
    ⟨appendTop (⟨S, M⟩ : LabObj (m + 1) (Tower P (m + 1)) C) d,
      appendTop_isCoarsening _ (isCoarsening_labEqToHom _), hlift⟩
  let bwd : (lam A).obj F ⟶ Qo :=
    ⟨(appendTop (liftTarget F.tgt) d' : liftTarget F.tgt ⟶ (⟨S, M⟩ : LabObj (m + 1)
        (Tower P (m + 1)) C)), appendTop_isCoarsening _ (isCoarsening_labEqToHom _), by
      change Q = ((lam A).obj F).map ≫ appendTop (liftTarget F.tgt) d'
      rw [hlift, Category.assoc, hdd', Category.comp_id]⟩
  -- terminality transport
  have hQo : IsNormalising Q ↔ IsNormalising F.map := by
    change IsNormalising Qo.map ↔ _
    rw [LabOutCoarse.isNormalising_iff_nonempty_isTerminal,
      nonempty_isTerminal_iff_of_homs fwd bwd,
      ← LabOutCoarse.isNormalising_iff_nonempty_isTerminal, lam_isNormalising_iff]
  rw [hQo]
  exact ⟨fun h => isNormalising_congr (congrArg (fun G => (⟨T.lower, G⟩ :
      LabObj m (Tower P m) (LabOneTruss C))) hcls) rfl h HEq.rfl,
    fun h => isNormalising_congr (congrArg (fun G => (⟨T.lower, G⟩ :
      LabObj m (Tower P m) (LabOneTruss C))) hcls).symm rfl h HEq.rfl⟩

/-- **`thm:draft-successor-normalising` (§5.5), printed form.**  Let
`Q = (F, c) : (T, L) → (S, M)` be a labelled coarsening of levelwise-open `(m+1)`-truss
bundles over `P`, with `f := Tot(F)`, and let `χ_M := χ_(S_(m+1), M) : S_m → B(C)` be the
classifier of the target's top labelled bundle.  Then `Q` is normalising iff both
1. `c : (T_(m+1), L) → f^*(S_(m+1), M)` is normalising over `T_m`, and
2. `F : (T_(≤m), χ_M ∘ f) → (S_(≤m), χ_M)` is normalising over `P`. -/
theorem succ_isNormalising_iff_of_isCoarsening {T S : Tower P (m + 1)}
    {L : (towerTot P (m + 1) T).carrier ⥤ C} {M : (towerTot P (m + 1) S).carrier ⥤ C}
    (Q : (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨S, M⟩) (hQ : IsCoarsening Q.1) :
    IsNormalising Q ↔ IsNormalising (topLab Q) ∧ IsNormalising (lowLab Q) :=
  ⟨fun h => ⟨isNormalising_topLab Q h,
      (isNormalising_iff_lowLab_of_topLab Q hQ (isNormalising_topLab Q h)).1 h⟩,
    fun h => (isNormalising_iff_lowLab_of_topLab Q hQ h.1).2 h.2⟩

/-- **`thm:draft-successor-normalising` (§5.5)**, for an arbitrary labelled map `Q`: both
sides force `Q` to be a coarsening (`thm:draft-successor-coarsening`). -/
theorem succ_isNormalising_iff {T S : Tower P (m + 1)}
    {L : (towerTot P (m + 1) T).carrier ⥤ C} {M : (towerTot P (m + 1) S).carrier ⥤ C}
    (Q : (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨S, M⟩) :
    IsNormalising Q ↔ IsNormalising (topLab Q) ∧ IsNormalising (lowLab Q) :=
  ⟨fun h => (succ_isNormalising_iff_of_isCoarsening Q h.1).1 h,
    fun h => (succ_isNormalising_iff_of_isCoarsening Q
      (isCoarsening_of_parts Q.1 h.2.1 h.1.1)).2 h⟩

/-- The forward direction, lower component (corollary of `succ_isNormalising_iff`). -/
theorem isNormalising_lowLab {T S : Tower P (m + 1)}
    {L : (towerTot P (m + 1) T).carrier ⥤ C} {M : (towerTot P (m + 1) S).carrier ⥤ C}
    (Q : (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨S, M⟩) (hQ : IsNormalising Q) :
    IsNormalising (lowLab Q) :=
  ((succ_isNormalising_iff Q).1 hQ).2

/-- The reverse direction (corollary of `succ_isNormalising_iff`). -/
theorem isNormalising_of_parts {T S : Tower P (m + 1)}
    {L : (towerTot P (m + 1) T).carrier ⥤ C} {M : (towerTot P (m + 1) S).carrier ⥤ C}
    (Q : (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨S, M⟩)
    (hc : IsNormalising (topLab Q)) (hF : IsNormalising (lowLab Q)) : IsNormalising Q :=
  (succ_isNormalising_iff Q).2 ⟨hc, hF⟩

end Succ

end Truss.Transfer
