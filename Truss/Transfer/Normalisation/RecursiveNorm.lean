/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.SuccNormalising

/-!
# Recursive normalisation of open `n`-truss bundles (§5.5, rows `N04`-`N06`)

This module closes the draft normalisation chapter's §"Open `n`-truss bundles" with its last
three statements: the successor normality criterion, the recursive normalisation
construction, and the construction's consequences.  Everything here is unconditional and
axiom-clean; nothing is `sorry`'d.

## Main definitions

* **Step 1** of `cons:draft-recursive-normalisation` — `ν_T`, its target and the classifier
  `χ*L` — is `succTopMap`, `succTopTarget`, `succClassifier`, defined in `TopReflection.lean`.
* `succStep` — **step 3**: the lift `Λ(F) = (F, ν_T)` of the recursive result `F`
  (`succStep_eq_lam`: it *is* the object part of `lam`, by `rfl`).
* `towerNormalise` — **`cons:draft-recursive-normalisation` (`N05`)**, the recursion itself.

## Main results

* `succ_isNormal_iff` — **`cor:draft-successor-normality` (`N04`)**.
* `towerNormalise_zero`, `towerNormalise_succ`, `towerNormalise_succ_fst`,
  `towerNormalise_succ_lower`, `towerNormalise_succ_base`, `towerNormalise_succ_topMap`,
  `towerNormalise_succ_totHom` — the **explicit reduction equations** for the construction's
  steps.  All but one hold by `rfl`.
* `towerNormalise_isNormalising` — **the construction is correct (`N05`)**: the returned
  labelled tower map is a normalising coarsening at every height.  Since 2026-09-26 the proof
  is terminality preservation by `Λ` (`lam_isNormalising_iff`), **not** the inductive
  characterisation `succ_isNormalising_iff`; `Audit/Reflection.lean` checks this.
* `exists_isNormalising_tower`, `towerNormalise_target_isNormal`, `towerNormalise_unique`,
  `towerNormalise_universal` — **`N06`**: existence, normality of the target (`C10`),
  uniqueness up to the unique compatible isomorphism, and the universal property in its
  printed form.

## How the recursion is packaged

The chapter says to *"induct simultaneously for all automorphism-free label categories, so
the recursive call may use `B(C)` as its label category"*.  That is formalised literally:
`towerNormalise` recurses on the height with the label category **universally quantified
inside** the recursion,

```
∀ (m : ℕ) {C : Type v} [Category.{v} C] (T : Tower P m) (L : Tot(T) ⥤ C), ...
```

and the successor step instantiates the recursive call at `LabOneTruss C = B(C)`.  This is
well-formed because `LabOneTruss : Type v → Type v` with `Category.{v} (LabOneTruss C)`, so
`B(-)` is an endo-operation on the label categories at a fixed universe level.  Only the
*lower-height* recursive result is ever used; no normalisation data is postulated at the same
height (`B10`, used at step 1, is about labelled **1-truss bundles**, a different category).

The chapter restricts the simultaneous induction to *automorphism-free* label categories.
That hypothesis is **not needed and not assumed here**: neither the reflection
(`lam_isNormalising_iff`) nor `B10` (`OpenBundle.bundleNormaliseMap_isNormalising'`) carries
it, so the recursion runs over every `C : Type v` with `Category.{v} C`.  The printed
statement is the specialisation.

The output is packaged as a `PSigma`: `towerNormalise P m T L` is the pair of the normalised
labelled tower and the normalising coarsening into it.  A pair is needed because the target
is genuinely produced by the construction rather than given; `PSigma` (rather than `Sigma`)
keeps the whole thing in `Type (max u v)`.

## Where the source's construction needs a transport

Step 3 of the chapter asserts the equation `(T'_(m+1), L') = f^*(S_(m+1), M)` and says it is
the strict-representative equation `totalise_comp`.  Both halves of that are indeed `rfl`
here (`labTotalise_comp`, `labTotalise_classify`), but the equation itself is **not** `rfl`:
it is obtained by applying `labTotalise` to the *propositional* label equation `F = G ∘ f`
carried by the recursive result.  So the assembled final bundle map is `c` followed by an
`eqToHom`, not `c` on the nose; see `succTopTarget_eq` and `towerNormalise_succ_topMap`.
That `eqToHom` is a coarsening (`isCoarsening_labEqToHom`), so it costs nothing in the
correctness proof, which is terminality transport along `Λ`; the label identification
`χ(π(G)) = G` it needs is `succClassifier_liftTarget` in `TopReflection.lean`.

## Deliberately not claimed

The chapter's final corollary — the one asserting **idempotence** and "canonical equality" of
normalisation in the chosen representatives — is **commented out** in the source, and the
verification plan tracks it as a proposed consequence only.  Nothing here asserts it.
`towerNormalise_unique` gives uniqueness up to the unique compatible isomorphism, which is
what `IsNormalising.unique_iso` (§5.2) supports; strict idempotence would additionally need a
strictness statement at tower level analogous to `OpenBundle.normalising_target_eq`, which is
not proved.
-/

universe u v w u₂ v₂

namespace Truss.Transfer

open CategoryTheory TrussLike

/-! ### `N04` -/

section Succ

variable {P : FPoset.{u}} {m : ℕ} {C : Type v} [Category.{v} C]

/-- **`cor:draft-successor-normality` (`N04`).**  The labelled `(m+1)`-truss bundle `(T, L)`
is normal iff the labelled `m`-truss bundle `(T_(≤m), χ_(T_(m+1),L))` is normal and the
labelled 1-truss bundle `(T_(m+1), L)` is normal. -/
theorem succ_isNormal_iff (T : Tower P (m + 1)) (L : (towerTot P (m + 1) T).carrier ⥤ C) :
    IsNormal (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ↔
      IsNormal (⟨T.lower, OpenBundle.classify T.top L⟩ :
          LabObj m (Tower P m) (LabOneTruss C)) ∧
        IsNormal (⟨T.top, L⟩ :
          LabObj 1 (OpenBundle (towerTot P m T.lower).carrier) C) := by
  rw [IsNormal, succ_isNormalising_iff, topLab_id, lowLab_id, IsNormal, IsNormal, and_comm]

/-! ### `N05`: the pieces of the successor step -/

/-- **Step 3**: the target identification used by the lift `(T'_(m+1), L') = f^*(S_(m+1), M)`. -/
theorem succTopTarget_eq (T : Tower P (m + 1)) (L : (towerTot P (m + 1) T).carrier ⥤ C)
    (D : LabObj m (Tower P m) (LabOneTruss C))
    (Fmap : (⟨T.lower, succClassifier T L⟩ : LabObj m (Tower P m) (LabOneTruss C)) ⟶ D) :
    succTopTarget T L
      = ⟨OpenBundle.reindex (Fmap.1 : T.lower ⟶ D.obj).totHom (totaliseBundle D.label),
         OpenBundle.pullbackLabel (Fmap.1 : T.lower ⟶ D.obj).totHom
           (totaliseBundle D.label) (totaliseLabel D.label)⟩ := by
  have h := congrArg labTotalise Fmap.2
  rw [labTotalise_comp] at h
  rw [show labTotalise (succClassifier T L) = succTopTarget T L from
    labTotalise_classify _ _] at h
  exact h

/-- **The successor step of `cons:draft-recursive-normalisation`**, as a standalone operation
on the result of the recursive call at height `m` in the label category `B(C)`: return the
lift `Λ(F) = (F, ν_T)` of `prop:draft-top-normalisation-reflection`.  Its target is
`liftTarget` of the recursive target and its map is `lift` with `c = ν_T`, exactly the object
part of `lam` (`succStep_eq_lam`). -/
noncomputable def succStep (T : Tower P (m + 1)) (L : (towerTot P (m + 1) T).carrier ⥤ C)
    (low : Σ' D : LabObj m (Tower P m) (LabOneTruss C),
        ((⟨T.lower, succClassifier T L⟩ : LabObj m (Tower P m) (LabOneTruss C)) ⟶ D)) :
    Σ' D : LabObj (m + 1) (Tower P (m + 1)) C,
      ((⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ D) :=
  ⟨liftTarget low.1, lift ⟨T, L⟩ (succTopMap T L) low.2⟩

/-- **Construction agreement (`R7`).**  The successor step *is* `Λ` applied to the recursive
result, on the nose: same target (tower and label) and same map (lower part, base map, top
map and label equation). -/
theorem succStep_eq_lam (T : Tower P (m + 1)) (L : (towerTot P (m + 1) T).carrier ⥤ C)
    (low : Σ' D : LabObj m (Tower P m) (LabOneTruss C),
        ((⟨T.lower, succClassifier T L⟩ : LabObj m (Tower P m) (LabOneTruss C)) ⟶ D))
    (hlow : IsCoarsening low.2.1) :
    succStep T L low = ⟨((lam ⟨T, L⟩).obj ⟨low.1, low.2, hlow⟩).tgt,
      ((lam ⟨T, L⟩).obj ⟨low.1, low.2, hlow⟩).map⟩ := rfl

/-- The successor step in the pre-reflection (`assemble`) presentation: identical by `rfl`
to the construction verified before 2026-09-26. -/
theorem succStep_eq_assemble (T : Tower P (m + 1)) (L : (towerTot P (m + 1) T).carrier ⥤ C)
    (low : Σ' D : LabObj m (Tower P m) (LabOneTruss C),
        ((⟨T.lower, succClassifier T L⟩ : LabObj m (Tower P m) (LabOneTruss C)) ⟶ D)) :
    succStep T L low
      = ⟨⟨(low.1.obj).succ (totaliseBundle low.1.label), totaliseLabel low.1.label⟩,
        assemble low.2.1 (succTopMap T L ≫ eqToHom (succTopTarget_eq T L low.1 low.2))⟩ :=
  rfl

end Succ

/-! ### `N05`: the recursion -/

section Recursion

/-- **`cons:draft-recursive-normalisation` (`N05`).**  Recursive normalisation of a labelled
levelwise-open `m`-truss bundle over `P`, by recursion on the height and **simultaneously for
every label category** at a fixed universe level: the recursive call at height `m` is made in
the label category `B(C) = LabOneTruss C`. -/
noncomputable def towerNormalise (P : FPoset.{u}) :
    ∀ (m : ℕ) {C : Type v} [Category.{v} C] (T : Tower P m)
      (L : (towerTot P m T).carrier ⥤ C),
      Σ' D : LabObj m (Tower P m) C, ((⟨T, L⟩ : LabObj m (Tower P m) C) ⟶ D)
  | 0, _, _, T, L => ⟨⟨T, L⟩, 𝟙 _⟩
  | m + 1, _, _, T, L => succStep T L (towerNormalise P m T.lower (succClassifier T L))

variable {m : ℕ} {C : Type v} [Category.{v} C]

/-- **Reduction equation, height `0`**: the identity of the bottom base with its label. -/
@[simp] theorem towerNormalise_zero {P : FPoset.{u}} (T : Tower P 0)
    (L : (towerTot P 0 T).carrier ⥤ C) :
    towerNormalise P 0 T L = ⟨⟨T, L⟩, 𝟙 (⟨T, L⟩ : LabObj 0 (Tower P 0) C)⟩ := rfl

/-- **Reduction equation, height `m+1`**: the three steps, packaged as `succStep`. -/
@[simp] theorem towerNormalise_succ {P : FPoset.{u}} (T : Tower P (m + 1))
    (L : (towerTot P (m + 1) T).carrier ⥤ C) :
    towerNormalise P (m + 1) T L
      = succStep T L (towerNormalise P m T.lower (succClassifier T L)) := rfl

/-- **Reduction equation: step 3**, the target `(S, M)` is `G` totalised and appended. -/
theorem towerNormalise_succ_fst {P : FPoset.{u}} (T : Tower P (m + 1))
    (L : (towerTot P (m + 1) T).carrier ⥤ C) :
    (towerNormalise P (m + 1) T L).1
      = ⟨((towerNormalise P m T.lower (succClassifier T L)).1.obj).succ
            (totaliseBundle (towerNormalise P m T.lower (succClassifier T L)).1.label),
         totaliseLabel (towerNormalise P m T.lower (succClassifier T L)).1.label⟩ := rfl

/-- **Reduction equation: step 2**, the lower component `F` is the recursive call. -/
theorem towerNormalise_succ_lower {P : FPoset.{u}} (T : Tower P (m + 1))
    (L : (towerTot P (m + 1) T).carrier ⥤ C) :
    (towerNormalise P (m + 1) T L).2.1.lower
      = (towerNormalise P m T.lower (succClassifier T L)).2.1 := rfl

/-- **Reduction equation: step 2**, the base map `f := Tot(F)`. -/
theorem towerNormalise_succ_base {P : FPoset.{u}} (T : Tower P (m + 1))
    (L : (towerTot P (m + 1) T).carrier ⥤ C) :
    (towerNormalise P (m + 1) T L).2.1.base
      = TowerMap.totHom (towerNormalise P m T.lower (succClassifier T L)).2.1 := rfl

/-- **Reduction equation: step 3**, the lift uses the step-1 top normaliser `ν_T`, transported
along the target identification `(T'_(m+1), L') = f^*(S_(m+1), M)`. -/
theorem towerNormalise_succ_topMap {P : FPoset.{u}} (T : Tower P (m + 1))
    (L : (towerTot P (m + 1) T).carrier ⥤ C) :
    (towerNormalise P (m + 1) T L).2.1.topMap
      = (succTopMap T L).1 ≫ eqToHom (congrArg LabObj.obj
          (succTopTarget_eq T L _ (towerNormalise P m T.lower (succClassifier T L)).2)) := by
  change (succTopMap T L ≫ eqToHom
    (succTopTarget_eq T L _ (towerNormalise P m T.lower (succClassifier T L)).2)).1 = _
  rw [LabObj.comp_coe, LabObj.eqToHom_coe]

/-- **Reduction equation: `q_(m+1) = f̃ ∘ Tot(c)`** (`rem:structural-successor-top-map`).
Here `Tot(c)` is the total map of the transported final bundle component, i.e. of the `ν_T` of
`towerNormalise_succ_topMap`. -/
theorem towerNormalise_succ_totHom {P : FPoset.{u}} (T : Tower P (m + 1))
    (L : (towerTot P (m + 1) T).carrier ⥤ C) :
    TowerMap.totHom (towerNormalise P (m + 1) T L).2.1
      = (OpenBundle.tildeHom
            (TowerMap.totHom (towerNormalise P m T.lower (succClassifier T L)).2.1)
            (totaliseBundle (towerNormalise P m T.lower (succClassifier T L)).1.label)).comp
          (BundleMap.totHom (towerNormalise P (m + 1) T L).2.1.topMap) := rfl

/-! ### `N05`: correctness -/

/-- The successor step returns a normalising coarsening whenever the recursive call does:
`Λ` preserves terminal objects (`lam_isNormalising_iff`, `prop:draft-top-normalisation-
reflection`).  This does **not** use the inductive characterisation of normalising
coarsenings.  Only the lower-height result is used. -/
theorem succStep_isNormalising {P : FPoset.{u}} (T : Tower P (m + 1))
    (L : (towerTot P (m + 1) T).carrier ⥤ C)
    (low : Σ' D : LabObj m (Tower P m) (LabOneTruss C),
        ((⟨T.lower, succClassifier T L⟩ : LabObj m (Tower P m) (LabOneTruss C)) ⟶ D))
    (hlow : IsNormalising low.2) : IsNormalising (succStep T L low).2 :=
  (lam_isNormalising_iff (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C)
    ⟨low.1, low.2, hlow.1⟩).2 hlow

/-- **Height `0` is normal.**  A `0`-tower over `P` is the point, `Tot` is the identity of
`P`, and a morphism of `LabObj 0 (Tower P 0) C` exists exactly when the two labels agree; so
the identity coarsening out of `(T, L)` is terminal. -/
theorem isNormal_zero {P : FPoset.{u}} (T : Tower P 0)
    (L : (towerTot P 0 T).carrier ⥤ C) :
    IsNormal (⟨T, L⟩ : LabObj 0 (Tower P 0) C) := by
  haveI hobj : Subsingleton (Tower P 0) := inferInstanceAs (Subsingleton PUnit)
  haveI hhom : ∀ X Y : Tower P 0, Subsingleton (X ⟶ Y) := fun _ _ =>
    inferInstanceAs (Subsingleton PUnit)
  refine ⟨IsCoarsening.id _, fun D r _ => ?_⟩
  obtain ⟨T', L'⟩ := D
  obtain rfl : T' = T := Subsingleton.elim _ _
  obtain rfl : L' = L := r.2.symm
  exact ⟨𝟙 _, ⟨IsCoarsening.id _, Subtype.ext (Subsingleton.elim _ _)⟩,
    fun _ _ => Subtype.ext (Subsingleton.elim _ _)⟩

/-- **`cons:draft-recursive-normalisation` is correct (`N05`).**  The recursion returns a
normalising coarsening at every height: at height `0` the identity is terminal, and at a
successor `Λ` preserves terminal objects (`succStep_isNormalising`, `R5`).  Only
the lower-height recursive result is used; no normalisation data is postulated at the same
height. -/
theorem towerNormalise_isNormalising (P : FPoset.{u}) :
    ∀ (m : ℕ) {C : Type v} [Category.{v} C] (T : Tower P m)
      (L : (towerTot P m T).carrier ⥤ C), IsNormalising (towerNormalise P m T L).2
  | 0, _, _, T, L => isNormal_zero T L
  | m + 1, _, _, T, L =>
      succStep_isNormalising T L _
        (towerNormalise_isNormalising P m T.lower (succClassifier T L))

end Recursion

/-! ### `N06`: consequences of the construction -/

section Consequences

variable {P : FPoset.{u}} {m : ℕ} {C : Type v} [Category.{v} C]
variable (T : Tower P m) (L : (towerTot P m T).carrier ⥤ C)

/-- **Existence (`N06`).**  Every labelled levelwise-open `m`-truss bundle over `P` admits a
normalising coarsening, namely the one produced by `cons:draft-recursive-normalisation`. -/
theorem exists_isNormalising_tower :
    ∃ (D : LabObj m (Tower P m) C) (r : (⟨T, L⟩ : LabObj m (Tower P m) C) ⟶ D),
      IsNormalising r :=
  ⟨_, _, towerNormalise_isNormalising P m T L⟩

/-- **Normal target (`N06`, by `C10`).** -/
theorem towerNormalise_target_isNormal : IsNormal (towerNormalise P m T L).1 :=
  (towerNormalise_isNormalising P m T L).target_isNormal

/-- **Uniqueness (`N06`, by `IsNormalising.unique_iso`).**  Any normalising coarsening out of
`(T, L)` differs from the constructed one by a compatible isomorphism. -/
theorem towerNormalise_unique {D : LabObj m (Tower P m) C}
    (r : (⟨T, L⟩ : LabObj m (Tower P m) C) ⟶ D) (hr : IsNormalising r) :
    ∃ e : D ≅ (towerNormalise P m T L).1, r ≫ e.hom = (towerNormalise P m T L).2 := by
  obtain ⟨e, e', -, -, hqe, -, hee', he'e⟩ :=
    hr.unique_iso (towerNormalise_isNormalising P m T L)
  exact ⟨⟨e, e', hee', he'e⟩, hqe.symm⟩

/-- **The universal property, in the printed form (the plan's §11 capstone).**  Every
labelled coarsening out of `(T, L)` factors through the constructed normalisation by a unique
coarsening. -/
theorem towerNormalise_universal :
    ∀ (D : LabObj m (Tower P m) C) (R : (⟨T, L⟩ : LabObj m (Tower P m) C) ⟶ D),
      IsCoarsening R.1 → ∃! H : D ⟶ (towerNormalise P m T L).1,
        IsCoarsening H.1 ∧ R ≫ H = (towerNormalise P m T L).2 := by
  intro D R hR
  obtain ⟨H, hH, huniq⟩ := (towerNormalise_isNormalising P m T L).2 D R hR
  exact ⟨H, ⟨hH.1, hH.2.symm⟩, fun k hk => huniq k ⟨hk.1, hk.2.symm⟩⟩

end Consequences

end Truss.Transfer
