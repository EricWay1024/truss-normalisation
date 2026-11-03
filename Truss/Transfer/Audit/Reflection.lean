/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.RecursiveNorm
import Truss.Transfer.Normalisation.SuccNormalisingDirect
import Truss.Transfer.Normalisation.NoAutIteration

/-!
# Audit: reflection-based normalisation (rows `R1`–`R8`)

Audit module for
[the reflection plan](../../../plan/ReflectionNormalisationVerification.md).
It contains **no new mathematics**:

1. **Exact-typed witnesses.**  Each accepted result is restated from scratch as the type of a
   `theorem`/`def` and then supplied by the proved declaration, so a refactor that quietly
   changes a statement breaks this file.
2. **Axiom audit.**  `#print axioms` for every construction, bridge and proof; the build log
   records the transitive axiom set.  The allowed set is `{propext, Classical.choice,
   Quot.sound}`.
3. **Proof-route gate.**  `#assert_no_dep d f` fails the build if the value or type of `d`
   transitively mentions the constant `f` (closure through `Truss.*` constants), and
   `#assert_dep d f` fails if it does not.  This is how the plan's dependency requirements are
   *checked*, not merely claimed: the reflection does not use the inductive criterion or the
   recursion, and recursive correctness goes through `Λ` (`lam_isNormalising_iff`), not the
   inductive criterion and not the superseded direct proof.

This file imports `SuccNormalisingDirect` **only** so that the gate can name the retired
constants; no witness below is supplied by them.
-/

universe u v

namespace Truss.Transfer.Audit.Reflection

open Lean Elab Command

/-- The constants mentioned by the type and value of `n`. -/
def directDeps (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let ty := ci.type.getUsedConstants
    match ci.value? with
    | some v => ty ++ v.getUsedConstants
    | none => ty

/-- A constant of this project: in the `Truss` namespace, possibly as a private auxiliary. -/
def isTrussConst (c : Name) : Bool :=
  (`Truss).isPrefixOf c || ((privateToUserName? c).map (`Truss).isPrefixOf).getD false

/-- The transitive closure of `directDeps`, following only project constants (a Mathlib or
core constant cannot mention a `Truss` constant). -/
partial def trussClosure (env : Environment) (root : Name) : NameSet :=
  go [root] {}
where
  /-- Worklist traversal. -/
  go : List Name → NameSet → NameSet
    | [], s => s
    | n :: rest, s =>
      if s.contains n then go rest s
      else
        let s' := s.insert n
        let next := (directDeps env n).toList.filter fun c =>
          isTrussConst c && !s'.contains c
        go (next ++ rest) s'

/-- `#assert_no_dep d f` fails unless `d` is free of `f` (transitively, through `Truss.*`). -/
elab "#assert_no_dep " d:ident f:ident : command => do
  let env ← getEnv
  let dn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let fn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo f
  if (trussClosure env dn).contains fn then
    throwError "proof-route gate FAILED: {dn} depends on {fn}"
  else
    logInfo m!"proof-route gate ok: {dn} does not depend on {fn}"

/-- `#assert_dep d f` fails unless `d` depends on `f` (transitively, through `Truss.*`). -/
elab "#assert_dep " d:ident f:ident : command => do
  let env ← getEnv
  let dn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let fn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo f
  if (trussClosure env dn).contains fn then
    logInfo m!"proof-route gate ok: {dn} depends on {fn}"
  else
    throwError "proof-route gate FAILED: {dn} does not depend on {fn}"

end Truss.Transfer.Audit.Reflection

namespace Truss.Transfer.Audit.Reflection

open CategoryTheory CategoryTheory.Limits Truss.Transfer TrussLike

/-! ## R1 — reflections between thin categories -/

section R1

variable {X : Type u} [Category.{v} X] {Y : Type u} [Category.{v} Y]
variable [Quiver.IsThin X] [Quiver.IsThin Y]

/-- `lem:draft-thin-reflection`: the adjunction. -/
noncomputable def w_R1_adj (Φ : X ⥤ Y) (Λ : Y ⥤ X) (hΦΛ : Λ ⋙ Φ = 𝟭 Y)
    (η : ∀ R : X, R ⟶ Λ.obj (Φ.obj R)) : Φ ⊣ Λ :=
  ThinReflection.adjunction Φ Λ hΦΛ η

/-- `lem:draft-thin-reflection`: full faithfulness. -/
def w_R1_ff (Φ : X ⥤ Y) (Λ : Y ⥤ X) (hΦΛ : Λ ⋙ Φ = 𝟭 Y) : Λ.FullyFaithful :=
  ThinReflection.fullyFaithful Φ Λ hΦΛ

/-- `lem:draft-thin-reflection`: preservation and reflection of terminal objects. -/
theorem w_R1_terminal (Φ : X ⥤ Y) (Λ : Y ⥤ X) (hΦΛ : Λ ⋙ Φ = 𝟭 Y)
    (η : ∀ R : X, R ⟶ Λ.obj (Φ.obj R)) (Z : Y) :
    Nonempty (IsTerminal (Λ.obj Z)) ↔ Nonempty (IsTerminal Z) :=
  ThinReflection.nonempty_isTerminal_obj_iff Φ Λ hΦΛ η Z

end R1

/-- `lem:draft-labelled-outcoarse-full`, thinness of the labelled outgoing category. -/
example {n : ℕ} {K : Type u} [Category.{u} K] [TrussLike.{u, u, u} n K] {C : Type v}
    [Category.{v} C] (A : LabObj n K C) : Quiver.IsThin (LabOutCoarse A) :=
  fun _ _ => inferInstance

/-- `def:draft-normalising`: normalising = terminal in `OutCoarse(X, L)`. -/
theorem w_R1_normalising_terminal {n : ℕ} {K : Type u} [Category.{u} K]
    [TrussLike.{u, u, u} n K] {C : Type v} [Category.{v} C] {A : LabObj n K C}
    (r : LabOutCoarse A) : IsNormalising r.map ↔ Nonempty (IsTerminal r) :=
  LabOutCoarse.isNormalising_iff_nonempty_isTerminal r

section Tower

variable {P : FPoset.{u}} {m : ℕ} {C : Type v} [Category.{v} C]

/-! ## R2 — top normalisation -/

/-- `def:draft-top-normalisation`: `τ_T` is a labelled coarsening. -/
theorem w_R2_coarsening (A : LabObj (m + 1) (Tower P (m + 1)) C) :
    IsCoarsening (topNorm A).1 := topNorm_isCoarsening A

/-- `def:draft-top-normalisation`: computation equations of `τ_T = (id, ν_T)`. -/
theorem w_R2_eqns (A : LabObj (m + 1) (Tower P (m + 1)) C) :
    (topNorm A).1.lower = 𝟙 A.obj.lower ∧ (topNorm A).1.base = OrderHom.id ∧
      (topNorm A).1.topMap = (succTopMap A.obj A.label).1 ∧
      topNormObj A = ⟨A.obj.lower.succ (succTopTarget A.obj A.label).obj,
        (succTopTarget A.obj A.label).label⟩ :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `ν_T` is the fixed-base normaliser of §5.4, and is normalising (`B10`). -/
theorem w_R2_nu (T : Tower P (m + 1)) (L : (towerTot P (m + 1) T).carrier ⥤ C) :
    succTopMap T L
        = OpenBundle.bundleNormaliseMap (fibrewiseThm (towerTot P m T.lower).carrier) T.top L ∧
      IsNormalising (succTopMap T L) :=
  ⟨rfl, succTopMap_isNormalising T L⟩

/-- Strict comparison of one-bundle normalisations (`prop:draft-labelled-outcoarse-1-bundle-
poset-iso`, retraction half): equal targets, equal maps after the identification. -/
theorem w_R2_strict {B : Type u} [PartialOrder B] [Finite B] {A : OpenBundle B}
    {L : A.Tot ⥤ C} {D D' : LabObj 1 (OpenBundle B) C}
    {q : (⟨A, L⟩ : LabObj 1 (OpenBundle B) C) ⟶ D}
    {q' : (⟨A, L⟩ : LabObj 1 (OpenBundle B) C) ⟶ D'}
    (hq : IsNormalising q) (hq' : IsNormalising q') : ∃ e : D = D', q ≫ eqToHom e = q' :=
  OpenBundle.normalising_target_eq hq hq'

/-! ## R3 — compatibility with arbitrary lower coarsenings -/

/-- `lem:draft-top-normalisation-along-lower` (1). -/
theorem w_R3_1 {A B : LabObj (m + 1) (Tower P (m + 1)) C} (R : A ⟶ B)
    (hR : IsCoarsening R.1) :
    ∃ e : succTopTarget A.obj A.label
        = ⟨OpenBundle.reindex R.1.base (succTopTarget B.obj B.label).obj,
           OpenBundle.pullbackLabel R.1.base (succTopTarget B.obj B.label).obj
             (succTopTarget B.obj B.label).label⟩,
      succTopMap A.obj A.label ≫ eqToHom e
        = topLab R ≫ OpenBundle.labReindex R.1.base (succTopMap B.obj B.label) :=
  topNorm_along_lower R hR

/-- `lem:draft-top-normalisation-along-lower` (2). -/
theorem w_R3_2 {A B : LabObj (m + 1) (Tower P (m + 1)) C} (R : A ⟶ B)
    (hR : IsCoarsening R.1) :
    succClassifier A.obj A.label = posetFunctor R.1.base ⋙ succClassifier B.obj B.label :=
  succClassifier_along_lower R hR

/-- `lem:draft-top-normalisation-along-lower` (2), labelled lower map. -/
theorem w_R3_2lab {A B : LabObj (m + 1) (Tower P (m + 1)) C} (R : A ⟶ B)
    (hR : IsCoarsening R.1) :
    (phiHom R hR).1 = R.1.lower ∧ IsCoarsening (phiHom R hR).1 :=
  ⟨rfl, isCoarsening_lower hR⟩

/-! ## R4 — general labelled lifting -/

/-- `lem:draft-lifting-lower-labelled-coarsenings`: for **any** labelled top coarsening `c`
(no normalising hypothesis) and any compatible lower labelled coarsening `J`, the lift is a
labelled coarsening; its base map is surjective; its target is identified on the nose. -/
theorem w_R4 (A : LabObj (m + 1) (Tower P (m + 1)) C)
    {D : LabObj 1 (OpenBundle (towerTot P m A.obj.lower).carrier) C}
    (c : (⟨A.obj.top, A.label⟩ : LabObj 1 (OpenBundle (towerTot P m A.obj.lower).carrier) C)
      ⟶ D) {Y : LabObj m (Tower P m) (LabOneTruss C)}
    (J : (⟨A.obj.lower, OpenBundle.classify D.obj D.label⟩ :
      LabObj m (Tower P m) (LabOneTruss C)) ⟶ Y)
    (hc : IsCoarsening c.1) (hJ : IsCoarsening J.1) :
    IsCoarsening (lift A c J).1 ∧
      Function.Surjective (J.1 : A.obj.lower ⟶ Y.obj).totHom ∧
      D = ⟨OpenBundle.reindex (J.1 : A.obj.lower ⟶ Y.obj).totHom (labTotalise Y.label).obj,
        OpenBundle.pullbackLabel (J.1 : A.obj.lower ⟶ Y.obj).totHom
          (labTotalise Y.label).obj (labTotalise Y.label).label⟩ ∧
      (lift A c J).1.lower = J.1 ∧
      (liftTarget Y).obj = Y.obj.succ (totaliseBundle Y.label) ∧
      (liftTarget Y).label = totaliseLabel Y.label :=
  ⟨lift_isCoarsening A hc hJ, lift_base_surjective A hJ, lift_target_eq A J, rfl, rfl, rfl⟩

/-- `lem:draft-lifting-lower-labelled-coarsenings`: the extension's top bundle is classified
by `Ĥ`. -/
theorem w_R4_classifier (Y : LabObj m (Tower P m) (LabOneTruss C)) :
    OpenBundle.classify (liftTarget Y).obj.top (liftTarget Y).label = Y.label :=
  classify_liftTarget Y

/-- `lem:draft-lifting-lower-labelled-coarsenings`, lifting mediators and composition. -/
theorem w_R4_comp (A : LabObj (m + 1) (Tower P (m + 1)) C)
    {D : LabObj 1 (OpenBundle (towerTot P m A.obj.lower).carrier) C}
    (c : (⟨A.obj.top, A.label⟩ : LabObj 1 (OpenBundle (towerTot P m A.obj.lower).carrier) C)
      ⟶ D) {Y Y' : LabObj m (Tower P m) (LabOneTruss C)}
    (J : (⟨A.obj.lower, OpenBundle.classify D.obj D.label⟩ :
      LabObj m (Tower P m) (LabOneTruss C)) ⟶ Y) (K : Y ⟶ Y') (hK : IsCoarsening K.1) :
    lift A c (J ≫ K) = lift A c J ≫ liftMed K ∧ IsCoarsening (liftMed K).1 ∧
      (liftMed K).1.lower = K.1 :=
  ⟨lift_comp A c J K, liftMed_isCoarsening hK, rfl⟩

/-! ## R5 — the reflection on all outgoing coarsenings -/

/-- `prop:draft-top-normalisation-reflection`: `Φ` and `Λ` on objects. -/
theorem w_R5_obj (A : LabObj (m + 1) (Tower P (m + 1)) C) (R : LabOutCoarse A)
    (J : LabOutCoarse (lowerObj A)) :
    ((phi A).obj R).tgt = ⟨R.tgt.obj.lower, succClassifier R.tgt.obj R.tgt.label⟩ ∧
      ((phi A).obj R).map.1 = R.map.1.lower ∧
      ((lam A).obj J).tgt = liftTarget J.tgt ∧
      ((lam A).obj J).map = lift A (succTopMap A.obj A.label) J.map :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `prop:draft-top-normalisation-reflection`: `Φ ∘ Λ = id_Q` as a functor equality. -/
theorem w_R5_retract (A : LabObj (m + 1) (Tower P (m + 1)) C) :
    lam A ⋙ phi A = 𝟭 (LabOutCoarse (lowerObj A)) := lam_comp_phi A

/-- `χ*(H) = Ĥ` for a lifted target: the label part of `Φ ∘ Λ = id`. -/
theorem w_R5_label (A : LabObj (m + 1) (Tower P (m + 1)) C) (J : LabOutCoarse (lowerObj A)) :
    succClassifier (liftTarget J.tgt).obj (liftTarget J.tgt).label = J.tgt.label :=
  succClassifier_liftTarget A J

/-- The unit factorisation `Λ(Φ(R)) = τ_U ∘ R` in the chosen representatives. -/
theorem w_R5_unit (A : LabObj (m + 1) (Tower P (m + 1)) C) (R : LabOutCoarse A) :
    ((lam A).obj ((phi A).obj R)).map = R.map ≫ appendTop R.tgt (unitTop R.tgt) ∧
      (appendTop R.tgt (unitTop R.tgt)).1.lower = 𝟙 R.tgt.obj.lower ∧
      (appendTop R.tgt (unitTop R.tgt)).1.topMap
        = (succTopMap R.tgt.obj R.tgt.label ≫ eqToHom (labTotalise_classify _ _).symm).1 :=
  ⟨lam_phi_map A R, rfl, rfl⟩

/-- The unit is `τ_U` in the chosen representatives. -/
theorem w_R5_unit_tau (B : LabObj (m + 1) (Tower P (m + 1)) C) :
    appendTop B (unitTop B) = topNorm B ≫ eqToHom (congrArg (appendObj B.obj.lower)
      (labTotalise_classify (succTopTarget B.obj B.label).obj
        (succTopTarget B.obj B.label).label).symm) :=
  unitTop_appendTop_eq B

/-- `Φ ⊣ Λ`. -/
noncomputable def w_R5_adj (A : LabObj (m + 1) (Tower P (m + 1)) C) : phi A ⊣ lam A :=
  reflection A

/-- `Λ` fully faithful. -/
noncomputable def w_R5_ff (A : LabObj (m + 1) (Tower P (m + 1)) C) : (lam A).FullyFaithful :=
  lamFullyFaithful A

/-- `Λ` preserves and reflects normalising coarsenings. -/
theorem w_R5_terminal (A : LabObj (m + 1) (Tower P (m + 1)) C)
    (J : LabOutCoarse (lowerObj A)) :
    IsNormalising ((lam A).obj J).map ↔ IsNormalising J.map :=
  lam_isNormalising_iff A J

/-! ## R6 — the inductive characterisation -/

/-- `thm:draft-successor-normalising`, printed form (for a labelled coarsening). -/
theorem w_R6 {T S : Tower P (m + 1)} {L : (towerTot P (m + 1) T).carrier ⥤ C}
    {M : (towerTot P (m + 1) S).carrier ⥤ C}
    (Q : (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨S, M⟩) (hQ : IsCoarsening Q.1) :
    IsNormalising Q ↔
      IsNormalising (topLab Q) ∧
      IsNormalising (lowLab Q : (⟨T.lower, posetFunctor Q.1.base ⋙ OpenBundle.classify S.top M⟩ :
        LabObj m (Tower P m) (LabOneTruss C)) ⟶ ⟨S.lower, OpenBundle.classify S.top M⟩) :=
  succ_isNormalising_iff_of_isCoarsening Q hQ

/-- `thm:draft-successor-normalising`, for arbitrary labelled maps. -/
theorem w_R6' {T S : Tower P (m + 1)} {L : (towerTot P (m + 1) T).carrier ⥤ C}
    {M : (towerTot P (m + 1) S).carrier ⥤ C}
    (Q : (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨S, M⟩) :
    IsNormalising Q ↔ IsNormalising (topLab Q) ∧ IsNormalising (lowLab Q) :=
  succ_isNormalising_iff Q

/-! ## R7 — identity normality and the recursion -/

/-- `cor:draft-successor-normality`. -/
theorem w_R7_normal (T : Tower P (m + 1)) (L : (towerTot P (m + 1) T).carrier ⥤ C) :
    IsNormal (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ↔
      IsNormal (⟨T.lower, OpenBundle.classify T.top L⟩ :
          LabObj m (Tower P m) (LabOneTruss C)) ∧
        IsNormal (⟨T.top, L⟩ : LabObj 1 (OpenBundle (towerTot P m T.lower).carrier) C) :=
  succ_isNormal_iff T L

/-- `cons:draft-recursive-normalisation`: the zero equation. -/
theorem w_R7_zero (T : Tower P 0) (L : (towerTot P 0 T).carrier ⥤ C) :
    towerNormalise P 0 T L = ⟨⟨T, L⟩, 𝟙 (⟨T, L⟩ : LabObj 0 (Tower P 0) C)⟩ := rfl

/-- `cons:draft-recursive-normalisation`: the successor equation is `Λ` applied to the
recursive result at the classifier of `ν_T`'s target, **on the nose**. -/
theorem w_R7_succ (T : Tower P (m + 1)) (L : (towerTot P (m + 1) T).carrier ⥤ C) :
    towerNormalise P (m + 1) T L
      = ⟨((lam ⟨T, L⟩).obj ⟨(towerNormalise P m T.lower (succClassifier T L)).1,
            (towerNormalise P m T.lower (succClassifier T L)).2,
            (towerNormalise_isNormalising P m T.lower (succClassifier T L)).1⟩).tgt,
         ((lam ⟨T, L⟩).obj ⟨(towerNormalise P m T.lower (succClassifier T L)).1,
            (towerNormalise P m T.lower (succClassifier T L)).2,
            (towerNormalise_isNormalising P m T.lower (succClassifier T L)).1⟩).map⟩ :=
  rfl

/-- Correctness of the recursion. -/
theorem w_R7_correct (T : Tower P m) (L : (towerTot P m T).carrier ⥤ C) :
    IsNormalising (towerNormalise P m T L).2 :=
  towerNormalise_isNormalising P m T L

/-- All-competitor universality: every labelled coarsening `R` out of `(T, L)` has a unique
labelled coarsening `H` with `R ≫ H = Q` for the returned `Q`. -/
theorem w_R7_universal (T : Tower P m) (L : (towerTot P m T).carrier ⥤ C)
    (D : LabObj m (Tower P m) C) (R : (⟨T, L⟩ : LabObj m (Tower P m) C) ⟶ D)
    (hR : IsCoarsening R.1) :
    ∃! H : D ⟶ (towerNormalise P m T L).1,
      IsCoarsening H.1 ∧ R ≫ H = (towerNormalise P m T L).2 :=
  towerNormalise_universal T L D R hR

/-- `prop:noaut-iteration`, inductive step: the recursive call's label category `B(C)` is
again automorphism-free, so the source's admissible class is closed under the recursion. -/
theorem w_R7_noAut_step (hC : NoAut C) : NoAut (LabOneTruss C) := noAut_labOneTruss hC

/-- `prop:noaut-iteration`: every iterate `B^r(C)` is automorphism-free. -/
theorem w_R7_noAut_iter (hC : NoAut C) (r : ℕ) : @NoAut (iterLab C r).1 (iterLab C r).2 :=
  noAut_iterLab hC r

/-- The source-specialised statement: the chapter runs the recursion over automorphism-free
label categories.  The formal recursion needs no such hypothesis; this witness records the
printed specialisation (the hypothesis is unused). -/
theorem w_R7_noAut (hC : NoAut C) (T : Tower P m) (L : (towerTot P m T).carrier ⥤ C) :
    IsNormalising (towerNormalise P m T L).2 :=
  let _ := hC; towerNormalise_isNormalising P m T L

end Tower

/-! ## R8 — axiom audit -/

#print axioms ThinReflection.adjunction
#print axioms ThinReflection.fullyFaithful
#print axioms ThinReflection.nonempty_isTerminal_obj_iff
#print axioms LabOutCoarse.isNormalising_iff_nonempty_isTerminal
#print axioms topNorm
#print axioms topNorm_isCoarsening
#print axioms topNorm_along_lower
#print axioms succClassifier_along_lower
#print axioms lift
#print axioms lift_isCoarsening
#print axioms lift_comp
#print axioms liftMed
#print axioms phi
#print axioms lam
#print axioms lam_comp_phi
#print axioms lam_phi_map
#print axioms unitHom
#print axioms reflection
#print axioms lamFullyFaithful
#print axioms lam_isNormalising_iff
#print axioms isNormalising_topLab
#print axioms isNormalising_iff_lowLab_of_topLab
#print axioms succ_isNormalising_iff_of_isCoarsening
#print axioms succ_isNormalising_iff
#print axioms succ_isNormal_iff
#print axioms succStep
#print axioms succStep_eq_lam
#print axioms towerNormalise
#print axioms towerNormalise_isNormalising
#print axioms towerNormalise_universal
#print axioms w_R7_succ
#print axioms noAut_labOneTruss
#print axioms noAut_iterLab

/-! ## R8 — proof-route gate -/

-- R3/R5 do not depend on the inductive criterion, the recursion, or the retired direct proof.
#assert_no_dep topNorm_along_lower succ_isNormalising_iff
#assert_no_dep topNorm_along_lower towerNormalise
#assert_no_dep lam_isNormalising_iff succ_isNormalising_iff
#assert_no_dep lam_isNormalising_iff isNormalising_iff_lowLab_of_topLab
#assert_no_dep lam_isNormalising_iff towerNormalise
#assert_no_dep lam_isNormalising_iff towerNormalise_isNormalising
#assert_no_dep lam_isNormalising_iff succ_isNormalising_iff_direct
#assert_no_dep lam_isNormalising_iff isNormalising_of_parts_direct
#assert_no_dep lam_comp_phi succ_isNormalising_iff
#assert_no_dep lam_phi_map succ_isNormalising_iff
#assert_no_dep reflection succ_isNormalising_iff
#assert_dep lam_isNormalising_iff ThinReflection.nonempty_isTerminal_obj_iff
#assert_dep lam_isNormalising_iff lam_comp_phi
#assert_dep lam_isNormalising_iff lam_phi_map
#assert_dep lam_phi_map topNorm_along_lower

-- R6 uses the reflection and not the retired direct proof.
#assert_dep succ_isNormalising_iff lam_isNormalising_iff
#assert_dep succ_isNormalising_iff isNormalising_topLab
#assert_no_dep succ_isNormalising_iff succ_isNormalising_iff_direct
#assert_no_dep succ_isNormalising_iff isNormalising_of_parts_direct
#assert_no_dep succ_isNormalising_iff isNormalising_lowLab_direct
#assert_no_dep succ_isNormalising_iff isNormalising_topLab_direct
#assert_no_dep succ_isNormalising_iff towerNormalise_isNormalising

-- R7: recursive correctness uses R5, not R6 and not the retired direct proof.
#assert_dep towerNormalise_isNormalising lam_isNormalising_iff
#assert_no_dep towerNormalise_isNormalising succ_isNormalising_iff
#assert_no_dep towerNormalise_isNormalising succ_isNormalising_iff_of_isCoarsening
#assert_no_dep towerNormalise_isNormalising isNormalising_iff_lowLab_of_topLab
#assert_no_dep towerNormalise_isNormalising isNormalising_of_parts
#assert_no_dep towerNormalise_isNormalising succ_isNormalising_iff_direct
#assert_no_dep towerNormalise_isNormalising isNormalising_of_parts_direct
#assert_no_dep towerNormalise_universal succ_isNormalising_iff
#assert_no_dep towerNormalise_universal succ_isNormalising_iff_direct
-- the construction itself uses the lift, and no normalisation proof
#assert_dep towerNormalise lift
#assert_no_dep towerNormalise succ_isNormalising_iff
#assert_no_dep towerNormalise lam_isNormalising_iff
-- negative control: the gate does detect a real dependency
/--
error: proof-route gate FAILED: Truss.Transfer.succ_isNormal_iff depends on Truss.Transfer.succ_isNormalising_iff
-/
#guard_msgs in
#assert_no_dep succ_isNormal_iff succ_isNormalising_iff

-- identity normality is the identity case of R6
#assert_dep succ_isNormal_iff succ_isNormalising_iff
#assert_no_dep succ_isNormal_iff succ_isNormalising_iff_direct

end Truss.Transfer.Audit.Reflection
