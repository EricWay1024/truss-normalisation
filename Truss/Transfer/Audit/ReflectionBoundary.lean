/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.RecursiveNorm

/-!
# Boundary probes for the reflection-based normalisation (row `R8`)

Non-vacuity and boundary probes asked for by
[the reflection plan](../../../plan/ReflectionNormalisationVerification.md), row `R8`, at the
three degenerate boundaries of the recursion.  Each probe is a proved statement about the
actual construction; none certifies a universal claim beyond its stated range.

* **Height zero.**  Every labelled map out of a height-`0` labelled tower lands in the source
  itself (`heightZero_out_tgt_eq`), so the identity returned by the recursion is the only
  outgoing coarsening, as `cons:draft-recursive-normalisation` asserts.
* **Empty base.**  Towers over the empty poset exist at every height (`emptyTower`), so the
  theorems are not vacuous there; every labelled tower over the empty base is normal
  (`isNormal_emptyBase`), proved through the new inductive criterion and the §5.4 criterion.
* **Height one.**  At height `1` the recursion's output has identity lower part and top map the
  fixed-base normaliser `ν_T` read through the representative identification, and its top
  component is normalising (`heightOne_*`): the recursion agrees with §5.4 there.
-/

universe u v

namespace Truss.Transfer.Audit.ReflectionBoundary

open CategoryTheory Truss.Transfer TrussLike

variable {C : Type v} [Category.{v} C]

/-! ### Height zero -/

/-- **Height zero: the identity is the only outgoing map.**  A labelled map out of a
height-`0` labelled tower has target equal to the source (the tower is the point over `P`,
and the label equation forces the labels to agree). -/
theorem heightZero_out_tgt_eq {P : FPoset.{u}} (T : Tower P 0)
    (L : (towerTot P 0 T).carrier ⥤ C) (D : LabObj 0 (Tower P 0) C)
    (r : (⟨T, L⟩ : LabObj 0 (Tower P 0) C) ⟶ D) : D = ⟨T, L⟩ := by
  obtain ⟨T', L'⟩ := D
  obtain rfl : T' = T := Subsingleton.elim (α := PUnit) _ _
  obtain rfl : L' = L := r.2.symm
  rfl

/-- The recursion at height zero returns the identity and it is normalising. -/
theorem heightZero_recursion {P : FPoset.{u}} (T : Tower P 0)
    (L : (towerTot P 0 T).carrier ⥤ C) :
    (towerNormalise P 0 T L).2.1 = 𝟙 T ∧ IsNormalising (towerNormalise P 0 T L).2 :=
  ⟨rfl, towerNormalise_isNormalising P 0 T L⟩

/-! ### Empty base -/

/-- The empty finite poset. -/
def emptyP : FPoset.{u} := ⟨PEmpty⟩

/-- The (unique) fibrewise-open 1-truss bundle over an empty base. -/
def OpenBundle.ofIsEmpty (B : Type u) [PartialOrder B] [IsEmpty B] : OpenBundle B where
  fib b := isEmptyElim b
  arr {b} _ := isEmptyElim b
  arr_id b := isEmptyElim b
  arr_comp {b} := isEmptyElim b

/-- Towers over the empty base, at every height, together with emptiness of their total
posets. -/
def emptyTowerAux : ∀ m : ℕ, Σ' T : Tower emptyP.{u} m, IsEmpty (towerTot emptyP m T).carrier
  | 0 => ⟨PUnit.unit, inferInstanceAs (IsEmpty PEmpty)⟩
  | m + 1 =>
    haveI := (emptyTowerAux m).2
    ⟨(emptyTowerAux m).1.succ (OpenBundle.ofIsEmpty _),
      ⟨fun x => (emptyTowerAux m).2.false x.1⟩⟩

/-- **Non-vacuity at the empty base**: a tower over the empty poset at every height. -/
def emptyTower (m : ℕ) : Tower emptyP.{u} m := (emptyTowerAux m).1

/-- The total poset of every tower over the empty base is empty. -/
theorem isEmpty_towerTot_emptyP : ∀ (m : ℕ) (T : Tower emptyP.{u} m),
    IsEmpty (towerTot emptyP m T).carrier
  | 0, _ => inferInstanceAs (IsEmpty PEmpty)
  | m + 1, T => ⟨fun x => (isEmpty_towerTot_emptyP m T.lower).false x.1⟩

/-- **Every labelled tower over the empty base is normal**, at every height and for every
label category: the inductive criterion (`succ_isNormal_iff`, the identity case of the new
`succ_isNormalising_iff`) reduces to the lower tower and to a labelled bundle over an empty
base, whose §5.4 normality criterion holds vacuously. -/
theorem isNormal_emptyBase : ∀ (m : ℕ) {C : Type v} [Category.{v} C]
    (T : Tower emptyP.{u} m) (L : (towerTot emptyP m T).carrier ⥤ C),
    IsNormal (⟨T, L⟩ : LabObj m (Tower emptyP m) C)
  | 0, _, _, T, L => isNormal_zero T L
  | m + 1, _, _, T, L => by
      rw [succ_isNormal_iff]
      refine ⟨isNormal_emptyBase m T.lower _, ?_⟩
      haveI := isEmpty_towerTot_emptyP m T.lower
      rw [OpenBundle.isNormal_iff_sing_eq_closure']
      funext b
      exact isEmptyElim b

/-- At the empty base the recursion's output is normalising (instance of the general
theorem; recorded so that the empty-base instance is exercised by the audit build). -/
theorem emptyBase_recursion (m : ℕ) (L : (towerTot emptyP.{u} m (emptyTower m)).carrier ⥤ C) :
    IsNormalising (towerNormalise emptyP m (emptyTower m) L).2 :=
  towerNormalise_isNormalising emptyP m (emptyTower m) L

/-! ### Height one -/

/-- **Height-one agreement.**  At height `1` the recursion's lower part is the identity of the
base tower, its base map is the identity, and its top map is the fixed-base normaliser `ν_T`
(`succTopMap`, the §5.4 construction) followed by the representative identification. -/
theorem heightOne_lower {P : FPoset.{u}} (T : Tower P 1)
    (L : (towerTot P 1 T).carrier ⥤ C) :
    (towerNormalise P 1 T L).2.1.lower = 𝟙 T.lower ∧
      (towerNormalise P 1 T L).2.1.base = OrderHom.id := ⟨rfl, rfl⟩

/-- Height one: the top map is `ν_T` up to the representative identification. -/
theorem heightOne_topMap {P : FPoset.{u}} (T : Tower P 1)
    (L : (towerTot P 1 T).carrier ⥤ C) :
    ∃ e, (towerNormalise P 1 T L).2.1.topMap = (succTopMap T L).1 ≫ eqToHom e :=
  ⟨_, towerNormalise_succ_topMap T L⟩

/-- Height one: the top component of the recursion's output is a normalising coarsening of
labelled 1-truss bundles over `T_0 = P`, i.e. the recursion restricts to §5.4's
normalisation. -/
theorem heightOne_top_isNormalising {P : FPoset.{u}} (T : Tower P 1)
    (L : (towerTot P 1 T).carrier ⥤ C) :
    IsNormalising (topLab (towerNormalise P 1 T L).2) :=
  isNormalising_topLab _ (towerNormalise_isNormalising P 1 T L)

#print axioms heightZero_out_tgt_eq
#print axioms isNormal_emptyBase
#print axioms emptyBase_recursion
#print axioms heightOne_topMap
#print axioms heightOne_top_isNormalising

end Truss.Transfer.Audit.ReflectionBoundary
