/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.Section54
import Truss.Transfer.Normalisation.SuccessorTFAE

/-!
# `thm:draft-successor-coarsening` unconditionally (§5.5, row N02)

`SuccessorTFAE.lean` proves the three-way equivalence against the fibrewise characterisation
of bundle coarsenings, taken there as the hypothesis `FibrewiseThmAll` — the form quantified
over **all** finite base posets.  That quantification is not a convenience: the theorem is
proved by induction on the height of the tower, and the induction hypothesis at height `m`
needs the characterisation over `Tot(T_(≤m-1))`, a *different* base.  `Fibrewise.lean` proves
it for an arbitrary finite base, so the hypothesis discharges in one step.

## Main results

* `fibrewiseThmAll` — the hypothesis, discharged.
* `successor_tfae'` — `thm:draft-successor-coarsening` in full: for a morphism `Q = (F,c)` of
  `(m+1)`-truss bundles, being a coarsening, the surjectivity-plus-signature condition, and
  the pair decomposition are equivalent.
-/

universe u

namespace Truss.Transfer

open CategoryTheory TrussLike

/-- The universally quantified fibrewise characterisation, discharged. -/
theorem fibrewiseThmAll : FibrewiseThmAll.{u} :=
  fun B _ _ => fibrewiseThm B

variable {P : FPoset.{u}} {m : ℕ}

/-- **Row `N02` — `thm:draft-successor-coarsening`, in full and unconditionally.** -/
theorem successor_tfae' {T S : Tower P (m + 1)} (Q : T ⟶ S) :
    [IsCoarsening Q,
      Function.Surjective (TowerMap.totHom Q) ∧
        ∀ x, Tower.dimsig P (m + 1) T x ≤ Tower.dimsig P (m + 1) S (TowerMap.totHom Q x),
      IsCoarsening (K := Tower P m) Q.lower ∧
        IsCoarsening (K := OpenBundle (towerTot P m T.lower).carrier) Q.topMap].TFAE :=
  successor_tfae fibrewiseThmAll Q

/-- `(1) → (2)`. -/
theorem tfae_one_to_two' {T S : Tower P m} (Q : T ⟶ S) (hQ : IsCoarsening Q) :
    Function.Surjective (TowerMap.totHom Q) ∧
      ∀ x, Tower.dimsig P m T x ≤ Tower.dimsig P m S (TowerMap.totHom Q x) :=
  surjective_and_dimsig_le_of_isCoarsening Q hQ

/-- `(2) → (3)`, the substantive direction. -/
theorem tfae_two_to_three' {T S : Tower P (m + 1)} (Q : T ⟶ S)
    (hsurj : Function.Surjective (TowerMap.totHom Q))
    (hdim : ∀ x, Tower.dimsig P (m + 1) T x ≤ Tower.dimsig P (m + 1) S (TowerMap.totHom Q x)) :
    IsCoarsening (K := Tower P m) Q.lower ∧
      IsCoarsening (K := OpenBundle (towerTot P m T.lower).carrier) Q.topMap :=
  isCoarsening_of_succ_two fibrewiseThmAll Q hsurj hdim

/-- `(3) → (1)`. -/
theorem tfae_three_to_one' {T S : Tower P (m + 1)} (Q : T ⟶ S)
    (hF : IsCoarsening (K := Tower P m) Q.lower)
    (hc : IsCoarsening (K := OpenBundle (towerTot P m T.lower).carrier) Q.topMap) :
    IsCoarsening Q := isCoarsening_succ_of Q hF hc

/-- The condition-(2) form of being a coarsening, at every height. -/
theorem isCoarsening_iff_two {T S : Tower P m} (Q : T ⟶ S) :
    IsCoarsening Q ↔
      Function.Surjective (TowerMap.totHom Q) ∧
        ∀ x, Tower.dimsig P m T x ≤ Tower.dimsig P m S (TowerMap.totHom Q x) :=
  ⟨tfae_one_to_two' Q, fun h => isCoarsening_of_two fibrewiseThmAll m Q h.1 h.2⟩

end Truss.Transfer
