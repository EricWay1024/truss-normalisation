/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.Tower

/-!
# Consecutive blocks of a tower

A tower of height `k + j` splits into its lower `k` layers and a genuine `j`-tower
over their total poset. `Tower.prefix` and `Tower.suffix` perform this splitting.
`Tower.suffix_tot` identifies the total poset of the suffix with the original total
poset. The equality is explicit because the recursive tower presentation does not
make an arbitrary cut definitionally transparent.

`FPoset.transportBundle` and `FPoset.pullLabel` record the transports used at a cut.
The successor equations say exactly how a suffix is obtained by adjoining the
original final bundle after this transport.
-/

universe u v

namespace Truss.Transfer

open CategoryTheory

namespace FPoset

/-- Transport a bundle between equal bundled finite posets. -/
def transportBundle {P Q : FPoset.{u}} (h : P = Q) (A : OpenBundle P.carrier) :
    OpenBundle Q.carrier := h ▸ A

/-- Transporting the base of a bundle preserves its total finite poset. -/
theorem transportBundle_tot {P Q : FPoset.{u}} (h : P = Q)
    (A : OpenBundle P.carrier) :
    (⟨OpenBundle.Tot (transportBundle h A)⟩ : FPoset.{u}) = ⟨OpenBundle.Tot A⟩ := by
  cases h
  rfl

/-- Successive base transports agree with transport along the composite equality. -/
theorem transportBundle_trans {P Q R : FPoset.{u}} (h : P = Q) (g : Q = R)
    (A : OpenBundle P.carrier) :
    transportBundle g (transportBundle h A) = transportBundle (h.trans g) A := by
  cases h
  cases g
  rfl

/-- The functor between the carriers induced by equality of finite posets. -/
def eqFunctor {P Q : FPoset.{u}} (h : P = Q) : P.carrier ⥤ Q.carrier := by
  cases h
  exact 𝟭 _

/-- The functor induced by reflexive equality is the identity functor. -/
@[simp] theorem eqFunctor_refl (P : FPoset.{u}) : eqFunctor (rfl : P = P) = 𝟭 _ := rfl

/-- Equality-induced functors compose according to transitivity of equalities. -/
theorem eqFunctor_trans {P Q R : FPoset.{u}} (h : P = Q) (g : Q = R) :
    eqFunctor h ⋙ eqFunctor g = eqFunctor (h.trans g) := by
  cases h
  cases g
  rfl

/-- Pull a label back along the explicit functor induced by equality of total posets. -/
def pullLabel {P Q : FPoset.{u}} (h : P = Q) {C : Type v} [Category.{v} C]
    (L : Q.carrier ⥤ C) : P.carrier ⥤ C := eqFunctor h ⋙ L

/-- Pulling a label along reflexive equality leaves the label unchanged. -/
@[simp] theorem pullLabel_refl {P : FPoset.{u}} {C : Type v} [Category.{v} C]
    (L : P.carrier ⥤ C) : pullLabel rfl L = L := by
  exact Functor.id_comp L

/-- Successive label pullbacks agree with pullback along the composite equality. -/
theorem pullLabel_trans {P Q R : FPoset.{u}} (h : P = Q) (g : Q = R)
    {C : Type v} [Category.{v} C] (L : R.carrier ⥤ C) :
    pullLabel h (pullLabel g L) = pullLabel (h.trans g) L := by
  cases h
  cases g
  simp only [pullLabel_refl]

end FPoset

namespace Tower

/-- Reindex the height of a tower along an explicit equality of natural numbers. -/
def castHeight {P : FPoset.{u}} {a b : ℕ} (h : a = b) (T : Tower P a) : Tower P b := h ▸ T

/-- Reindexing the height leaves the total poset unchanged. -/
theorem towerTot_castHeight {P : FPoset.{u}} {a b : ℕ} (h : a = b) (T : Tower P a) :
    towerTot P b (castHeight h T) = towerTot P a T := by
  cases h
  rfl

/-- Reindex a label together with the height of its tower using the explicit total equality. -/
def castHeightLabel {P : FPoset.{u}} {a b : ℕ} (h : a = b) (T : Tower P a)
    {C : Type v} [Category.{v} C] (L : (towerTot P a T).carrier ⥤ C) :
    (towerTot P b (castHeight h T)).carrier ⥤ C :=
  FPoset.pullLabel (towerTot_castHeight h T) L

/-- The lower `k` layers of a tower of height `k + j`, obtained by discarding `j` tops. -/
def «prefix» {P : FPoset.{u}} (k : ℕ) : (j : ℕ) → Tower P (k + j) → Tower P k
  | 0, T => T
  | j + 1, T => Tower.prefix k j T.lower

/-- Cutting off no layers leaves the original tower. -/
@[simp] theorem prefix_zero {P : FPoset.{u}} (k : ℕ) (T : Tower P k) :
    Tower.prefix k 0 T = T := rfl

/-- A positive suffix is removed by first discarding the original final bundle. -/
@[simp] theorem prefix_succ {P : FPoset.{u}} (k j : ℕ) (T : Tower P (k + (j + 1))) :
    Tower.prefix k (j + 1) T = Tower.prefix k j T.lower := rfl

/-- Simultaneously construct the upper block and its identification with the original total
poset, so the next successor bundle can be transported along that identification. -/
def suffixPkg {P : FPoset.{u}} (k : ℕ) :
    (j : ℕ) → (T : Tower P (k + j)) →
      { U : Tower (towerTot P k (Tower.prefix k j T)) j //
        towerTot (towerTot P k (Tower.prefix k j T)) j U = towerTot P (k + j) T }
  | 0, _ => ⟨PUnit.unit, rfl⟩
  | j + 1, T =>
      let s := suffixPkg k j T.lower
      ⟨s.1.succ (FPoset.transportBundle s.2.symm T.top),
        FPoset.transportBundle_tot s.2.symm T.top⟩

/-- The upper `j` layers as a genuine tower over the total poset of the lower `k` layers. -/
def suffix {P : FPoset.{u}} (k j : ℕ) (T : Tower P (k + j)) :
    Tower (towerTot P k (Tower.prefix k j T)) j := (suffixPkg k j T).1

/-- The upper block has exactly the original total poset, with the transport made explicit. -/
theorem suffix_tot {P : FPoset.{u}} (k j : ℕ) (T : Tower P (k + j)) :
    towerTot (towerTot P k (Tower.prefix k j T)) j (suffix k j T) =
      towerTot P (k + j) T := (suffixPkg k j T).2

/-- The suffix of height zero is the unique zero tower over the lower total poset. -/
@[simp] theorem suffix_zero {P : FPoset.{u}} (k : ℕ) (T : Tower P k) :
    suffix k 0 T = PUnit.unit := rfl

/-- The lower part of a positive suffix is the suffix of the lower original tower. -/
@[simp] theorem suffix_succ_lower {P : FPoset.{u}} (k j : ℕ)
    (T : Tower P (k + (j + 1))) :
    (suffix k (j + 1) T).lower = suffix k j T.lower := rfl

/-- The top of a positive suffix is the original top bundle, transported along the equality
of the lower total posets. -/
@[simp] theorem suffix_succ_top {P : FPoset.{u}} (k j : ℕ)
    (T : Tower P (k + (j + 1))) :
    (suffix k (j + 1) T).top =
      FPoset.transportBundle (suffix_tot k j T.lower).symm T.top := rfl

/-- At a cut, pull the original label back to the actual total poset of the upper block. -/
def suffixLabel {P : FPoset.{u}} (k j : ℕ) (T : Tower P (k + j))
    {C : Type v} [Category.{v} C] (L : (towerTot P (k + j) T).carrier ⥤ C) :
    (towerTot (towerTot P k (Tower.prefix k j T)) j (suffix k j T)).carrier ⥤ C :=
  FPoset.pullLabel (suffix_tot k j T) L

/-- At a successor cut, the suffix label is exactly the original top label transported
along the total-poset equality for the transported top bundle. -/
theorem suffixLabel_succ {P : FPoset.{u}} (k j : ℕ)
    (T : Tower P (k + (j + 1))) {C : Type v} [Category.{v} C]
    (L : (towerTot P (k + (j + 1)) T).carrier ⥤ C) :
    suffixLabel k (j + 1) T L =
      FPoset.pullLabel
        (FPoset.transportBundle_tot (suffix_tot k j T.lower).symm T.top) L := rfl

/-- Towers obtained by appending bundles agree when their lower towers and their transported
top bundles agree. This is the dependent-pair equality used to reconstruct a cut tower. -/
theorem succ_eq_of_lower_eq {P : FPoset.{u}} {n : ℕ} {T S : Tower P n}
    (h : T = S) (A : OpenBundle (towerTot P n T).carrier)
    (B : OpenBundle (towerTot P n S).carrier)
    (hA : FPoset.transportBundle (congrArg (towerTot P n) h) A = B) :
    T.succ A = S.succ B := by
  cases h
  cases hA
  rfl

/-- Append an upper tower while simultaneously recording the total-poset identification
needed to append its next layer. -/
def appendPkg {P : FPoset.{u}} {k : ℕ} (S : Tower P k) :
    (j : ℕ) → (U : Tower (towerTot P k S) j) →
      { T : Tower P (k + j) // towerTot P (k + j) T = towerTot (towerTot P k S) j U }
  | 0, _ => ⟨S, rfl⟩
  | j + 1, U =>
      let t := appendPkg S j U.lower
      ⟨t.1.succ (FPoset.transportBundle t.2.symm U.top),
        FPoset.transportBundle_tot t.2.symm U.top⟩

/-- Concatenate a lower `k`-tower and an upper `j`-tower over its total poset. -/
def append {P : FPoset.{u}} {k : ℕ} (S : Tower P k) (j : ℕ)
    (U : Tower (towerTot P k S) j) : Tower P (k + j) := (appendPkg S j U).1

/-- The total poset of a concatenation is the total poset of its upper block. -/
theorem append_tot {P : FPoset.{u}} {k : ℕ} (S : Tower P k) (j : ℕ)
    (U : Tower (towerTot P k S) j) :
    towerTot P (k + j) (append S j U) = towerTot (towerTot P k S) j U :=
  (appendPkg S j U).2

/-- Appending a zero tower leaves the lower tower unchanged. -/
@[simp] theorem append_zero {P : FPoset.{u}} {k : ℕ} (S : Tower P k)
    (U : Tower (towerTot P k S) 0) : append S 0 U = S := rfl

/-- Concatenation commutes with truncating the upper block's final bundle. -/
@[simp] theorem append_succ_lower {P : FPoset.{u}} {k : ℕ} (S : Tower P k) (j : ℕ)
    (U : Tower (towerTot P k S) (j + 1)) :
    (append S (j + 1) U).lower = append S j U.lower := rfl

/-- The top bundle in a concatenation is the upper block's original top, transported along
the identification of its lower total poset. -/
@[simp] theorem append_succ_top {P : FPoset.{u}} {k : ℕ} (S : Tower P k) (j : ℕ)
    (U : Tower (towerTot P k S) (j + 1)) :
    (append S (j + 1) U).top =
      FPoset.transportBundle (append_tot S j U.lower).symm U.top := rfl

/-- Splitting a tower and concatenating the two actual blocks reconstructs that tower. -/
theorem append_prefix_suffix {P : FPoset.{u}} (k : ℕ) :
    (j : ℕ) → (T : Tower P (k + j)) →
      append (Tower.prefix k j T) j (suffix k j T) = T
  | 0, _ => rfl
  | j + 1, T => by
      apply succ_eq_of_lower_eq (append_prefix_suffix k j T.lower)
      change FPoset.transportBundle _ (FPoset.transportBundle _
        (FPoset.transportBundle _ T.top)) = T.top
      rw [FPoset.transportBundle_trans, FPoset.transportBundle_trans]
      rfl

end Tower

end Truss.Transfer
