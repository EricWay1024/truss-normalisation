/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.Successor
import Truss.Transfer.Normalisation.BundleLabel
import Truss.Transfer.Normalisation.BundleNorm
import Truss.Transfer.Geometry.OpenBordism

/-!
# `thm:draft-successor-coarsening` in full (§5.5, row `N02`)

`Truss/Transfer/Normalisation/Successor.lean` proves the two easy implications of the
successor decomposition of coarsenings, `(3) → (1)` and `(1) → (2)`, together with the
descent of `(2)` to the lower tower.  This module supplies the remaining implication
`(2) → (3)` and assembles the three-way equivalence.

The one input that is still open is the fibrewise characterisation of bundle coarsenings
(`prop:fibrewise-characterisation-bundle-coarsenings`, §5.4); it is taken here as an
explicit hypothesis `FibrewiseThm`, so that every result below becomes unconditional the
moment that proposition lands.

## Main results

* `Geometry.Bord1.rel_lower`, `Geometry.Bord1.rel_upper` — a 1-truss bordism between **open**
  1-trusses relates lower endpoint to lower endpoint and upper endpoint to upper endpoint.
* `totHom_const_of_zigzagIn` — the heart of `(2) → (3)`: the image under `q_{m+1}` of a
  regular section of the top bundle that is compatible with the arrow bordisms is constant
  along a zigzag inside a point fibre of the base map.
* `topMap_fibMap_lower`, `topMap_fibMap_upper` — the constant images *are* the endpoints of
  the target fibre, so every `c_b` preserves endpoints.
* `surjective_fibMap_of_two`, `isCoarsening_topMap_of_two` — each `c_b` is surjective, hence
  (with the fibrewise theorem) `c` is a coarsening of bundles.
* `isCoarsening_of_two` — `(2) → (1)` at every height, by induction.
* `isCoarsening_of_succ_two` — `(2) → (3)`.
* `successor_tfae` — the three-way equivalence, as a `List.TFAE`, together with the three
  named implications `tfae_one_to_two`, `tfae_two_to_three`, `tfae_three_to_one`.

## On the shape of the fibrewise hypothesis

The chapter's proof is an induction on the height, and the induction hypothesis is used at
*every* lower height: closing `(2) → (1)` at height `m + 1` needs `(2) → (1)` at height `m`,
which — as soon as `m` is itself a successor — needs the fibrewise theorem over the total
poset of a *lower* tower.  A single instance `FibrewiseThm B` for one base `B` is therefore
not enough to run the induction, and the results below take the universally quantified form
`FibrewiseThmAll`, i.e. `FibrewiseThm B` for every finite poset `B`.  `FibrewiseThm` itself
is stated exactly as §5.4 states it.
-/

universe u

namespace Truss.Transfer

open CategoryTheory Geometry Geometry.OneTruss

/-! ### Two face-order facts used throughout -/

/-- Nothing lies strictly below a regular cell of a 1-truss: a face comparison whose target
is regular is an identity. -/
private theorem eq_of_le_of_regular {T : OneTruss} {x y : T.El} (h : x ≤ y)
    (hy : T.IsRegular y) : x = y := by
  rcases OneTruss.le_iff_faceLE.1 h with heq | ⟨-, hy0, -⟩
  · exact heq
  · rw [hy] at hy0
    exact absurd hy0 (by decide)

namespace OpenBundle

variable {B : Type u} [PartialOrder B]

/-- Two comparable points of the total poset of a bundle that lie over the **same** base
point and whose upper fibre component is regular are equal.  This is §5.5's *"two
face-comparable regular elements of `S_m(z)` are equal"*, in the total poset. -/
theorem tot_eq_of_le_of_regular (A : OpenBundle B) {p q : A.Tot} (h : p ≤ q)
    (hb : p.1 = q.1) (hq : (A.fib q.1).toOneTruss.IsRegular q.2) : p = q := by
  obtain ⟨b, x⟩ := p
  obtain ⟨c, y⟩ := q
  simp only at hb
  subst hb
  obtain ⟨_hle, hrel⟩ := h
  exact congrArg _ (eq_of_le_of_regular ((A.arr_id b x y).1 hrel) hq)

/-- Two points of the total poset of a bundle are equal as soon as they lie over the same
base point and their fibre components have the same frame coordinate. -/
theorem tot_eq_of_idx_eq (A : OpenBundle B) {p q : A.Tot} (hb : p.1 = q.1)
    (hidx : (idx p.2).val = (idx q.2).val) : p = q := by
  obtain ⟨b, x⟩ := p
  obtain ⟨c, y⟩ := q
  simp only at hb
  subst hb
  exact congrArg _ (idx_injective (Fin.ext hidx))

end OpenBundle

/-! ### Step 1: a bordism between open 1-trusses relates endpoints to endpoints -/

namespace Geometry.Bord1

variable {T S : OpenTruss}

/-- **Source: §5.5, "the 1-truss bordism from `T_m(b)` to `T_m(b')` relates their respective
lower endpoints".**  Read off the interval formula of `proc:induced-truss-bordism`: the lower
endpoint sits at frame coordinate `0`, and `loNat f 0 = 0`. -/
theorem rel_lower (R : Bord1 T.toOneTruss S.toOneTruss) :
    R.rel T.toOneTruss.lower S.toOneTruss.lower := by
  rw [← induceOpen_singHom R, induceOpen_rel]
  simp [loNat_zero]

/-- **Source: §5.5, the same sentence for upper endpoints.**  The upper endpoint of an open
1-truss sits at frame coordinate `2k`, and `hiNat f (2k) = 2l`. -/
theorem rel_upper (R : Bord1 T.toOneTruss S.toOneTruss) :
    R.rel T.toOneTruss.upper S.toOneTruss.upper := by
  rw [← induceOpen_singHom R, induceOpen_rel]
  have hT : (idx T.toOneTruss.upper).val = 2 * T.numSing := by
    rw [idx_upper, T.len_eq]
  have hS : (idx S.toOneTruss.upper).val = 2 * S.numSing := by
    rw [idx_upper, S.len_eq]
  rw [hT, hS]
  have hhi : hiNat (singHom R) (2 * T.numSing) = 2 * S.numSing :=
    hiNat_of_ge (singHom R) le_rfl
  exact ⟨(loNat_le_hiNat (singHom R) le_rfl).trans hhi.le, hhi.ge⟩

end Geometry.Bord1

/-! ### The fibrewise characterisation, as a hypothesis

`FibrewiseThm` is declared in `BundleNorm.lean`; only the universally-quantified form, which
the induction on the height of the tower needs, is introduced here. -/

/-- The universally quantified form of `FibrewiseThm`, which is what the induction on the
height of the tower needs; see the module docstring. -/
abbrev FibrewiseThmAll : Prop :=
  ∀ (B : Type u) [PartialOrder B] [Finite B], FibrewiseThm B

/-! ### Step 2: the endpoint images are constant on a point fibre of the base map -/

variable {P : FPoset.{u}} {m : ℕ}

/-- **Source: §5.5, proof of `(2) → (3)`, the constancy argument.**

Let `e` be a choice of a *regular* cell in each fibre of the top bundle of `T` which the
arrow bordisms relate to each other (the two instances are the lower and the upper
endpoints, by `Geometry.Bord1.rel_lower` and `Geometry.Bord1.rel_upper`).  Then the image of
`(b, e b)` under `q_{m+1}` is constant as `b` runs along a zigzag inside a point fibre of the
base map `f`.

The single step is the chapter's: for `b ≤ b'` the two points are comparable in `Tot(T_{m+1})`,
so their images are comparable; the images lie over the same point of `S_m`, and both are
regular by `topMap_preserves_regular_of`; and two face-comparable regular cells are equal. -/
theorem totHom_const_of_zigzagIn {T S : Tower P (m + 1)} (Q : T ⟶ S)
    (hdim : ∀ x, Tower.dimsig P (m + 1) T x
      ≤ Tower.dimsig P (m + 1) S (TowerMap.totHom Q x))
    (e : ∀ b : (towerTot P m T.lower).carrier, (T.top.fib b).toOneTruss.El)
    (hreg : ∀ b, (T.top.fib b).toOneTruss.IsRegular (e b))
    (hrel : ∀ {b c : (towerTot P m T.lower).carrier} (h : b ≤ c),
      (T.top.arr h).rel (e b) (e c))
    {z : (towerTot P m S.lower).carrier} {b₁ b₂ : (towerTot P m T.lower).carrier}
    (hzz : ZigzagIn (pointFibre Q.base z) b₁ b₂) :
    TowerMap.totHom Q ⟨b₁, e b₁⟩ = TowerMap.totHom Q ⟨b₂, e b₂⟩ := by
  have hregimg : ∀ b : (towerTot P m T.lower).carrier,
      (S.top.fib (TowerMap.totHom Q (⟨b, e b⟩ : OpenBundle.Tot T.top)).1).toOneTruss.IsRegular
        (TowerMap.totHom Q (⟨b, e b⟩ : OpenBundle.Tot T.top)).2 :=
    fun b => topMap_preserves_regular_of Q hdim b (e b) (hreg b)
  induction hzz with
  | refl => rfl
  | @tail c d _ hstep ih =>
      refine ih.trans ?_
      obtain ⟨hc, hd, hcd⟩ := hstep
      have hcz : Q.base c = z := hc
      have hdz : Q.base d = z := hd
      have hfst : (TowerMap.totHom Q (⟨c, e c⟩ : OpenBundle.Tot T.top)).1
          = (TowerMap.totHom Q (⟨d, e d⟩ : OpenBundle.Tot T.top)).1 := by
        change Q.base c = Q.base d
        rw [hcz, hdz]
      rcases hcd with h | h
      · have hle : TowerMap.totHom Q (⟨c, e c⟩ : OpenBundle.Tot T.top)
            ≤ TowerMap.totHom Q (⟨d, e d⟩ : OpenBundle.Tot T.top) :=
          (TowerMap.totHom Q).monotone ⟨h, hrel h⟩
        exact S.top.tot_eq_of_le_of_regular hle hfst (hregimg d)
      · have hle : TowerMap.totHom Q (⟨d, e d⟩ : OpenBundle.Tot T.top)
            ≤ TowerMap.totHom Q (⟨c, e c⟩ : OpenBundle.Tot T.top) :=
          (TowerMap.totHom Q).monotone ⟨h, hrel h⟩
        exact (S.top.tot_eq_of_le_of_regular hle hfst.symm (hregimg c)).symm

/-! ### Step 3: the constant images are the endpoints -/

/-- **Source: §5.5, "surjectivity of `q_{m+1}` and frame monotonicity force these two
constant images to be the two endpoints of `S_m(z)`", lower half.**

Surjectivity produces a point of `T_{m+1}` over the lower endpoint of `S_m(z)`; frame
monotonicity of the fibre map there pushes the lower endpoint of its own fibre onto frame
coordinate `0`, i.e. onto the lower endpoint; and constancy along the zigzag transports the
conclusion to every `b` in the point fibre. -/
theorem topMap_fibMap_lower {T S : Tower P (m + 1)} (Q : T ⟶ S)
    (hbase : IsPosetCoarsening Q.base)
    (hsurj : Function.Surjective (TowerMap.totHom Q))
    (hdim : ∀ x, Tower.dimsig P (m + 1) T x
      ≤ Tower.dimsig P (m + 1) S (TowerMap.totHom Q x))
    (b : (towerTot P m T.lower).carrier) :
    Q.topMap.fibMap b (T.top.fib b).toOneTruss.lower
      = (S.top.fib (Q.base b)).toOneTruss.lower := by
  set z : (towerTot P m S.lower).carrier := Q.base b with hz
  set e : ∀ c : (towerTot P m T.lower).carrier, (T.top.fib c).toOneTruss.El :=
    fun c => (T.top.fib c).toOneTruss.lower with he
  -- a point of `T_{m+1}` over the lower endpoint of `S_m(z)`
  obtain ⟨x, hx⟩ := hsurj (⟨z, (S.top.fib z).toOneTruss.lower⟩ : OpenBundle.Tot S.top)
  have hx1 : Q.base x.1 = z := congrArg (fun p : OpenBundle.Tot S.top => p.1) hx
  have hxidx : (idx (Q.topMap.fibMap x.1 x.2)).val = 0 := by
    have := congrArg (fun p : OpenBundle.Tot S.top => (idx p.2).val) hx
    simpa using this
  -- at that point the lower endpoint already goes to the lower endpoint
  have hbase0 : TowerMap.totHom Q (⟨x.1, e x.1⟩ : OpenBundle.Tot T.top)
      = (⟨z, (S.top.fib z).toOneTruss.lower⟩ : OpenBundle.Tot S.top) := by
    refine S.top.tot_eq_of_idx_eq hx1 ?_
    have hle : (idx (Q.topMap.fibMap x.1 (e x.1))).val
        ≤ (idx (Q.topMap.fibMap x.1 x.2)).val :=
      (Q.topMap.fibMap x.1).idx_map_lower_le x.2
    rw [hxidx] at hle
    simpa using Nat.le_antisymm hle (Nat.zero_le _)
  -- constancy along the zigzag joining `b` to `x.1`
  have hconst := totHom_const_of_zigzagIn Q hdim e
    (fun c => (T.top.fib c).isOpen.1) (fun {c d} h => Geometry.Bord1.rel_lower (T.top.arr h))
    (hbase.pointFibre_connected z b (by simpa using hz.symm) x.1 (by simpa using hx1))
  have hfinal : (⟨z, Q.topMap.fibMap b (e b)⟩ : OpenBundle.Tot S.top)
      = ⟨z, (S.top.fib z).toOneTruss.lower⟩ := hconst.trans hbase0
  exact OpenBundle.tot_mk_inj (A := S.top) (b := z) hfinal

/-- **Source: §5.5, the same sentence, upper half.** -/
theorem topMap_fibMap_upper {T S : Tower P (m + 1)} (Q : T ⟶ S)
    (hbase : IsPosetCoarsening Q.base)
    (hsurj : Function.Surjective (TowerMap.totHom Q))
    (hdim : ∀ x, Tower.dimsig P (m + 1) T x
      ≤ Tower.dimsig P (m + 1) S (TowerMap.totHom Q x))
    (b : (towerTot P m T.lower).carrier) :
    Q.topMap.fibMap b (T.top.fib b).toOneTruss.upper
      = (S.top.fib (Q.base b)).toOneTruss.upper := by
  set z : (towerTot P m S.lower).carrier := Q.base b with hz
  set e : ∀ c : (towerTot P m T.lower).carrier, (T.top.fib c).toOneTruss.El :=
    fun c => (T.top.fib c).toOneTruss.upper with he
  obtain ⟨x, hx⟩ := hsurj (⟨z, (S.top.fib z).toOneTruss.upper⟩ : OpenBundle.Tot S.top)
  have hx1 : Q.base x.1 = z := congrArg (fun p : OpenBundle.Tot S.top => p.1) hx
  have hxidx : (idx (Q.topMap.fibMap x.1 x.2)).val
      = (idx (S.top.fib z).toOneTruss.upper).val := by
    have := congrArg (fun p : OpenBundle.Tot S.top => (idx p.2).val) hx
    simpa using this
  have hbase0 : TowerMap.totHom Q (⟨x.1, e x.1⟩ : OpenBundle.Tot T.top)
      = (⟨z, (S.top.fib z).toOneTruss.upper⟩ : OpenBundle.Tot S.top) := by
    refine S.top.tot_eq_of_idx_eq hx1 ?_
    have hle : (idx (Q.topMap.fibMap x.1 x.2)).val
        ≤ (idx (Q.topMap.fibMap x.1 (e x.1))).val :=
      (Q.topMap.fibMap x.1).idx_map_le_upper x.2
    rw [hxidx] at hle
    have h1 : (idx (Q.topMap.fibMap x.1 (e x.1))).val
        ≤ (idx (S.top.fib (Q.base x.1)).toOneTruss.upper).val :=
      idx_le_upper (T := (S.top.fib (Q.base x.1)).toOneTruss) _
    have h2 : (idx (S.top.fib (Q.base x.1)).toOneTruss.upper).val
        = (idx (S.top.fib z).toOneTruss.upper).val :=
      congrArg (fun p : OpenBundle.Tot S.top =>
        (idx (S.top.fib p.1).toOneTruss.upper).val) hx
    change (idx (Q.topMap.fibMap x.1 (e x.1))).val = (idx (S.top.fib z).toOneTruss.upper).val
    omega
  have hconst := totHom_const_of_zigzagIn Q hdim e
    (fun c => (T.top.fib c).isOpen.2) (fun {c d} h => Geometry.Bord1.rel_upper (T.top.arr h))
    (hbase.pointFibre_connected z b (by simpa using hz.symm) x.1 (by simpa using hx1))
  have hfinal : (⟨z, Q.topMap.fibMap b (e b)⟩ : OpenBundle.Tot S.top)
      = ⟨z, (S.top.fib z).toOneTruss.upper⟩ := hconst.trans hbase0
  exact OpenBundle.tot_mk_inj (A := S.top) (b := z) hfinal

/-- **Source: §5.5, "by `lem:truss-map-surjective-iff-endpoints`, each `c_b` is
surjective".**  G03 turns endpoint preservation into surjectivity. -/
theorem surjective_fibMap_of_two {T S : Tower P (m + 1)} (Q : T ⟶ S)
    (hbase : IsPosetCoarsening Q.base)
    (hsurj : Function.Surjective (TowerMap.totHom Q))
    (hdim : ∀ x, Tower.dimsig P (m + 1) T x
      ≤ Tower.dimsig P (m + 1) S (TowerMap.totHom Q x))
    (b : (towerTot P m T.lower).carrier) :
    Function.Surjective (Q.topMap.fibMap b).toFun :=
  (Geometry.TrussMap.surjective_iff_endpoints (Q.topMap.fibMap b)).2
    ⟨topMap_fibMap_lower Q hbase hsurj hdim b, topMap_fibMap_upper Q hbase hsurj hdim b⟩

/-- **Source: §5.5, `(2) → (3)`, upper half.**  Each `c_b` is surjective (Step 3) and
preserves regular cells (`topMap_preserves_regular_of`), hence is a coarsening of open
1-trusses by T02; the fibrewise theorem then makes `c` a coarsening of bundles. -/
theorem isCoarsening_topMap_of_two {T S : Tower P (m + 1)}
    (hFib : FibrewiseThm (towerTot P m T.lower).carrier) (Q : T ⟶ S)
    (hbase : IsPosetCoarsening Q.base)
    (hsurj : Function.Surjective (TowerMap.totHom Q))
    (hdim : ∀ x, Tower.dimsig P (m + 1) T x
      ≤ Tower.dimsig P (m + 1) S (TowerMap.totHom Q x)) :
    IsCoarsening (K := OpenBundle (towerTot P m T.lower).carrier) Q.topMap := by
  refine hFib Q.topMap fun b => ?_
  rw [isCoarsening_iff_surjective_regular]
  exact ⟨surjective_fibMap_of_two Q hbase hsurj hdim b,
    fun i hi => topMap_preserves_regular_of Q hdim b i hi⟩

/-! ### Step 4: the induction -/

/-- **Source: `thm:draft-successor-coarsening`, `(2) → (1)` (§5.5).**  By induction on the
height.  At height zero the top total map is the identity of `B`.  At height `m + 1` the
hypothesis `(2)` descends to the lower tower (`surjective_lower_of`, `dimsig_le_lower_of`),
so the induction hypothesis makes `F` a coarsening; `isCoarsening_topMap_of_two` makes `c` a
coarsening; and `isCoarsening_succ_of` — the already-proved `(3) → (1)` — concludes. -/
theorem isCoarsening_of_two (hFib : FibrewiseThmAll.{u}) :
    ∀ (m : ℕ) {T S : Tower P m} (Q : T ⟶ S),
      Function.Surjective (TowerMap.totHom Q) →
      (∀ x, Tower.dimsig P m T x ≤ Tower.dimsig P m S (TowerMap.totHom Q x)) →
      IsCoarsening Q
  | 0, _, _, Q, _, _ => by
      refine ⟨?_, fun _ i => i.elim0⟩
      rw [Tower.totMap_eq]
      exact IsPosetCoarsening.id
  | m + 1, T, S, Q, hsurj, hdim => by
      have hF : IsCoarsening (K := Tower P m) Q.lower :=
        isCoarsening_of_two hFib m Q.lower (surjective_lower_of Q hsurj)
          (dimsig_le_lower_of Q hdim)
      have hbase : IsPosetCoarsening Q.base := by
        have h := hF.tot
        rw [Tower.totMap_eq, Q.base_eq] at h
        exact h
      exact isCoarsening_succ_of Q hF
        (isCoarsening_topMap_of_two (hFib _) Q hbase hsurj hdim)

/-- **Source: `thm:draft-successor-coarsening`, `(2) → (3)` (§5.5).** -/
theorem isCoarsening_of_succ_two (hFib : FibrewiseThmAll.{u}) {T S : Tower P (m + 1)}
    (Q : T ⟶ S) (hsurj : Function.Surjective (TowerMap.totHom Q))
    (hdim : ∀ x, Tower.dimsig P (m + 1) T x
      ≤ Tower.dimsig P (m + 1) S (TowerMap.totHom Q x)) :
    IsCoarsening (K := Tower P m) Q.lower ∧
      IsCoarsening (K := OpenBundle (towerTot P m T.lower).carrier) Q.topMap := by
  have hF : IsCoarsening (K := Tower P m) Q.lower :=
    isCoarsening_of_two hFib m Q.lower (surjective_lower_of Q hsurj)
      (dimsig_le_lower_of Q hdim)
  have hbase : IsPosetCoarsening Q.base := by
    have h := hF.tot
    rw [Tower.totMap_eq, Q.base_eq] at h
    exact h
  exact ⟨hF, isCoarsening_topMap_of_two (hFib _) Q hbase hsurj hdim⟩

/-! ### The three-way equivalence -/

/-- `(1) → (2)`, restated at a successor height for the cycle. -/
theorem tfae_one_to_two {T S : Tower P (m + 1)} (Q : T ⟶ S) (hQ : IsCoarsening Q) :
    Function.Surjective (TowerMap.totHom Q) ∧
      ∀ x, Tower.dimsig P (m + 1) T x
        ≤ Tower.dimsig P (m + 1) S (TowerMap.totHom Q x) :=
  surjective_and_dimsig_le_of_isCoarsening Q hQ

/-- `(2) → (3)`, restated for the cycle. -/
theorem tfae_two_to_three (hFib : FibrewiseThmAll.{u}) {T S : Tower P (m + 1)} (Q : T ⟶ S)
    (h : Function.Surjective (TowerMap.totHom Q) ∧
      ∀ x, Tower.dimsig P (m + 1) T x
        ≤ Tower.dimsig P (m + 1) S (TowerMap.totHom Q x)) :
    IsCoarsening (K := Tower P m) Q.lower ∧
      IsCoarsening (K := OpenBundle (towerTot P m T.lower).carrier) Q.topMap :=
  isCoarsening_of_succ_two hFib Q h.1 h.2

/-- `(3) → (1)`, restated for the cycle. -/
theorem tfae_three_to_one {T S : Tower P (m + 1)} (Q : T ⟶ S)
    (h : IsCoarsening (K := Tower P m) Q.lower ∧
      IsCoarsening (K := OpenBundle (towerTot P m T.lower).carrier) Q.topMap) :
    IsCoarsening Q :=
  isCoarsening_succ_of Q h.1 h.2

/-- **`thm:draft-successor-coarsening` (§5.5, row `N02`).**  For a morphism
`Q = (F, c)` of levelwise-open `(m+1)`-truss bundle towers over a finite poset, the
following are equivalent:

1. `Q` is a coarsening;
2. `q_{m+1} = Tot(Q)` is surjective and does not decrease the dimension signature;
3. `F` is a coarsening of `m`-towers and `c` is a coarsening of 1-truss bundles over `T_m`.

Conditional on the fibrewise characterisation of bundle coarsenings only. -/
theorem successor_tfae (hFib : FibrewiseThmAll.{u}) {T S : Tower P (m + 1)} (Q : T ⟶ S) :
    [IsCoarsening Q,
      Function.Surjective (TowerMap.totHom Q) ∧
        ∀ x, Tower.dimsig P (m + 1) T x
          ≤ Tower.dimsig P (m + 1) S (TowerMap.totHom Q x),
      IsCoarsening (K := Tower P m) Q.lower ∧
        IsCoarsening (K := OpenBundle (towerTot P m T.lower).carrier) Q.topMap].TFAE := by
  tfae_have 1 → 2 := tfae_one_to_two Q
  tfae_have 2 → 3 := tfae_two_to_three hFib Q
  tfae_have 3 → 1 := tfae_three_to_one Q
  tfae_finish

end Truss.Transfer
