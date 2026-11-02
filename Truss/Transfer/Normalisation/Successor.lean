/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.Tower

/-!
# Successor decomposition of coarsenings (§5.5, row `N02`), unconditional half

This module formalises the parts of `thm:draft-successor-coarsening` that do **not** depend
on `prop:fibrewise-characterisation-bundle-coarsenings` (which is open): the implication
`(3) → (1)`, the implication `(1) → (2)`, and the descent of condition `(2)` to the lower
tower together with its last-coordinate reading as fibrewise regularity preservation.

## Main results

* `OpenBundle.isPosetCoarsening_tildeHom` — the geometric input to `(3) → (1)`: if
  `f : B' →o B` is a poset coarsening then so is `f̃ : Tot(f^*A) →o Tot(A)`.
* `isCoarsening_succ_of` — `(3) → (1)`.
* `surjective_and_dimsig_le_of_isCoarsening` — `(1) → (2)`.
* `surjective_lower_of`, `dimsig_le_lower_of` — the descent of `(2)` to the lower tower.
* `topMap_preserves_regular_of` — the last coordinate of `(2)` makes every `c_b` preserve
  regular cells.

## The pullback square used for `f̃`

The chapter says that `f̃ : Tot(f^*A) → Tot(A)` *is* the pullback of `f` along the bundle
projection `ρ : Tot(A) → B`, and then invokes `prop:draft-poset-coarsening-properties` (3).
In the formalisation this has to be said with the two projections named.  The square is

```
Tot(f^* A) --f̃--> Tot(A)
    | r               | ρ
    v                 v
    B' ------f------> B
```

so `f̃` is the projection of the pullback of `f` along `ρ` **onto the `Tot(A)` factor**.  In
the `Pullback q f` notation of `Truss.Transfer.Poset` (whose `pullbackSnd q f` is the
pullback of `q` along `f`) one must therefore take `q := f` and `f := ρ`, giving
`pullbackSnd f ρ : Pullback f ρ →o Tot(A)`; the hypothesis of
`IsPosetCoarsening.pullback_proj` is then exactly `IsPosetCoarsening f`, which is what we
have.  With the other arrangement, `Pullback ρ f`, the map corresponding to `f̃` would be
`pullbackFst`, and `pullback_proj` would ask for `ρ` to be a coarsening, which is false in
general.  So route (i) of the task goes through with the square `Pullback f ρ`; see
`OpenBundle.reindexTotOrderIso`.
-/

universe u v

namespace Truss.Transfer

open CategoryTheory Geometry Geometry.OneTruss

/-! ### Order isomorphisms are poset coarsenings -/

/-- An order isomorphism, viewed as a monotone map, is a poset coarsening: it is bijective,
open (transport a comparison through the inverse), and each of its arrow fibres is a
singleton, hence zigzag connected. -/
theorem IsPosetCoarsening.of_orderIso {α : Type u} {β : Type v} [PartialOrder α]
    [PartialOrder β] (e : α ≃o β) : IsPosetCoarsening (⟨e, e.monotone⟩ : α →o β) := by
  have hopen : IsOpenPosetMap (e : α → β) := by
    rw [isOpenPosetMap_iff_exists_le e.monotone]
    intro y z hz
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    simpa using e.symm.monotone hz
  refine ⟨e.surjective, hopen, ?_⟩
  intro y y' _ a ha b hb
  have hsrc : a.src = b.src := e.injective (ha.1.trans hb.1.symm)
  have htgt : a.tgt = b.tgt := e.injective (ha.2.trans hb.2.symm)
  have : a = b := Arr.ext hsrc htgt
  subst this
  exact ZigzagIn.refl _

/-! ### `f̃` as a pullback projection -/

namespace OpenBundle

variable {B B' : Type u} [PartialOrder B] [PartialOrder B']

/-- **Source: `prop:reindexing-total-space` (Chapter 2).**  The pullback presentation of the
total poset of a reindexed bundle: `Tot(f^* A) ≅ {(b, s) ∈ B' × Tot(A) | f b = ρ s}`, with
the induced product order.  The forward map is `(b, v) ↦ (b, (f b, v))`. -/
def reindexTotOrderIso (f : B' →o B) (A : OpenBundle B) :
    (reindex f A).Tot ≃o Pullback f A.proj where
  toFun p := ⟨p.1, ⟨f p.1, p.2⟩, rfl⟩
  invFun a := ⟨a.fst, cast (congrArg (fun b => (A.fib b).toOneTruss.El) a.compat.symm) a.snd.2⟩
  left_inv p := by cases p; rfl
  right_inv a := by
    obtain ⟨b, ⟨z, v⟩, h⟩ := a
    cases h
    rfl
  map_rel_iff' := by
    intro p q
    constructor
    · rintro ⟨hb, _, hrel⟩
      exact ⟨hb, hrel⟩
    · rintro ⟨hb, hrel⟩
      exact ⟨hb, f.monotone hb, hrel⟩

/-- `f̃` is the composite of the pullback presentation with the projection onto `Tot(A)`. -/
theorem tildeHom_eq_pullbackSnd (f : B' →o B) (A : OpenBundle B) :
    tildeHom f A
      = (pullbackSnd f A.proj).comp ⟨reindexTotOrderIso f A, (reindexTotOrderIso f A).monotone⟩ :=
  rfl

/-- **(A) Source: §5.5, proof of `(3) → (1)`.**  If `f` is a poset coarsening then so is
`f̃ : Tot(f^* A) →o Tot(A)`, because `f̃` is the pullback of `f` along the bundle projection
`ρ : Tot(A) →o B` (see the module docstring for the direction of the square). -/
theorem isPosetCoarsening_tildeHom (f : B' →o B) (hf : IsPosetCoarsening f)
    (A : OpenBundle B) : IsPosetCoarsening (tildeHom f A) := by
  rw [tildeHom_eq_pullbackSnd]
  exact (IsPosetCoarsening.of_orderIso (reindexTotOrderIso f A)).comp (hf.pullback_proj A.proj)

end OpenBundle

/-! ### Bridges between the two spellings of the total map -/

section Bridges

variable {P : FPoset.{u}} {m : ℕ}

/-- The truss-like total map of a tower map is its `TowerMap.totHom`. -/
theorem Tower.totMap_eq {T S : Tower P m} (Q : T ⟶ S) :
    (TrussLike.totMap Q : (towerTot P m T).carrier →o (towerTot P m S).carrier)
      = TowerMap.totHom Q := rfl

/-- The truss-like total map of a bundle map is its `BundleMap.totHom`. -/
theorem OpenBundle.totMap_eq {B : Type u} [PartialOrder B] [Finite B] {A A' : OpenBundle B}
    (q : A ⟶ A') : (TrussLike.totMap q : A.Tot →o A'.Tot) = BundleMap.totHom q := rfl

end Bridges

/-! ### (B) `(3) → (1)` -/

/-- **(B) Source: `thm:draft-successor-coarsening`, `(3) → (1)` (§5.5).**  If the lower
component `F` of `Q = (F, c)` is a coarsening of `m`-towers and the top component `c` is a
coarsening of 1-truss bundles over `T_m`, then `Q` is a coarsening of `(m+1)`-towers.

The poset half is `q_{m+1} = f̃ ∘ Tot(c)` (`TowerMap.totHom_eq_succ`) together with
`OpenBundle.isPosetCoarsening_tildeHom` and `IsPosetCoarsening.comp`; the dimension half is
`Tower.dimsig_succ_split`, whose first `m` coordinates come from `F` and whose last
coordinate comes from `c`, the fibre of `f^* S_{m+1}` over `b` being the fibre of `S_{m+1}`
over `f b`. -/
theorem isCoarsening_succ_of {P : FPoset.{u}} {m : ℕ} {T S : Tower P (m + 1)} (Q : T ⟶ S)
    (hF : IsCoarsening (K := Tower P m) Q.lower)
    (hc : IsCoarsening (K := OpenBundle (towerTot P m T.lower).carrier) Q.topMap) :
    IsCoarsening Q := by
  have hbase : IsPosetCoarsening Q.base := by
    have h := hF.tot
    rw [Tower.totMap_eq, Q.base_eq] at h
    exact h
  have htop : IsPosetCoarsening Q.topMap.totHom := by
    have h := hc.tot
    rw [OpenBundle.totMap_eq] at h
    exact h
  refine ⟨?_, ?_⟩
  · rw [Tower.totMap_eq, TowerMap.totHom_eq_succ]
    exact htop.comp (OpenBundle.isPosetCoarsening_tildeHom Q.base hbase S.top)
  · intro x i
    rw [Tower.totMap_eq]
    change Tower.dimsig P (m + 1) T x i ≤ Tower.dimsig P (m + 1) S (TowerMap.totHom Q x) i
    refine Fin.lastCases ?_ ?_ i
    · rw [Tower.dimsig_succ_last, Tower.dimsig_succ_last]
      exact hc.dimsig_le x 0
    · intro j
      rw [Tower.dimsig_succ_castSucc, Tower.dimsig_succ_castSucc]
      have h := hF.dimsig_le x.1 j
      rw [Tower.totMap_eq, Q.base_eq] at h
      exact h

/-! ### (C) `(1) → (2)` -/

/-- **(C) Source: `thm:draft-successor-coarsening`, `(1) → (2)` (§5.5).**  A coarsening of
towers has surjective top total map and does not decrease the dimension signature.  This is
immediate from `def:draft-coarsening`; it is stated because it is a clause of the theorem. -/
theorem surjective_and_dimsig_le_of_isCoarsening {P : FPoset.{u}} {m : ℕ} {T S : Tower P m}
    (Q : T ⟶ S) (hQ : IsCoarsening Q) :
    Function.Surjective (TowerMap.totHom Q) ∧
      ∀ x, Tower.dimsig P m T x ≤ Tower.dimsig P m S (TowerMap.totHom Q x) := by
  refine ⟨?_, fun x i => ?_⟩
  · have h := hQ.tot.surjective
    rwa [Tower.totMap_eq] at h
  · have h := hQ.dimsig_le x i
    rwa [Tower.totMap_eq] at h

/-! ### (D) condition `(2)` descends to the lower tower -/

/-- **(D) Source: `thm:draft-successor-coarsening`, "`(2)` in the `(m+1)`-case descends easily
to `(2)` in the `m`-case" (§5.5), surjectivity half.**  The fibres of an open 1-truss bundle
are nonempty, so the projection `Tot(S_{m+1}) → S_m` is surjective; since
`q_{m+1}(b, x) = (f b, c_b x)`, surjectivity of `q_{m+1}` forces surjectivity of `f`. -/
theorem surjective_lower_of {P : FPoset.{u}} {m : ℕ} {T S : Tower P (m + 1)} (Q : T ⟶ S)
    (hsurj : Function.Surjective (TowerMap.totHom Q)) :
    Function.Surjective (TowerMap.totHom Q.lower) := by
  intro z
  obtain ⟨w⟩ := (inferInstance : Nonempty (S.top.fib z).toOneTruss.El)
  obtain ⟨x, hx⟩ := hsurj ⟨z, w⟩
  refine ⟨x.1, ?_⟩
  rw [Q.base_eq]
  exact congrArg Sigma.fst hx

/-- **(D) Source: same sentence, dimension half.**  Evaluating the `(m+1)`-dimensional
inequality at a point of the (nonempty) fibre over `b` and reading off the first `m`
coordinates gives the `m`-dimensional inequality. -/
theorem dimsig_le_lower_of {P : FPoset.{u}} {m : ℕ} {T S : Tower P (m + 1)} (Q : T ⟶ S)
    (hdim : ∀ x, Tower.dimsig P (m + 1) T x ≤ Tower.dimsig P (m + 1) S (TowerMap.totHom Q x)) :
    ∀ b, Tower.dimsig P m T.lower b ≤ Tower.dimsig P m S.lower (TowerMap.totHom Q.lower b) := by
  intro b j
  obtain ⟨y⟩ := (inferInstance : Nonempty (T.top.fib b).toOneTruss.El)
  have h := hdim ⟨b, y⟩ j.castSucc
  rw [Tower.dimsig_succ_castSucc, Tower.dimsig_succ_castSucc] at h
  rw [Q.base_eq]
  exact h

/-! ### (E) the last coordinate is fibrewise regularity preservation -/

/-- **(E) Source: `thm:draft-successor-coarsening`, "restricting the `dimsig` inequality to
the last coordinate makes each `c_b` preserve regular elements" (§5.5).**

Note the spelling of the target fibre: `Q.topMap` lands in `Q.base^* S_{m+1}`, and
`Q.base` is only *propositionally* equal to `Tot(Q.lower)` (`TowerMap.base_eq` is stored
data, not a definitional identity), so the statement has to be phrased with `Q.base`.  For
the definitionally-equal spelling in the successor presentation see
`topMap_preserves_regular_of_succ`. -/
theorem topMap_preserves_regular_of {P : FPoset.{u}} {m : ℕ} {T S : Tower P (m + 1)}
    (Q : T ⟶ S)
    (hdim : ∀ x, Tower.dimsig P (m + 1) T x ≤ Tower.dimsig P (m + 1) S (TowerMap.totHom Q x))
    (b : (towerTot P m T.lower).carrier) (x : (T.top.fib b).toOneTruss.El)
    (hx : (T.top.fib b).toOneTruss.IsRegular x) :
    ((OpenBundle.reindex Q.base S.top).fib b).toOneTruss.IsRegular (Q.topMap.fibMap b x) := by
  have h := hdim ⟨b, x⟩ (Fin.last m)
  rw [Tower.dimsig_succ_last, Tower.dimsig_succ_last, hx] at h
  have h' : (1 : Fin 2)
      ≤ (S.top.fib (Q.base b)).toOneTruss.dim (Q.topMap.fibMap b x) := h
  change (S.top.fib (Q.base b)).toOneTruss.dim (Q.topMap.fibMap b x) = 1
  rcases OneTruss.eq_zero_or_one
      ((S.top.fib (Q.base b)).toOneTruss.dim (Q.topMap.fibMap b x)) with h0 | h1
  · rw [h0] at h'; exact absurd h' (by decide)
  · exact h1

/-- **(E), successor presentation.**  For `Q = (F, c)` built by `TowerMap.succ`, the base map
is `Tot(F)` definitionally, so the conclusion can be stated with `F.totHom`. -/
theorem topMap_preserves_regular_of_succ {P : FPoset.{u}} {m : ℕ} {T S : Tower P (m + 1)}
    (F : TowerMap P m T.lower S.lower)
    (c : BundleMap T.top (OpenBundle.reindex F.totHom S.top))
    (hdim : ∀ x, Tower.dimsig P (m + 1) T x
      ≤ Tower.dimsig P (m + 1) S (TowerMap.totHom (TowerMap.succ F c) x))
    (b : (towerTot P m T.lower).carrier) (x : (T.top.fib b).toOneTruss.El)
    (hx : (T.top.fib b).toOneTruss.IsRegular x) :
    ((OpenBundle.reindex F.totHom S.top).fib b).toOneTruss.IsRegular (c.fibMap b x) :=
  topMap_preserves_regular_of (TowerMap.succ F c) hdim b x hx

end Truss.Transfer
