/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.Bundle

/-!
# The open `n`-truss bundle tower and its dimension signature (§5.5)

Chapter 2 defines a total-space `n`-truss bundle over a poset `B` **recursively**
(`def:total-space-n-bundle`): a `0`-bundle is the trivial tower with `T_0 = B`, and an
`(n+1)`-bundle is an `n`-bundle together with a 1-truss bundle over its total poset `T_n`.
This module formalises that recursion in the fibrewise-open case, together with the
successor presentation of bundle maps (`def:n-bundle-map`,
`prop:structural-successor-equivalence`) and the dimension signature
(`def:dimension-signature`), and assembles the category `K_n` of §5.5 into an `n`-truss-like
category.

## Main definitions

* `FPoset` — a bundled finite poset; the tower's levels are `FPoset`s, so that each stage
  can serve as the base of the next 1-truss bundle.
* `towerStep`, `Tower`, `towerTot` — the recursion.  A single recursion produces the *type*
  `Tower P n` of `n`-towers over `P` and the assignment of its total poset `towerTot P n T`
  at once, avoiding mutual recursion.
* `Tower.lower`, `Tower.top`, `Tower.succ` — the truncation, the final bundle, and the
  successor constructor.
* `TowerMap` — base-preserving structural tower maps, in the successor presentation of
  `prop:structural-successor-equivalence`: a map of `(n+1)`-towers is a lower map `F`
  together with a bundle map from the top bundle to the reindexing of the target's top
  bundle along `Tot F`.
* `OpenBundle.reindex`, `OpenBundle.tildeHom`, `BundleMap.reindex` — reindexing of bundles,
  of their total posets, and of bundle maps.
* `Tower.dimsig` — `def:dimension-signature`.
* `Tower.totFunctor`, `Tower.instTrussLike` — `K_n` as an `n`-truss-like category.

## Main results

* `TowerMap.totHom_succ` — `rem:structural-successor-top-map`: the top total map of
  `(F, c)` is `Tot(c)` followed by `f̃ (b, v) := (f b, v)`.
* `TowerMap.totHom_injective` — **`Tot` is faithful**.  This is §5.5's "the projections are
  surjective, so the top component of a bundle map determines all its lower components":
  the fibres of an open 1-truss bundle are nonempty, so the top total map determines the
  base map of the final bundle, hence (by the stored tower law) the lower map's total map,
  hence by induction the lower map itself.
* `Tower.dimsig_antitone` — the dimension signature is a functor into `([2]^n)^op`.
* `Tower.dimsig_succ_split` — the coordinate splitting used by §5.5's proof of `(3) → (1)`:
  the first `n` coordinates are the lower tower's signature and the last is the fibre
  dimension.

## Encoding notes

The successor presentation makes the *type* of the top bundle map depend on the total map of
the lower tower map, which would force a transport into the definition of composition (the
equation `Tot(F ; G) = Tot(G) ∘ Tot(F)` is only propositional for a variable height).  To
keep composition transport-free, a tower map of height `n+1` stores its lower total map `f`
**as redundant data** together with the law `Tot(F) = f`; the law is a `Prop`, so this
changes nothing mathematically (`TowerMap.exists_succ` recovers the displayed presentation),
but it makes the composite's total map `g ∘ f` *definitionally* the composite of the total
maps.  Consequently `TowerMap.totHom_id`, `TowerMap.totHom_comp` and `TowerMap.totHom_succ`
all hold by `rfl` at the successor stage, and the category laws follow from faithfulness.

The dimension signature is indexed with `Fin.snoc`: coordinate `i.castSucc` is the lower
tower's `i`-th coordinate and coordinate `Fin.last n` is the final fibre dimension.  This is
the chapter's order `(d_1(y_1), …, d_n(y_n))`, lower coordinates first.
-/

universe u

namespace Truss.Transfer

open CategoryTheory Geometry Geometry.OneTruss

/-! ### Bundled finite posets -/

/-- A bundled finite poset.  The stages of an `n`-truss bundle tower are finite posets which
are themselves bases of the next 1-truss bundle, so it is convenient to carry the order and
finiteness instances with the carrier. -/
structure FPoset : Type (u + 1) where
  /-- The underlying carrier. -/
  carrier : Type u
  /-- The partial order. -/
  [order : PartialOrder carrier]
  /-- Finiteness. -/
  [finite : Finite carrier]

attribute [instance] FPoset.order FPoset.finite

/-- The carrier of an `FPoset` is a `Fintype`; needed to land in `FinPartOrd`. -/
noncomputable instance FPoset.instFintype (P : FPoset.{u}) : Fintype P.carrier :=
  Fintype.ofFinite _

/-! ### Reindexing of bundles, total posets and bundle maps -/

namespace OpenBundle

variable {B B' B'' : Type u} [PartialOrder B] [PartialOrder B'] [PartialOrder B'']

/-- **Source: `def:bundle-reindexing` (Chapter 2).**  The reindexing `f^* A` of a
fibrewise-open 1-truss bundle along a monotone map `f : B' →o B`: the fibre over `b` is the
fibre of `A` over `f b`, and the arrow fibre over `b ≤ c` is that of `A` over `f b ≤ f c`.
Both functoriality laws are those of `A` at the images of the comparisons. -/
def reindex (f : B' →o B) (A : OpenBundle B) : OpenBundle B' where
  fib b := A.fib (f b)
  arr h := A.arr (f.monotone h)
  arr_id b x y := A.arr_id (f b) x y
  arr_comp h₁ h₂ x z := A.arr_comp (f.monotone h₁) (f.monotone h₂) x z

@[simp] theorem reindex_fib (f : B' →o B) (A : OpenBundle B) (b : B') :
    (reindex f A).fib b = A.fib (f b) := rfl

/-- Reindexing along the identity is the identity. -/
theorem reindex_id (A : OpenBundle B) : reindex (OrderHom.id) A = A := rfl

/-- Reindexing is contravariantly functorial. -/
theorem reindex_comp (f : B'' →o B') (g : B' →o B) (A : OpenBundle B) :
    reindex f (reindex g A) = reindex (g.comp f) A := rfl

/-- **Source: `prop:reindexing-total-space` (Chapter 2).**  The canonical map
`f̃ : Tot(f^* A) → Tot(A)`, `(b, v) ↦ (f b, v)`, out of the pullback presentation of the
total poset of a reindexed bundle. -/
def tildeHom (f : B' →o B) (A : OpenBundle B) : (reindex f A).Tot →o A.Tot where
  toFun p := ⟨f p.1, p.2⟩
  monotone' := by rintro p q ⟨h, hrel⟩; exact ⟨f.monotone h, hrel⟩

@[simp] theorem tildeHom_apply (f : B' →o B) (A : OpenBundle B) (p : (reindex f A).Tot) :
    tildeHom f A p = ⟨f p.1, p.2⟩ := rfl

end OpenBundle

namespace BundleMap

variable {B B' : Type u} [PartialOrder B] [PartialOrder B']

/-- **Source: `rem:Reindexing structural bundle maps` (Chapter 2).**  The reindexing of a
base-preserving structural bundle map: `(f^* q)_b := q_{f b}`. -/
def reindex (f : B' →o B) {A A' : OpenBundle B} (d : BundleMap A A') :
    BundleMap (OpenBundle.reindex f A) (OpenBundle.reindex f A') where
  fibMap b := d.fibMap (f b)
  face := fun {_ _} h {_ _} hrel => d.face (f.monotone h) hrel

@[simp] theorem reindex_fibMap (f : B' →o B) {A A' : OpenBundle B} (d : BundleMap A A')
    (b : B') (x : (A.fib (f b)).toOneTruss.El) :
    (d.reindex f).fibMap b x = d.fibMap (f b) x := rfl

end BundleMap

/-! ### The tower -/

/-- **Source: `def:total-space-n-bundle` (Chapter 2).**  One recursion producing both the
type of height-`n` levelwise-open towers over `P` *and* the total poset of each of them.
Producing the pair at once avoids a mutual recursion between `Tower` and `towerTot`. -/
def towerStep (P : FPoset.{u}) : ℕ → Σ (X : Type u), (X → FPoset.{u})
  | 0 => ⟨PUnit, fun _ => P⟩
  | n + 1 => ⟨Σ T : (towerStep P n).1, OpenBundle ((towerStep P n).2 T).carrier,
              fun TA => ⟨OpenBundle.Tot TA.2⟩⟩

/-- **Source: `def:total-space-n-bundle`.**  A levelwise-open `n`-truss bundle over `P`. -/
def Tower (P : FPoset.{u}) (n : ℕ) : Type u := (towerStep P n).1

/-- **Source: `def:total-space-n-bundle`, `Tot(T_n)`.**  The top total poset of a tower. -/
def towerTot (P : FPoset.{u}) (n : ℕ) (T : Tower P n) : FPoset.{u} := (towerStep P n).2 T

/-- The base case of the recursion: `T_0 = B`. -/
theorem towerTot_zero (P : FPoset.{u}) (T : Tower P 0) : towerTot P 0 T = P := rfl

/-- The truncation `T ↦ T_{≤ n}` of an `(n+1)`-tower to its lower `n`-tower. -/
def Tower.lower {P : FPoset.{u}} {n : ℕ} (T : Tower P (n + 1)) : Tower P n := T.1

/-- The final 1-truss bundle `p_{n+1}` of an `(n+1)`-tower, over the lower total poset. -/
def Tower.top {P : FPoset.{u}} {n : ℕ} (T : Tower P (n + 1)) :
    OpenBundle (towerTot P n T.lower).carrier := T.2

/-- The successor constructor: append a 1-truss bundle over `T_n` to an `n`-tower. -/
def Tower.succ {P : FPoset.{u}} {n : ℕ} (T : Tower P n)
    (A : OpenBundle (towerTot P n T).carrier) : Tower P (n + 1) := ⟨T, A⟩

@[simp] theorem Tower.succ_lower {P : FPoset.{u}} {n : ℕ} (T : Tower P n)
    (A : OpenBundle (towerTot P n T).carrier) : (T.succ A).lower = T := rfl

@[simp] theorem Tower.succ_top {P : FPoset.{u}} {n : ℕ} (T : Tower P n)
    (A : OpenBundle (towerTot P n T).carrier) : (T.succ A).top = A := rfl

/-- Every `(n+1)`-tower is its truncation with its final bundle appended. -/
theorem Tower.succ_eta {P : FPoset.{u}} {n : ℕ} (T : Tower P (n + 1)) :
    T.lower.succ T.top = T := rfl

/-- The successor step of the recursion: the total poset of `T_{≤ n}` with `A` appended is
the total poset of `A`. -/
theorem towerTot_succ {P : FPoset.{u}} {n : ℕ} (T : Tower P n)
    (A : OpenBundle (towerTot P n T).carrier) :
    towerTot P (n + 1) (T.succ A) = ⟨OpenBundle.Tot A⟩ := rfl

/-- The top total poset of an `(n+1)`-tower is the total poset of its final bundle. -/
theorem towerTot_succ' {P : FPoset.{u}} {n : ℕ} (T : Tower P (n + 1)) :
    (towerTot P (n + 1) T).carrier = OpenBundle.Tot T.top := rfl

/-! ### Maps of towers -/

/-- A congruence lemma for composition of monotone maps, used to keep the successor step of
`towerMapPkg` free of dependent rewriting. -/
private theorem orderHom_comp_congr {A B C : Type u} [Preorder A] [Preorder B] [Preorder C]
    {f f' : A →o B} {g g' : B →o C} (hf : f = f') (hg : g = g') : g.comp f = g'.comp f' := by
  rw [hf, hg]

/-- The package produced by the recursion defining tower maps: the hom-types, the top total
map, identities and composition, together with the two functoriality laws of `Tot`.  Bundling
the laws with the data is what lets the successor step build composites without transporting
along `Tot(F ; G) = Tot(G) ∘ Tot(F)`. -/
structure TowerMapPkg (P : FPoset.{u}) (n : ℕ) : Type (u + 1) where
  /-- The type of base-preserving structural tower maps. -/
  Hom : Tower P n → Tower P n → Type u
  /-- The induced map of top total posets. -/
  tot : ∀ {T S : Tower P n}, Hom T S → (towerTot P n T).carrier →o (towerTot P n S).carrier
  /-- The identity tower map. -/
  id : ∀ T : Tower P n, Hom T T
  /-- Composition of tower maps. -/
  comp : ∀ {T S U : Tower P n}, Hom T S → Hom S U → Hom T U
  /-- `Tot` preserves identities. -/
  tot_id : ∀ T : Tower P n, tot (id T) = OrderHom.id
  /-- `Tot` preserves composition. -/
  tot_comp : ∀ {T S U : Tower P n} (F : Hom T S) (G : Hom S U),
    tot (comp F G) = (tot G).comp (tot F)

/-- **Source: `def:n-bundle-map` and `prop:structural-successor-equivalence` (Chapter 2).**
The recursion defining base-preserving structural tower maps in the successor presentation.
A map of `(n+1)`-towers is a lower tower map `F`, its total map `f` (stored as redundant data
subject to `Tot F = f`; see the module docstring), and a bundle map from the final bundle of
the source to the reindexing of the final bundle of the target along `f`. -/
def towerMapPkg (P : FPoset.{u}) : (n : ℕ) → TowerMapPkg P n
  | 0 =>
    { Hom := fun _ _ => PUnit
      tot := fun _ => OrderHom.id
      id := fun _ => ⟨⟩
      comp := fun _ _ => ⟨⟩
      tot_id := fun _ => rfl
      tot_comp := fun _ _ => rfl }
  | n + 1 =>
    { Hom := fun T S => Σ' (F : (towerMapPkg P n).Hom T.lower S.lower)
               (f : (towerTot P n T.lower).carrier →o (towerTot P n S.lower).carrier)
               (_ : (towerMapPkg P n).tot F = f),
               BundleMap T.top (OpenBundle.reindex f S.top)
      tot := fun {_ S} Q => (OpenBundle.tildeHom Q.2.1 S.top).comp Q.2.2.2.totHom
      id := fun T => ⟨(towerMapPkg P n).id T.lower, OrderHom.id,
               (towerMapPkg P n).tot_id _, BundleMap.id T.top⟩
      comp := fun {_ _ _} Q R => ⟨(towerMapPkg P n).comp Q.1 R.1, R.2.1.comp Q.2.1,
               ((towerMapPkg P n).tot_comp Q.1 R.1).trans
                 (orderHom_comp_congr Q.2.2.1 R.2.2.1),
               (R.2.2.2.reindex Q.2.1).comp Q.2.2.2⟩
      tot_id := fun _ => rfl
      tot_comp := fun _ _ => rfl }

/-- **Source: `def:n-bundle-map`, base-preserving (Chapter 2); the morphisms of §5.5's
`K_n`.**  A base-preserving structural map of levelwise-open `n`-truss bundles over `P`. -/
def TowerMap (P : FPoset.{u}) (n : ℕ) (T S : Tower P n) : Type u := (towerMapPkg P n).Hom T S

namespace TowerMap

variable {P : FPoset.{u}} {n : ℕ}

/-- **Source: `def:n-bundle-map`, derived part.**  The top component `q_n : T_n → S_n`, the
induced map of total posets. -/
def totHom {T S : Tower P n} (Q : TowerMap P n T S) :
    (towerTot P n T).carrier →o (towerTot P n S).carrier := (towerMapPkg P n).tot Q

/-- The identity tower map. -/
protected def id (T : Tower P n) : TowerMap P n T T := (towerMapPkg P n).id T

/-- Composition of tower maps, in diagrammatic order. -/
protected def comp {T S U : Tower P n} (Q : TowerMap P n T S) (R : TowerMap P n S U) :
    TowerMap P n T U := (towerMapPkg P n).comp Q R

/-- `Tot` preserves identities. -/
theorem totHom_id (T : Tower P n) : (TowerMap.id T).totHom = OrderHom.id :=
  (towerMapPkg P n).tot_id T

/-- `Tot` preserves composition. -/
theorem totHom_comp {T S U : Tower P n} (Q : TowerMap P n T S) (R : TowerMap P n S U) :
    (Q.comp R).totHom = R.totHom.comp Q.totHom := (towerMapPkg P n).tot_comp Q R

/-- The lower component `F : T_{≤ n} → S_{≤ n}` of a map of `(n+1)`-towers. -/
def lower {T S : Tower P (n + 1)} (Q : TowerMap P (n + 1) T S) :
    TowerMap P n T.lower S.lower := Q.1

/-- The base map `f = Tot(F)` of the final bundle map, stored as data. -/
def base {T S : Tower P (n + 1)} (Q : TowerMap P (n + 1) T S) :
    (towerTot P n T.lower).carrier →o (towerTot P n S.lower).carrier := Q.2.1

/-- **Source: `def:n-bundle-map`, the (tower) law.**  The stored base map is the total map of
the lower component. -/
theorem base_eq {T S : Tower P (n + 1)} (Q : TowerMap P (n + 1) T S) : Q.lower.totHom = Q.base :=
  Q.2.2.1

/-- The final component `c : A → f^* D` of a map of `(n+1)`-towers. -/
def topMap {T S : Tower P (n + 1)} (Q : TowerMap P (n + 1) T S) :
    BundleMap T.top (OpenBundle.reindex Q.base S.top) := Q.2.2.2

/-- **Source: `prop:structural-successor-equivalence` (Chapter 2).**  The successor
constructor: a lower tower map `F` together with a bundle map `c : A → Tot(F)^* D` assemble
into a map of `(n+1)`-towers. -/
protected def succ {T S : Tower P (n + 1)} (F : TowerMap P n T.lower S.lower)
    (c : BundleMap T.top (OpenBundle.reindex F.totHom S.top)) : TowerMap P (n + 1) T S :=
  ⟨F, F.totHom, rfl, c⟩

@[simp] theorem succ_lower {T S : Tower P (n + 1)} (F : TowerMap P n T.lower S.lower)
    (c : BundleMap T.top (OpenBundle.reindex F.totHom S.top)) :
    (TowerMap.succ F c).lower = F := rfl

@[simp] theorem succ_base {T S : Tower P (n + 1)} (F : TowerMap P n T.lower S.lower)
    (c : BundleMap T.top (OpenBundle.reindex F.totHom S.top)) :
    (TowerMap.succ F c).base = F.totHom := rfl

@[simp] theorem succ_topMap {T S : Tower P (n + 1)} (F : TowerMap P n T.lower S.lower)
    (c : BundleMap T.top (OpenBundle.reindex F.totHom S.top)) :
    (TowerMap.succ F c).topMap = c := rfl

/-- **Source: `prop:structural-successor-equivalence`, surjectivity on morphisms.**  Every
map of `(n+1)`-towers is of the displayed form `(F, c)`. -/
theorem exists_succ {T S : Tower P (n + 1)} (Q : TowerMap P (n + 1) T S) :
    ∃ c : BundleMap T.top (OpenBundle.reindex Q.lower.totHom S.top),
      Q = TowerMap.succ Q.lower c := by
  obtain ⟨F, f, hf, c⟩ := Q
  subst hf
  exact ⟨c, rfl⟩

/-- **Source: `rem:structural-successor-top-map` (Chapter 2).**  The top total map of a map
of `(n+1)`-towers factors as `Tot(c)` followed by `f̃ (b, v) := (f b, v)`. -/
theorem totHom_succ {T S : Tower P (n + 1)} (F : TowerMap P n T.lower S.lower)
    (c : BundleMap T.top (OpenBundle.reindex F.totHom S.top)) :
    (TowerMap.succ F c).totHom = (OpenBundle.tildeHom F.totHom S.top).comp c.totHom := rfl

/-- The same factorisation, for an arbitrary map of `(n+1)`-towers. -/
theorem totHom_eq_succ {T S : Tower P (n + 1)} (Q : TowerMap P (n + 1) T S) :
    Q.totHom = (OpenBundle.tildeHom Q.base S.top).comp Q.topMap.totHom := rfl

/-- The top total map in coordinates: `q_{n+1}(b, x) = (f b, c_b x)`. -/
theorem totHom_apply_succ {T S : Tower P (n + 1)} (Q : TowerMap P (n + 1) T S)
    (x : OpenBundle.Tot T.top) :
    Q.totHom x = ⟨Q.base x.1, Q.topMap.fibMap x.1 x.2⟩ := rfl

/-- **Source: §5.5, "the projections are surjective, so the top component of a bundle map
determines all its lower components".**  `Tot` is faithful on towers.

The induction step is exactly that argument: the fibres of an open 1-truss bundle are
nonempty, so the projection `Tot(A) → T_n` is surjective; therefore the top total map
`q_{n+1}(b, x) = (f b, c_b x)` determines `f`, hence the total map of the lower component,
hence by induction the lower component itself, and finally the fibre maps `c_b`. -/
theorem totHom_injective : ∀ (n : ℕ) {T S : Tower P n} {Q R : TowerMap P n T S},
    Q.totHom = R.totHom → Q = R
  | 0, _, _, _, _, _ => rfl
  | n + 1, T, S, Q, R, h => by
      obtain ⟨F, f, hf, c⟩ := Q
      obtain ⟨G, g, hg, d⟩ := R
      have hpt : ∀ x : OpenBundle.Tot T.top,
          (⟨f x.1, c.fibMap x.1 x.2⟩ : OpenBundle.Tot S.top)
            = ⟨g x.1, d.fibMap x.1 x.2⟩ := fun x => DFunLike.congr_fun h x
      have hfg : f = g := by
        refine OrderHom.ext _ _ (funext fun b => ?_)
        obtain ⟨y⟩ := (inferInstance : Nonempty (T.top.fib b).toOneTruss.El)
        exact congrArg Sigma.fst (hpt ⟨b, y⟩)
      subst hfg
      have hFG : F = G := totHom_injective n (hf.trans hg.symm)
      subst hFG
      have hcd : c = d := by
        refine BundleMap.ext fun b x => ?_
        have hx := hpt ⟨b, x⟩
        rw [Sigma.mk.injEq] at hx
        exact eq_of_heq hx.2
      subst hcd
      rfl

/-- Extensionality: a tower map is determined by its top total map. -/
theorem ext {T S : Tower P n} {Q R : TowerMap P n T S} (h : ∀ x, Q.totHom x = R.totHom x) :
    Q = R := totHom_injective n (OrderHom.ext _ _ (funext h))

end TowerMap

/-- **Source: §5.5.**  The category `K_n` of levelwise-open `n`-truss bundles over `P` and
base-preserving structural tower maps.  The laws follow from faithfulness of `Tot`. -/
instance Tower.instCategory (P : FPoset.{u}) (n : ℕ) : Category.{u} (Tower P n) where
  Hom T S := TowerMap P n T S
  id T := TowerMap.id T
  comp Q R := Q.comp R
  id_comp _ := TowerMap.totHom_injective n (by
    rw [TowerMap.totHom_comp, TowerMap.totHom_id]; rfl)
  comp_id _ := TowerMap.totHom_injective n (by
    rw [TowerMap.totHom_comp, TowerMap.totHom_id]; rfl)
  assoc _ _ _ := TowerMap.totHom_injective n (by
    rw [TowerMap.totHom_comp, TowerMap.totHom_comp, TowerMap.totHom_comp,
      TowerMap.totHom_comp]; rfl)

/-! ### The dimension signature -/

/-- **Source: `def:dimension-signature` (Chapter 2).**  The dimension signature
`dimsig_T : T_n → [2]^n`, `y ↦ (d_1(y_1), …, d_n(y_n))`, by recursion on the height: the
first `n` coordinates are the lower tower's signature at the projected point, and the last
coordinate is the dimension of `y` in the fibre `T_n(y_n)` of the final bundle. -/
def Tower.dimsig (P : FPoset.{u}) : (n : ℕ) → (T : Tower P n) →
    (towerTot P n T).carrier → DimCube n
  | 0, _, _ => fun i => i.elim0
  | n + 1, T, x =>
      Fin.snoc (α := fun _ => Fin 2) (Tower.dimsig P n T.lower x.1)
        ((T.top.fib x.1).toOneTruss.dim x.2)

/-- The defining successor equation of the dimension signature. -/
theorem Tower.dimsig_succ (P : FPoset.{u}) (n : ℕ) (T : Tower P (n + 1))
    (x : OpenBundle.Tot T.top) :
    Tower.dimsig P (n + 1) T x
      = Fin.snoc (α := fun _ => Fin 2) (Tower.dimsig P n T.lower x.1)
          ((T.top.fib x.1).toOneTruss.dim x.2) := rfl

/-- The lower coordinates of the signature are the lower tower's signature. -/
theorem Tower.dimsig_succ_castSucc (P : FPoset.{u}) (n : ℕ) (T : Tower P (n + 1))
    (x : OpenBundle.Tot T.top) (i : Fin n) :
    Tower.dimsig P (n + 1) T x i.castSucc = Tower.dimsig P n T.lower x.1 i := by
  change Fin.snoc (α := fun _ => Fin 2) _ _ i.castSucc = _
  rw [Fin.snoc_castSucc]

/-- The final coordinate of the signature is the fibre dimension. -/
theorem Tower.dimsig_succ_last (P : FPoset.{u}) (n : ℕ) (T : Tower P (n + 1))
    (x : OpenBundle.Tot T.top) :
    Tower.dimsig P (n + 1) T x (Fin.last n) = (T.top.fib x.1).toOneTruss.dim x.2 := by
  change Fin.snoc (α := fun _ => Fin 2) _ _ (Fin.last n) = _
  rw [Fin.snoc_last]

/-- **The coordinate splitting used by §5.5's proof of `(3) → (1)`.**  At a point `(b, x)` of
`Tot(T_{n+1})`, the first `n` coordinates of the dimension signature are the signature of `b`
in the lower tower, and the last coordinate is the dimension of `x` in the fibre over `b`. -/
theorem Tower.dimsig_succ_split (P : FPoset.{u}) (n : ℕ) (T : Tower P (n + 1))
    (x : OpenBundle.Tot T.top) :
    (∀ i : Fin n, Tower.dimsig P (n + 1) T x i.castSucc = Tower.dimsig P n T.lower x.1 i) ∧
      Tower.dimsig P (n + 1) T x (Fin.last n) = (T.top.fib x.1).toOneTruss.dim x.2 :=
  ⟨Tower.dimsig_succ_castSucc P n T x, Tower.dimsig_succ_last P n T x⟩

/-- **Source: `def:n-truss-like category` (§5.2), the signature condition.**  The dimension
signature is antitone, i.e. a functor `Tot(T) → ([2]^n)^op`.  The lower coordinates are
handled by induction and the last by `OpenBundle.dimsigOf_antitone`, which is the statement
that a bordism between open 1-trusses sends singular cells to singular cells. -/
theorem Tower.dimsig_antitone (P : FPoset.{u}) : ∀ (n : ℕ) (T : Tower P n),
    Antitone (Tower.dimsig P n T)
  | 0, _ => fun _ _ _ i => i.elim0
  | n + 1, T => by
      rintro x y hxy i
      obtain ⟨hb, hrel⟩ := hxy
      refine Fin.lastCases ?_ ?_ i
      · rw [Tower.dimsig_succ_last, Tower.dimsig_succ_last]
        exact T.top.dimsigOf_antitone (⟨hb, hrel⟩ : x ≤ y) 0
      · intro j
        rw [Tower.dimsig_succ_castSucc, Tower.dimsig_succ_castSucc]
        exact Tower.dimsig_antitone P n T.lower hb j

/-! ### `K_n` is `n`-truss-like -/

/-- **Source: §5.5.**  The total-poset functor of `K_n`. -/
noncomputable def Tower.totFunctor (P : FPoset.{u}) (n : ℕ) : Tower P n ⥤ FinPartOrd.{u} where
  obj T := FinPartOrd.of (towerTot P n T).carrier
  map Q := FinPartOrd.ofHom (TowerMap.totHom Q)
  map_id T := FinPartOrd.hom_ext (by
    change (TowerMap.totHom (TowerMap.id T) : _ →o _) = _
    rw [TowerMap.totHom_id]; rfl)
  map_comp Q R := FinPartOrd.hom_ext (by
    change (TowerMap.totHom (TowerMap.comp Q R) : _ →o _) = _
    rw [TowerMap.totHom_comp]; rfl)

/-- **Source: §5.5 section context.**  The category of levelwise-open `n`-truss bundles over
a finite poset is `n`-truss-like, with `Tot` the top total poset and `dimsig` the dimension
signature of `def:dimension-signature`. -/
noncomputable instance Tower.instTrussLike (P : FPoset.{u}) (n : ℕ) :
    TrussLike.{u, u, u} n (Tower P n) where
  tot := Tower.totFunctor P n
  tot_faithful := ⟨fun h => TowerMap.totHom_injective n (congrArg (fun f => f.hom.hom) h)⟩
  dimsig T := Tower.dimsig P n T
  dimsig_antitone T := Tower.dimsig_antitone P n T

@[simp] theorem Tower.totMap_apply {P : FPoset.{u}} {n : ℕ} {T S : Tower P n} (Q : T ⟶ S)
    (x : (towerTot P n T).carrier) : TrussLike.totMap Q x = TowerMap.totHom Q x := rfl

@[simp] theorem Tower.dimsig_apply {P : FPoset.{u}} {n : ℕ} (T : Tower P n)
    (x : (towerTot P n T).carrier) (i : Fin n) :
    TrussLike.dimsig T x i = Tower.dimsig P n T x i := rfl

end Truss.Transfer
