/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.BundleLabel
import Truss.Transfer.Normalisation.StablePullback
import Truss.Transfer.Normalisation.Tower

/-!
# Reindexing a labelled bundle, and the set-theoretic core of `B11`

`prop:open-pullbacks-preserve-normalisation` (§5.4, row `B11`) says that pulling a normalising
coarsening of labelled 1-truss bundles back along an **open** base map again gives a
normalising coarsening.  Its proof has four ingredients:

1. the pulled-back map is a coarsening, because it is fibrewise the same coarsening
   (**needs the converse of the fibrewise characterisation — OPEN**);
2. the label equation pulls back;
3. `ret(f^*q)_p = ret(q)_(f p)` and `NonTriv(f^*(A,L))_p = NonTriv(A,L)_(f p)`;
4. the displayed union identity `⋃_(a ≤ p) σ_(f a,f p)(E_(f a)) = ⋃_(z ≤ f p) σ_(z,f p)(E_z)`,
   which holds *because `f` is open*.

Items 2–4 are proved here; 4 is `Transport.closure_comap`, applied through
`singTransport_reindex`.  Item 1, and hence the theorem itself, is **not** proved here.

Reindexing itself (`OpenBundle.reindex`, `tildeHom`, `BundleMap.reindex`) lives in
`Tower.lean`; this module only establishes how it interacts with `σ`, `ret` and `NonTriv`.
-/

universe u u' v

namespace Truss.Transfer

open CategoryTheory Geometry Geometry.OneTruss TrussLike

variable {B : Type u} {B' : Type u} [PartialOrder B] [PartialOrder B']

namespace OpenBundle

/-! ### The singular transport of a reindexed bundle -/

/-- Reindexing does not change the singular functions: the fibres and the arrow bordisms of
`f^*A` are *literally* those of `A`. -/
theorem sigma_reindex (f : B' →o B) (A : OpenBundle B) {p p' : B'} (h : p ≤ p')
    (i : Fin ((reindex f A).fib p).numSing) :
    (reindex f A).sigma h i = A.sigma (f.monotone h) i := rfl

/-! ### Retained and non-trivially labelled families pull back pointwise -/

/-- The fibre map of a reindexed bundle map is the fibre map of the original at `f p`. -/
@[simp] theorem reindex_fibMap' (f : B' →o B) {A A' : OpenBundle B} (q : A ⟶ A') (p : B')
    (x : ((reindex f A).fib p).toOneTruss.El) :
    (BundleMap.reindex f q).fibMap p x = q.fibMap (f p) x := rfl

/-- **`ret(f^*q)_p = ret(q)_(f p)`.** -/
theorem retFam_reindex (f : B' →o B) {A A' : OpenBundle B} (q : A ⟶ A') (p : B') :
    retFam (BundleMap.reindex f q) p = retFam q (f p) := rfl

variable {C : Type v} [Category.{v} C]

/-- The label pulled back along reindexing: precompose with `f̃`. -/
def pullbackLabel (f : B' →o B) (A : OpenBundle B) (L : A.Tot ⥤ C) :
    (reindex f A).Tot ⥤ C := posetFunctor (tildeHom f A) ⋙ L

/-- Restricting a pulled-back label to a fibre gives the original restriction at `f p`:
both composites send `x` to `L.obj ⟨f p, x⟩`. -/
theorem restrictLabel_pullbackLabel (f : B' →o B) (A : OpenBundle B) (L : A.Tot ⥤ C) (p : B') :
    (reindex f A).restrictLabel (pullbackLabel f A L) p = A.restrictLabel L (f p) := rfl

/-- **`NonTriv(f^*(A,L))_p = NonTriv(A,L)_(f p)`.** -/
theorem nonTrivFam_reindex (f : B' →o B) (A : OpenBundle B) (L : A.Tot ⥤ C) (p : B') :
    (reindex f A).nonTrivFam (pullbackLabel f A L) p = A.nonTrivFam L (f p) := rfl

/-! ### The displayed union identity -/

/-- **The key equality of `prop:open-pullbacks-preserve-normalisation`.**  For an **open**
base map, the forward-stable closure of the pulled-back non-trivially-labelled family is the
pullback of the closure:

`⋃_(a ≤ p) σ_(f a,f p)(E_(f a)) = ⋃_(z ≤ f p) σ_(z,f p)(E_z)`,

*"because `f(↓p) = ↓f(p)`"*.  As the chapter says, surjectivity and connected fibres of `f`
are **not** used. -/
theorem nonTrivClosure_reindex (f : B' →o B) (hf : IsOpenPosetMap f) (A : OpenBundle B)
    (L : A.Tot ⥤ C) (p : B') :
    (reindex f A).nonTrivClosure (pullbackLabel f A L) p = A.nonTrivClosure L (f p) := by
  ext y
  constructor
  · -- a witness over `a ≤ p` gives one over `f a ≤ f p`
    rintro ⟨a, hap, x, hx, rfl⟩
    exact ⟨f a, f.monotone hap, x, hx, rfl⟩
  · -- exact target lifting: `z ≤ f p` has a preimage `a ≤ p`.  This is the ONLY place
    -- openness of `f` is used, exactly as the chapter says.
    rintro ⟨z, hz, x, hx, rfl⟩
    obtain ⟨a, hap, rfl⟩ := hf.exists_le hz
    exact ⟨a, hap, x, hx, rfl⟩

/-- The pulled-back label really is the label of the pulled-back bundle map: if `q` carries
the label equation `L = M ∘ Tot(q)`, so does `f^*q`. -/
theorem descendsAlong_reindex (f : B' →o B) {A A' : OpenBundle B} (q : A ⟶ A')
    (M : A'.Tot ⥤ C) :
    pullbackLabel f A (posetFunctor (BundleMap.totHom q) ⋙ M)
      = posetFunctor (BundleMap.totHom (BundleMap.reindex f q))
        ⋙ pullbackLabel f A' M := rfl

end OpenBundle

end Truss.Transfer
