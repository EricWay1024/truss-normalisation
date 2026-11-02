/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.Poset
import Truss.Transfer.Normalisation.StableFamily

/-!
# Pulling back a transport, and the key identity of the open-pullback theorem

`prop:open-pullbacks-preserve-normalisation` (§5.4, row `B11`) turns on the single set
identity

> `⋃_(a ≤ p) σ_(f(a),f(p))(E_(f(a))) = ⋃_(z ≤ f(p)) σ_(z,f(p))(E_z)`,
>
> *"because `f(↓p) = ↓f(p)`"*,

i.e. on the **openness** of the base map `f`.  The chapter adds, correctly, that
*"surjectivity and connected fibres of `f` are not required"*.

That identity is pure order theory, so it is proved here once and for all, with no trusses
present: it says the forward-stable closure commutes with pulling a `Transport` back along an
open monotone map.  `Truss.Transfer.IsOpenPosetMap` is the `P01` notion, whose
`isOpenPosetMap_iff_exists_le` form is exactly the lifting needed for one inclusion.
-/

universe u u' v

namespace Truss.Transfer

variable {B : Type u} {P : Type u'} [PartialOrder B] [PartialOrder P]
variable {E : B → Type v}

namespace Transport

/-- Pull a transport back along a monotone map: transport along `p ≤ p'` in `P` is transport
along `f p ≤ f p'` in `B`.  (`≤` is a `Prop`, so the two comparison proofs agree.) -/
def comap (f : P →o B) (σ : Transport E) : Transport (fun p => E (f p)) where
  map h := σ.map (f.monotone h)
  map_id p x := σ.map_id (f p) x
  map_comp h₁ h₂ x := σ.map_comp (f.monotone h₁) (f.monotone h₂) x

@[simp] theorem comap_map (f : P →o B) (σ : Transport E) {p p' : P} (h : p ≤ p')
    (x : E (f p)) : (σ.comap f).map h x = σ.map (f.monotone h) x := rfl

/-- The pullback of a family along `f`. -/
def pullbackFamily (f : P →o B) (σ : Transport E) (U : σ.Family) : (σ.comap f).Family :=
  fun p => U (f p)

@[simp] theorem pullbackFamily_apply (f : P →o B) (σ : Transport E) (U : σ.Family) (p : P) :
    σ.pullbackFamily f U p = U (f p) := rfl

/-- The pullback of a forward-stable family is forward-stable.  No hypothesis on `f`. -/
theorem isForwardStable_pullbackFamily (f : P →o B) (σ : Transport E) {U : σ.Family}
    (hU : σ.IsForwardStable U) : (σ.comap f).IsForwardStable (σ.pullbackFamily f U) := by
  rw [isForwardStable_iff]
  intro p p' h x hx
  exact (isForwardStable_iff σ).1 hU (f.monotone h) x hx

/-- One inclusion needs nothing: a witness over `a ≤ p` gives a witness over `f a ≤ f p`. -/
theorem closure_comap_le (f : P →o B) (σ : Transport E) (U : σ.Family) (p : P) :
    (σ.comap f).closure (σ.pullbackFamily f U) p ⊆ σ.closure U (f p) := by
  rintro y ⟨a, hap, x, hx, rfl⟩
  exact ⟨f a, f.monotone hap, x, hx, rfl⟩

/-- **The key identity of `prop:open-pullbacks-preserve-normalisation`.**  For an **open**
monotone `f`, the closure of a pulled-back family is the pullback of its closure.  The
non-trivial inclusion is exactly `↓f(p) ⊆ f(↓p)`, i.e. exact target lifting.  Surjectivity
and connected fibres of `f` are **not** used. -/
theorem closure_comap (f : P →o B) (hf : IsOpenPosetMap f) (σ : Transport E) (U : σ.Family) :
    (σ.comap f).closure (σ.pullbackFamily f U) = fun p => σ.closure U (f p) := by
  funext p
  apply Set.Subset.antisymm (σ.closure_comap_le f U p)
  rintro y ⟨z, hz, x, hx, rfl⟩
  -- exact target lifting: `z ≤ f p` has a preimage `a ≤ p`
  obtain ⟨a, hap, rfl⟩ := hf.exists_le hz
  exact ⟨a, hap, x, hx, rfl⟩

/-- Consequently the pullback of the closure is the closure of the pullback, in the form
§5.4 uses: the two displayed unions agree. -/
theorem closure_comap_apply (f : P →o B) (hf : IsOpenPosetMap f) (σ : Transport E)
    (U : σ.Family) (p : P) :
    (σ.comap f).closure (σ.pullbackFamily f U) p = σ.closure U (f p) :=
  congrFun (σ.closure_comap f hf U) p

end Transport

end Truss.Transfer
