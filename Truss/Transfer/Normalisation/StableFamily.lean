/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.Hom.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.Set.Lattice

/-!
# Forward-stable families and their closure

The generic order theory behind §5.4 of the draft normalisation chapter (rows `B03` and
`B06` of
[`plan/DraftNormalisationVerification.md`](../../../plan/DraftNormalisationVerification.md)).

The chapter works with a *singular family* `U = (U_b)` of subsets of the fibres of a bundle,
calls it **forward-stable** when `σ_(b,c)(U_b) ⊆ U_c` for `b ≤ c`, and defines the
**forward-stable closure**

> `\overline{U}_b = ⋃_(a ≤ b) σ_(a,b)(U_a)`,

remarking that it "clearly" is forward-stable and is contained in any forward-stable family
containing `U`.  Those two "clearly"s are `closure_isForwardStable` and `closure_le` below;
the second is where the functoriality of `σ` is actually used, and it is not quite immediate.

Nothing here mentions trusses: the input is a poset `B`, a family of types `E b`, and a
functorial transport `σ`.  In §5.4, `E b` is the set of singular cells of the fibre `A_b` and
`σ` is the singular function of the arrow-fibre bordism.  Finiteness is never used.

## Main definitions

* `Transport E` — a functorial family of maps `E b → E c` for `b ≤ c`.
* `Family E` — a family of subsets, ordered fibrewise.
* `Transport.IsForwardStable`, `Transport.closure`.

## Main results

* `closure_isForwardStable`, `le_closure`, `closure_le`, `closure_idem`,
  `IsForwardStable.closure_eq`, `closure_mono` — the closure is a closure operator whose
  fixed points are exactly the forward-stable families.
* `isForwardStable_iInter`, `isForwardStable_iUnion` — forward-stable families are closed
  under arbitrary intersections and unions, so they form a complete lattice.
-/

universe u v

namespace Truss.Transfer

/-- A functorial transport along a poset: a map `E b → E c` for every `b ≤ c`, compatible
with identities and composition.  This is the abstract form of the chapter's singular
functions `σ_(b,c)`. -/
structure Transport {B : Type u} [Preorder B] (E : B → Type v) where
  /-- The transport map along `b ≤ c`. -/
  map : ∀ {b c : B}, b ≤ c → E b → E c
  /-- Transport along a reflexivity is the identity. -/
  map_id : ∀ (b : B) (x : E b), map (le_refl b) x = x
  /-- Transport is functorial. -/
  map_comp : ∀ {b c d : B} (h₁ : b ≤ c) (h₂ : c ≤ d) (x : E b),
    map h₂ (map h₁ x) = map (h₁.trans h₂) x

namespace Transport

variable {B : Type u} [Preorder B] {E : B → Type v} (σ : Transport E)

/-- Transport along two proofs of the same comparison agrees: `≤` is a `Prop`. -/
theorem map_congr {b c : B} (h h' : b ≤ c) (x : E b) : σ.map h x = σ.map h' x := rfl

/-- A *family* of subsets of the fibres.  The chapter's "singular family". -/
abbrev Family (_ : Transport E) : Type max u v := ∀ b : B, Set (E b)

/-- **Source: `def:Singular family` (§5.4).**  Inclusion of families is fibrewise. -/
protected def Le (U V : σ.Family) : Prop := ∀ b, U b ⊆ V b

instance : PartialOrder σ.Family where
  le := σ.Le
  le_refl _ _ := subset_rfl
  le_trans _ _ _ h₁ h₂ b := (h₁ b).trans (h₂ b)
  le_antisymm _ _ h₁ h₂ := funext fun b => Set.Subset.antisymm (h₁ b) (h₂ b)

theorem le_def {U V : σ.Family} : U ≤ V ↔ ∀ b, U b ⊆ V b := Iff.rfl

/-- **Source: `def:Forward-stable singular family` (§5.4).** -/
def IsForwardStable (U : σ.Family) : Prop :=
  ∀ {b c : B} (h : b ≤ c), σ.map h '' U b ⊆ U c

theorem isForwardStable_iff {U : σ.Family} :
    σ.IsForwardStable U ↔ ∀ {b c : B} (h : b ≤ c), ∀ x ∈ U b, σ.map h x ∈ U c := by
  constructor
  · intro hU _ _ h x hx; exact hU h ⟨x, hx, rfl⟩
  · rintro hU _ _ h _ ⟨x, hx, rfl⟩; exact hU h x hx

/-- **Source: `def:Forward-stable closure` (§5.4).**
`\overline{U}_b = ⋃_(a ≤ b) σ_(a,b)(U_a)`. -/
def closure (U : σ.Family) : σ.Family :=
  fun b => {y | ∃ (a : B) (h : a ≤ b) (x : E a), x ∈ U a ∧ σ.map h x = y}

theorem mem_closure {U : σ.Family} {b : B} {y : E b} :
    y ∈ σ.closure U b ↔ ∃ (a : B) (h : a ≤ b) (x : E a), x ∈ U a ∧ σ.map h x = y := Iff.rfl

/-- The closure is extensive. -/
theorem le_closure (U : σ.Family) : U ≤ σ.closure U := by
  intro b x hx
  exact ⟨b, le_rfl, x, hx, σ.map_id b x⟩

/-- **The first "clearly": the closure is forward-stable.**  Functoriality composes the
witnessing comparison with the new one. -/
theorem closure_isForwardStable (U : σ.Family) : σ.IsForwardStable (σ.closure U) := by
  rw [isForwardStable_iff]
  rintro b c h y ⟨a, hab, x, hx, rfl⟩
  exact ⟨a, hab.trans h, x, hx, (σ.map_comp hab h x).symm⟩

/-- **The second "clearly": the closure is least.**  Any forward-stable family containing
`U` contains its closure. -/
theorem closure_le {U V : σ.Family} (hUV : U ≤ V) (hV : σ.IsForwardStable V) :
    σ.closure U ≤ V := by
  rintro b y ⟨a, hab, x, hx, rfl⟩
  exact (isForwardStable_iff σ).1 hV hab x (hUV a hx)

/-- A forward-stable family is its own closure. -/
theorem closure_eq_of_isForwardStable {U : σ.Family} (hU : σ.IsForwardStable U) :
    σ.closure U = U :=
  le_antisymm (σ.closure_le le_rfl hU) (σ.le_closure U)

/-- The closure is idempotent. -/
theorem closure_idem (U : σ.Family) : σ.closure (σ.closure U) = σ.closure U :=
  σ.closure_eq_of_isForwardStable (σ.closure_isForwardStable U)

/-- The closure is monotone. -/
theorem closure_mono {U V : σ.Family} (h : U ≤ V) : σ.closure U ≤ σ.closure V :=
  σ.closure_le (h.trans (σ.le_closure V)) (σ.closure_isForwardStable V)

/-- A family is forward-stable exactly when it is its own closure. -/
theorem isForwardStable_iff_closure_eq {U : σ.Family} :
    σ.IsForwardStable U ↔ σ.closure U = U :=
  ⟨fun h => σ.closure_eq_of_isForwardStable h, fun h => h ▸ σ.closure_isForwardStable U⟩

/-! ### The lattice of forward-stable families -/

theorem isForwardStable_top : σ.IsForwardStable (fun b => (Set.univ : Set (E b))) := by
  rw [isForwardStable_iff]; intro _ _ _ _ _; trivial

theorem isForwardStable_bot : σ.IsForwardStable (fun b => (∅ : Set (E b))) := by
  rw [isForwardStable_iff]; rintro _ _ _ _ ⟨⟩

theorem isForwardStable_iInter {ι : Type*} {U : ι → σ.Family}
    (hU : ∀ i, σ.IsForwardStable (U i)) :
    σ.IsForwardStable (fun b => ⋂ i, U i b) := by
  rw [isForwardStable_iff]
  intro b c h x hx
  simp only [Set.mem_iInter] at hx ⊢
  exact fun i => (isForwardStable_iff σ).1 (hU i) h x (hx i)

theorem isForwardStable_iUnion {ι : Type*} {U : ι → σ.Family}
    (hU : ∀ i, σ.IsForwardStable (U i)) :
    σ.IsForwardStable (fun b => ⋃ i, U i b) := by
  rw [isForwardStable_iff]
  intro b c h x hx
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨i, hi⟩ := hx
  exact ⟨i, (isForwardStable_iff σ).1 (hU i) h x hi⟩

theorem isForwardStable_inter {U V : σ.Family} (hU : σ.IsForwardStable U)
    (hV : σ.IsForwardStable V) : σ.IsForwardStable (fun b => U b ∩ V b) := by
  rw [isForwardStable_iff]
  intro b c h x hx
  exact ⟨(isForwardStable_iff σ).1 hU h x hx.1, (isForwardStable_iff σ).1 hV h x hx.2⟩

theorem isForwardStable_union {U V : σ.Family} (hU : σ.IsForwardStable U)
    (hV : σ.IsForwardStable V) : σ.IsForwardStable (fun b => U b ∪ V b) := by
  rw [isForwardStable_iff]
  rintro b c h x (hx | hx)
  · exact Or.inl ((isForwardStable_iff σ).1 hU h x hx)
  · exact Or.inr ((isForwardStable_iff σ).1 hV h x hx)

/-- **Source: `def:Forward-stable singular family` (§5.4).**  The poset `R(A)` of
forward-stable families under fibrewise inclusion. -/
def Stable : Type max u v := {U : σ.Family // σ.IsForwardStable U}

instance : PartialOrder σ.Stable := Subtype.partialOrder _

theorem Stable.le_iff {U V : σ.Stable} : U ≤ V ↔ ∀ b, U.1 b ⊆ V.1 b := Iff.rfl

@[ext] theorem Stable.ext {U V : σ.Stable} (h : U.1 = V.1) : U = V := Subtype.ext h

/-- The closure, as a map into the forward-stable families. -/
def stableClosure (U : σ.Family) : σ.Stable := ⟨σ.closure U, σ.closure_isForwardStable U⟩

/-- The closure is left adjoint to the inclusion of forward-stable families: this is the
universal property that `B06` needs. -/
theorem stableClosure_le_iff (U : σ.Family) (V : σ.Stable) :
    σ.stableClosure U ≤ V ↔ U ≤ V.1 :=
  ⟨fun h => (σ.le_closure U).trans h, fun h => σ.closure_le h V.2⟩

end Transport

end Truss.Transfer
