/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finite.Sigma
import Truss.Transfer.Geometry.OpenCoord
import Truss.Transfer.Normalisation.StableFamily
import Truss.Transfer.Normalisation.Context

/-!
# Fibrewise-open 1-truss bundles over a finite poset (§5.4, row B01)

Chapter 2 gives two equivalent presentations of a 1-truss bundle and *begins* with the
functorial one (`Bun_1(B) := Fun(B, TBord^1)`); the total-space presentation is recovered by
`def:total-poset-bundle`, whose displayed order is

> `(b,x) ⊴_F (c,y) ⟺ b ≤ c and F(b≤c)(x,y)`.

That is exactly the definition used here: an `OpenBundle B` is a functor from `B` to the
bordism category, with open fibres, and `Tot` is the displayed total poset.  Taking the
functorial presentation as primitive is what makes classification and totalisation
transparent later; nothing is assumed about them.

## Main definitions

* `OpenBundle B` — the chapter's fibrewise-open 1-truss bundle, functorially.
* `OpenBundle.Tot` — the total poset, with the displayed order.
* `OpenBundle.proj` — the monotone projection to `B`.
* `BundleMap` — a base-preserving structural bundle map (`def:n-bundle-map` at height one).
* `OpenBundle.sigmaRel`, and the `Transport` of singular cells that §5.4's `σ_(b,c)` names.

## Main results

* `Bord1.isSingular_of_rel_of_isSingular` — a bordism between **open** 1-trusses sends a
  singular cell only to singular cells.  This is the chapter's "bordisms weakly decrease
  dimension", proved from (functorial) and (cofunctional): a singular cell of an open truss
  has two *distinct* regular neighbours, both of which would be related to a regular image,
  contradicting cofunctionality.
* `OpenBundle.instPartialOrder` — the displayed relation really is a partial order.
-/

universe u

namespace Truss.Transfer

open CategoryTheory Geometry Geometry.OneTruss

/-! ### Bordisms between open 1-trusses preserve singularity -/

namespace Geometry.Bord1

variable {T S : OneTruss}

/-- In an **open** 1-truss a singular cell is never an endpoint, so it has two distinct
regular neighbours, both below it in the face order. -/
theorem exists_two_neighbours (hT : T.IsOpen) {x : T.El} (hx : T.IsSingular x) :
    ∃ x₁ x₂ : T.El, T.IsRegular x₁ ∧ T.IsRegular x₂ ∧ x₁ ≤ x ∧ x₂ ≤ x ∧ x₁ ≠ x₂ := by
  -- a singular cell of an open 1-truss is not an endpoint
  have hlow : x ≠ T.lower := by
    rintro rfl
    have h1 : T.dim T.lower = 1 := hT.1
    rw [hx] at h1
    exact absurd h1 (by decide)
  have hup : x ≠ T.upper := by
    rintro rfl
    have h1 : T.dim T.upper = 1 := hT.2
    rw [hx] at h1
    exact absurd h1 (by decide)
  have h0 : 0 < (idx x).val := by
    rcases Nat.eq_zero_or_pos (idx x).val with hz | hp
    · exact absurd (idx_injective (Fin.ext (by rw [hz, idx_lower]))) hlow
    · exact hp
  have hlt : (idx x).val < T.len := by
    rcases eq_or_lt_of_le (by simpa using idx_le_upper x) with heq | hlt
    · exact absurd (idx_injective (Fin.ext (by rw [heq, idx_upper]))) hup
    · exact hlt
  set x₁ : T.El := ofIdx ⟨(idx x).val - 1, by omega⟩ with hx₁def
  set x₂ : T.El := ofIdx ⟨(idx x).val + 1, by omega⟩ with hx₂def
  have i₁ : (idx x₁).val = (idx x).val - 1 := rfl
  have i₂ : (idx x₂).val = (idx x).val + 1 := rfl
  have r₁ : T.IsRegular x₁ := by
    refine T.isRegular_of_parity_ne hx ?_
    rw [i₁]; omega
  have r₂ : T.IsRegular x₂ := by
    refine T.isRegular_of_parity_ne hx ?_
    rw [i₂]; omega
  refine ⟨x₁, x₂, r₁, r₂, Or.inr ⟨r₁, hx, Or.inr ?_⟩, Or.inr ⟨r₂, hx, Or.inl ?_⟩, ?_⟩
  · rw [i₁]; omega
  · rw [i₂]
  · intro hc
    have hv : (idx x₁).val = (idx x₂).val := congrArg (fun e => (idx e).val) hc
    rw [i₁, i₂] at hv
    omega

/-- **A bordism between open 1-trusses sends singular cells to singular cells.**
This is Chapter 2's "bordisms weakly decrease dimension", in the form §5.4 needs.  If a
singular `x` were related to a regular `y`, then (functorial) would relate *both* regular
neighbours of `x` to `y`, contradicting (cofunctional). -/
theorem isSingular_of_rel_of_isSingular (R : Bord1 T S) (hT : T.IsOpen) {x : T.El} {y : S.El}
    (hx : T.IsSingular x) (hrel : R.rel x y) : S.IsSingular y := by
  by_contra hy
  rw [OneTruss.not_isSingular_iff] at hy
  obtain ⟨x₁, x₂, hr₁, hr₂, h1, h2, hne⟩ := exists_two_neighbours hT hx
  have rel1 : R.rel x₁ y := R.functorial h1 hrel le_rfl
  have rel2 : R.rel x₂ y := R.functorial h2 hrel le_rfl
  obtain ⟨x₀, -, huniq⟩ := R.cofunctional y hy
  exact hne ((huniq x₁ ⟨hr₁, rel1⟩).trans (huniq x₂ ⟨hr₂, rel2⟩).symm)

end Geometry.Bord1

/-! ### The bundle -/

variable {B : Type u} [PartialOrder B]

/-- **Source: `Functorial 1-truss bundles` (Chapter 2) with open fibres, the category `K` of
§5.4.**  A fibrewise-open 1-truss bundle over `B` is a functor from `B` to the 1-truss
bordism category whose values are open. -/
structure OpenBundle (B : Type u) [PartialOrder B] where
  /-- The point fibre over `b`. -/
  fib : B → OpenTruss
  /-- The arrow fibre over `b ≤ c`. -/
  arr : ∀ {b c : B}, b ≤ c → Geometry.Bord1 (fib b).toOneTruss (fib c).toOneTruss
  /-- The identity bordism is the face relation. -/
  arr_id : ∀ (b : B) (x y : (fib b).toOneTruss.El), (arr (le_refl b)).rel x y ↔ x ≤ y
  /-- Functoriality: the composite bordism is relational composition. -/
  arr_comp : ∀ {b c d : B} (h₁ : b ≤ c) (h₂ : c ≤ d)
    (x : (fib b).toOneTruss.El) (z : (fib d).toOneTruss.El),
    (arr (h₁.trans h₂)).rel x z ↔ ∃ y, (arr h₁).rel x y ∧ (arr h₂).rel y z

namespace OpenBundle

variable (A : OpenBundle B)

/-- **Source: `def:total-poset-bundle` (Chapter 2).**  The total space of the bundle. -/
def Tot : Type u := Σ b : B, (A.fib b).toOneTruss.El

/-- **Source: `def:total-poset-bundle`, face order.**
`(b,x) ⊴ (c,y) ⟺ b ≤ c and F(b≤c)(x,y)`. -/
protected def Le (p q : A.Tot) : Prop := ∃ h : p.1 ≤ q.1, (A.arr h).rel p.2 q.2

theorem le_def {p q : A.Tot} : A.Le p q ↔ ∃ h : p.1 ≤ q.1, (A.arr h).rel p.2 q.2 := Iff.rfl

instance instPartialOrder : PartialOrder A.Tot where
  le := A.Le
  le_refl p := ⟨le_rfl, (A.arr_id p.1 p.2 p.2).2 le_rfl⟩
  le_trans p q r := by
    rintro ⟨h₁, hr₁⟩ ⟨h₂, hr₂⟩
    exact ⟨h₁.trans h₂, (A.arr_comp h₁ h₂ p.2 r.2).2 ⟨q.2, hr₁, hr₂⟩⟩
  le_antisymm p q := by
    rintro ⟨h₁, hr₁⟩ ⟨h₂, hr₂⟩
    obtain ⟨b, x⟩ := p
    obtain ⟨c, y⟩ := q
    have hbc : b = c := le_antisymm h₁ h₂
    subst hbc
    have hxy : x ≤ y := (A.arr_id b x y).1 hr₁
    have hyx : y ≤ x := (A.arr_id b y x).1 hr₂
    exact congrArg _ (le_antisymm hxy hyx)

/-- The bundle projection. -/
def proj : A.Tot →o B where
  toFun p := p.1
  monotone' _ _ h := h.1

@[simp] theorem proj_apply (p : A.Tot) : A.proj p = p.1 := rfl

/-- The point fibre over `b`, as the carrier of the 1-truss `A_b`. -/
theorem mem_fibre_iff (b : B) (p : A.Tot) : A.proj p = b ↔ p.1 = b := Iff.rfl

instance instFinite [Finite B] : Finite A.Tot := inferInstanceAs (Finite (Σ _, _))

noncomputable instance instFintype [Finite B] : Fintype A.Tot := Fintype.ofFinite _

/-! ### The singular transport `σ` -/

/-- **Source: §5.4, `σ_(b,c)`.**  The singular function of the arrow-fibre bordism, as a map
of singular-cell indices.  Well defined by `Bord1.isSingular_of_rel_of_isSingular`. -/
noncomputable def sigma {b c : B} (h : b ≤ c) (i : Fin (A.fib b).numSing) :
    Fin (A.fib c).numSing :=
  (A.fib c).singIdx rfl ((A.arr h).singFun ((A.fib b).singAt rfl i))

theorem sigma_rel {b c : B} (h : b ≤ c) (i : Fin (A.fib b).numSing) :
    (A.arr h).rel ((A.fib b).singAt rfl i).el ((A.fib c).singAt rfl (A.sigma h i)).el := by
  unfold sigma
  rw [OpenTruss.singAt_singIdx]
  exact (A.arr h).singFun_rel _

/-- `σ` is determined by the relation: it is the unique singular image. -/
theorem sigma_eq_of_rel {b c : B} (h : b ≤ c) (i : Fin (A.fib b).numSing)
    {y : (A.fib c).toOneTruss.El} (hy : (A.fib c).toOneTruss.IsSingular y)
    (hrel : (A.arr h).rel ((A.fib b).singAt rfl i).el y) :
    y = ((A.fib c).singAt rfl (A.sigma h i)).el := by
  have := (A.arr h).singFun_unique ((A.fib b).singAt rfl i) hy hrel
  rw [this]
  unfold sigma
  rw [OpenTruss.singAt_singIdx]

@[simp] theorem sigma_id (b : B) (i : Fin (A.fib b).numSing) : A.sigma (le_refl b) i = i := by
  refine (A.fib b).singAt_injective rfl ?_
  refine Sing.ext ?_
  refine ((A.sigma_eq_of_rel (le_refl b) i ((A.fib b).singAt rfl i).isSingular ?_).symm)
  exact (A.arr_id b _ _).2 le_rfl

theorem sigma_comp {b c d : B} (h₁ : b ≤ c) (h₂ : c ≤ d) (i : Fin (A.fib b).numSing) :
    A.sigma h₂ (A.sigma h₁ i) = A.sigma (h₁.trans h₂) i := by
  refine (A.fib d).singAt_injective rfl (Sing.ext ?_)
  refine A.sigma_eq_of_rel (h₁.trans h₂) i
    ((A.fib d).singAt rfl (A.sigma h₂ (A.sigma h₁ i))).isSingular ?_
  exact (A.arr_comp h₁ h₂ _ _).2 ⟨_, A.sigma_rel h₁ i, A.sigma_rel h₂ _⟩

/-- **Source: §5.4.**  The singular functions assemble into a `Transport`, so the generic
forward-stable theory of `Truss.Transfer.Transport` applies verbatim. -/
noncomputable def singTransport : Transport (fun b : B => Fin (A.fib b).numSing) where
  map h := A.sigma h
  map_id := A.sigma_id
  map_comp h₁ h₂ x := A.sigma_comp h₁ h₂ x

/-! ### The dimension signature -/

/-- **Source: §5.4.**  The fibrewise dimension, as the dimension signature of the bundle:
`dimsig_A (b,x) := dim_(A_b)(x)`. -/
def dimsigOf (p : A.Tot) : DimCube 1 := fun _ => (A.fib p.1).toOneTruss.dim p.2

/-- The chapter's editorial TODO — *"the functoriality of this fibrewise dimension signature
should eventually be stated in Chapter 2"* — discharged: the fibrewise dimension is a functor
`Tot(A) → [2]^op`, i.e. antitone.  The content is that a bordism relates a singular cell only
to singular cells. -/
theorem dimsigOf_antitone : Antitone A.dimsigOf := by
  rintro p q ⟨h, hrel⟩ i
  show (A.fib q.1).toOneTruss.dim q.2 ≤ (A.fib p.1).toOneTruss.dim p.2
  rcases OneTruss.eq_zero_or_one ((A.fib p.1).toOneTruss.dim p.2) with hp | hp
  · have hq : (A.fib q.1).toOneTruss.IsSingular q.2 :=
      Geometry.Bord1.isSingular_of_rel_of_isSingular (A.arr h) (A.fib p.1).isOpen hp hrel
    rw [hp, hq]
  · rw [hp]
    exact Fin.le_last _

end OpenBundle

/-! ### Base-preserving structural bundle maps -/

/-- **Source: `def:n-bundle-map` at height one, base-preserving (§5.4's category `K`).**
A family of 1-truss maps on the fibres whose total map is face-monotone, i.e. compatible with
every arrow-fibre bordism.  The base component is the identity by construction. -/
structure BundleMap (A A' : OpenBundle B) where
  /-- The 1-truss map on each fibre. -/
  fibMap : ∀ b : B, Geometry.TrussMap (A.fib b).toOneTruss (A'.fib b).toOneTruss
  /-- The total map is face-monotone. -/
  face : ∀ {b c : B} (h : b ≤ c) {x : (A.fib b).toOneTruss.El} {y : (A.fib c).toOneTruss.El},
    (A.arr h).rel x y → (A'.arr h).rel (fibMap b x) (fibMap c y)

namespace BundleMap

variable {A A' A'' : OpenBundle B}

@[ext] theorem ext {q r : BundleMap A A'} (h : ∀ b x, q.fibMap b x = r.fibMap b x) : q = r := by
  cases q with
  | mk qf _ =>
    cases r with
    | mk rf _ =>
      have hf : qf = rf := funext fun b => Geometry.TrussMap.ext (h b)
      subst hf
      rfl

/-- The identity bundle map. -/
def id (A : OpenBundle B) : BundleMap A A where
  fibMap _ := Geometry.TrussMap.id _
  face := fun {_ _} _ {_ _} hrel => hrel

/-- Composition of bundle maps. -/
def comp (r : BundleMap A' A'') (q : BundleMap A A') : BundleMap A A'' where
  fibMap b := (r.fibMap b).comp (q.fibMap b)
  face := fun {_ _} h {_ _} hrel => r.face h (q.face h hrel)

@[simp] theorem id_fibMap (A : OpenBundle B) (b : B) (x : (A.fib b).toOneTruss.El) :
    (BundleMap.id A).fibMap b x = x := rfl

@[simp] theorem comp_fibMap (r : BundleMap A' A'') (q : BundleMap A A') (b : B)
    (x : (A.fib b).toOneTruss.El) : (r.comp q).fibMap b x = r.fibMap b (q.fibMap b x) := rfl

/-- The induced map of total posets. -/
def totHom (q : BundleMap A A') : A.Tot →o A'.Tot where
  toFun p := ⟨p.1, q.fibMap p.1 p.2⟩
  monotone' _ _ := by rintro ⟨h, hrel⟩; exact ⟨h, q.face h hrel⟩

@[simp] theorem totHom_apply (q : BundleMap A A') (p : A.Tot) :
    q.totHom p = ⟨p.1, q.fibMap p.1 p.2⟩ := rfl

/-- A bundle map is determined by its total map: `Tot` is faithful. -/
theorem totHom_injective {q r : BundleMap A A'} (h : q.totHom = r.totHom) : q = r := by
  refine BundleMap.ext fun b x => ?_
  have hb : (⟨b, q.fibMap b x⟩ : A'.Tot) = ⟨b, r.fibMap b x⟩ :=
    congrArg (fun k : A.Tot →o A'.Tot => k ⟨b, x⟩) h
  simpa using hb

end BundleMap

/-! ### `K` is a 1-truss-like category -/

namespace OpenBundle

instance instCategory : Category (OpenBundle B) where
  Hom A A' := BundleMap A A'
  id A := BundleMap.id A
  comp q r := r.comp q
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem id_fib (A : OpenBundle B) (b : B) (x : (A.fib b).toOneTruss.El) :
    (𝟙 A : BundleMap A A).fibMap b x = x := rfl

@[simp] theorem comp_fib {A A' A'' : OpenBundle B} (q : A ⟶ A') (r : A' ⟶ A'') (b : B)
    (x : (A.fib b).toOneTruss.El) :
    ((q ≫ r : A ⟶ A'')).fibMap b x = r.fibMap b (q.fibMap b x) := rfl

variable (B) in
/-- The total-poset functor of §5.4. -/
noncomputable def totFunctor [Finite B] : OpenBundle B ⥤ FinPartOrd.{u} where
  obj A := FinPartOrd.of A.Tot
  map q := FinPartOrd.ofHom q.totHom
  map_id _ := FinPartOrd.hom_ext (by ext p; rfl)
  map_comp _ _ := FinPartOrd.hom_ext (by ext p; rfl)

/-- **Source: §5.4 section context.**  The category of fibrewise-open 1-truss bundles over a
finite poset is 1-truss-like, with `Tot` the total poset and `dimsig` the fibrewise
dimension. -/
noncomputable instance instTrussLike [Finite B] : TrussLike 1 (OpenBundle B) where
  tot := totFunctor B
  tot_faithful := ⟨fun h => BundleMap.totHom_injective (congrArg (fun f => f.hom.hom) h)⟩
  dimsig A := A.dimsigOf
  dimsig_antitone A := A.dimsigOf_antitone

@[simp] theorem totMap_apply [Finite B] {A A' : OpenBundle B} (q : A ⟶ A') (p : A.Tot) :
    TrussLike.totMap q p = ⟨p.1, q.fibMap p.1 p.2⟩ := rfl

@[simp] theorem dimsig_apply [Finite B] (A : OpenBundle B) (p : A.Tot) (i : Fin 1) :
    TrussLike.dimsig A p i = (A.fib p.1).toOneTruss.dim p.2 := rfl

end OpenBundle

end Truss.Transfer
