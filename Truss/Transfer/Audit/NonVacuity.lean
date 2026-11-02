/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.Terminality
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Non-vacuity and diagnostic audit of the draft normalisation interface (§9, §3.3)

This module discharges the audit asked for by §9 and §3.3 of
[`plan/DraftNormalisationVerification.md`](../../../plan/DraftNormalisationVerification.md):
the abstract interface of `Truss.Transfer.Normalisation` is shown to be *inhabited*, its
label categories are shown to be *non-degenerate*, and the arrow-fibre-connectivity clause of
`IsPosetCoarsening` is shown to be *necessary* for `prop:draft-label-descent`.

## Contents

* **(A) `TrussLike` is inhabited.**  `finPosTrussLike` is the honest model
  `K = FinPos`, `Tot = 𝟭`, constant dimension signature.  `finPos_isCoarsening_iff` records
  that the dimension clause of `def:draft-coarsening` is vacuous there, so a coarsening in
  this model is exactly a poset coarsening.  `isPosetCoarsening_chainToPoint` exhibits a
  specific non-injective (hence non-invertible) coarsening.
* **(B) Non-degenerate label categories.**  `labDiscrete`, `labFinTwo` and
  `labParallelPair` use, as the label category `C` of a `LabObj`, respectively the terminal
  category `Discrete PUnit`, the two-element poset category `Fin 2`, and the gaunt category
  `WalkingParallelPair`, which carries the parallel non-identity arrows
  `left ≠ right` (`walkingParallelPairHom_left_ne_right`).
* **(C) The key diagnostic.**  `q4` is an open, object-surjective monotone map with connected
  *point* fibres and a disconnected *arrow* fibre.  Labelling its source by
  `parallelLabel : V4 ⥤ WalkingParallelPair` gives a label that sends every collapsed arrow
  to an identity and yet does **not** descend:
  `arrowFibre_connectivity_necessary`.  Hence `SendsCollapsedToId` alone is not sufficient
  for `prop:draft-label-descent`; the arrow-fibre clause of `IsPosetCoarsening` is load
  bearing.
* **(D) Surjectivity does not imply openness.**  `q3` is surjective on objects and on arrows
  but is not open (`q3_not_isOpen`), hence not a poset coarsening.

## Conventions

The two counterexample posets are small `inductive` types with a `Bool`-valued order, so that
`DecidableRel` is available and the order axioms, monotonicity, surjectivity and openness are
all discharged by `decide`.  Zigzag connectivity is not decidable (it is a reflexive
transitive closure), so those facts are proved by hand from
`isZigzagConnected_of_forall_zigzag`.
-/

universe u

namespace Truss.Transfer.Audit

open CategoryTheory CategoryTheory.Limits TrussLike

/-! ### A zigzag helper -/

/-- A set with a member comparable-by-zigzag to every other member is zigzag connected. -/
theorem isZigzagConnected_of_forall_zigzag {α : Type*} [Preorder α] {S : Set α} {m : α}
    (h : ∀ p ∈ S, ZigzagIn S p m) : IsZigzagConnected S :=
  fun p hp r hr => (h p hp).trans (h r hr).symm

/-! ## (A) `TrussLike` is inhabited -/

/-- **Plan §9, inhabitation.**  The honest model of `def:n-truss-like category`: the category
of finite posets, with `Tot` the identity functor and the constant dimension signature.  This
is deliberately a `def` and not a global `instance`: the dimension index `n` of `TrussLike` is
an `outParam`, so a global instance for every `n` would make instance resolution ambiguous.
Use it with `letI := finPosTrussLike n`. -/
def finPosTrussLike (n : ℕ) : TrussLike n FinPartOrd.{u} where
  tot := 𝟭 _
  tot_faithful := inferInstance
  dimsig _ _ := fun _ => 0
  dimsig_antitone _ := fun _ _ _ => le_rfl

/-- **Plan §9.**  In the model `finPosTrussLike` the dimension clause of
`def:draft-coarsening` is vacuous: a coarsening of finite posets is exactly a poset
coarsening in the sense of §5.1.  This is what makes the model *honest* rather than
*degenerate-by-construction*: the whole content of `IsCoarsening` here is `IsPosetCoarsening`,
which the rest of this file shows is a genuinely restrictive condition. -/
theorem finPos_isCoarsening_iff {n : ℕ} {X Y : FinPartOrd.{u}} (q : X ⟶ Y) :
    @IsCoarsening n FinPartOrd.{u} _ (finPosTrussLike n) X Y q ↔
      IsPosetCoarsening q.hom.hom := by
  letI := finPosTrussLike.{u} n
  constructor
  · intro h; exact h.tot
  · intro h; exact ⟨h, fun _ => le_rfl⟩

/-- The monotone collapse of the two-element chain onto the point. -/
def chainToPoint : Fin 2 →o Fin 1 where
  toFun _ := 0
  monotone' := by decide

/-- **Plan §9, a specific non-identity coarsening.**  The collapse of the two-element chain
onto the point is a poset coarsening: it is surjective, open (the target is a point, so exact
target lifting is trivial), and its single arrow fibre — all three arrows of the two-element
chain — is connected through the arrow `0 ≤ 1`. -/
theorem isPosetCoarsening_chainToPoint : IsPosetCoarsening chainToPoint := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [isOpenPosetMap_iff_exists_le chainToPoint.monotone]; decide
  · intro y y' _
    have hm : (⟨0, 1, by decide⟩ : Arr (Fin 2)) ∈ arrowFibre chainToPoint y y' :=
      ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    refine isZigzagConnected_of_forall_zigzag (m := (⟨0, 1, by decide⟩ : Arr (Fin 2))) ?_
    intro A hA
    have key : ∀ s t : Fin 2, s ≤ t →
        ((s ≤ (0 : Fin 2) ∧ t ≤ (1 : Fin 2)) ∨ ((0 : Fin 2) ≤ s ∧ (1 : Fin 2) ≤ t)) := by decide
    rcases key A.src A.tgt A.le with h | h
    · exact ZigzagIn.of_le hA hm h
    · exact ZigzagIn.of_ge hA hm h

/-- The witnessing coarsening is not an isomorphism: it is not injective.  So the model
`finPosTrussLike` carries coarsenings other than the identities. -/
theorem chainToPoint_not_injective : ¬ Function.Injective chainToPoint := by
  intro h
  exact absurd (h (a₁ := 0) (a₂ := 1) (Subsingleton.elim _ _)) (by decide)

/-! ## (B) Label categories that are not degenerate -/

/-- **Plan §9, gauntness witness.**  `WalkingParallelPair` carries two *distinct* parallel
non-identity arrows `zero ⟶ one`.  This is what makes it a usable probe for the failure of
label descent in part (C): a label category in which every parallel pair of arrows agreed
could never detect it. -/
theorem walkingParallelPairHom_left_ne_right :
    (WalkingParallelPairHom.left : WalkingParallelPair.zero ⟶ WalkingParallelPair.one) ≠
      WalkingParallelPairHom.right := by decide

/-- **(B.1)** A labelled object whose label category is the terminal category. -/
def labDiscrete : @LabObj 1 FinPartOrd.{0} _ (finPosTrussLike 1) (Discrete PUnit) _ :=
  letI := finPosTrussLike.{0} 1
  { obj := FinPartOrd.of (Fin 2)
    label := (Functor.const _).obj ⟨PUnit.unit⟩ }

/-- **(B.2)** A labelled object whose label category is the non-trivial finite poset category
`Fin 2`, labelled by the identity — so the label really does separate the two points. -/
def labFinTwo : @LabObj 1 FinPartOrd.{0} _ (finPosTrussLike 1) (Fin 2) _ :=
  letI := finPosTrussLike.{0} 1
  { obj := FinPartOrd.of (Fin 2)
    label := 𝟭 _ }

/-! ## (C) Arrow-fibre connectivity is necessary for label descent

The source poset `V4` has two minimal elements `a`, `b` and two *incomparable* maximal
elements `c`, `u`, with `a, b < c` and `a, b < u`.  The map `q4` collapses `{a, b, c}` to the
bottom of the two-element chain and sends `u` to the top. -/

/-- The four-element poset `a, b < c`, `a, b < u`, with `c` and `u` incomparable. -/
inductive V4 : Type
  | /-- a minimal element -/ a
  | /-- the other minimal element -/ b
  | /-- a maximal element -/ c
  | /-- the other maximal element -/ u
  deriving DecidableEq, Repr

instance : Fintype V4 where
  elems := {V4.a, V4.b, V4.c, V4.u}
  complete := by intro x; cases x <;> decide

/-- The order relation of `V4`, as a decidable `Bool`-valued table. -/
def V4.leb : V4 → V4 → Bool
  | .a, .a => true
  | .a, .c => true
  | .a, .u => true
  | .b, .b => true
  | .b, .c => true
  | .b, .u => true
  | .c, .c => true
  | .u, .u => true
  | _, _ => false

/-- The order relation of `V4`, as a `Prop`. -/
protected def V4.le (x y : V4) : Prop := V4.leb x y = true

instance : DecidableRel V4.le := fun x y => inferInstanceAs (Decidable (V4.leb x y = true))

instance : PartialOrder V4 where
  le := V4.le
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableRel ((· ≤ ·) : V4 → V4 → Prop) :=
  fun x y => inferInstanceAs (Decidable (V4.leb x y = true))

/-- The two maximal elements of `V4` are incomparable; this is what disconnects the arrow
fibre below. -/
theorem V4.c_not_le_u : ¬ (V4.c ≤ V4.u) := by decide

/-- The collapse `a, b, c ↦ 0`, `u ↦ 1` onto the two-element chain. -/
def q4 : V4 →o Fin 2 where
  toFun
    | .u => 1
    | _ => 0
  monotone' := by decide

/-- **(C.1)** `q4` is surjective on objects. -/
theorem q4_surjective : Function.Surjective q4 := by decide

/-- **(C.2)** `q4` is open: the only non-trivial lifting problem is `0 ≤ q4 u`, solved by
`a ≤ u`. -/
theorem q4_isOpen : IsOpenPosetMap q4 := by
  rw [isOpenPosetMap_iff_exists_le q4.monotone]; decide

/-- The point fibre of `q4` over the bottom is `{a, b, c}`, connected through `c`. -/
theorem q4_pointFibre_zero_connected : IsZigzagConnected (pointFibre q4 0) := by
  have hc : V4.c ∈ pointFibre q4 (0 : Fin 2) := rfl
  refine isZigzagConnected_of_forall_zigzag (m := V4.c) ?_
  intro p hp
  have hp' : q4 p = 0 := hp
  cases p
  · exact ZigzagIn.of_le rfl hc (by decide)
  · exact ZigzagIn.of_le rfl hc (by decide)
  · exact ZigzagIn.refl _
  · exact absurd hp' (by decide)

/-- The point fibre of `q4` over the top is the singleton `{u}`. -/
theorem q4_pointFibre_one_connected : IsZigzagConnected (pointFibre q4 1) := by
  have hu : V4.u ∈ pointFibre q4 (1 : Fin 2) := rfl
  refine isZigzagConnected_of_forall_zigzag (m := V4.u) ?_
  intro p hp
  have hp' : q4 p = 1 := hp
  cases p
  · exact absurd hp' (by decide)
  · exact absurd hp' (by decide)
  · exact absurd hp' (by decide)
  · exact ZigzagIn.refl _

/-- **(C.3)** *Every* point fibre of `q4` is zigzag connected. -/
theorem q4_pointFibre_connected (y : Fin 2) : IsZigzagConnected (pointFibre q4 y) := by
  have h : ∀ z : Fin 2, z = 0 ∨ z = 1 := by decide
  rcases h y with rfl | rfl
  · exact q4_pointFibre_zero_connected
  · exact q4_pointFibre_one_connected

/-- Inside the arrow fibre of `q4` over `0 ≤ 1` the target is forced to be `u` and the source
is forced into `{a, b}`; since `a` and `b` are incomparable, a comparison of two members of
that fibre forces their sources to agree. -/
theorem q4_src_eq_of_le_in_arrowFibre {A B : Arr V4} (hA : A ∈ arrowFibre q4 0 1)
    (hB : B ∈ arrowFibre q4 0 1) (hAB : A ≤ B) : A.src = B.src := by
  have key : ∀ s t s' t' : V4, s ≤ t → s' ≤ t' → q4 s = 0 → q4 t = 1 → q4 s' = 0 →
      q4 t' = 1 → s ≤ s' → s = s' := by decide
  exact key A.src A.tgt B.src B.tgt A.le B.le hA.1 hA.2 hB.1 hB.2 hAB.1

/-- The source of an arrow is a zigzag invariant inside the arrow fibre of `q4` over `0 ≤ 1`. -/
theorem q4_src_const_of_zigzag {A B : Arr V4} (h : ZigzagIn (arrowFibre q4 0 1) A B) :
    A.src = B.src := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      refine ih.trans ?_
      rcases hstep.2.2 with hle | hle
      · exact q4_src_eq_of_le_in_arrowFibre hstep.1 hstep.2.1 hle
      · exact (q4_src_eq_of_le_in_arrowFibre hstep.2.1 hstep.1 hle).symm

/-- The arrow fibre of `q4` over `0 ≤ 1` is exactly `{(a, u), (b, u)}`: the target must be
`u`, and the source must be one of the two minimal elements, because `c` is not below `u`. -/
theorem q4_mem_arrowFibre_iff (A : Arr V4) :
    A ∈ arrowFibre q4 0 1 ↔ (A.src = V4.a ∨ A.src = V4.b) ∧ A.tgt = V4.u := by
  constructor
  · intro hA
    have key : ∀ s t : V4, s ≤ t → q4 s = 0 → q4 t = 1 →
        ((s = V4.a ∨ s = V4.b) ∧ t = V4.u) := by decide
    exact key A.src A.tgt A.le hA.1 hA.2
  · rintro ⟨hs, ht⟩
    refine ⟨?_, by rw [ht]; rfl⟩
    rcases hs with h | h
    · rw [h]; rfl
    · rw [h]; rfl

/-- `(a, u)` lies in the arrow fibre of `q4` over `0 ≤ 1`. -/
theorem q4_au_mem : (⟨V4.a, V4.u, by decide⟩ : Arr V4) ∈ arrowFibre q4 0 1 := ⟨rfl, rfl⟩

/-- `(b, u)` lies in the arrow fibre of `q4` over `0 ≤ 1`. -/
theorem q4_bu_mem : (⟨V4.b, V4.u, by decide⟩ : Arr V4) ∈ arrowFibre q4 0 1 := ⟨rfl, rfl⟩

/-- **(C.4)** The arrow fibre of `q4` over `0 ≤ 1` is `{(a, u), (b, u)}` and is *not*
connected: `a` and `b` are incomparable, so no zigzag inside the fibre joins the two arrows. -/
theorem q4_arrowFibre_not_connected : ¬ IsZigzagConnected (arrowFibre q4 0 1) := by
  intro h
  have := q4_src_const_of_zigzag (h _ q4_au_mem _ q4_bu_mem)
  exact absurd this (by decide)

/-- **(C.4)** Consequently `q4` is not a poset coarsening, although it is open, surjective and
has connected point fibres. -/
theorem q4_not_isPosetCoarsening : ¬ IsPosetCoarsening q4 := by
  intro h
  exact q4_arrowFibre_not_connected (h.arrowFibre_connected 0 1 (by decide))

/-! ### The label functor exposing the descent failure -/

/-- Object part of the probe label: `a, b, c ↦ zero` and `u ↦ one`. -/
def parallelLabelObj : V4 → WalkingParallelPair
  | .u => .one
  | _ => .zero

/-- Arrow part of the probe label: the two arrows `a ≤ u` and `b ≤ u` receive the two distinct
parallel arrows `left` and `right`; every arrow inside `{a, b, c}` receives an identity. -/
def parallelLabelMap : ∀ (x y : V4), x ≤ y → (parallelLabelObj x ⟶ parallelLabelObj y)
  | .a, .a, _ => 𝟙 _
  | .a, .c, _ => 𝟙 _
  | .a, .u, _ => WalkingParallelPairHom.left
  | .b, .b, _ => 𝟙 _
  | .b, .c, _ => 𝟙 _
  | .b, .u, _ => WalkingParallelPairHom.right
  | .c, .c, _ => 𝟙 _
  | .u, .u, _ => 𝟙 _
  | .a, .b, h => absurd h (by decide)
  | .b, .a, h => absurd h (by decide)
  | .c, .a, h => absurd h (by decide)
  | .c, .b, h => absurd h (by decide)
  | .c, .u, h => absurd h (by decide)
  | .u, .a, h => absurd h (by decide)
  | .u, .b, h => absurd h (by decide)
  | .u, .c, h => absurd h (by decide)

/-- **(C.5)** The probe label `L : V4 ⥤ WalkingParallelPair`. -/
def parallelLabel : V4 ⥤ WalkingParallelPair where
  obj := parallelLabelObj
  map {x y} h := parallelLabelMap x y (leOfHom h)
  map_id x := by cases x <;> rfl
  map_comp {x y z} f g := by
    have h1 := leOfHom f
    have h2 := leOfHom g
    revert h1 h2
    cases x <;> cases y <;> cases z <;> intro h1 h2 <;>
      first
        | rfl
        | exact absurd h1 (by decide)
        | exact absurd h2 (by decide)

/-- **(C.5), the descent hypothesis.**  `parallelLabel` sends every arrow collapsed by `q4` to
an identity — the collapsed arrows are exactly those inside `{a, b, c}` together with the
identity of `u`, and all of them are labelled by identities. -/
theorem sendsCollapsedToId_parallelLabel : SendsCollapsedToId q4 parallelLabel := by
  intro x y h hq
  revert h hq
  cases x <;> cases y <;> intro h hq <;>
    first
      | exact absurd h (by decide)
      | exact absurd hq (by decide)
      | exact ⟨rfl, rfl⟩

/-- A bookkeeping lemma: conjugation by object bridges is injective on morphisms. -/
private theorem eqToHom_conj_cancel {C : Type*} [Category C] {X Y X' Y' : C}
    (α β : X ⟶ Y) (p : X' = X) (q : Y = Y')
    (h : eqToHom p ≫ α ≫ eqToHom q = eqToHom p ≫ β ≫ eqToHom q) : α = β := by
  subst p; subst q; simpa using h

/-- **(C.5), THE KEY DIAGNOSTIC.**  The arrow-fibre-connectivity clause of
`IsPosetCoarsening` is *necessary* for `prop:draft-label-descent`.

`q4` is monotone, surjective on objects, open, and has connected point fibres
(`q4_surjective`, `q4_isOpen`, `q4_pointFibre_connected`); its only defect is the
disconnected arrow fibre over `0 ≤ 1` (`q4_arrowFibre_not_connected`).  The label
`parallelLabel` satisfies the descent criterion `SendsCollapsedToId`
(`sendsCollapsedToId_parallelLabel`), yet it does *not* factor through `q4`: a factorisation
`K` would send the unique arrow `0 ⟶ 1` of the base to a morphism whose pullback along `q4`
is simultaneously `left` (via `a ≤ u`) and `right` (via `b ≤ u`), forcing
`left = right` in the gaunt label category `WalkingParallelPair`.

So `SendsCollapsedToId` alone is **not** sufficient for label descent, and the hypothesis
`IsPosetCoarsening` in `label_descent` cannot be weakened to openness plus point-fibre
connectivity. -/
theorem arrowFibre_connectivity_necessary :
    ¬ ∃ K : Fin 2 ⥤ WalkingParallelPair, posetFunctor q4 ⋙ K = parallelLabel := by
  rintro ⟨K, hK⟩
  have hau : V4.a ≤ V4.u := by decide
  have hbu : V4.b ≤ V4.u := by decide
  have h1 := Functor.congr_hom hK (homOfLE hau)
  have h2 := Functor.congr_hom hK (homOfLE hbu)
  have hmid : (posetFunctor q4 ⋙ K).map (homOfLE hau)
      = (posetFunctor q4 ⋙ K).map (homOfLE hbu) :=
    congrArg (fun f : ((0 : Fin 2) ⟶ (1 : Fin 2)) => K.map f) (Subsingleton.elim _ _)
  rw [h1, h2] at hmid
  have hlr : parallelLabel.map (homOfLE hau) = parallelLabel.map (homOfLE hbu) :=
    eqToHom_conj_cancel _ _ _ _ hmid
  exact walkingParallelPairHom_left_ne_right hlr

/-- **(B.3)** A labelled object whose label category is the gaunt category
`WalkingParallelPair`, labelled by the probe functor of part (C).  This is the `LabObj` in
which the descent failure `arrowFibre_connectivity_necessary` lives. -/
def labParallelPair : @LabObj 1 FinPartOrd.{0} _ (finPosTrussLike 1) WalkingParallelPair _ :=
  letI := finPosTrussLike.{0} 1
  { obj := FinPartOrd.of V4
    label := parallelLabel }

/-! ## (D) Object- and arrow-surjectivity do not imply openness

`V3` is the disjoint union of the two-element chain `p0 < p1` with the isolated point `p2`;
`q3` sends `p0` to the bottom of the two-element chain and both `p1` and `p2` to the top. -/

/-- The three-element poset `p0 < p1`, with `p2` isolated. -/
inductive V3 : Type
  | /-- the bottom of the chain -/ p0
  | /-- the top of the chain -/ p1
  | /-- the isolated point -/ p2
  deriving DecidableEq, Repr

instance : Fintype V3 where
  elems := {V3.p0, V3.p1, V3.p2}
  complete := by intro x; cases x <;> decide

/-- The order relation of `V3`, as a decidable `Bool`-valued table. -/
def V3.leb : V3 → V3 → Bool
  | .p0, .p0 => true
  | .p0, .p1 => true
  | .p1, .p1 => true
  | .p2, .p2 => true
  | _, _ => false

/-- The order relation of `V3`, as a `Prop`. -/
protected def V3.le (x y : V3) : Prop := V3.leb x y = true

instance : DecidableRel V3.le := fun x y => inferInstanceAs (Decidable (V3.leb x y = true))

instance : PartialOrder V3 where
  le := V3.le
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableRel ((· ≤ ·) : V3 → V3 → Prop) :=
  fun x y => inferInstanceAs (Decidable (V3.leb x y = true))

/-- The collapse `p0 ↦ 0`, `p1, p2 ↦ 1` onto the two-element chain. -/
def q3 : V3 →o Fin 2 where
  toFun
    | .p0 => 0
    | _ => 1
  monotone' := by decide

/-- **(D.1)** `q3` is surjective on objects. -/
theorem q3_surjective : Function.Surjective q3 := by decide

/-- **(D.2)** `q3` is surjective on arrows: every arrow of the two-element chain is the image
of an arrow of `V3` (the arrow `0 ≤ 1` lifts to `p0 ≤ p1`). -/
theorem q3_arrMap_surjective : Function.Surjective (Arr.map q3) := by
  intro A
  have key : ∀ s t : Fin 2, s ≤ t → ∃ x y : V3, x ≤ y ∧ q3 x = s ∧ q3 y = t := by decide
  obtain ⟨x, y, hxy, hx, hy⟩ := key A.src A.tgt A.le
  exact ⟨⟨x, y, hxy⟩, Arr.ext hx hy⟩

/-- **(D.3)** `q3` is *not* open: `0 ≤ q3 p2` has no lift below `p2`, because `p2` is
isolated.  So object- and arrow-surjectivity are strictly weaker than openness. -/
theorem q3_not_isOpen : ¬ IsOpenPosetMap q3 := by
  rw [isOpenPosetMap_iff_exists_le q3.monotone]
  intro h
  obtain ⟨x, hx, hxq⟩ := h V3.p2 0 (by decide)
  revert hx hxq
  cases x <;> decide

/-- **(D.3)** Consequently `q3` is not a poset coarsening, although it is surjective on both
objects and arrows. -/
theorem q3_not_isPosetCoarsening : ¬ IsPosetCoarsening q3 := fun h => q3_not_isOpen h.isOpen

end Truss.Transfer.Audit

/-
## Axiom audit

Produced by `#print axioms` in `scratch/draft-normalisation/axioms.lean` (untracked output),
against the module built by `lake build Truss.Transfer.Audit.NonVacuity`.  Every declaration
stays inside `{propext, Classical.choice, Quot.sound}`; nothing depends on `sorryAx`.

```
'Truss.Transfer.Audit.finPosTrussLike'                    [propext, Classical.choice, Quot.sound]
'Truss.Transfer.Audit.finPos_isCoarsening_iff'            [propext, Classical.choice, Quot.sound]
'Truss.Transfer.Audit.isPosetCoarsening_chainToPoint'     [propext, Classical.choice, Quot.sound]
'Truss.Transfer.Audit.chainToPoint_not_injective'         [propext, Classical.choice, Quot.sound]
'Truss.Transfer.Audit.walkingParallelPairHom_left_ne_right'  does not depend on any axioms
'Truss.Transfer.Audit.labDiscrete'                        [propext, Classical.choice, Quot.sound]
'Truss.Transfer.Audit.labFinTwo'                          [propext, Classical.choice, Quot.sound]
'Truss.Transfer.Audit.labParallelPair'                    [propext, Classical.choice, Quot.sound]
'Truss.Transfer.Audit.q4_surjective'                      [propext, Classical.choice, Quot.sound]
'Truss.Transfer.Audit.q4_isOpen'                          [propext, Classical.choice, Quot.sound]
'Truss.Transfer.Audit.q4_pointFibre_connected'            [propext, Classical.choice, Quot.sound]
'Truss.Transfer.Audit.q4_mem_arrowFibre_iff'              [propext, Classical.choice, Quot.sound]
'Truss.Transfer.Audit.q4_arrowFibre_not_connected'        [propext, Classical.choice, Quot.sound]
'Truss.Transfer.Audit.q4_not_isPosetCoarsening'           [propext, Classical.choice, Quot.sound]
'Truss.Transfer.Audit.parallelLabel'                      [propext, Quot.sound]
'Truss.Transfer.Audit.sendsCollapsedToId_parallelLabel'   [propext, Classical.choice, Quot.sound]
'Truss.Transfer.Audit.arrowFibre_connectivity_necessary'  [propext, Classical.choice, Quot.sound]
'Truss.Transfer.Audit.q3_surjective'                      [propext, Classical.choice, Quot.sound]
'Truss.Transfer.Audit.q3_arrMap_surjective'               [propext, Classical.choice, Quot.sound]
'Truss.Transfer.Audit.q3_not_isOpen'                      [propext, Classical.choice, Quot.sound]
'Truss.Transfer.Audit.q3_not_isPosetCoarsening'           [propext, Classical.choice, Quot.sound]
```
-/
