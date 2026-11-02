/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.Bundle
import Truss.Transfer.Normalisation.NonTriv

/-!
# Fibres of a bundle, retained families and `NonTriv` (§5.4, rows B03 and B07)

This module connects §5.4's fibrewise language to the 1-truss theory of §5.3.

## Main definitions

* `OpenBundle.fibreIncl` — the inclusion of a point fibre into the total poset, an order
  embedding (the fibre order is the identity-arrow bordism, by `arr_id`).
* `OpenBundle.restrictLabel` — `L|_(A_b)`, the restriction of a label to a fibre.
* `OpenBundle.retFam` — `ret(q) = (ret(q_b))_b`, the **retained singular family** of a
  bundle coarsening (`def:Singular family`).
* `OpenBundle.nonTrivFam` — `NonTriv(A,L) = (NonTriv(A_b, L|_(A_b)))_b`.

## Main results

* `OpenBundle.retFam_isForwardStable` — **the chapter's unnamed lemma "the retained family of
  any coarsening is forward-stable"**.  The proof is short in this presentation: `σ` relates
  the singular cell `i` of `A_b` to `σ(i)` in `A_c`, the bundle map carries that relation over
  to `A'`, and a bordism between *open* 1-trusses relates a singular cell only to singular
  cells — so a retained cell stays retained.
* `OpenBundle.collapsed_in_fibre` — every arrow collapsed by a base-preserving bundle map lies
  in a single base fibre, which is the first step of
  `prop:Outgoing labelled bundle coarsenings`.
-/

universe u v

namespace Truss.Transfer

open CategoryTheory Geometry Geometry.OneTruss TrussLike

variable {B : Type u} [PartialOrder B]

namespace OpenBundle

variable (A A' : OpenBundle B)

/-! ### Point fibres -/

/-- The inclusion of the point fibre over `b` into the total poset. -/
def fibreIncl (b : B) : (A.fib b).toOneTruss.El →o A.Tot where
  toFun x := ⟨b, x⟩
  monotone' _ _ h := ⟨le_rfl, (A.arr_id b _ _).2 h⟩

@[simp] theorem fibreIncl_apply (b : B) (x : (A.fib b).toOneTruss.El) :
    A.fibreIncl b x = ⟨b, x⟩ := rfl

/-- The fibre inclusion reflects the order: the fibre carries the identity-arrow bordism,
which `arr_id` identifies with the face order of `A_b`. -/
theorem fibreIncl_le_iff (b : B) (x y : (A.fib b).toOneTruss.El) :
    A.fibreIncl b x ≤ A.fibreIncl b y ↔ x ≤ y := by
  constructor
  · rintro ⟨h, hrel⟩
    exact (A.arr_id b x y).1 hrel
  · intro h
    exact ⟨le_rfl, (A.arr_id b x y).2 h⟩

/-- **Source: §5.4.**  Every arrow of the total poset that is collapsed by a base-preserving
bundle map lies inside a single base fibre: equality of images forces equality of the base
projections. -/
theorem collapsed_in_fibre {A A' : OpenBundle B} (q : BundleMap A A') {p p' : A.Tot}
    (h : q.totHom p = q.totHom p') : p.1 = p'.1 :=
  congrArg (fun t : A'.Tot => t.1) h

/-! ### Restricting a label to a fibre -/

variable {C : Type v} [Category C]

/-- **Source: §5.4, `L|_(A_b)`.** -/
def restrictLabel (L : A.Tot ⥤ C) (b : B) : (A.fib b).toOneTruss.El ⥤ C :=
  posetFunctor (A.fibreIncl b) ⋙ L

@[simp] theorem restrictLabel_obj (L : A.Tot ⥤ C) (b : B) (x : (A.fib b).toOneTruss.El) :
    (A.restrictLabel L b).obj x = L.obj ⟨b, x⟩ := rfl

/-! ### The retained family and the non-trivially labelled family -/

variable {A A'}

/-- **Source: `def:Singular family` (§5.4).**  The retained singular family of a bundle
coarsening: fibrewise, the singular cells whose image is again singular. -/
def retFam (q : A ⟶ A') (b : B) : Set (Fin (A.fib b).numSing) :=
  {i | (A'.fib b).toOneTruss.IsSingular ((q.fibMap b).toFun ((A.fib b).singEl rfl i))}

theorem mem_retFam {q : A ⟶ A'} {b : B} {i : Fin (A.fib b).numSing} :
    i ∈ retFam q b ↔ (A'.fib b).toOneTruss.IsSingular ((q.fibMap b).toFun
      ((A.fib b).singEl rfl i)) := Iff.rfl

/-- **Source: §5.4, the lemma "the retained family of any coarsening is forward-stable".**

In this presentation the proof is three steps: `σ` relates the singular cell `i` of `A_b` to
`σ(i)` in `A_c`; the bundle map carries that relation to `A'`; and a bordism between **open**
1-trusses relates a singular cell only to singular cells.  Note that no coarsening hypothesis
is used — the statement holds for every base-preserving bundle map. -/
theorem retFam_isForwardStable (q : A ⟶ A') :
    A.singTransport.IsForwardStable (retFam q) := by
  rw [Transport.isForwardStable_iff]
  intro b c h i hi
  -- `σ` relates the singular cell `i` to `σ(i)`
  have hrel := A.sigma_rel h i
  -- the bundle map carries the relation over
  have hrel' := q.face h hrel
  -- the source is singular in `A'_b`, hence so is the target in `A'_c`
  have hsing : (A'.fib b).toOneTruss.IsSingular ((q.fibMap b).toFun ((A.fib b).singEl rfl i)) :=
    hi
  have := Geometry.Bord1.isSingular_of_rel_of_isSingular (A'.arr h) (A'.fib b).isOpen hsing hrel'
  exact this

variable (A) in
/-- **Source: §5.4.**  The non-trivially labelled singular family of a labelled bundle. -/
noncomputable def nonTrivFam (L : A.Tot ⥤ C) (b : B) : Set (Fin (A.fib b).numSing) :=
  ↑(NonTriv (A.fib b) (A.restrictLabel L b))

theorem mem_nonTrivFam {L : A.Tot ⥤ C} {b : B} {i : Fin (A.fib b).numSing} :
    i ∈ A.nonTrivFam L b ↔ IsNonTriv (A.fib b) (A.restrictLabel L b) i := by
  simp [nonTrivFam]

/-- The forward-stable closure of the non-trivially labelled family: the chapter's
`\overline{NonTriv(A,L)}`, which `cor:coarsening-normalising-iff-return-equals-nontrivial`
compares with the retained family. -/
noncomputable def nonTrivClosure (L : A.Tot ⥤ C) : A.singTransport.Family :=
  A.singTransport.closure (A.nonTrivFam L)

theorem nonTrivClosure_isForwardStable (L : A.Tot ⥤ C) :
    A.singTransport.IsForwardStable (A.nonTrivClosure L) :=
  A.singTransport.closure_isForwardStable _

/-- The closure is contained in a retained family exactly when the bare family is: this is
the chapter's *"equivalently, `R(A,L)` consists of families `U` with
`\overline{NonTriv(A,L)} ⊆ U`"*. -/
theorem nonTrivClosure_le_iff (L : A.Tot ⥤ C) (U : A.singTransport.Family)
    (hU : A.singTransport.IsForwardStable U) :
    A.nonTrivClosure L ≤ U ↔ A.nonTrivFam L ≤ U :=
  ⟨fun h => (A.singTransport.le_closure _).trans h, fun h => A.singTransport.closure_le h hU⟩

end OpenBundle

end Truss.Transfer
