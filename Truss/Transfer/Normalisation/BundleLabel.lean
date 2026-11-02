/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.BundleFibre

/-!
# Labelled bundle coarsenings (§5.4, rows B02-forward and B08)

Two things are proved here.

* **The easy half of `prop:fibrewise-characterisation-bundle-coarsenings`** (row `B02`):
  a coarsening of bundles restricts to a coarsening on every fibre.  Object-surjectivity
  restricts because the map is base-preserving, and the dimension inequality *is* fibrewise
  regularity-preservation.  (The converse — that fibrewise coarsenings assemble — is the
  substantive direction and is not proved here.)
* **`prop:Outgoing labelled bundle coarsenings`** (row `B08`), the label criterion:
  a bundle coarsening is label-preserving exactly when `NonTriv(A,L) ⊆ ret(q)`, equivalently
  (since `ret(q)` is forward-stable) exactly when `\overline{NonTriv(A,L)} ⊆ ret(q)`.
  The chapter's proof is followed step for step: collapsed arrows lie in a single base fibre,
  so they are precisely the arrows collapsed by the fibre maps, and §5.3's labelled 1-truss
  criterion then applies fibrewise.
-/

universe u v

namespace Truss.Transfer

open CategoryTheory Geometry Geometry.OneTruss TrussLike

variable {B : Type u} [PartialOrder B] [Finite B]

namespace OpenBundle

/-! ### The forward half of the fibrewise characterisation -/

/-- The fibre map of a bundle map, as a morphism of open 1-trusses. -/
def fibHom {A A' : OpenBundle B} (q : A ⟶ A') (b : B) : A.fib b ⟶ A'.fib b := q.fibMap b

omit [Finite B] in
@[simp] theorem fibHom_toFun {A A' : OpenBundle B} (q : A ⟶ A') (b : B)
    (x : (A.fib b).toOneTruss.El) : (fibHom q b).toFun x = q.fibMap b x := rfl

omit [Finite B] in
/-- Two points of the total poset in the **same** fibre are equal exactly when their fibre
components are. -/
theorem tot_mk_inj {A : OpenBundle B} {b : B} {x y : (A.fib b).toOneTruss.El}
    (h : (⟨b, x⟩ : A.Tot) = ⟨b, y⟩) : x = y := by
  have h' : (⟨b, x⟩ : Σ c : B, (A.fib c).toOneTruss.El) = ⟨b, y⟩ := h
  simpa using h'

/-- **Source: `prop:fibrewise-characterisation-bundle-coarsenings` (§5.4), forward half.**
A coarsening of fibrewise-open 1-truss bundles restricts to a coarsening on every fibre. -/
theorem isCoarsening_fibHom {A A' : OpenBundle B} {q : A ⟶ A'} (hq : IsCoarsening q) (b : B) :
    IsCoarsening (fibHom q b) := by
  rw [isCoarsening_iff_surjective_regular]
  constructor
  · -- object-surjectivity restricts, because the map is base-preserving
    intro u
    obtain ⟨p, hp⟩ := hq.tot.surjective (⟨b, u⟩ : A'.Tot)
    have hb : p.1 = b := congrArg (fun t : A'.Tot => t.1) hp
    obtain ⟨pb, px⟩ := p
    subst hb
    exact ⟨px, tot_mk_inj hp⟩
  · -- the dimension inequality is fibrewise regularity-preservation
    intro x hx
    have hd := hq.dimsig_le (⟨b, x⟩ : A.Tot) ⟨0, Nat.zero_lt_one⟩
    simp only [dimsig_apply, totMap_apply] at hd
    rw [hx] at hd
    have : (A'.fib b).toOneTruss.dim ((q.fibMap b).toFun x) = 1 := le_antisymm (Fin.le_last _) hd
    exact this

/-! ### The label criterion -/

variable {C : Type v} [Category C]

/-- A collapsed comparison of the total poset is a comparison **inside one fibre** that the
fibre map collapses.  This is the chapter's *"any arrow collapsed by `Tot(q)` lies in a single
fibre: equality of the images of its endpoints forces equality of their projections to `B`"*. -/
theorem collapsed_iff_fibrewise {A A' : OpenBundle B} (q : A ⟶ A') (L : A.Tot ⥤ C) :
    SendsCollapsedToId (TrussLike.totMap q) L ↔
      ∀ b : B, SendsCollapsedToId (TrussLike.totMap (fibHom q b))
        (A.restrictLabel L b) := by
  constructor
  · intro h b x y hxy hcol
    obtain ⟨e, he⟩ := h ⟨b, x⟩ ⟨b, y⟩ ((A.fibreIncl_le_iff b x y).2 hxy) (by
      show (⟨b, (q.fibMap b).toFun x⟩ : A'.Tot) = ⟨b, (q.fibMap b).toFun y⟩
      exact congrArg _ hcol)
    exact ⟨e, he⟩
  · intro h p p' hpp' hcol
    have hb : p.1 = p'.1 := congrArg (fun t : A'.Tot => t.1) hcol
    obtain ⟨b, x⟩ := p
    obtain ⟨b', y⟩ := p'
    simp only at hb
    subst hb
    have hxy : x ≤ y := (A.fibreIncl_le_iff b x y).1 hpp'
    have hcol' : (q.fibMap b).toFun x = (q.fibMap b).toFun y := tot_mk_inj hcol
    obtain ⟨e, he⟩ := h b x y hxy hcol'
    exact ⟨e, he⟩

/-- **Source: `prop:Outgoing labelled bundle coarsenings` (§5.4).**  A bundle coarsening is
label-preserving exactly when every fibrewise non-trivially labelled singular cell is
retained. -/
theorem descendsAlong_iff_nonTrivFam_le {A A' : OpenBundle B} (q : A ⟶ A')
    (hq : IsCoarsening q) (L : A.Tot ⥤ C) :
    DescendsAlong q L ↔ A.nonTrivFam L ≤ retFam q := by
  rw [DescendsAlong, collapsed_iff_fibrewise]
  constructor
  · intro h b i hi
    exact (sendsCollapsedToId_iff_nonTriv_retained (fibHom q b) (isCoarsening_fibHom hq b)
      (A.restrictLabel L b)).1 (h b) i (by simpa [nonTrivFam] using hi)
  · intro h b
    refine (sendsCollapsedToId_iff_nonTriv_retained (fibHom q b) (isCoarsening_fibHom hq b)
      (A.restrictLabel L b)).2 ?_
    intro i hi
    exact h b (by simpa [nonTrivFam] using hi)

/-- **Source: `prop:Outgoing labelled bundle coarsenings` (§5.4), the closed form.**
Since `ret(q)` is forward-stable, the criterion may equally be stated with the forward-stable
closure of `NonTriv(A,L)`. -/
theorem descendsAlong_iff_nonTrivClosure_le {A A' : OpenBundle B} (q : A ⟶ A')
    (hq : IsCoarsening q) (L : A.Tot ⥤ C) :
    DescendsAlong q L ↔ A.nonTrivClosure L ≤ retFam q := by
  rw [descendsAlong_iff_nonTrivFam_le q hq L, nonTrivClosure]
  exact ⟨fun h => A.singTransport.closure_le h (retFam_isForwardStable q),
    fun h => (A.singTransport.le_closure _).trans h⟩

end OpenBundle

end Truss.Transfer
