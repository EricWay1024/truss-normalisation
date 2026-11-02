/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.Section54

/-!
# The retraction half of `prop:draft-outcoarse-1-bundle-poset-iso` (§5.4, row `B05`)

`BundleQuotient.lean` supplies the **section** of the draft chapter's poset isomorphism
`OutCoarse(A) ≃ R(A)^op`: a forward-stable family `U` gives a bundle coarsening
`q_U : A ⟶ A^U` whose retained family is `U` again.  This module supplies the **retraction**,
the clause the commented proof of `prop:draft-outcoarse-1-bundle-poset-iso` ends with —

> *"These constructions recover `q` and `U`."*

— namely that *every* bundle coarsening **is** the quotient map at its own retained family.

## Main definitions

* `OpenBundle.retFinset` — the retained family `ret(q)` as a `Finset`-valued family, so that
  it can be fed to `OpenBundle.quotient`.

## Main results

* `OpenBundle.retFinset_isForwardStableFam` — `ret(q)` is a forward-stable family.
* `OpenBundle.fibMap_singAt_of_mem` — **the image of a retained singular cell**: a coarsening
  sends the singular cell `i ∈ ret(q_b)` to the singular cell of `A'_b` at the counted
  position `cnt_(ret q_b)(i)`.
* `OpenBundle.sigma_retFinset` — **the Step-2 lemma, the real content**: for a retained cell
  `i ∈ ret(q_b)` the singular function of `A'` sends the singular cell of `A'_b` at position
  `cnt (ret q_b) i` to the singular cell of `A'_c` at position `cnt (ret q_c) (σ_(b,c) i)`.
* `OpenBundle.eq_of_sigma_val_eq` — an extensionality principle for bundles: two
  fibrewise-open 1-truss bundles with the same fibre sizes and the same singular functions are
  **equal**.  This is where skeletality of `OpenTruss` and the reconstruction of a bordism
  from its singular function are used.
* `OpenBundle.quotient_retFinset_eq` — `A^(ret q) = A'`, an honest equality of bundles.
* `OpenBundle.quotientMap_retFinset_eq` — `q_(ret q) ≫ eqToHom … = q`, the bundle analogue of
  `OpenTruss.qU_ret`.
* `OpenBundle.retFinset_quotientMap` — `ret(q_U) = U`, the `Finset` form of the section half.

Together the last three say that `q ↦ ret(q)` and `U ↦ q_U` are mutually inverse on
coarsenings out of `A`, which is `prop:draft-outcoarse-1-bundle-poset-iso` up to the
order-reversal clause (that clause is `OpenBundle.exists_mediator_iff_retFam_le'`).
-/

universe u

namespace Truss.Transfer

open CategoryTheory Geometry Geometry.OneTruss

namespace OpenBundle

variable {B : Type u} [PartialOrder B] [Finite B]

/-! ### An extensionality principle for fibrewise-open 1-truss bundles

`OpenTruss` is skeletal (`OpenTruss.eq_of_numSing_eq`) and a bordism between open 1-trusses is
determined by its singular function (`Geometry.induceOpen_singHom`).  Hence a bundle is
determined by the sizes of its fibres together with its singular functions `σ_(b,c)`. -/

omit [Finite B] in
/-- **Bundles are determined by their fibre sizes and their singular functions.**  Both
clauses are stated in `ℕ`-coordinates, so no transport appears in the hypotheses. -/
theorem eq_of_sigma_val_eq {A₁ A₂ : OpenBundle B}
    (hnum : ∀ b : B, (A₁.fib b).numSing = (A₂.fib b).numSing)
    (hsig : ∀ ⦃b c : B⦄ (h : b ≤ c) (i : Fin (A₁.fib b).numSing)
      (j : Fin (A₂.fib b).numSing), i.val = j.val →
        (A₁.sigma h i).val = (A₂.sigma h j).val) :
    A₁ = A₂ := by
  have hfib : A₁.fib = A₂.fib := funext fun b => OpenTruss.eq_of_numSing_eq (hnum b)
  obtain ⟨f₁, a₁, i₁, c₁⟩ := A₁
  obtain ⟨f₂, a₂, i₂, c₂⟩ := A₂
  have hfib' : f₁ = f₂ := hfib
  subst hfib'
  have harr : @a₁ = @a₂ := by
    funext b c h
    rw [← induceOpen_singHom (a₁ h), ← induceOpen_singHom (a₂ h)]
    congr 1
    refine OrderHom.ext _ _ (funext fun i => Fin.ext ?_)
    exact hsig h i i rfl
  subst harr
  rfl

/-! ### The retained family as a `Finset` -/

variable {A A' : OpenBundle B}

/-- **Source: `def:Singular family` (§5.4).**  The retained singular family of a bundle map,
as a `Finset`-valued family, so that it can be fed to `OpenBundle.quotient`. -/
def retFinset (q : A ⟶ A') (b : B) : Finset (Fin (A.fib b).numSing) :=
  OpenTruss.retOf rfl (fibHom q b)

omit [Finite B] in
/-- Membership in `ret(q)_b`, unfolded. -/
theorem mem_retFinset {q : A ⟶ A'} {b : B} {i : Fin (A.fib b).numSing} :
    i ∈ retFinset q b ↔
      (A'.fib b).toOneTruss.IsSingular (q.fibMap b ((A.fib b).singAt rfl i).el) :=
  OpenTruss.mem_retOf rfl (fibHom q b) i

omit [Finite B] in
/-- `ret(q)` unfolded to §5.3's `retOf`. -/
theorem retFinset_eq (q : A ⟶ A') (b : B) :
    retFinset q b = OpenTruss.retOf (rfl : (A.fib b).numSing = (A.fib b).numSing)
      (fibHom q b) := rfl

omit [Finite B] in
/-- **`retFam_eq_coe_retOf`, in the present notation**: the `Finset` family `ret(q)` coerces
to the `Set` family `retFam q`. -/
theorem coe_retFinset (q : A ⟶ A') (b : B) :
    (↑(retFinset q b) : Set (Fin (A.fib b).numSing)) = retFam q b :=
  (retFam_eq_coe_retOf q b).symm

omit [Finite B] in
/-- **Source: §5.4, "the retained family of any coarsening is forward-stable".**  The
`Finset` form, transported through `isForwardStableFam_iff` from
`OpenBundle.retFam_isForwardStable`.  As there, no coarsening hypothesis is needed. -/
theorem retFinset_isForwardStableFam (q : A ⟶ A') : A.IsForwardStableFam (retFinset q) := by
  have hcoe : (fun b => (↑(retFinset q b) : Set (Fin (A.fib b).numSing))) = retFam q :=
    funext fun b => coe_retFinset q b
  rw [isForwardStableFam_iff, hcoe]
  exact @retFam_isForwardStable B _ A A' q

variable {q : A ⟶ A'}

/-- **`coarsening_idx_eq`, fibrewise.**  On each fibre a bundle coarsening acts on frame
coordinates by the counting formula of its retained set. -/
theorem coarsening_fib_idx (hq : IsCoarsening q) (b : B) (x : (A.fib b).toOneTruss.El) :
    (idx (q.fibMap b x)).val = OpenTruss.qUIdx (retFinset q b) (idx x).val :=
  OpenTruss.coarsening_idx_eq (rfl : (A.fib b).numSing = (A.fib b).numSing)
    (isCoarsening_fibHom hq b) x

/-! ### Step 1: the fibres already agree, on the nose -/

/-- **Step 1.**  The fibre of the target of a bundle coarsening has exactly `|ret(q_b)|`
singular cells: `numSing_eq_card_ret`, fibrewise. -/
theorem numSing_fib_eq (hq : IsCoarsening q) (b : B) :
    (A'.fib b).numSing = (retFinset q b).card :=
  OpenTruss.numSing_eq_card_ret (rfl : (A.fib b).numSing = (A.fib b).numSing)
    (isCoarsening_fibHom hq b)

/-- **Step 1, as an equality of fibres.**  Skeletality of `OpenTruss` plus
`Retained.target_eq`: the fibre `A'_b` *is* the coarse fibre of the quotient at `ret(q)`. -/
theorem fib_eq (hq : IsCoarsening q) :
    A'.fib = (A.quotient (retFinset q) (retFinset_isForwardStableFam q)).fib :=
  funext fun b => OpenTruss.target_eq (rfl : (A.fib b).numSing = (A.fib b).numSing)
    (isCoarsening_fibHom hq b)

/-! ### Step 2: the arrow bordisms agree -/

/-- **The image of a retained singular cell.**  A coarsening `q_b` sends the singular cell `i`
of `A_b` to the singular cell of `A'_b` at the counted position `cnt_(ret q_b)(i)`.  This is
`coarsening_idx_eq` read at an odd frame coordinate. -/
theorem fibMap_singAt_of_mem (hq : IsCoarsening q) {b : B} {i : Fin (A.fib b).numSing}
    (hi : i ∈ retFinset q b) (p : Fin (A'.fib b).numSing)
    (hp : p.val = OpenTruss.cnt (retFinset q b) i.val) :
    q.fibMap b ((A.fib b).singAt rfl i).el = ((A'.fib b).singAt rfl p).el := by
  refine OpenTruss.el_eq_of_idx_eq _ ?_
  rw [coarsening_fib_idx hq b, (A.fib b).idx_singAt, (A'.fib b).idx_singAt,
    OpenTruss.qUIdx_odd, if_pos ((OpenTruss.memAt_val _ i).2 hi), hp]

/-- **Step 2 — the real content.**  For a **retained** cell `i ∈ ret(q_b)`, the singular
function of `A'` sends the singular cell of `A'_b` at position `cnt (ret q_b) i` to the
singular cell of `A'_c` at position `cnt (ret q_c) (σ_(b,c) i)`.

The proof is the chapter's: `σ_(b,c)` relates `sing i` to `sing (σ i)`; `q.face` carries that
relation to `A'`; both images are singular because `i` and `σ i` are retained; and
`sigma_eq_of_rel` (uniqueness of the singular image) identifies the result with `σ'`. -/
theorem sigma_retFinset (hq : IsCoarsening q) {b c : B} (h : b ≤ c)
    {i : Fin (A.fib b).numSing} (hi : i ∈ retFinset q b) (p : Fin (A'.fib b).numSing)
    (hp : p.val = OpenTruss.cnt (retFinset q b) i.val) :
    (A'.sigma h p).val = OpenTruss.cnt (retFinset q c) (A.sigma h i).val := by
  -- `σ i` is retained, by forward stability of `ret(q)`
  have hi' : A.sigma h i ∈ retFinset q c := retFinset_isForwardStableFam q h i hi
  -- the coarse position of `σ i`
  have hlt : OpenTruss.cnt (retFinset q c) (A.sigma h i).val < (A'.fib c).numSing := by
    rw [numSing_fib_eq hq c]
    exact OpenTruss.cnt_lt_card_of_memAt ((OpenTruss.memAt_val _ _).2 hi')
  obtain ⟨p', hp'⟩ : ∃ p' : Fin (A'.fib c).numSing,
      p'.val = OpenTruss.cnt (retFinset q c) (A.sigma h i).val := ⟨⟨_, hlt⟩, rfl⟩
  -- transport the defining relation of `σ` along `q`
  have hrel := q.face h (A.sigma_rel h i)
  rw [fibMap_singAt_of_mem hq hi p hp,
    fibMap_singAt_of_mem hq hi' p' hp'] at hrel
  -- uniqueness of the singular image
  have huniq := A'.sigma_eq_of_rel h p ((A'.fib c).singAt rfl p').isSingular hrel
  have := congrArg (fun s : (A'.fib c).toOneTruss.El => (idx s).val) huniq
  simp only [(A'.fib c).idx_singAt] at this
  omega

/-! ### Step 3: the retraction -/

/-- **Step 3 — `A^(ret q) = A'`.**  The quotient of `A` at the retained family of a bundle
coarsening `q : A ⟶ A'` *is* `A'`, as an honest equality of bundles: Step 1 gives the fibres
and Step 2 the singular functions, and `eq_of_sigma_val_eq` assembles them. -/
theorem quotient_retFinset_eq (hq : IsCoarsening q) :
    A.quotient (retFinset q) (retFinset_isForwardStableFam q) = A' := by
  refine eq_of_sigma_val_eq (fun b => ?_) (fun b c h p p' hpp' => ?_)
  · rw [quotient_fib, OpenTruss.numSing_ofNumSing, numSing_fib_eq hq b]
  · -- the left-hand side is `restrictSigma`, by reconstruction from the singular function
    have hQ : (A.quotient (retFinset q) (retFinset_isForwardStableFam q)).sigma h p
        = quotientHom (retFinset_isForwardStableFam q) h p := by
      change singHom ((A.quotient (retFinset q) (retFinset_isForwardStableFam q)).arr h) p = _
      rw [show (A.quotient (retFinset q) (retFinset_isForwardStableFam q)).arr h
          = induceOpen (quotientHom (retFinset_isForwardStableFam q) h) from rfl,
        singHom_induceOpen]
      rfl
    rw [hQ, quotientHom_val, restrictSigma_val]
    -- the right-hand side is Step 2 at the retained cell enumerated by `p`
    refine (sigma_retFinset hq h (mem_stableIdx (U := retFinset q) b _) p' ?_).symm
    rw [cnt_stableIdx]
    exact hpp'.symm

omit [Finite B] in
/-- Transport along an equality of bundles does not move frame coordinates. -/
theorem idx_eqToHom_fibMap {A₁ A₂ : OpenBundle B} (e : A₁ = A₂) (b : B)
    (x : (A₁.fib b).toOneTruss.El) :
    (idx ((eqToHom e : A₁ ⟶ A₂).fibMap b x)).val = (idx x).val := by
  subst e
  rfl

/-- **Step 3 — `q` IS the quotient map at its retained family.**  The bundle analogue of
`OpenTruss.qU_ret`, in the same `eqToHom`-conjugated form: the quotient map at `ret(q)`,
followed by the canonical identification `A^(ret q) = A'` of `quotient_retFinset_eq`, is `q`
on the nose. -/
theorem quotientMap_retFinset_eq (hq : IsCoarsening q) :
    A.quotientMap (retFinset q) (retFinset_isForwardStableFam q) ≫
        eqToHom (quotient_retFinset_eq hq) = q := by
  refine BundleMap.ext fun b x => OpenTruss.el_eq_of_idx_eq _ ?_
  rw [show ((A.quotientMap (retFinset q) (retFinset_isForwardStableFam q) ≫
        eqToHom (quotient_retFinset_eq hq)) : A ⟶ A').fibMap b x
      = (eqToHom (quotient_retFinset_eq hq)).fibMap b
        ((A.quotientMap (retFinset q) (retFinset_isForwardStableFam q)).fibMap b x) from rfl,
    idx_eqToHom_fibMap]
  exact (coarsening_fib_idx hq b x).symm

/-! ### The section half, in `Finset` form, and the two halves together -/

omit [Finite B] in
/-- **Source: §5.4, `ret(q_U) = U`.**  The `Finset` form of `ret_quotientMap`; fibrewise this
is `OpenTruss.ret_qU`. -/
theorem retFinset_quotientMap (A : OpenBundle B)
    (U : ∀ b : B, Finset (Fin (A.fib b).numSing)) (hU : A.IsForwardStableFam U) :
    retFinset (A.quotientMap U hU) = U :=
  funext fun b => OpenTruss.ret_qU (A.fib b) rfl (U b)

/-- **`prop:draft-outcoarse-1-bundle-poset-iso`, both halves.**  `q ↦ ret(q)` and
`U ↦ q_U` are mutually inverse on coarsenings out of `A`: the second component is the
retraction `quotient_retFinset_eq` / `quotientMap_retFinset_eq`, packaged as an existence
statement so that the `eqToHom` transport is explicit. -/
theorem retFinset_quotientMap_bijective (A : OpenBundle B) :
    (∀ (U : ∀ b : B, Finset (Fin (A.fib b).numSing)) (hU : A.IsForwardStableFam U),
      retFinset (A.quotientMap U hU) = U) ∧
    (∀ {A' : OpenBundle B} (q : A ⟶ A') (_ : IsCoarsening q),
      ∃ e : A.quotient (retFinset q) (retFinset_isForwardStableFam q) = A',
        A.quotientMap (retFinset q) (retFinset_isForwardStableFam q) ≫ eqToHom e = q) :=
  ⟨fun U hU => retFinset_quotientMap A U hU,
    fun _ hq => ⟨quotient_retFinset_eq hq, quotientMap_retFinset_eq hq⟩⟩

end OpenBundle

end Truss.Transfer
