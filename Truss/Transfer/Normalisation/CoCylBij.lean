/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.CoCyl

/-!
# Surjectivity of the mapping-cocylinder correspondence (§5.3, row T04)

Source: `dphil-notes-typst/transfer/ch03-normalisation-draft.typ`, §"Open $1$-trusses",
`prop:Coarsenings and injective 1-truss bordisms`:

> Fix open 1-trusses `T` and `S`.  There is a bijection between coarsenings `T → S` and
> 1-truss bordisms `S → T` with an injective singular function, given by the mapping
> cocylinder.

`Truss/Transfer/Normalisation/CoCyl.lean` supplies the forward map `coCylMap` and its
injectivity (`coCylMap_injective`).  This module supplies the missing **converse**: every
`R : S ⇸ T` with injective singular function is a mapping cocylinder.

## The route taken

The chapter's proof runs through the regular cofunction (send a regular element `r` to
`g_R(r)`, a singular element to the common image of its regular neighbours, …).  Here we use
instead the two classifications that are already available, which is shorter and avoids any
case analysis on neighbours:

* by `openBordEquiv`, `R` is exactly its singular function in coordinates,
  `f := singHom R : Fin S.numSing →o Fin T.numSing`, and `R.singFun` is injective exactly
  when `f` is (`injective_singHom_iff`);
* an injective monotone `f` is strictly monotone, so it *is* the increasing enumeration of
  its image `U := Finset.image f Finset.univ`, a statement recorded here in `cnt`
  coordinates as `OpenTruss.cnt_image_val`;
* by `Retained.lean`, `q_U : T ⟶ S_(|U|)` is a coarsening, and `S ≅ S_(|U|)` canonically
  since `S.numSing = |U|` (`OpenTruss.eq_of_numSing_eq`).

The coarsening witnessing surjectivity is therefore `q := q_U ≫ eqToHom (S_(|U|) = S)`, and
the two bordisms `coCyl q` and `R` are compared through their singular functions.

## Main results

* `OpenTruss.cnt_image_val` — the counting lemma: for a strictly monotone `f`, the number of
  elements of `image f univ` strictly below `f i` is `i`.  This says `f` is the increasing
  enumeration of its image.
* `singFun_coCyl_eq` — the singular function of `coCyl q` sends `s` to the unique singular
  cell over it: if `q(t) = s` with both singular then `(coCyl q).singFun s = t`.
* `singFun_coCyl_qU` — **the singular function of a retained-set cocylinder is the increasing
  enumeration of `U`**: the `i`-th singular cell of `S_U` goes to the singular cell of `T`
  indexed by the unique `j ∈ U` with `cnt U j = i`.
* `coCylMap_surjective` — the missing clause of row `T04`.
* `coCylEquiv` — `prop:Coarsenings and injective 1-truss bordisms` in full.
-/

universe u

namespace Truss.Transfer

open CategoryTheory Geometry Geometry.OneTruss OpenTruss

namespace OpenTruss

/-! ### A strictly monotone map is the increasing enumeration of its image -/

/-- **The counting lemma.**  If `f : Fin l →o Fin k` is injective — equivalently strictly
monotone — then exactly `i` elements of its image lie strictly below `f i`.  Equivalently:
`f` *is* the increasing enumeration of `Finset.image f Finset.univ`. -/
theorem cnt_image_val {k l : ℕ} (f : Fin l →o Fin k) (hf : Function.Injective f) (i : Fin l) :
    cnt (Finset.image f Finset.univ) (f i).val = i.val := by
  have hsm : StrictMono f := f.monotone.strictMono_of_injective hf
  have himg : (Finset.image f Finset.univ).filter (fun c : Fin k => c.val < (f i).val)
      = Finset.image f (Finset.univ.filter fun j : Fin l => j.val < i.val) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨j, rfl⟩, hlt⟩
      exact ⟨j, Fin.lt_def.1 (hsm.lt_iff_lt.1 (Fin.lt_def.2 hlt)), rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, rfl⟩, Fin.lt_def.1 (hsm (Fin.lt_def.2 hj))⟩
  have hfin : cnt (Finset.univ : Finset (Fin l)) i.val = i.val := cnt_univ i.isLt.le
  rw [cnt, himg, Finset.card_image_of_injective _ hf]
  exact hfin

end OpenTruss

/-! ### The singular function of a mapping cocylinder -/

variable {T S : OpenTruss}

/-- **The singular function of `coCyl q`, characterised.**  A singular cell `t` of `T` lying
over a singular cell `s` of `S` *is* the value of the singular function of `coCyl q` at `s`;
`coCyl`'s functionality makes such a `t` unique. -/
theorem singFun_coCyl_eq (q : T ⟶ S) (hq : IsCoarsening q) (s : Sing S.toOneTruss)
    (t : Sing T.toOneTruss) (h : q.toFun t.el = s.el) : (coCyl q hq).singFun s = t :=
  (Sing.ext ((coCyl q hq).singFun_unique s t.isSingular (h ▸ le_rfl))).symm

/-- **The singular function of a retained-set cocylinder is the increasing enumeration of
`U`.**  The `i`-th singular cell of `S_U` is sent to the singular cell of `T` indexed by the
unique `j ∈ U` with `cnt U j = i` — that is, to the `i`-th element of `U`. -/
theorem singFun_coCyl_qU (T : OpenTruss) {k : ℕ} (hk : T.numSing = k) (U : Finset (Fin k))
    {i : Fin U.card} {j : Fin k} (hjU : j ∈ U) (hj : cnt U j.val = i.val) :
    (coCyl (qU T U) (qU_isCoarsening T hk U)).singFun
        ((ofNumSing U.card).singAt (numSing_ofNumSing U.card) i) = T.singAt hk j := by
  refine singFun_coCyl_eq _ _ _ _ ((ofNumSing U.card).el_eq_of_idx_eq ?_)
  rw [idx_qU, idx_singAt, qUIdx_odd, if_pos ((memAt_val U j).2 hjU), hj,
    (ofNumSing U.card).idx_singAt (numSing_ofNumSing U.card) i]

/-! ### Surjectivity of the cocylinder correspondence -/

/-- **Source: `prop:Coarsenings and injective 1-truss bordisms` (§5.3), surjectivity.**
Every 1-truss bordism `S ⇸ T` with injective singular function is the mapping cocylinder of a
coarsening `T ⟶ S`.  The coarsening is the retained-set coarsening of the image of the
singular function, followed by the canonical identification of its target with `S`. -/
theorem coCylMap_surjective (T S : OpenTruss) : Function.Surjective (coCylMap T S) := by
  rintro ⟨R, hR⟩
  have hf : Function.Injective (singHom R) := (injective_singHom_iff R).2 hR
  set f : Fin S.numSing →o Fin T.numSing := singHom R with hfdef
  set U : Finset (Fin T.numSing) := Finset.image f Finset.univ with hUdef
  have hmem : ∀ i : Fin S.numSing, f i ∈ U := fun i =>
    Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
  have hcard : U.card = S.numSing := by
    rw [hUdef, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  have hSeq : ofNumSing U.card = S :=
    eq_of_numSing_eq (by rw [numSing_ofNumSing, hcard])
  set q : T ⟶ S := qU T U ≫ eqToHom hSeq with hqdef
  have hq : IsCoarsening q :=
    IsCoarsening.comp (qU_isCoarsening T rfl U) (isCoarsening_eqToHom hSeq)
  -- the frame-coordinate formula for `q`
  have hidx : ∀ x : T.toOneTruss.El, (idx (q.toFun x)).val = qUIdx U (idx x).val := by
    intro x
    rw [hqdef, show ((qU T U ≫ eqToHom hSeq) : T ⟶ S).toFun x
        = (eqToHom hSeq : ofNumSing U.card ⟶ S).toFun ((qU T U).toFun x) from rfl,
      idx_eqToHom, idx_qU]
  refine ⟨⟨q, hq⟩, Subtype.ext ?_⟩
  change coCyl q hq = R
  have key : singHom (coCyl q hq) = f := by
    refine OrderHom.ext _ _ (funext fun i => ?_)
    change T.singIdx rfl ((coCyl q hq).singFun (S.singAt rfl i)) = f i
    have hval : q.toFun (T.singAt rfl (f i)).el = (S.singAt rfl i).el := by
      refine S.el_eq_of_idx_eq ?_
      rw [hidx, idx_singAt, qUIdx_odd, if_pos ((memAt_val U (f i)).2 (hmem i)),
        cnt_image_val f hf i, S.idx_singAt rfl i]
    rw [singFun_coCyl_eq q hq (S.singAt rfl i) (T.singAt rfl (f i)) hval, T.singIdx_singAt]
  calc coCyl q hq = induceOpen (singHom (coCyl q hq)) := (induceOpen_singHom _).symm
    _ = induceOpen (singHom R) := by rw [key, hfdef]
    _ = R := induceOpen_singHom R

/-- **Source: `prop:Coarsenings and injective 1-truss bordisms` (§5.3), in full.**  The
mapping cocylinder is a bijection between the coarsenings `T ⟶ S` and the 1-truss bordisms
`S ⇸ T` with injective singular function.  Its incidence formula is `coCyl_rel`:
`coCyl q (s, t) ↔ s ≤ q(t)`. -/
noncomputable def coCylEquiv (T S : OpenTruss) :
    {q : T ⟶ S // IsCoarsening q} ≃
      {R : Bord1 S.toOneTruss T.toOneTruss // Function.Injective R.singFun} :=
  Equiv.ofBijective (coCylMap T S) ⟨coCylMap_injective T S, coCylMap_surjective T S⟩

/-- The bijection of `coCylEquiv` is the mapping cocylinder. -/
@[simp] theorem coCylEquiv_apply (T S : OpenTruss) (q : {q : T ⟶ S // IsCoarsening q}) :
    (coCylEquiv T S q).1 = coCyl q.1 q.2 := rfl

end Truss.Transfer
