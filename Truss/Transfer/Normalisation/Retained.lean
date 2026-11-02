/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Geometry.OpenCoord

/-!
# Retained singulars and the retained-set coarsening (§5.3)

This module formalises rows `T05` and `T06` of the draft normalisation chapter's §5.3
(`transfer/ch03-normalisation-draft.typ`, `cons:retained-set-coarsening-1-truss` and
`prop:draft-outcoarse-poset-iso`), in the **unlabelled** case.

The chapter builds `q_U` through the induced 1-truss bordism of the strictly increasing
function `ι_U : sing(S_U) → sing(T)`.  Here `q_U` is built **directly in frame coordinates**,
as the counting map

> `2j ↦ 2·cnt_U(j)`,  `2i+1 ↦ 2·cnt_U(i) + 1` if `i ∈ U`,  `2i+1 ↦ 2·cnt_U(i)` if `i ∉ U`,

where `cnt_U(j)` is the number of retained singulars strictly below the regular cell `j`, and
it is shown to be a coarsening through row `T02`
(`isCoarsening_iff_surjective_regular`).  Nothing in this file uses 1-truss bordisms.

## Main definitions

* `OpenTruss.cnt` — the counting function `cnt_U`.
* `OpenTruss.qUIdx`, `OpenTruss.qU` — the frame-index formula of `q_U`, and `q_U` itself.
* `OpenTruss.retOf`, `OpenTruss.ret` — `ret(q) = {s ∈ sing(T) | q(s) ∈ sing(S)}`.
* `OpenTruss.push` — the push-forward of `W ⊆ V` along `q_V`, used to build mediators.
* `OpenTruss.OutCoarsePoset` — `OutCoarse(T)` with its factorisation order.

## Main results

* `OpenTruss.qU_isCoarsening` and `OpenTruss.ret_qU` —
  `cons:retained-set-coarsening-1-truss`: `q_U` is a coarsening and `ret(q_U) = U`.
* `OpenTruss.coarsening_idx_eq`, `OpenTruss.numSing_eq_card_ret`, `OpenTruss.qU_ret` —
  `q_(ret q) = q`.  The first is the frame-coordinate statement (an equality of natural
  numbers, so no transport is involved); the third is its packaged form
  `q ≫ eqToHom (target_eq …) = q_(ret q)`, using skeletality of `OpenTruss`.
* `OpenTruss.exists_mediator_iff_ret_subset`, `OpenTruss.mediator_unique`,
  `OpenTruss.isIso_iff_ret_eq_univ` — the order-reversal and invertibility clauses of
  `prop:draft-outcoarse-poset-iso`.
* `OpenTruss.retOrderIso` — the poset isomorphism `OutCoarse(T) ≅ R(T)^op` itself.

## Not proved here

The agreement of this direct `q_U` with the chapter's bordism construction (the mapping
cocylinder route through `coinduce`) is a **separate** obligation and is **OPEN**; nothing
in this file asserts it.
-/
namespace Truss.Transfer

open CategoryTheory Geometry Geometry.OneTruss

namespace OpenTruss

/-! ### Counting a subset of singular indices below a frame position -/

variable {k : ℕ}

/-- Membership of a natural number in a `Finset (Fin k)`, as a decidable predicate on `ℕ`. -/
def MemAt (U : Finset (Fin k)) (n : ℕ) : Prop := ∃ i ∈ U, i.val = n

/-- Membership of a natural number in a `Finset (Fin k)` is decidable. -/
instance (U : Finset (Fin k)) (n : ℕ) : Decidable (MemAt U n) :=
  inferInstanceAs (Decidable (∃ i ∈ U, i.val = n))

/-- `MemAt` at the value of an index is ordinary membership. -/
@[simp] theorem memAt_val (U : Finset (Fin k)) (i : Fin k) : MemAt U i.val ↔ i ∈ U :=
  ⟨fun ⟨j, hj, hv⟩ => (Fin.val_injective hv : j = i) ▸ hj, fun h => ⟨i, h, rfl⟩⟩

/-- Only indices below `k` can be members. -/
theorem lt_of_memAt {U : Finset (Fin k)} {n : ℕ} (h : MemAt U n) : n < k := by
  obtain ⟨i, -, rfl⟩ := h; exact i.isLt

/-- **The counting function.** `cnt U j` is the number of elements of `U` strictly below the
frame position `j`. -/
def cnt (U : Finset (Fin k)) (j : ℕ) : ℕ := (U.filter fun i : Fin k => i.val < j).card

/-- Nothing lies below the first frame position. -/
@[simp] theorem cnt_zero (U : Finset (Fin k)) : cnt U 0 = 0 := by simp [cnt]

/-- Past the last singular index the counting function is constant at `|U|`. -/
theorem cnt_of_card_le (U : Finset (Fin k)) {j : ℕ} (hj : k ≤ j) : cnt U j = U.card := by
  unfold cnt
  exact congrArg Finset.card (Finset.filter_true_of_mem fun i _ => lt_of_lt_of_le i.isLt hj)

/-- At the last frame position the counting function is `|U|`. -/
@[simp] theorem cnt_top (U : Finset (Fin k)) : cnt U k = U.card := cnt_of_card_le U le_rfl

/-- The defining recursion of the counting function. -/
theorem cnt_succ (U : Finset (Fin k)) (j : ℕ) :
    cnt U (j + 1) = cnt U j + if MemAt U j then 1 else 0 := by
  have hsplit : (U.filter fun i : Fin k => i.val < j + 1)
      = (U.filter fun i : Fin k => i.val < j) ∪ (U.filter fun i : Fin k => i.val = j) := by
    rw [← Finset.filter_or]
    exact Finset.filter_congr fun i _ => by omega
  have hdisj : Disjoint (U.filter fun i : Fin k => i.val < j)
      (U.filter fun i : Fin k => i.val = j) := by
    refine Finset.disjoint_left.2 fun i hi hi' => ?_
    have h1 := (Finset.mem_filter.1 hi).2
    have h2 := (Finset.mem_filter.1 hi').2
    omega
  have hcard : (U.filter fun i : Fin k => i.val = j).card = if MemAt U j then 1 else 0 := by
    by_cases hm : MemAt U j
    · obtain ⟨i, hiU, rfl⟩ := hm
      rw [if_pos ⟨i, hiU, rfl⟩]
      refine Finset.card_eq_one.2 ⟨i, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩⟩
      · exact Finset.mem_filter.2 ⟨hiU, rfl⟩
      · exact fun x hx => Fin.val_injective (Finset.mem_filter.1 hx).2
    · rw [if_neg hm, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun {i} hi hv => hm ⟨i, hi, hv⟩
  rw [cnt, hsplit, Finset.card_union_of_disjoint hdisj, hcard]
  rfl

/-- The counting function is monotone. -/
theorem cnt_mono (U : Finset (Fin k)) : Monotone (cnt U) := by
  intro a b h
  refine Finset.card_le_card fun i hi => ?_
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, lt_of_lt_of_le hi.2 h⟩

/-- The counting function is bounded by `|U|`. -/
theorem cnt_le_card (U : Finset (Fin k)) (j : ℕ) : cnt U j ≤ U.card :=
  Finset.card_le_card (Finset.filter_subset _ U)

/-- At a member of `U` the counting function is strictly below `|U|`. -/
theorem cnt_lt_card_of_memAt {U : Finset (Fin k)} {j : ℕ} (h : MemAt U j) :
    cnt U j < U.card := by
  have h1 : cnt U (j + 1) ≤ U.card := cnt_le_card U (j + 1)
  rw [cnt_succ, if_pos h] at h1
  omega

/-- The counting function strictly increases across an element of `U`. -/
theorem cnt_lt_cnt_of_memAt {U : Finset (Fin k)} {i j : ℕ} (hi : MemAt U i) (hij : i < j) :
    cnt U i < cnt U j := by
  have h1 : cnt U (i + 1) ≤ cnt U j := cnt_mono U hij
  rw [cnt_succ, if_pos hi] at h1
  omega

/-! ### The frame-index formula of the retained-set coarsening -/

/-- **The frame-index formula of `q_U`.**  A regular element at frame index `2j` is sent to
the regular element at frame index `2·cnt U j`; a singular element at frame index `2i+1` is
sent to the singular element at `2·cnt U i + 1` if `i ∈ U`, and collapsed onto the regular
element at `2·cnt U i` otherwise. -/
def qUIdx (U : Finset (Fin k)) (n : ℕ) : ℕ :=
  2 * cnt U (n / 2) + if n % 2 = 1 ∧ MemAt U (n / 2) then 1 else 0

/-- The value of `q_U` at the regular element of frame index `2j`. -/
@[simp] theorem qUIdx_even (U : Finset (Fin k)) (j : ℕ) : qUIdx U (2 * j) = 2 * cnt U j := by
  have h1 : 2 * j / 2 = j := by omega
  have h2 : ¬ ((2 * j) % 2 = 1 ∧ MemAt U (2 * j / 2)) := by rintro ⟨h, -⟩; omega
  unfold qUIdx
  rw [if_neg h2, h1, Nat.add_zero]

/-- The value of `q_U` at the singular element of frame index `2m+1`. -/
@[simp] theorem qUIdx_odd (U : Finset (Fin k)) (m : ℕ) :
    qUIdx U (2 * m + 1) = 2 * cnt U m + if MemAt U m then 1 else 0 := by
  have h1 : (2 * m + 1) / 2 = m := by omega
  unfold qUIdx
  rw [h1]
  by_cases hm : MemAt U m
  · rw [if_pos ⟨by omega, hm⟩, if_pos hm]
  · rw [if_neg (fun h => hm h.2), if_neg hm]

/-- `q_U` preserves the lower endpoint. -/
@[simp] theorem qUIdx_zero (U : Finset (Fin k)) : qUIdx U 0 = 0 := by
  simpa using qUIdx_even U 0

/-- `q_U` preserves the upper endpoint. -/
theorem qUIdx_top (U : Finset (Fin k)) : qUIdx U (2 * k) = 2 * U.card := by
  rw [qUIdx_even, cnt_top]

/-- The index formula lands in the carrier of `S_U`. -/
theorem qUIdx_le (U : Finset (Fin k)) (n : ℕ) : qUIdx U n ≤ 2 * U.card := by
  unfold qUIdx
  by_cases h : n % 2 = 1 ∧ MemAt U (n / 2)
  · rw [if_pos h]
    have := cnt_lt_card_of_memAt h.2
    omega
  · rw [if_neg h]
    have := cnt_le_card U (n / 2)
    omega

/-- The index formula does not decrease across one frame step. -/
theorem qUIdx_succ_le (U : Finset (Fin k)) (n : ℕ) : qUIdx U n ≤ qUIdx U (n + 1) := by
  rcases Nat.even_or_odd n with he | ho
  · have hn : n % 2 = 0 := Nat.even_iff.1 he
    obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j := ⟨n / 2, by omega⟩
    rw [qUIdx_even, qUIdx_odd]
    exact Nat.le_add_right _ _
  · have hn : n % 2 = 1 := Nat.odd_iff.1 ho
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    have h : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
    rw [qUIdx_odd, h, qUIdx_even, cnt_succ]
    by_cases hm : MemAt U m
    · rw [if_pos hm]; omega
    · rw [if_neg hm]; omega

/-- The index formula is frame monotone. -/
theorem qUIdx_mono (U : Finset (Fin k)) : Monotone (qUIdx U) :=
  monotone_nat_of_le_succ (qUIdx_succ_le U)

/-- The image of an odd frame index is odd exactly when the corresponding singular index is
retained; the image of an even frame index is always even. -/
theorem qUIdx_mod_two (U : Finset (Fin k)) (n : ℕ) :
    qUIdx U n % 2 = if n % 2 = 1 ∧ MemAt U (n / 2) then 1 else 0 := by
  unfold qUIdx
  by_cases h : n % 2 = 1 ∧ MemAt U (n / 2) <;> simp [h]

/-! ### The retained-set coarsening as a truss map -/

/-- **Source: `cons:retained-set-coarsening-1-truss` (§5.3).**  The retained-set coarsening
`q_U : T → S_U`, built directly in frame coordinates. -/
def qU (T : OpenTruss) (U : Finset (Fin k)) : T ⟶ ofNumSing U.card where
  toFun x := ofIdx ⟨qUIdx U (idx x).val, Nat.lt_succ_of_le (qUIdx_le U _)⟩
  face_monotone := by
    intro i j hij
    rcases OneTruss.le_iff_faceLE.1 hij with rfl | ⟨hi, hj, hadj⟩
    · exact le_rfl
    have hie : (idx i).val % 2 = 0 := (isRegular_iff_even T).1 hi
    have hjo : (idx j).val % 2 = 1 := (isSingular_iff_odd T).1 hj
    obtain ⟨m, hm⟩ : ∃ m, (idx j).val = 2 * m + 1 := ⟨(idx j).val / 2, by omega⟩
    have hdiv : (idx j).val / 2 = m := by omega
    by_cases hmU : MemAt U m
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · refine (isRegular_iff_even (ofNumSing U.card)).2 ?_
        change qUIdx U (idx i).val % 2 = 0
        rw [qUIdx_mod_two, if_neg (fun h => absurd h.1 (by omega))]
      · refine (isSingular_iff_odd (ofNumSing U.card)).2 ?_
        change qUIdx U (idx j).val % 2 = 1
        rw [qUIdx_mod_two, if_pos ⟨hjo, by rw [hdiv]; exact hmU⟩]
      · change qUIdx U (idx i).val = qUIdx U (idx j).val + 1 ∨
          qUIdx U (idx j).val = qUIdx U (idx i).val + 1
        rcases hadj with h | h
        · left
          rw [show (idx i).val = 2 * (m + 1) by omega, hm, qUIdx_even, qUIdx_odd,
            if_pos hmU, cnt_succ, if_pos hmU]
          omega
        · right
          rw [show (idx i).val = 2 * m by omega, hm, qUIdx_even, qUIdx_odd, if_pos hmU]
    · have heq : qUIdx U (idx i).val = qUIdx U (idx j).val := by
        rcases hadj with h | h
        · rw [show (idx i).val = 2 * (m + 1) by omega, hm, qUIdx_even, qUIdx_odd,
            if_neg hmU, cnt_succ, if_neg hmU]
          omega
        · rw [show (idx i).val = 2 * m by omega, hm, qUIdx_even, qUIdx_odd, if_neg hmU]
          omega
      exact le_of_eq (congrArg OneTruss.ofIdx (Fin.ext heq))
  frame_monotone := by
    intro i j hij
    change qUIdx U (idx i).val ≤ qUIdx U (idx j).val
    exact qUIdx_mono U hij

/-- `q_U` acts on frame indices by the index formula. -/
@[simp] theorem idx_qU (T : OpenTruss) (U : Finset (Fin k)) (x : T.toOneTruss.El) :
    (idx ((qU T U).toFun x)).val = qUIdx U (idx x).val := rfl

/-! ### Retained singulars -/

/-- Singularity is decidable: it unfolds to an equation in `[2]`. -/
instance decidableIsSingular (T : OneTruss) (x : T.El) : Decidable (T.IsSingular x) :=
  decidable_of_iff (T.dim x = 0) Iff.rfl

/-- **Source: §5.3, `ret(q) = {s ∈ sing(T) | q(s) ∈ sing(S)}`.**  The retained singulars of a
truss map, read off in the frame-order enumeration of the singular cells. -/
def retOf {T S : OpenTruss} {k : ℕ} (hk : T.numSing = k) (q : T ⟶ S) : Finset (Fin k) :=
  Finset.univ.filter fun i => S.toOneTruss.IsSingular (q.toFun (T.singAt hk i).el)

/-- Membership in the retained set, unfolded. -/
@[simp] theorem mem_retOf {T S : OpenTruss} {k : ℕ} (hk : T.numSing = k) (q : T ⟶ S)
    (i : Fin k) :
    i ∈ retOf hk q ↔ S.toOneTruss.IsSingular (q.toFun (T.singAt hk i).el) := by
  simp [retOf]

/-- **Source: §5.3, `ret(q)`.**  The retained singulars, in the canonical enumeration. -/
abbrev ret {T S : OpenTruss} (q : T ⟶ S) : Finset (Fin T.numSing) := retOf rfl q

/-! ### The retained-set coarsening is a coarsening, and retains exactly `U` -/

/-- **Source: `cons:retained-set-coarsening-1-truss` (§5.3).**  `q_U` is a coarsening. -/
theorem qU_isCoarsening (T : OpenTruss) {k : ℕ} (hk : T.numSing = k) (U : Finset (Fin k)) :
    IsCoarsening (qU T U) := by
  have hlen : T.toOneTruss.len = 2 * k := by rw [T.len_eq, hk]
  rw [isCoarsening_iff_surjective_regular]
  refine ⟨?_, ?_⟩
  · rw [TrussMap.surjective_iff_endpoints]
    constructor
    · refine OneTruss.idx_injective (Fin.ext ?_)
      change qUIdx U (idx T.toOneTruss.lower).val = (idx (ofNumSing U.card).toOneTruss.lower).val
      simp
    · refine OneTruss.idx_injective (Fin.ext ?_)
      change qUIdx U (idx T.toOneTruss.upper).val = (idx (ofNumSing U.card).toOneTruss.upper).val
      rw [OneTruss.idx_upper, OneTruss.idx_upper, hlen, qUIdx_top]
      rfl
  · intro i hi
    refine (isRegular_iff_even (ofNumSing U.card)).2 ?_
    change qUIdx U (idx i).val % 2 = 0
    have hie : (idx i).val % 2 = 0 := (isRegular_iff_even T).1 hi
    rw [qUIdx_mod_two, if_neg (fun h => absurd h.1 (by omega))]

/-- **Source: `cons:retained-set-coarsening-1-truss` (§5.3), `ret(q_U) = U`.** -/
theorem ret_qU (T : OpenTruss) {k : ℕ} (hk : T.numSing = k) (U : Finset (Fin k)) :
    retOf hk (qU T U) = U := by
  ext i
  rw [mem_retOf, isSingular_iff_odd]
  change qUIdx U (idx (T.singAt hk i).el).val % 2 = 1 ↔ i ∈ U
  rw [idx_singAt, qUIdx_mod_two]
  have hdiv : (2 * i.val + 1) / 2 = i.val := by omega
  rw [hdiv]
  by_cases hm : i ∈ U
  · rw [if_pos ⟨by omega, (memAt_val U i).2 hm⟩]
    simp [hm]
  · rw [if_neg (fun h => hm ((memAt_val U i).1 h.2))]
    simp [hm]

/-! ### Every coarsening out of `T` is the retained-set coarsening of its retained set -/

/-- **Source: `prop:draft-outcoarse-poset-iso`, `q_(ret q) = q`.**  In frame coordinates,
every coarsening out of an open 1-truss is given by the counting formula of its retained
set.  This is the content of `q_(ret q) = q`; the identification of the targets is
`numSing_eq_card_ret` below. -/
theorem coarsening_idx_eq {T S : OpenTruss} {k : ℕ} (hk : T.numSing = k) {q : T ⟶ S}
    (hq : IsCoarsening q) (x : T.toOneTruss.El) :
    (idx (q.toFun x)).val = qUIdx (retOf hk q) (idx x).val := by
  obtain ⟨hsurj, hreg⟩ := (isCoarsening_iff_surjective_regular q).1 hq
  obtain ⟨hlow, -⟩ := (TrussMap.surjective_iff_endpoints q).1 hsurj
  have hlen : T.toOneTruss.len = 2 * k := by rw [T.len_eq, hk]
  set W := retOf hk q with hWdef
  suffices H : ∀ n : ℕ, ∀ y : T.toOneTruss.El, (idx y).val = n →
      (idx (q.toFun y)).val = qUIdx W n from H _ x rfl
  intro n
  induction n with
  | zero =>
      intro y hy
      have hyl : y = T.toOneTruss.lower := OneTruss.idx_injective (Fin.ext (by simp [hy]))
      rw [hyl, hlow, qUIdx_zero]
      simp
  | succ n ih =>
      intro y hy
      have hyle : (idx y).val ≤ T.toOneTruss.len := by simpa using OneTruss.idx_le_upper y
      have hpos : 0 < (idx y).val := by omega
      have hzidx : (idx (framePred y hpos)).val = n := by rw [idx_framePred]; omega
      have hihz := ih (framePred y hpos) hzidx
      have hstep : (idx (q.toFun y)).val ≤ (idx (q.toFun (framePred y hpos))).val + 1 :=
        q.idx_step (by omega)
      have hmono : (idx (q.toFun (framePred y hpos))).val ≤ (idx (q.toFun y)).val :=
        q.idx_mono (by omega)
      rw [hihz] at hstep hmono
      rcases Nat.even_or_odd n with he | ho
      · -- `n = 2m`: `y` is the `m`-th singular element
        have hn : n % 2 = 0 := Nat.even_iff.1 he
        obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
        have hmk : m < k := by omega
        have hysing : y = (T.singAt hk ⟨m, hmk⟩).el :=
          OneTruss.idx_injective (Fin.ext (by rw [hy]; simp))
        have hmem : MemAt W m ↔ S.toOneTruss.IsSingular (q.toFun y) := by
          rw [hysing, hWdef]
          exact ⟨fun h => (mem_retOf hk q ⟨m, hmk⟩).1 ((memAt_val _ ⟨m, hmk⟩).1 h),
            fun h => (memAt_val _ ⟨m, hmk⟩).2 ((mem_retOf hk q ⟨m, hmk⟩).2 h)⟩
        rw [qUIdx_even] at hstep hmono
        rw [qUIdx_odd]
        by_cases hmm : MemAt W m
        · have hodd : (idx (q.toFun y)).val % 2 = 1 := (isSingular_iff_odd S).1 (hmem.1 hmm)
          rw [if_pos hmm]
          omega
        · have hev : (idx (q.toFun y)).val % 2 = 0 :=
            (isRegular_iff_even S).1 ((OneTruss.not_isSingular_iff _ _).1 fun hc =>
              hmm (hmem.2 hc))
          rw [if_neg hmm]
          omega
      · -- `n = 2m+1`: `y` is the `(m+1)`-st regular element
        have hn : n % 2 = 1 := Nat.odd_iff.1 ho
        obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
        have hyreg : T.toOneTruss.IsRegular y := (isRegular_iff_even T).2 (by omega)
        have hev : (idx (q.toFun y)).val % 2 = 0 := (isRegular_iff_even S).1 (hreg y hyreg)
        rw [qUIdx_odd] at hstep hmono
        rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, qUIdx_even, cnt_succ]
        by_cases hmm : MemAt W m
        · rw [if_pos hmm] at hstep hmono ⊢
          omega
        · rw [if_neg hmm] at hstep hmono ⊢
          omega

/-- **Source: `prop:draft-outcoarse-poset-iso`.**  The target of a coarsening out of `T` has
exactly `|ret q|` singular elements. -/
theorem numSing_eq_card_ret {T S : OpenTruss} {k : ℕ} (hk : T.numSing = k) {q : T ⟶ S}
    (hq : IsCoarsening q) : S.numSing = (retOf hk q).card := by
  obtain ⟨hsurj, -⟩ := (isCoarsening_iff_surjective_regular q).1 hq
  obtain ⟨-, hupp⟩ := (TrussMap.surjective_iff_endpoints q).1 hsurj
  have hlen : T.toOneTruss.len = 2 * k := by rw [T.len_eq, hk]
  have h := coarsening_idx_eq hk hq T.toOneTruss.upper
  rw [hupp, OneTruss.idx_upper, OneTruss.idx_upper, hlen, qUIdx_top] at h
  have hS := S.len_eq
  omega

/-! ### Transport along an equality of open 1-trusses -/

/-- Transport along an equality of open 1-trusses does not move frame indices. -/
theorem idx_eqToHom {S S' : OpenTruss} (h : S = S') (x : S.toOneTruss.El) :
    (idx ((eqToHom h : S ⟶ S').toFun x)).val = (idx x).val := by
  subst h
  rw [eqToHom_refl]
  rfl

/-- Transport along an equality of open 1-trusses is a coarsening. -/
theorem isCoarsening_eqToHom {S S' : OpenTruss} (h : S = S') :
    IsCoarsening (eqToHom h : S ⟶ S') := by
  subst h
  rw [eqToHom_refl]
  exact IsCoarsening.id _

/-- **Source: `prop:draft-outcoarse-poset-iso`.**  The target of a coarsening out of `T` is
the canonical open 1-truss on its retained set. -/
theorem target_eq {T S : OpenTruss} {k : ℕ} (hk : T.numSing = k) {q : T ⟶ S}
    (hq : IsCoarsening q) : S = ofNumSing (retOf hk q).card :=
  eq_of_numSing_eq (by rw [numSing_eq_card_ret hk hq, numSing_ofNumSing])

/-- **Source: `prop:draft-outcoarse-poset-iso`, `q_(ret q) = q`.**  Every coarsening out of
`T` *is* the retained-set coarsening of its retained set, after the canonical identification
of its target with `S_(ret q)`. -/
theorem qU_ret {T S : OpenTruss} {k : ℕ} (hk : T.numSing = k) {q : T ⟶ S}
    (hq : IsCoarsening q) : q ≫ eqToHom (target_eq hk hq) = qU T (retOf hk q) := by
  refine TrussMap.ext fun x => OneTruss.idx_injective (Fin.ext ?_)
  rw [show ((q ≫ eqToHom (target_eq hk hq)) : T ⟶ _).toFun x
      = (eqToHom (target_eq hk hq) : S ⟶ _).toFun (q.toFun x) from rfl,
    idx_eqToHom, idx_qU]
  exact coarsening_idx_eq hk hq x

/-! ### The push-forward of a subset along a retained-set coarsening -/

/-- The counting function is injective on `V`. -/
theorem cnt_val_inj {V : Finset (Fin k)} {i j : Fin k} (hi : i ∈ V) (hj : j ∈ V)
    (h : cnt V i.val = cnt V j.val) : i = j := by
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (cnt_lt_cnt_of_memAt ((memAt_val V i).2 hi) hlt))
  · exact Fin.val_injective heq
  · exact absurd h.symm (Nat.ne_of_lt (cnt_lt_cnt_of_memAt ((memAt_val V j).2 hj) hgt))

/-- **The push-forward of `W ⊆ V` along `q_V`.**  The singular elements of `S_V` are indexed
by `Fin |V|` through the counting function; `push V W` is the image of `W` under that
indexing. -/
def push (V W : Finset (Fin k)) : Finset (Fin V.card) :=
  Finset.univ.filter fun c => ∃ i ∈ W, cnt V i.val = c.val

/-- The push-forward of `W` contains the `V`-index of `i` exactly when `i ∈ W`. -/
theorem memAt_push {V W : Finset (Fin k)} (hWV : W ⊆ V) {i : Fin k} (hiV : i ∈ V) :
    MemAt (push V W) (cnt V i.val) ↔ i ∈ W := by
  constructor
  · rintro ⟨c, hc, hcv⟩
    obtain ⟨j, hjW, hj⟩ := (Finset.mem_filter.1 hc).2
    exact cnt_val_inj (hWV hjW) hiV (hj.trans hcv) ▸ hjW
  · intro hiW
    refine ⟨⟨cnt V i.val, cnt_lt_card_of_memAt ((memAt_val V i).2 hiV)⟩, ?_, rfl⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨i, hiW, rfl⟩⟩

/-- Counting `push V W` below the `V`-index of `j` counts `W` below `j`. -/
theorem cnt_push {V W : Finset (Fin k)} (hWV : W ⊆ V) (j : ℕ) :
    cnt (push V W) (cnt V j) = cnt W j := by
  induction j with
  | zero => simp
  | succ j ih =>
      by_cases hjV : MemAt V j
      · obtain ⟨i, hiV, rfl⟩ := hjV
        have hmV : MemAt V i.val := ⟨i, hiV, rfl⟩
        rw [cnt_succ V, if_pos hmV, cnt_succ (push V W), cnt_succ W, ih]
        by_cases hiW : i ∈ W
        · rw [if_pos ((memAt_push hWV hiV).2 hiW), if_pos ((memAt_val W i).2 hiW)]
        · rw [if_neg (fun h => hiW ((memAt_push hWV hiV).1 h)),
            if_neg (fun h => hiW ((memAt_val W i).1 h))]
      · have hjW : ¬ MemAt W j := fun ⟨i, hiW, hiv⟩ => hjV ⟨i, hWV hiW, hiv⟩
        rw [cnt_succ V, if_neg hjV, Nat.add_zero, ih, cnt_succ W, if_neg hjW, Nat.add_zero]

/-- The push-forward of `W ⊆ V` has the same cardinality as `W`. -/
theorem card_push {V W : Finset (Fin k)} (hWV : W ⊆ V) : (push V W).card = W.card := by
  have h := cnt_push hWV k
  rw [cnt_top V, cnt_top (push V W), cnt_top W] at h
  exact h

/-- **The composition law for retained-set coarsenings.**  Coarsening `T` onto `V` and then
onto the push-forward of `W` is coarsening `T` onto `W`. -/
theorem qUIdx_push {V W : Finset (Fin k)} (hWV : W ⊆ V) (n : ℕ) :
    qUIdx (push V W) (qUIdx V n) = qUIdx W n := by
  rcases Nat.even_or_odd n with he | ho
  · have hn : n % 2 = 0 := Nat.even_iff.1 he
    obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j := ⟨n / 2, by omega⟩
    rw [qUIdx_even, qUIdx_even, qUIdx_even, cnt_push hWV]
  · have hn : n % 2 = 1 := Nat.odd_iff.1 ho
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    rw [qUIdx_odd, qUIdx_odd]
    by_cases hmV : MemAt V m
    · obtain ⟨i, hiV, rfl⟩ := hmV
      rw [if_pos ⟨i, hiV, rfl⟩, qUIdx_odd, cnt_push hWV]
      by_cases hiW : i ∈ W
      · rw [if_pos ((memAt_push hWV hiV).2 hiW), if_pos ((memAt_val W i).2 hiW)]
      · rw [if_neg (fun h => hiW ((memAt_push hWV hiV).1 h)),
          if_neg (fun h => hiW ((memAt_val W i).1 h))]
    · have hmW : ¬ MemAt W m := fun ⟨i, hiW, hiv⟩ => hmV ⟨i, hWV hiW, hiv⟩
      rw [if_neg hmV, if_neg hmW, Nat.add_zero, qUIdx_even, cnt_push hWV, Nat.add_zero]

/-! ### Order reversal: mediators are inclusions of retained sets -/

/-- **Source: `prop:draft-outcoarse-poset-iso`, order reversal.**  A mediating coarsening
`h : Y → Z` with `q = h ∘ r` exists exactly when `ret q ⊆ ret r`. -/
theorem exists_mediator_iff_ret_subset {T Y Z : OpenTruss} {k : ℕ} (hk : T.numSing = k)
    {r : T ⟶ Y} {q : T ⟶ Z} (hr : IsCoarsening r) (hq : IsCoarsening q) :
    (∃ h : Y ⟶ Z, IsCoarsening h ∧ q = r ≫ h) ↔ retOf hk q ⊆ retOf hk r := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    intro i hi
    rw [mem_retOf] at hi ⊢
    by_contra hc
    have hregY : Y.toOneTruss.IsRegular (r.toFun (T.singAt hk i).el) :=
      (OneTruss.not_isSingular_iff _ _).1 hc
    obtain ⟨-, hhreg⟩ := (isCoarsening_iff_surjective_regular h).1 hh
    have hreg := hhreg _ hregY
    have hsing : Z.toOneTruss.IsSingular (h.toFun (r.toFun (T.singAt hk i).el)) := hi
    exact absurd (hsing.symm.trans hreg) (by decide)
  · intro hsub
    refine ⟨eqToHom (target_eq hk hr) ≫ qU (ofNumSing (retOf hk r).card)
        (push (retOf hk r) (retOf hk q)) ≫ eqToHom (congrArg ofNumSing (card_push hsub)) ≫
        eqToHom (target_eq hk hq).symm, ?_, ?_⟩
    · exact (isCoarsening_eqToHom _).comp
        ((qU_isCoarsening _ (numSing_ofNumSing _) _).comp
          ((isCoarsening_eqToHom _).comp (isCoarsening_eqToHom _)))
    · refine TrussMap.ext fun x => OneTruss.idx_injective (Fin.ext ?_)
      simp only [comp_toFun, Function.comp_apply]
      rw [idx_eqToHom, idx_eqToHom, idx_qU, idx_eqToHom, coarsening_idx_eq hk hr x,
        qUIdx_push hsub]
      exact coarsening_idx_eq hk hq x

/-- Mediators in `OutCoarse(T)` are unique: a coarsening is an epimorphism. -/
theorem mediator_unique {T Y Z : OpenTruss} {r : T ⟶ Y} (hr : IsCoarsening r)
    {h h' : Y ⟶ Z} (hh : r ≫ h = r ≫ h') : h = h' := hr.cancel_right hh

/-! ### The invertibility criterion -/

/-- Counting the full set below `j ≤ k` gives `j`. -/
theorem cnt_univ {j : ℕ} (hj : j ≤ k) : cnt (Finset.univ : Finset (Fin k)) j = j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hjk : j < k := by omega
      rw [cnt_succ, if_pos ⟨⟨j, hjk⟩, Finset.mem_univ _, rfl⟩, ih (by omega)]

/-- Retaining every singular element leaves every frame index fixed. -/
theorem qUIdx_univ {n : ℕ} (hn : n ≤ 2 * k) :
    qUIdx (Finset.univ : Finset (Fin k)) n = n := by
  rcases Nat.even_or_odd n with he | ho
  · have hnm : n % 2 = 0 := Nat.even_iff.1 he
    obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j := ⟨n / 2, by omega⟩
    rw [qUIdx_even, cnt_univ (by omega)]
  · have hnm : n % 2 = 1 := Nat.odd_iff.1 ho
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    have hmk : m < k := by omega
    rw [qUIdx_odd, cnt_univ (by omega), if_pos ⟨⟨m, hmk⟩, Finset.mem_univ _, rfl⟩]

/-- **Source: `prop:draft-outcoarse-poset-iso`, invertibility criterion.**  A coarsening out
of an open 1-truss is invertible exactly when it retains every singular element. -/
theorem isIso_iff_ret_eq_univ {T S : OpenTruss} {k : ℕ} (hk : T.numSing = k) {q : T ⟶ S}
    (hq : IsCoarsening q) : IsIso q ↔ retOf hk q = Finset.univ := by
  have hlen : T.toOneTruss.len = 2 * k := by rw [T.len_eq, hk]
  constructor
  · intro hiso
    have hinj : Function.Injective q.toFun := by
      intro a b hab
      have hstep : (inv q).toFun (q.toFun a) = (inv q).toFun (q.toFun b) := by rw [hab]
      have hid : ((q ≫ inv q).toFun) a = ((q ≫ inv q).toFun) b := hstep
      rw [IsIso.hom_inv_id] at hid
      simpa using hid
    refine Finset.eq_univ_of_forall fun i => ?_
    by_contra hiW
    have hmem : ¬ MemAt (retOf hk q) i.val := fun h => hiW ((memAt_val _ i).1 h)
    have hb1 : 2 * i.val < T.toOneTruss.len + 1 := by have := i.isLt; omega
    have hb2 : 2 * i.val + 2 < T.toOneTruss.len + 1 := by have := i.isLt; omega
    have hne : (OneTruss.ofIdx ⟨2 * i.val, hb1⟩ : T.toOneTruss.El)
        ≠ OneTruss.ofIdx ⟨2 * i.val + 2, hb2⟩ := by
      intro hc
      have h2 : (2 * i.val : ℕ) = 2 * i.val + 2 :=
        congrArg (fun z => (OneTruss.idx z).val) hc
      omega
    refine hne (hinj (OneTruss.idx_injective (Fin.ext ?_)))
    rw [coarsening_idx_eq hk hq, coarsening_idx_eq hk hq]
    change qUIdx (retOf hk q) (2 * i.val) = qUIdx (retOf hk q) (2 * i.val + 2)
    rw [qUIdx_even, show 2 * i.val + 2 = 2 * (i.val + 1) by omega, qUIdx_even, cnt_succ,
      if_neg hmem, Nat.add_zero]
  · intro hW
    have hcard : (retOf hk q).card = k := by rw [hW]; simp
    have hTS : T = S := eq_of_numSing_eq (by rw [numSing_eq_card_ret hk hq, hcard, hk])
    have hqe : q = eqToHom hTS := by
      refine TrussMap.ext fun x => OneTruss.idx_injective (Fin.ext ?_)
      rw [coarsening_idx_eq hk hq, idx_eqToHom, hW]
      exact qUIdx_univ (by have := Nat.lt_succ_iff.1 (idx x).isLt; omega)
    rw [hqe]
    infer_instance

/-! ### The poset isomorphism `OutCoarse(T) ≅ R(T)ᵒᵖ` -/

/-- Outgoing coarsenings with the same retained set are equal: the target is pinned by
skeletality and the map is pinned by the counting formula. -/
theorem outCoarse_ext {T : OpenTruss} {r s : OutCoarse T}
    (h : retOf rfl r.map = retOf rfl s.map) : r = s := by
  obtain ⟨Y, rm, hrm⟩ := r
  obtain ⟨Z, sm, hsm⟩ := s
  have hYZ : Y = Z :=
    eq_of_numSing_eq (by rw [numSing_eq_card_ret rfl hrm, numSing_eq_card_ret rfl hsm, h])
  subst hYZ
  congr 1
  refine TrussMap.ext fun x => OneTruss.idx_injective (Fin.ext ?_)
  rw [coarsening_idx_eq rfl hrm, coarsening_idx_eq rfl hsm, h]

/-- **Source: `prop:draft-outcoarse-poset-iso`.**  `OutCoarse(T)` as a poset: it is thin, so
`r ≤ q` means that a (necessarily unique) mediating coarsening `r → q` exists, and it is
skeletal by `outCoarse_ext`, so this relation is antisymmetric. -/
def OutCoarsePoset (T : OpenTruss) : Type := OutCoarse T

namespace OutCoarsePoset

/-- The underlying outgoing coarsening. -/
def out {T : OpenTruss} (r : OutCoarsePoset T) : OutCoarse T := r

/-- An outgoing coarsening, viewed as an element of the poset. -/
def of {T : OpenTruss} (r : OutCoarse T) : OutCoarsePoset T := r

/-- `out` inverts `of`. -/
@[simp] theorem out_of {T : OpenTruss} (r : OutCoarse T) : (of r).out = r := rfl

/-- `of` inverts `out`. -/
@[simp] theorem of_out {T : OpenTruss} (r : OutCoarsePoset T) : of r.out = r := rfl

/-- The factorisation order on outgoing coarsenings: `r ≤ q` exactly when `OutCoarse(T)`
has a morphism `r ⟶ q`. -/
instance instPartialOrder (T : OpenTruss) : PartialOrder (OutCoarsePoset T) where
  le r q := ∃ h : r.out.tgt ⟶ q.out.tgt, IsCoarsening h ∧ q.out.map = r.out.map ≫ h
  le_refl _ := ⟨𝟙 _, IsCoarsening.id _, by simp⟩
  le_trans _ _ _ := by
    rintro ⟨h, hh, hcomp⟩ ⟨h', hh', hcomp'⟩
    exact ⟨h ≫ h', hh.comp hh', by rw [hcomp', hcomp, Category.assoc]⟩
  le_antisymm r q hrq hqr := by
    have h1 : retOf rfl q.out.map ⊆ retOf rfl r.out.map :=
      (exists_mediator_iff_ret_subset rfl r.out.isCoarsening q.out.isCoarsening).1 hrq
    have h2 : retOf rfl r.out.map ⊆ retOf rfl q.out.map :=
      (exists_mediator_iff_ret_subset rfl q.out.isCoarsening r.out.isCoarsening).1 hqr
    exact outCoarse_ext (Finset.Subset.antisymm h2 h1)

/-- The order relation, unfolded: it is exactly the hom-set of `OutCoarse(T)`. -/
theorem le_iff {T : OpenTruss} (r q : OutCoarsePoset T) :
    r ≤ q ↔ ∃ h : r.out.tgt ⟶ q.out.tgt, IsCoarsening h ∧ q.out.map = r.out.map ≫ h :=
  Iff.rfl

end OutCoarsePoset

/-- **Source: `prop:draft-outcoarse-poset-iso`.**  The poset isomorphism
`OutCoarse(T) ≅ R(T)^op`, given by `q ↦ ret(q)` and `U ↦ q_U`. -/
def retOrderIso (T : OpenTruss) :
    OutCoarsePoset T ≃o (Finset (Fin T.numSing))ᵒᵈ where
  toFun r := OrderDual.toDual (retOf rfl r.out.map)
  invFun U := OutCoarsePoset.of
    ⟨ofNumSing (OrderDual.ofDual U).card, qU T (OrderDual.ofDual U),
      qU_isCoarsening T rfl (OrderDual.ofDual U)⟩
  left_inv r := outCoarse_ext (by simpa using ret_qU T rfl (retOf rfl r.out.map))
  right_inv U := by
    change OrderDual.toDual (retOf rfl (qU T (OrderDual.ofDual U))) = U
    rw [ret_qU]
    rfl
  map_rel_iff' := by
    intro r q
    change (retOf rfl q.out.map ⊆ retOf rfl r.out.map) ↔ r ≤ q
    rw [OutCoarsePoset.le_iff,
      ← exists_mediator_iff_ret_subset rfl r.out.isCoarsening q.out.isCoarsening]

end OpenTruss

end Truss.Transfer
