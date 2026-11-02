/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.OneTruss

/-!
# Non-vacuity probe for the open 1-truss coarsening characterisation (rows T01/T02)

Tracked evidence for
[`plan/DraftNormalisationVerification.md`](../../../plan/DraftNormalisationVerification.md)
§9.  A characterisation theorem is worth nothing if one side is empty, so this module
exhibits an inhabitant of each side of `isCoarsening_iff_surjective_regular`:

* the collapse of the three-element open 1-truss `reg < sing > reg` onto the one-element open
  1-truss **is** a coarsening;
* the inclusion of that point as the lower endpoint is a perfectly good truss map that is
  **not** a coarsening.

It also confirms the cardinality convention: the open 1-truss with one singular element has
`2·1 + 1 = 3` elements, alternating regular/singular/regular, checked cell by cell.
-/

namespace Truss.Transfer.Audit

open Geometry Truss.Transfer

/-- The one-element open 1-truss `[1]`: a single regular cell. -/
def pt : OpenTruss := ⟨⟨0, 1⟩, (OneTruss.isOpen_iff _).2 ⟨rfl, rfl⟩⟩

/-- The three-element open 1-truss `[3]`, i.e. `reg < sing > reg`.  It has one singular
element, matching `cons:retained-set-coarsening-1-truss`'s height `2|U| + 1`. -/
def iv : OpenTruss := ⟨⟨2, 1⟩, (OneTruss.isOpen_iff _).2 ⟨rfl, rfl⟩⟩

/-- Cell `0` of `[3]` is regular. -/
theorem iv_zero_isRegular : iv.toOneTruss.IsRegular (OneTruss.ofIdx 0) := rfl

/-- Cell `1` of `[3]` is singular. -/
theorem iv_one_isSingular : iv.toOneTruss.IsSingular (OneTruss.ofIdx 1) := rfl

/-- Cell `2` of `[3]` is regular. -/
theorem iv_two_isRegular : iv.toOneTruss.IsRegular (OneTruss.ofIdx 2) := rfl

/-- The collapse `[3] → [1]`, discarding the single singular element. -/
def collapse : iv ⟶ pt where
  toFun _ := OneTruss.ofIdx 0
  face_monotone _ := le_rfl
  frame_monotone _ := le_rfl

/-- **The positive side of the characterisation is inhabited.**  The collapse really is a
coarsening: it is surjective and preserves regularity. -/
theorem collapse_isCoarsening : IsCoarsening collapse :=
  (isCoarsening_iff_surjective_regular collapse).2
    ⟨fun z => ⟨OneTruss.ofIdx 0, OneTruss.idx_injective (Fin.ext (by
        have h : (OneTruss.idx z).val < 1 := (OneTruss.idx z).isLt
        have h2 : (OneTruss.idx (collapse.toFun (OneTruss.ofIdx 0))).val = 0 := rfl
        omega))⟩, fun _ _ => rfl⟩

/-- The inclusion of the point as the lower endpoint of the interval.  A legitimate truss
map: it is monotone for both orders. -/
def incl : pt ⟶ iv where
  toFun _ := OneTruss.ofIdx 0
  face_monotone _ := le_rfl
  frame_monotone _ := le_rfl

/-- **The negative side is inhabited too.**  The endpoint inclusion is a truss map that is
not a coarsening, because it is not surjective.  So `isCoarsening_iff_surjective_regular` is
not vacuously true on either side. -/
theorem incl_not_isCoarsening : ¬ IsCoarsening incl := by
  intro h
  have hs := ((isCoarsening_iff_surjective_regular incl).1 h).1
  obtain ⟨x, hx⟩ := hs (OneTruss.ofIdx 1)
  have hval : (OneTruss.idx (incl.toFun x)).val = (OneTruss.idx (OneTruss.ofIdx 1)).val :=
    congrArg (fun e => (OneTruss.idx e).val) hx
  simp [incl, OneTruss.idx, OneTruss.ofIdx] at hval
  exact absurd hval (by decide)

end Truss.Transfer.Audit
