/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Geometry.Bordism
import Truss.Transfer.Normalisation.OneTruss

/-!
# Coordinates for open 1-trusses

`Truss/Transfer/Geometry/OneTruss.lean` proves that an open 1-truss has `ε = 1` and an even
`len`, i.e. an odd carrier `[2k+1]` with `k` singular elements at the odd frame indices and
`k+1` regular elements at the even ones.  This module turns that into a usable coordinate
system, which every later section of the draft chapter is phrased in:

* `OpenTruss.numSing` — the number `k` of singular elements;
* `OpenTruss.singEquiv : Fin k ≃o Sing T` and `OpenTruss.regEquiv : Fin (k+1) ≃o Reg T`,
  the frame-order enumerations;
* `OpenTruss.skeletal` — an open 1-truss is *determined* by `k`, so the category of open
  1-trusses is skeletal in the coordinate model.

The index arithmetic is kept at the level of `ℕ` throughout: `Fin k` never appears in a type
that depends on `T.toOneTruss.len`, so no type-level rewriting is ever needed.
-/

namespace Truss.Transfer

open Geometry Geometry.OneTruss

namespace OpenTruss

variable (T : OpenTruss)

/-- **The number of singular elements of an open 1-truss.**  Its carrier is `[2·numSing+1]`. -/
def numSing : ℕ := T.toOneTruss.len / 2

theorem eps_eq : T.toOneTruss.eps = 1 := ((OneTruss.isOpen_iff _).1 T.isOpen).1

theorem len_even : T.toOneTruss.len % 2 = 0 := ((OneTruss.isOpen_iff _).1 T.isOpen).2

theorem len_eq : T.toOneTruss.len = 2 * T.numSing := by
  have h := T.len_even
  unfold numSing
  omega

/-- **The open 1-truss with `k` singular elements**, i.e. the carrier `[2k+1]`. -/
def ofNumSing (k : ℕ) : OpenTruss :=
  ⟨⟨2 * k, 1⟩, (OneTruss.isOpen_iff _).2 ⟨rfl, Nat.mul_mod_right 2 k⟩⟩

@[simp] theorem numSing_ofNumSing (k : ℕ) : (ofNumSing k).numSing = k :=
  Nat.mul_div_cancel_left k (by norm_num)

/-- An open 1-truss is determined by its underlying 1-truss; the openness field is a `Prop`. -/
theorem ext' {T S : OpenTruss} (h : T.toOneTruss = S.toOneTruss) : T = S := by
  obtain ⟨t, ht⟩ := T
  obtain ⟨s, hs⟩ := S
  cases h
  rfl

/-- **The category of open 1-trusses is skeletal in the coordinate model**: an open 1-truss
is determined by its number of singular elements. -/
theorem skeletal : T = ofNumSing T.numSing := by
  refine ext' ?_
  show T.toOneTruss = ⟨2 * T.numSing, 1⟩
  rw [← T.len_eq, ← T.eps_eq]

theorem eq_of_numSing_eq {T S : OpenTruss} (h : T.numSing = S.numSing) : T = S := by
  rw [T.skeletal, S.skeletal, h]

/-! ### The dimension of a cell, by index parity -/

theorem isSingular_iff_odd {x : T.toOneTruss.El} :
    T.toOneTruss.IsSingular x ↔ (idx x).val % 2 = 1 := by
  unfold OneTruss.IsSingular OneTruss.dim
  rw [eps_eq]
  by_cases h : (idx x).val % 2 = 0
  · rw [if_pos h]
    constructor
    · intro hc; exact absurd hc (by decide)
    · intro hc; omega
  · rw [if_neg h]
    exact ⟨fun _ => by omega, fun _ => rfl⟩

theorem isRegular_iff_even {x : T.toOneTruss.El} :
    T.toOneTruss.IsRegular x ↔ (idx x).val % 2 = 0 := by
  rw [← OneTruss.not_isSingular_iff, isSingular_iff_odd]
  constructor
  · intro h; omega
  · intro h hc; omega

/-! ### Frame-order enumerations of the singular and regular cells -/

/-- The `i`-th singular cell, at frame index `2i+1`. -/
def singAt {k : ℕ} (hk : T.numSing = k) (i : Fin k) : Sing T.toOneTruss :=
  ⟨ofIdx ⟨2 * i.val + 1, by have := T.len_eq; have := i.isLt; omega⟩, by
    rw [isSingular_iff_odd]
    show (2 * i.val + 1) % 2 = 1
    omega⟩

/-- The `j`-th regular cell, at frame index `2j`. -/
def regAt {k : ℕ} (hk : T.numSing = k) (j : Fin (k + 1)) : Reg T.toOneTruss :=
  ⟨ofIdx ⟨2 * j.val, by have := T.len_eq; have := j.isLt; omega⟩, by
    rw [isRegular_iff_even]
    show (2 * j.val) % 2 = 0
    omega⟩

@[simp] theorem idx_singAt {k : ℕ} (hk : T.numSing = k) (i : Fin k) :
    (idx (T.singAt hk i).el).val = 2 * i.val + 1 := rfl

@[simp] theorem idx_regAt {k : ℕ} (hk : T.numSing = k) (j : Fin (k + 1)) :
    (idx (T.regAt hk j).el).val = 2 * j.val := rfl

theorem singAt_injective {k : ℕ} (hk : T.numSing = k) : Function.Injective (T.singAt hk) := by
  intro i j h
  have hv := congrArg (fun s => (idx s.el).val) h
  simp only [idx_singAt] at hv
  exact Fin.ext (by omega)

theorem regAt_injective {k : ℕ} (hk : T.numSing = k) : Function.Injective (T.regAt hk) := by
  intro i j h
  have hv := congrArg (fun s => (idx s.el).val) h
  simp only [idx_regAt] at hv
  exact Fin.ext (by omega)

/-- The frame position of a singular cell among the singular cells. -/
def singIdx {k : ℕ} (hk : T.numSing = k) (s : Sing T.toOneTruss) : Fin k :=
  ⟨(idx s.el).val / 2, by
    have hodd := (isSingular_iff_odd T).1 s.isSingular
    have hle : (idx s.el).val ≤ T.toOneTruss.len := by simpa using idx_le_upper s.el
    have hlen := T.len_eq
    omega⟩

/-- The frame position of a regular cell among the regular cells. -/
def regIdx {k : ℕ} (hk : T.numSing = k) (r : Reg T.toOneTruss) : Fin (k + 1) :=
  ⟨(idx r.el).val / 2, by
    have heven := (isRegular_iff_even T).1 r.isRegular
    have hle : (idx r.el).val ≤ T.toOneTruss.len := by simpa using idx_le_upper r.el
    have hlen := T.len_eq
    omega⟩

@[simp] theorem singIdx_singAt {k : ℕ} (hk : T.numSing = k) (i : Fin k) :
    T.singIdx hk (T.singAt hk i) = i := by
  refine Fin.ext ?_
  show (2 * i.val + 1) / 2 = i.val
  omega

@[simp] theorem singAt_singIdx {k : ℕ} (hk : T.numSing = k) (s : Sing T.toOneTruss) :
    T.singAt hk (T.singIdx hk s) = s := by
  have hodd := (isSingular_iff_odd T).1 s.isSingular
  refine Sing.ext (idx_injective (Fin.ext ?_))
  show 2 * ((idx s.el).val / 2) + 1 = (idx s.el).val
  omega

@[simp] theorem regIdx_regAt {k : ℕ} (hk : T.numSing = k) (j : Fin (k + 1)) :
    T.regIdx hk (T.regAt hk j) = j := by
  refine Fin.ext ?_
  show (2 * j.val) / 2 = j.val
  omega

@[simp] theorem regAt_regIdx {k : ℕ} (hk : T.numSing = k) (r : Reg T.toOneTruss) :
    T.regAt hk (T.regIdx hk r) = r := by
  have heven := (isRegular_iff_even T).1 r.isRegular
  refine Reg.ext (idx_injective (Fin.ext ?_))
  show 2 * ((idx r.el).val / 2) = (idx r.el).val
  omega

/-- **The frame-order enumeration of the singular cells.** -/
def singEquiv {k : ℕ} (hk : T.numSing = k) : Fin k ≃o Sing T.toOneTruss where
  toFun := T.singAt hk
  invFun := T.singIdx hk
  left_inv := T.singIdx_singAt hk
  right_inv := T.singAt_singIdx hk
  map_rel_iff' := by
    intro i j
    rw [Sing.le_iff]
    simp only [Equiv.coe_fn_mk, idx_singAt]
    exact ⟨fun h => by omega, fun h => by omega⟩

/-- **The frame-order enumeration of the regular cells.** -/
def regEquiv {k : ℕ} (hk : T.numSing = k) : Fin (k + 1) ≃o Reg T.toOneTruss where
  toFun := T.regAt hk
  invFun := T.regIdx hk
  left_inv := T.regIdx_regAt hk
  right_inv := T.regAt_regIdx hk
  map_rel_iff' := by
    intro i j
    rw [Reg.le_iff]
    simp only [Equiv.coe_fn_mk, idx_regAt]
    exact ⟨fun h => by omega, fun h => by omega⟩

/-! ### Endpoints in coordinates -/

theorem lower_eq_regAt {k : ℕ} (hk : T.numSing = k) :
    T.toOneTruss.lower = (T.regAt hk ⟨0, Nat.succ_pos k⟩).el :=
  idx_injective (Fin.ext (by simp))

theorem upper_eq_regAt {k : ℕ} (hk : T.numSing = k) :
    T.toOneTruss.upper = (T.regAt hk ⟨k, Nat.lt_succ_self k⟩).el := by
  refine idx_injective (Fin.ext ?_)
  have := T.len_eq
  show T.toOneTruss.len = 2 * k
  omega

end OpenTruss

end Truss.Transfer
