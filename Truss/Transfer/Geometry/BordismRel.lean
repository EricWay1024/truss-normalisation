/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Geometry.OpenCoord

/-!
# Totality and frame-convexity of a 1-truss bordism relation

Facts about the relation underlying a 1-truss bordism, each proved **directly from the five
bordism laws**, with no reconstruction theorem:

* `Bord1.exists_rel_right` — every cell of the source is related to something;
* `Bord1.exists_rel_left` — every cell of an **open** target is related to something;
* `Bord1.preimage_frameConvex` — `R⁻¹(y)` is an interval in the frame order;
* `Bord1.image_frameConvex` — `R(x,-)` is an interval in the frame order.

The convexity arguments are the pretty ones: because the frame order of a 1-truss is
**total**, the (bimonotone) law pins an intermediate cell's partner down to a single value.
Preimages and images are also face-downsets and face-upsets by (functorial), recorded as
`preimage_downClosed` and `image_upClosed`.

These are the facts §5.4's fibrewise characterisation reasons with when it speaks of the
"nonempty frame intervals" and of incident source intervals.
-/

namespace Truss.Transfer.Geometry

open OneTruss

namespace OneTruss

variable {T : OneTruss}

/-- A regular cell of a 1-truss with more than one cell lies below an adjacent singular
cell. -/
theorem exists_singular_above {x : T.El} (hx : T.IsRegular x) (hlen : 0 < T.len) :
    ∃ s : T.El, T.IsSingular s ∧ x ≤ s := by
  have hub : (idx x).val ≤ T.len := by simpa using idx_le_upper x
  rcases lt_or_eq_of_le hub with hlt | heq
  · refine ⟨ofIdx ⟨(idx x).val + 1, by omega⟩, ?_, Or.inr ⟨hx, ?_, Or.inr rfl⟩⟩ <;>
      refine T.isSingular_of_parity_ne hx ?_ <;>
      · show ((idx x).val + 1) % 2 ≠ (idx x).val % 2
        omega
  · refine ⟨ofIdx ⟨(idx x).val - 1, by omega⟩, ?_, Or.inr ⟨hx, ?_, Or.inl ?_⟩⟩
    · refine T.isSingular_of_parity_ne hx ?_
      show ((idx x).val - 1) % 2 ≠ (idx x).val % 2
      omega
    · refine T.isSingular_of_parity_ne hx ?_
      show ((idx x).val - 1) % 2 ≠ (idx x).val % 2
      omega
    · show (idx x).val = (idx x).val - 1 + 1
      omega

/-- A singular cell of an **open** 1-truss lies above an adjacent regular cell: it is not the
lower endpoint, because that endpoint is regular. -/
theorem exists_regular_below (hT : T.IsOpen) {y : T.El} (hy : T.IsSingular y) :
    ∃ r : T.El, T.IsRegular r ∧ r ≤ y := by
  have hpos : 0 < (idx y).val := by
    rcases Nat.eq_zero_or_pos (idx y).val with hz | hp
    · exfalso
      have hylow : y = T.lower := idx_injective (Fin.ext (by rw [hz, idx_lower]))
      have h1 : T.dim T.lower = 1 := hT.1
      rw [hylow] at hy
      rw [hy] at h1
      exact absurd h1 (by decide)
    · exact hp
  have hub : (idx y).val ≤ T.len := by simpa using idx_le_upper y
  refine ⟨ofIdx ⟨(idx y).val - 1, by omega⟩, ?_, Or.inr ⟨?_, hy, Or.inr ?_⟩⟩
  · refine T.isRegular_of_parity_ne hy ?_
    show ((idx y).val - 1) % 2 ≠ (idx y).val % 2
    omega
  · refine T.isRegular_of_parity_ne hy ?_
    show ((idx y).val - 1) % 2 ≠ (idx y).val % 2
    omega
  · show (idx y).val = (idx y).val - 1 + 1
    omega

/-- A 1-truss with a single cell: every cell equals every other. -/
theorem eq_of_len_zero (hlen : T.len = 0) (x y : T.El) : x = y := by
  have h1 : (idx x).val ≤ T.len := by simpa using idx_le_upper x
  have h2 : (idx y).val ≤ T.len := by simpa using idx_le_upper y
  exact idx_injective (Fin.ext (by omega))

end OneTruss

namespace Bord1

variable {T S : OneTruss} (R : Bord1 T S)

/-! ### Face closure properties -/

/-- `R⁻¹(y)` is closed downwards in the face order. -/
theorem preimage_downClosed {x x' : T.El} {y : S.El} (h : x' ≤ x) (hr : R.rel x y) :
    R.rel x' y := R.functorial h hr le_rfl

/-- `R(x,-)` is closed upwards in the face order. -/
theorem image_upClosed {x : T.El} {y y' : S.El} (hr : R.rel x y) (h : y ≤ y') :
    R.rel x y' := R.functorial le_rfl hr h

/-! ### Totality -/

/-- **Every cell of the source is related to something.**  A singular cell has its singular
image by (functional); a regular cell inherits one from an adjacent singular cell by
(functorial); and a one-cell 1-truss is handled by (nonempty). -/
theorem exists_rel_right (x : T.El) : ∃ y : S.El, R.rel x y := by
  rcases T.isSingular_or_isRegular x with hx | hx
  · obtain ⟨y, hy, -⟩ := R.functional x hx
    exact ⟨y, hy.2⟩
  · rcases Nat.eq_zero_or_pos T.len with hz | hp
    · obtain ⟨x₀, y₀, hr₀⟩ := R.nonempty
      exact ⟨y₀, by rwa [OneTruss.eq_of_len_zero hz x x₀]⟩
    · obtain ⟨s, hsing, hxs⟩ := OneTruss.exists_singular_above hx hp
      obtain ⟨y, hy, -⟩ := R.functional s hsing
      exact ⟨y, R.preimage_downClosed hxs hy.2⟩

/-- **Every cell of an open target is related to something.**  A regular cell has its regular
partner by (cofunctional); a singular cell of an **open** 1-truss lies above a regular
neighbour, and (functorial) transports that neighbour's partner up. -/
theorem exists_rel_left (hS : S.IsOpen) (y : S.El) : ∃ x : T.El, R.rel x y := by
  rcases S.isSingular_or_isRegular y with hy | hy
  · obtain ⟨r, hr, hry⟩ := OneTruss.exists_regular_below hS hy
    obtain ⟨x, hx, -⟩ := R.cofunctional r hr
    exact ⟨x, R.image_upClosed hx.2 hry⟩
  · obtain ⟨x, hx, -⟩ := R.cofunctional y hy
    exact ⟨x, hx.2⟩

/-! ### Frame convexity -/

/-- **`R⁻¹(y)` is a frame interval.**  If `x` and `x''` are both related to `y` and `x'` lies
between them in the frame order, then any partner `y'` of `x'` satisfies `¬(y' ≺ y)` and
`¬(y ≺ y')` by (bimonotone) on each side; the frame order is total, so `y' = y`. -/
theorem preimage_frameConvex {x x' x'' : T.El} {y : S.El} (h₁ : (idx x).val < (idx x').val)
    (h₂ : (idx x').val < (idx x'').val) (hx : R.rel x y) (hx'' : R.rel x'' y) :
    R.rel x' y := by
  obtain ⟨y', hy'⟩ := R.exists_rel_right x'
  have hb₁ := R.bimonotone hx hy' h₁
  have hb₂ := R.bimonotone hy' hx'' h₂
  have heq : (idx y').val = (idx y).val := by omega
  rwa [idx_injective (Fin.ext heq)] at hy'

/-- **`R(x,-)` is a frame interval**, by the dual argument. -/
theorem image_frameConvex (hS : S.IsOpen) {x : T.El} {y y' y'' : S.El}
    (h₁ : (idx y).val < (idx y').val) (h₂ : (idx y').val < (idx y'').val) (hy : R.rel x y)
    (hy'' : R.rel x y'') : R.rel x y' := by
  obtain ⟨x', hx'⟩ := R.exists_rel_left hS y'
  rcases lt_trichotomy (idx x').val (idx x).val with hlt | heq | hgt
  · have hb := R.bimonotone hx' hy hlt
    omega
  · rwa [idx_injective (Fin.ext heq)] at hx'
  · have hb := R.bimonotone hy'' hx' hgt
    omega

end Bord1

end Truss.Transfer.Geometry
