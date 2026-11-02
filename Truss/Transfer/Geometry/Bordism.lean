/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Geometry.OneTruss

/-!
# Chapter 2's 1-truss bordisms (G05)

This module formalises the primitive bordism interface of
`dphil-notes-typst/transfer/ch02-trusses.typ`, §"Bordisms of 1-trusses": row `G05` of
[`plan/DraftNormalisationVerification.md`](../../../plan/DraftNormalisationVerification.md).

## Main definitions

* `Sing`, `Reg` — the singular and regular subsets, **with the frame order inherited from the
  1-truss** (`def:sing-reg`).
* `AdmSing` — `def:admissible-singular-function`: a frame-nondecreasing
  `sing T → sing S` preserving whichever endpoints are singular.
* `AdmReg` — `def:admissible-regular-cofunction`: a frame-nondecreasing
  `reg S → reg T` preserving whichever endpoints are regular.  Note the **direction
  reversal**: a regular cofunction runs from `S` to `T`.
* `Bord1` — `def:truss-bordism`: a relation on `T × S` satisfying the five displayed laws
  (nonempty, functorial, functional, cofunctional, bimonotone).
* `Bord1.singFun`, `Bord1.regCofun` — the derived singular function `f_R` and regular
  cofunction `g_R`.  The chapter records these as `derived`, not as fields: they are
  determined by the two bifunctionality laws and are **not** additional choices.  That is
  what `singFun_spec` / `singFun_unique` and `regCofun_spec` / `regCofun_unique` record.

## Main results

* `Bord1.singFun_mono`, `Bord1.regCofun_mono` — the derived functions are frame-nondecreasing.
* `Bord1.lower_isSingular`, `upper_isSingular`, `lower_isRegular`, `upper_isRegular` — the
  endpoint *type* clauses: a singular endpoint of `T` forces a singular endpoint of `S`, and a
  regular endpoint of `S` forces a regular endpoint of `T`.
* `Bord1.singFun_lower`, `singFun_upper`, `regCofun_lower`, `regCofun_upper` — the endpoint
  *value* equations.
* `Bord1.toAdmSing`, `Bord1.toAdmReg` — consequently `R ↦ f_R` and `R ↦ g_R` are well-typed
  maps `Bord1 T S → AdmSing T S` and `Bord1 T S → AdmReg T S`.  This is one half of
  `prop:Reconstruction from the singular function` and of `prop:regular-reconstruction`.

All of these are proved from the five bordism laws alone; no endpoint hypothesis is added to
`Bord1`, and no openness is assumed.

## What is deliberately absent, and is therefore OPEN

Rows `G06` (`proc:induced-truss-bordism` and its reconstruction) and `G07`
(`proc:coinduced-truss-bordism`, `prop:regular-reconstruction`).  The **other** half of each
reconstruction proposition — the interval-case constructions `induce` and `coinduce`, and
both inverse equations — is not formalised here.  In particular there is **no** statement of
the form `Bord1 T S ≅ AdmSing T S`, only the two forward maps, and nothing downstream may
assume the inverse exists.  This module contains no partial or `sorry`-scaffolded version of
them.
-/

namespace Truss.Transfer.Geometry

open OneTruss

/-! ### The singular and regular subsets, with the inherited frame order -/

/-- **Source: `def:sing-reg`.**  The singular elements of `T`, carrying the frame order
inherited from `T`. -/
def Sing (T : OneTruss) : Type := {i : T.El // T.IsSingular i}

/-- **Source: `def:sing-reg`.**  The regular elements of `T`, carrying the frame order
inherited from `T`. -/
def Reg (T : OneTruss) : Type := {i : T.El // T.IsRegular i}

/-- The converse of `OneTruss.not_isSingular_iff`.  (Belongs upstream in
`Truss/Transfer/Geometry/OneTruss.lean`; kept here so that file is not edited while it is in
use by concurrent work.) -/
theorem OneTruss.not_isRegular_iff (T : OneTruss) (i : T.El) :
    ¬ T.IsRegular i ↔ T.IsSingular i := by
  rw [← not_isSingular_iff]
  exact not_not

/-! ### Parity helpers

These belong upstream in `Truss/Transfer/Geometry/OneTruss.lean`; they are kept here so that
file is not edited while it is in use by concurrent work. -/

/-- Two elements have the same dimension exactly when their frame indices have the same
parity: the dimension alternates along the frame order. -/
theorem OneTruss.dim_eq_iff_parity (T : OneTruss) (i j : T.El) :
    T.dim i = T.dim j ↔ (idx i).val % 2 = (idx j).val % 2 := by
  unfold OneTruss.dim
  by_cases hi : (idx i).val % 2 = 0 <;> by_cases hj : (idx j).val % 2 = 0
  · simp [hi, hj]
  · rw [if_pos hi, if_neg hj]
    exact ⟨fun hc => absurd hc.symm (flip_ne T.eps), fun hc => absurd hc (by omega)⟩
  · rw [if_neg hi, if_pos hj]
    exact ⟨fun hc => absurd hc (flip_ne T.eps), fun hc => absurd hc (by omega)⟩
  · rw [if_neg hi, if_neg hj]
    exact ⟨fun _ => by omega, fun _ => rfl⟩

theorem OneTruss.parity_eq_of_isSingular (T : OneTruss) {i j : T.El} (hi : T.IsSingular i)
    (hj : T.IsSingular j) : (idx i).val % 2 = (idx j).val % 2 :=
  (T.dim_eq_iff_parity i j).1 (by rw [hi, hj])

theorem OneTruss.parity_eq_of_isRegular (T : OneTruss) {i j : T.El} (hi : T.IsRegular i)
    (hj : T.IsRegular j) : (idx i).val % 2 = (idx j).val % 2 :=
  (T.dim_eq_iff_parity i j).1 (by rw [hi, hj])

/-- An element whose index has the opposite parity to a singular element is regular. -/
theorem OneTruss.isRegular_of_parity_ne (T : OneTruss) {i j : T.El} (hj : T.IsSingular j)
    (h : (idx i).val % 2 ≠ (idx j).val % 2) : T.IsRegular i := by
  have hne : T.dim i ≠ T.dim j := fun hc => h ((T.dim_eq_iff_parity i j).1 hc)
  rw [hj] at hne
  rcases eq_zero_or_one (T.dim i) with h0 | h1
  · exact absurd h0 hne
  · exact h1

/-- An element whose index has the opposite parity to a regular element is singular. -/
theorem OneTruss.isSingular_of_parity_ne (T : OneTruss) {i j : T.El} (hj : T.IsRegular j)
    (h : (idx i).val % 2 ≠ (idx j).val % 2) : T.IsSingular i := by
  have hne : T.dim i ≠ T.dim j := fun hc => h ((T.dim_eq_iff_parity i j).1 hc)
  rw [hj] at hne
  rcases eq_zero_or_one (T.dim i) with h0 | h1
  · exact h0
  · exact absurd h1 hne

namespace Sing

variable {T : OneTruss}

/-- The underlying carrier element of a singular element. -/
def el (x : Sing T) : T.El := x.1

theorem isSingular (x : Sing T) : T.IsSingular x.el := x.2

@[ext] theorem ext {x y : Sing T} (h : x.el = y.el) : x = y := Subtype.ext h

@[simp] theorem el_mk (i : T.El) (h : T.IsSingular i) : Sing.el ⟨i, h⟩ = i := rfl

instance : DecidableEq (Sing T) := fun x y =>
  decidable_of_iff (x.el = y.el) ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩

/-- The inherited **frame** order on singular elements. -/
instance : LinearOrder (Sing T) :=
  LinearOrder.lift' (fun x => idx x.el) (fun _ _ h => Subtype.ext (idx_injective h))

theorem le_iff {x y : Sing T} : x ≤ y ↔ (idx x.el).val ≤ (idx y.el).val := Iff.rfl

theorem lt_iff {x y : Sing T} : x < y ↔ (idx x.el).val < (idx y.el).val := Iff.rfl

end Sing

namespace Reg

variable {T : OneTruss}

/-- The underlying carrier element of a regular element. -/
def el (x : Reg T) : T.El := x.1

theorem isRegular (x : Reg T) : T.IsRegular x.el := x.2

@[ext] theorem ext {x y : Reg T} (h : x.el = y.el) : x = y := Subtype.ext h

@[simp] theorem el_mk (i : T.El) (h : T.IsRegular i) : Reg.el ⟨i, h⟩ = i := rfl

instance : DecidableEq (Reg T) := fun x y =>
  decidable_of_iff (x.el = y.el) ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩

/-- The inherited **frame** order on regular elements. -/
instance : LinearOrder (Reg T) :=
  LinearOrder.lift' (fun x => idx x.el) (fun _ _ h => Subtype.ext (idx_injective h))

theorem le_iff {x y : Reg T} : x ≤ y ↔ (idx x.el).val ≤ (idx y.el).val := Iff.rfl

theorem lt_iff {x y : Reg T} : x < y ↔ (idx x.el).val < (idx y.el).val := Iff.rfl

end Reg

/-! ### G05: admissible singular functions and regular cofunctions -/

/-- **Source: `def:admissible-singular-function`.**  A frame-nondecreasing map on singular
elements that preserves whichever endpoints happen to be singular. -/
structure AdmSing (T S : OneTruss) where
  /-- The underlying function on singular elements. -/
  toFun : Sing T → Sing S
  /-- Frame-nondecreasing. -/
  mono : ∀ {x x' : Sing T}, x ≤ x' → toFun x ≤ toFun x'
  /-- If the lower endpoint of `T` is singular, so is that of `S`, and it is its image. -/
  lower_preserving : ∀ h : T.IsSingular T.lower,
    ∃ h' : S.IsSingular S.lower, toFun ⟨T.lower, h⟩ = ⟨S.lower, h'⟩
  /-- If the upper endpoint of `T` is singular, so is that of `S`, and it is its image. -/
  upper_preserving : ∀ h : T.IsSingular T.upper,
    ∃ h' : S.IsSingular S.upper, toFun ⟨T.upper, h⟩ = ⟨S.upper, h'⟩

/-- **Source: `def:admissible-regular-cofunction`.**  A frame-nondecreasing map on regular
elements, **from `S` to `T`**, preserving whichever endpoints happen to be regular. -/
structure AdmReg (T S : OneTruss) where
  /-- The underlying function on regular elements, running from `S` to `T`. -/
  toFun : Reg S → Reg T
  /-- Frame-nondecreasing. -/
  mono : ∀ {y y' : Reg S}, y ≤ y' → toFun y ≤ toFun y'
  /-- If the lower endpoint of `S` is regular, so is that of `T`, and it is its image. -/
  lower_preserving : ∀ h : S.IsRegular S.lower,
    ∃ h' : T.IsRegular T.lower, toFun ⟨S.lower, h⟩ = ⟨T.lower, h'⟩
  /-- If the upper endpoint of `S` is regular, so is that of `T`, and it is its image. -/
  upper_preserving : ∀ h : S.IsRegular S.upper,
    ∃ h' : T.IsRegular T.upper, toFun ⟨S.upper, h⟩ = ⟨T.upper, h'⟩

/-! ### G05: 1-truss bordisms -/

/-- **Source: `def:truss-bordism`.**  A 1-truss bordism `R : T ⇸ S` is a relation on
`T × S` satisfying the five displayed laws.  The face orders are the `≤` of `OneTruss.El`;
the frame orders are compared through `idx`. -/
structure Bord1 (T S : OneTruss) where
  /-- The underlying relation. -/
  rel : T.El → S.El → Prop
  /-- (nonempty) -/
  nonempty : ∃ x y, rel x y
  /-- (functorial) -/
  functorial : ∀ {x x' : T.El} {y y' : S.El}, x' ≤ x → rel x y → y ≤ y' → rel x' y'
  /-- (functional) every singular element of `T` is related to a unique singular element
  of `S`. -/
  functional : ∀ x : T.El, T.IsSingular x → ∃! y : S.El, S.IsSingular y ∧ rel x y
  /-- (cofunctional) every regular element of `S` is related to a unique regular element
  of `T`. -/
  cofunctional : ∀ y : S.El, S.IsRegular y → ∃! x : T.El, T.IsRegular x ∧ rel x y
  /-- (bimonotone) -/
  bimonotone : ∀ {x x' : T.El} {y y' : S.El}, rel x y → rel x' y' →
    (idx x).val < (idx x').val → ¬ ((idx y').val < (idx y).val)

namespace Bord1

variable {T S : OneTruss}

/-- **Source: `def:truss-bordism`, derived.**  The singular function `f_R`: the unique
singular element of `S` related to a given singular element of `T`.  It is determined by the
(functional) law and is not an additional choice. -/
noncomputable def singFun (R : Bord1 T S) (x : Sing T) : Sing S :=
  ⟨(R.functional x.el x.isSingular).choose,
    (R.functional x.el x.isSingular).choose_spec.1.1⟩

theorem singFun_rel (R : Bord1 T S) (x : Sing T) : R.rel x.el (R.singFun x).el :=
  (R.functional x.el x.isSingular).choose_spec.1.2

theorem singFun_unique (R : Bord1 T S) (x : Sing T) {y : S.El} (hy : S.IsSingular y)
    (hrel : R.rel x.el y) : y = (R.singFun x).el :=
  (R.functional x.el x.isSingular).choose_spec.2 y ⟨hy, hrel⟩

/-- **Source: `def:truss-bordism`, derived.**  The regular cofunction `g_R`: the unique
regular element of `T` related to a given regular element of `S`.  Determined by the
(cofunctional) law. -/
noncomputable def regCofun (R : Bord1 T S) (y : Reg S) : Reg T :=
  ⟨(R.cofunctional y.el y.isRegular).choose,
    (R.cofunctional y.el y.isRegular).choose_spec.1.1⟩

theorem regCofun_rel (R : Bord1 T S) (y : Reg S) : R.rel (R.regCofun y).el y.el :=
  (R.cofunctional y.el y.isRegular).choose_spec.1.2

theorem regCofun_unique (R : Bord1 T S) (y : Reg S) {x : T.El} (hx : T.IsRegular x)
    (hrel : R.rel x y.el) : x = (R.regCofun y).el :=
  (R.cofunctional y.el y.isRegular).choose_spec.2 x ⟨hx, hrel⟩

/-! #### The derived functions are admissible

These are the well-definedness claims that make the two reconstruction propositions of
Chapter 2 well typed.  Monotonicity is (bimonotone) plus the totality of the frame order;
endpoint preservation is (functorial) applied to a face comparison with an endpoint. -/

/-- The derived singular function is frame-nondecreasing. -/
theorem singFun_mono (R : Bord1 T S) {x x' : Sing T} (h : x ≤ x') :
    R.singFun x ≤ R.singFun x' := by
  rcases eq_or_lt_of_le h with heq | hlt
  · rw [heq]
  · rw [Sing.le_iff]
    by_contra hcon
    push_neg at hcon
    exact R.bimonotone (R.singFun_rel x) (R.singFun_rel x') (Sing.lt_iff.1 hlt) hcon

/-- The derived regular cofunction is frame-nondecreasing. -/
theorem regCofun_mono (R : Bord1 T S) {y y' : Reg S} (h : y ≤ y') :
    R.regCofun y ≤ R.regCofun y' := by
  rcases eq_or_lt_of_le h with heq | hlt
  · rw [heq]
  · rw [Reg.le_iff]
    by_contra hcon
    push_neg at hcon
    exact R.bimonotone (R.regCofun_rel y') (R.regCofun_rel y) hcon (Reg.lt_iff.1 hlt)

/-! #### The endpoint laws of admissibility

The remaining clauses of `def:admissible-singular-function` and
`def:admissible-regular-cofunction`.  Each is proved from (bimonotone) together with the two
bifunctionality laws: the frame order is total, the endpoints are its extreme elements, and
dimensions alternate, so a misplaced image is contradicted by comparing it with the
(co)function value at an adjacent endpoint-side element. -/

/-- If the lower endpoint of `T` is singular, so is that of `S`. -/
theorem lower_isSingular (R : Bord1 T S) (h : T.IsSingular T.lower) : S.IsSingular S.lower := by
  by_contra hreg
  rw [not_isSingular_iff] at hreg
  obtain ⟨x, hx, -⟩ := R.cofunctional S.lower hreg
  have hs0 : T.dim T.lower = 0 := h
  have hxne : (idx T.lower).val < (idx x).val := by
    have hne : x ≠ T.lower := by
      rintro rfl
      have h1 : T.dim T.lower = 1 := hx.1
      rw [hs0] at h1
      exact absurd h1 (by decide)
    have hz : (idx x).val ≠ 0 := fun hz => hne (idx_injective (Fin.ext (by simp [hz])))
    simpa using Nat.pos_of_ne_zero hz
  have hb := R.bimonotone (R.singFun_rel ⟨T.lower, h⟩) hx.2 hxne
  have hy0 : (idx (R.singFun ⟨T.lower, h⟩).el).val = 0 := by
    simp only [idx_lower, not_lt] at hb; omega
  have heq : (R.singFun ⟨T.lower, h⟩).el = S.lower :=
    idx_injective (Fin.ext (by rw [hy0]; simp))
  have hsing0 : S.dim S.lower = 0 := heq ▸ (R.singFun ⟨T.lower, h⟩).isSingular
  have hr : S.dim S.lower = 1 := hreg
  rw [hsing0] at hr
  exact absurd hr (by decide)

/-- If the upper endpoint of `T` is singular, so is that of `S`. -/
theorem upper_isSingular (R : Bord1 T S) (h : T.IsSingular T.upper) : S.IsSingular S.upper := by
  by_contra hreg
  rw [not_isSingular_iff] at hreg
  obtain ⟨x, hx, -⟩ := R.cofunctional S.upper hreg
  have hs0 : T.dim T.upper = 0 := h
  have hxne : (idx x).val < (idx T.upper).val := by
    have hne : x ≠ T.upper := by
      rintro rfl
      have h1 : T.dim T.upper = 1 := hx.1
      rw [hs0] at h1
      exact absurd h1 (by decide)
    rcases eq_or_lt_of_le (idx_le_upper x) with heq | hlt
    · exact absurd (idx_injective (Fin.ext heq)) hne
    · exact hlt
  have hb := R.bimonotone hx.2 (R.singFun_rel ⟨T.upper, h⟩) hxne
  have hy : (idx S.upper).val ≤ (idx (R.singFun ⟨T.upper, h⟩).el).val := by
    simp only [not_lt] at hb; exact hb
  have heq : (R.singFun ⟨T.upper, h⟩).el = S.upper :=
    idx_injective (Fin.ext (Nat.le_antisymm (idx_le_upper _) hy))
  have hsing0 : S.dim S.upper = 0 := heq ▸ (R.singFun ⟨T.upper, h⟩).isSingular
  have hr : S.dim S.upper = 1 := hreg
  rw [hsing0] at hr
  exact absurd hr (by decide)

/-- If the lower endpoint of `S` is regular, so is that of `T`. -/
theorem lower_isRegular (R : Bord1 T S) (h : S.IsRegular S.lower) : T.IsRegular T.lower := by
  by_contra hsing
  rw [not_isRegular_iff] at hsing
  obtain ⟨x, hx, -⟩ := R.cofunctional S.lower h
  have hs0 : T.dim T.lower = 0 := hsing
  have hxne : (idx T.lower).val < (idx x).val := by
    have hne : x ≠ T.lower := by
      rintro rfl
      have h1 : T.dim T.lower = 1 := hx.1
      rw [hs0] at h1
      exact absurd h1 (by decide)
    have hz : (idx x).val ≠ 0 := fun hz => hne (idx_injective (Fin.ext (by simp [hz])))
    simpa using Nat.pos_of_ne_zero hz
  have hb := R.bimonotone (R.singFun_rel ⟨T.lower, hsing⟩) hx.2 hxne
  have hy0 : (idx (R.singFun ⟨T.lower, hsing⟩).el).val = 0 := by
    simp only [idx_lower, not_lt] at hb; omega
  have heq : (R.singFun ⟨T.lower, hsing⟩).el = S.lower :=
    idx_injective (Fin.ext (by rw [hy0]; simp))
  have hsing0 : S.dim S.lower = 0 := heq ▸ (R.singFun ⟨T.lower, hsing⟩).isSingular
  have hr : S.dim S.lower = 1 := h
  rw [hsing0] at hr
  exact absurd hr (by decide)

/-- If the upper endpoint of `S` is regular, so is that of `T`. -/
theorem upper_isRegular (R : Bord1 T S) (h : S.IsRegular S.upper) : T.IsRegular T.upper := by
  by_contra hsing
  rw [not_isRegular_iff] at hsing
  obtain ⟨x, hx, -⟩ := R.cofunctional S.upper h
  have hs0 : T.dim T.upper = 0 := hsing
  have hxne : (idx x).val < (idx T.upper).val := by
    have hne : x ≠ T.upper := by
      rintro rfl
      have h1 : T.dim T.upper = 1 := hx.1
      rw [hs0] at h1
      exact absurd h1 (by decide)
    rcases eq_or_lt_of_le (idx_le_upper x) with heq | hlt
    · exact absurd (idx_injective (Fin.ext heq)) hne
    · exact hlt
  have hb := R.bimonotone hx.2 (R.singFun_rel ⟨T.upper, hsing⟩) hxne
  have hy : (idx S.upper).val ≤ (idx (R.singFun ⟨T.upper, hsing⟩).el).val := by
    simp only [not_lt] at hb; exact hb
  have heq : (R.singFun ⟨T.upper, hsing⟩).el = S.upper :=
    idx_injective (Fin.ext (Nat.le_antisymm (idx_le_upper _) hy))
  have hsing0 : S.dim S.upper = 0 := heq ▸ (R.singFun ⟨T.upper, hsing⟩).isSingular
  have hr : S.dim S.upper = 1 := h
  rw [hsing0] at hr
  exact absurd hr (by decide)

/-! #### The endpoint values

Not merely that the endpoint *types* match, but that the derived functions take the endpoint
to the endpoint.  Each proof compares the endpoint's image with the (co)function value at the
adjacent cell on the endpoint side, which has the opposite dimension parity; (bimonotone)
then pins the image down. -/

/-- If the lower endpoint of `T` is singular, the derived singular function sends it to the
lower endpoint of `S`. -/
theorem singFun_lower (R : Bord1 T S) (h : T.IsSingular T.lower) :
    (R.singFun ⟨T.lower, h⟩).el = S.lower := by
  have hSlow : S.IsSingular S.lower := R.lower_isSingular h
  by_contra hne
  have hy0 : 0 < (idx (R.singFun ⟨T.lower, h⟩).el).val := by
    rcases Nat.eq_zero_or_pos (idx (R.singFun ⟨T.lower, h⟩).el).val with hz | hp
    · exact absurd (idx_injective (Fin.ext (by rw [hz, idx_lower]))) hne
    · exact hp
  have hpar : (idx (R.singFun ⟨T.lower, h⟩).el).val % 2 = 0 := by
    have hp := S.parity_eq_of_isSingular (R.singFun ⟨T.lower, h⟩).isSingular hSlow
    simpa using hp
  have hy2 : 2 ≤ (idx (R.singFun ⟨T.lower, h⟩).el).val := by omega
  have hlen : (1 : ℕ) < S.len + 1 := by
    have hu := idx_le_upper (R.singFun ⟨T.lower, h⟩).el
    rw [idx_upper] at hu
    omega
  have hrreg : S.IsRegular (ofIdx ⟨1, hlen⟩) := by
    refine S.isRegular_of_parity_ne hSlow ?_
    have hr1 : (idx (ofIdx ⟨1, hlen⟩ : S.El)).val = 1 := rfl
    rw [idx_lower, hr1]
    decide
  obtain ⟨xr, hxr, -⟩ := R.cofunctional (ofIdx ⟨1, hlen⟩) hrreg
  have hs0 : T.dim T.lower = 0 := h
  have hxrne : (idx T.lower).val < (idx xr).val := by
    have hne' : xr ≠ T.lower := by
      rintro rfl
      have h1 : T.dim T.lower = 1 := hxr.1
      rw [hs0] at h1
      exact absurd h1 (by decide)
    have hz : (idx xr).val ≠ 0 := fun hz => hne' (idx_injective (Fin.ext (by rw [hz, idx_lower])))
    rw [idx_lower]
    exact Nat.pos_of_ne_zero hz
  have hb := R.bimonotone (R.singFun_rel ⟨T.lower, h⟩) hxr.2 hxrne
  simp only [not_lt] at hb
  have hr1 : (idx (ofIdx ⟨1, hlen⟩ : S.El)).val = 1 := rfl
  omega

/-- If the upper endpoint of `T` is singular, the derived singular function sends it to the
upper endpoint of `S`. -/
theorem singFun_upper (R : Bord1 T S) (h : T.IsSingular T.upper) :
    (R.singFun ⟨T.upper, h⟩).el = S.upper := by
  have hSup : S.IsSingular S.upper := R.upper_isSingular h
  by_contra hne
  have hyle : (idx (R.singFun ⟨T.upper, h⟩).el).val ≤ S.len := by
    simpa using idx_le_upper (R.singFun ⟨T.upper, h⟩).el
  have hylt : (idx (R.singFun ⟨T.upper, h⟩).el).val < S.len := by
    rcases eq_or_lt_of_le hyle with heq | hlt
    · exact absurd (idx_injective (Fin.ext (by rw [heq, idx_upper]))) hne
    · exact hlt
  have hpar : (idx (R.singFun ⟨T.upper, h⟩).el).val % 2 = S.len % 2 := by
    have hp := S.parity_eq_of_isSingular (R.singFun ⟨T.upper, h⟩).isSingular hSup
    rw [idx_upper] at hp
    exact hp
  have hy2 : (idx (R.singFun ⟨T.upper, h⟩).el).val + 2 ≤ S.len := by omega
  have hlen : S.len - 1 < S.len + 1 := by omega
  have hrreg : S.IsRegular (ofIdx ⟨S.len - 1, hlen⟩) := by
    refine S.isRegular_of_parity_ne hSup ?_
    rw [idx_upper]
    have : (idx (ofIdx ⟨S.len - 1, hlen⟩ : S.El)).val = S.len - 1 := rfl
    rw [this]
    omega
  obtain ⟨xr, hxr, -⟩ := R.cofunctional (ofIdx ⟨S.len - 1, hlen⟩) hrreg
  have hs0 : T.dim T.upper = 0 := h
  have hxrlt : (idx xr).val < (idx T.upper).val := by
    have hne' : xr ≠ T.upper := by
      rintro rfl
      have h1 : T.dim T.upper = 1 := hxr.1
      rw [hs0] at h1
      exact absurd h1 (by decide)
    rcases eq_or_lt_of_le (idx_le_upper xr) with heq | hlt
    · exact absurd (idx_injective (Fin.ext heq)) hne'
    · exact hlt
  have hb := R.bimonotone hxr.2 (R.singFun_rel ⟨T.upper, h⟩) hxrlt
  simp only [not_lt] at hb
  have hr1 : (idx (ofIdx ⟨S.len - 1, hlen⟩ : S.El)).val = S.len - 1 := rfl
  omega

/-- If the lower endpoint of `S` is regular, the derived regular cofunction sends it to the
lower endpoint of `T`. -/
theorem regCofun_lower (R : Bord1 T S) (h : S.IsRegular S.lower) :
    (R.regCofun ⟨S.lower, h⟩).el = T.lower := by
  have hTlow : T.IsRegular T.lower := R.lower_isRegular h
  by_contra hne
  have hx0 : 0 < (idx (R.regCofun ⟨S.lower, h⟩).el).val := by
    rcases Nat.eq_zero_or_pos (idx (R.regCofun ⟨S.lower, h⟩).el).val with hz | hp
    · exact absurd (idx_injective (Fin.ext (by rw [hz, idx_lower]))) hne
    · exact hp
  have hpar : (idx (R.regCofun ⟨S.lower, h⟩).el).val % 2 = 0 := by
    have hp := T.parity_eq_of_isRegular (R.regCofun ⟨S.lower, h⟩).isRegular hTlow
    simpa using hp
  have hx2 : 2 ≤ (idx (R.regCofun ⟨S.lower, h⟩).el).val := by omega
  have hlen : (1 : ℕ) < T.len + 1 := by
    have hu := idx_le_upper (R.regCofun ⟨S.lower, h⟩).el
    rw [idx_upper] at hu
    omega
  have hssing : T.IsSingular (ofIdx ⟨1, hlen⟩) := by
    refine T.isSingular_of_parity_ne hTlow ?_
    have hr1 : (idx (ofIdx ⟨1, hlen⟩ : T.El)).val = 1 := rfl
    rw [idx_lower, hr1]
    decide
  have hlt : (idx (ofIdx ⟨1, hlen⟩ : T.El)).val < (idx (R.regCofun ⟨S.lower, h⟩).el).val := by
    have hr1 : (idx (ofIdx ⟨1, hlen⟩ : T.El)).val = 1 := rfl
    omega
  have hb := R.bimonotone (R.singFun_rel ⟨_, hssing⟩) (R.regCofun_rel ⟨S.lower, h⟩) hlt
  simp only [Reg.el_mk, idx_lower, not_lt, Nat.le_zero] at hb
  have hys : (R.singFun ⟨(ofIdx ⟨1, hlen⟩ : T.El), hssing⟩).el = S.lower :=
    idx_injective (Fin.ext (by rw [hb, idx_lower]))
  have h0 : S.dim S.lower = 0 := hys ▸ (R.singFun ⟨_, hssing⟩).isSingular
  have h1 : S.dim S.lower = 1 := h
  rw [h0] at h1
  exact absurd h1 (by decide)

/-- If the upper endpoint of `S` is regular, the derived regular cofunction sends it to the
upper endpoint of `T`. -/
theorem regCofun_upper (R : Bord1 T S) (h : S.IsRegular S.upper) :
    (R.regCofun ⟨S.upper, h⟩).el = T.upper := by
  have hTup : T.IsRegular T.upper := R.upper_isRegular h
  by_contra hne
  have hxle : (idx (R.regCofun ⟨S.upper, h⟩).el).val ≤ T.len := by
    simpa using idx_le_upper (R.regCofun ⟨S.upper, h⟩).el
  have hxlt : (idx (R.regCofun ⟨S.upper, h⟩).el).val < T.len := by
    rcases eq_or_lt_of_le hxle with heq | hlt
    · exact absurd (idx_injective (Fin.ext (by rw [heq, idx_upper]))) hne
    · exact hlt
  have hpar : (idx (R.regCofun ⟨S.upper, h⟩).el).val % 2 = T.len % 2 := by
    have hp := T.parity_eq_of_isRegular (R.regCofun ⟨S.upper, h⟩).isRegular hTup
    rw [idx_upper] at hp
    exact hp
  have hx2 : (idx (R.regCofun ⟨S.upper, h⟩).el).val + 2 ≤ T.len := by omega
  have hlen : T.len - 1 < T.len + 1 := by omega
  have hssing : T.IsSingular (ofIdx ⟨T.len - 1, hlen⟩) := by
    refine T.isSingular_of_parity_ne hTup ?_
    rw [idx_upper]
    have : (idx (ofIdx ⟨T.len - 1, hlen⟩ : T.El)).val = T.len - 1 := rfl
    rw [this]
    omega
  have hlt : (idx (R.regCofun ⟨S.upper, h⟩).el).val < (idx (ofIdx ⟨T.len - 1, hlen⟩ : T.El)).val := by
    have hr1 : (idx (ofIdx ⟨T.len - 1, hlen⟩ : T.El)).val = T.len - 1 := rfl
    omega
  have hb := R.bimonotone (R.regCofun_rel ⟨S.upper, h⟩) (R.singFun_rel ⟨_, hssing⟩) hlt
  simp only [Reg.el_mk, not_lt] at hb
  have hys : (R.singFun ⟨(ofIdx ⟨T.len - 1, hlen⟩ : T.El), hssing⟩).el = S.upper :=
    idx_injective (Fin.ext (Nat.le_antisymm (idx_le_upper _) hb))
  have h0 : S.dim S.upper = 0 := hys ▸ (R.singFun ⟨_, hssing⟩).isSingular
  have h1 : S.dim S.upper = 1 := h
  rw [h0] at h1
  exact absurd h1 (by decide)

/-! #### The two maps `R ↦ f_R` and `R ↦ g_R` -/

/-- **Source: `prop:Reconstruction from the singular function` (Chapter 2), one half.**
The derived singular function of a bordism really is an admissible singular function, so
`R ↦ f_R` is a well-typed map `Bord1 T S → AdmSing T S`. -/
noncomputable def toAdmSing (R : Bord1 T S) : AdmSing T S where
  toFun := R.singFun
  mono := R.singFun_mono
  lower_preserving h := ⟨R.lower_isSingular h, Sing.ext (R.singFun_lower h)⟩
  upper_preserving h := ⟨R.upper_isSingular h, Sing.ext (R.singFun_upper h)⟩

/-- **Source: `prop:regular-reconstruction` (Chapter 2), one half.**
The derived regular cofunction of a bordism really is an admissible regular cofunction, so
`R ↦ g_R` is a well-typed map `Bord1 T S → AdmReg T S`. -/
noncomputable def toAdmReg (R : Bord1 T S) : AdmReg T S where
  toFun := R.regCofun
  mono := R.regCofun_mono
  lower_preserving h := ⟨R.lower_isRegular h, Reg.ext (R.regCofun_lower h)⟩
  upper_preserving h := ⟨R.upper_isRegular h, Reg.ext (R.regCofun_upper h)⟩

end Bord1

end Truss.Transfer.Geometry
