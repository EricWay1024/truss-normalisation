/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Geometry.OpenCoord

/-!
# Bordisms between open 1-trusses (G06, G07, T03)

This module formalises rows `G06` and `G07` of Chapter 2
(`dphil-notes-typst/transfer/ch02-trusses.typ`, §"Bordisms of 1-trusses") **in the open
setting**, together with the draft chapter's §5.3 row `T03`.

## The open simplification

For an open 1-truss both endpoints are regular, so the two conditional endpoint laws of
`AdmSing` are vacuous: an admissible singular function between open 1-trusses is just a
frame-nondecreasing map `Sing T → Sing S`, i.e. a monotone `Fin k →o Fin l` through
`OpenTruss.singEquiv` (`openAdmSingEquiv`).  Dually the two endpoint laws of `AdmReg` are
**always active**, so an admissible regular cofunction is a monotone `Fin (l+1) →o Fin (k+1)`
*preserving both endpoints* (`openAdmRegEquiv`).

## The uniform interval formula

Writing a singular cell of index `i` at frame coordinate `2i+1` and a regular cell of index
`j` at `2j`, the four interval cases of `proc:induced-truss-bordism` collapse into the single
pair of ℕ-valued bounds `loNat`, `hiNat`, and `R_f (x, y) ⟺ loNat (idx x) ≤ idx y ≤ hiNat
(idx x)` for **every** `x`, singular or regular.

## Main definitions

* `fNat`, `loNat`, `hiNat`, `cvNat`, `gNat`, `fineNat` — the ℕ-level coordinates.
* `induceOpen` — `proc:induced-truss-bordism` for open 1-trusses.
* `singHom`, `regHom` — the singular function and regular cofunction in coordinates.
* `openBordEquiv` — `prop:Reconstruction from the singular function`, open case.
* `OpenAdmReg`, `coinduceOpen`, `openBordRegEquiv` — `proc:coinduced-truss-bordism` and
  `prop:regular-reconstruction`, open case.
* `idBord`, `compBord` — the identity bordism and `def:bordism-composition`.

## Main results

* `openBordEquiv`, `openBordRegEquiv` — the two reconstruction propositions.
* `singHom_idBord`, `singHom_compBord` (and `singFun_id`, `singFun_comp`) — functoriality of
  the classification.
* `injective_singFun_iff_surjective_regCofun` — row `T03`.

## The four interval cases, checked against the source

With `lo (2j) = if j = 0 then 0 else 2·f(j-1)+1` and `hi (2j) = if j = k then 2l else
2·f(j)+1`, the regular cell `2j` has singular neighbours `2j-1` (present iff `j ≠ 0`, of
singular index `j-1`) and `2j+1` (present iff `j ≠ k`, of singular index `j`).  Hence:
`0 < j < k` is the chapter's case 1, `[f(s₋), f(s₊)]`; `j = k > 0` is case 2, `[f(s₋), u_S]`
(`u_S` is at `2l`); `j = 0 < k` is case 3, `[ℓ_S, f(s₊)]` (`ℓ_S` is at `0`); and `k = 0`,
where `j = 0 = k` forces `lo = 0`, `hi = 2l`, is case 4, `J = S`.

## A correction to the naive dual statement

`coinduceOpen` **cannot** take an arbitrary monotone `Fin (l+1) →o Fin (k+1)`: for `k = l =
1` there is exactly one bordism (`Fin 1 →o Fin 1` is a singleton) but three monotone maps
`Fin 2 →o Fin 2`.  The endpoint laws of `AdmReg` are what cut the three down to one, and they
are *not* vacuous in the open setting; `openAdmRegEquiv` is the formal statement that
`AdmReg T S` is exactly `OpenAdmReg k l`.
-/

namespace Truss.Transfer

open Geometry Geometry.OneTruss

/-! ### ℕ-level coordinates -/

section Coords

variable {k l : ℕ}

/-- The ℕ-valued extension of a monotone map `Fin k →o Fin l`, with junk value `l` outside
`[0, k)`.  The junk value is the *top* one, which keeps the extension monotone. -/
def fNat (f : Fin k →o Fin l) (i : ℕ) : ℕ := if h : i < k then (f ⟨i, h⟩).val else l

/-- The value of `fNat` inside the range. -/
theorem fNat_of_lt (f : Fin k →o Fin l) {i : ℕ} (h : i < k) : fNat f i = (f ⟨i, h⟩).val :=
  dif_pos h

/-- The junk value of `fNat` outside the range is the top value `l`. -/
theorem fNat_of_ge (f : Fin k →o Fin l) {i : ℕ} (h : k ≤ i) : fNat f i = l :=
  dif_neg (Nat.not_lt.2 h)

/-- `fNat` takes values in `[0, l)` inside the range. -/
theorem fNat_lt (f : Fin k →o Fin l) {i : ℕ} (h : i < k) : fNat f i < l := by
  rw [fNat_of_lt f h]; exact (f ⟨i, h⟩).isLt

/-- `fNat` is bounded by `l` everywhere. -/
theorem fNat_le (f : Fin k →o Fin l) (i : ℕ) : fNat f i ≤ l := by
  by_cases h : i < k
  · exact (fNat_lt f h).le
  · rw [fNat_of_ge f (Nat.not_lt.1 h)]

/-- `fNat` is monotone on all of `ℕ`, thanks to the choice of junk value. -/
theorem fNat_mono (f : Fin k →o Fin l) : Monotone (fNat f) := by
  intro i j hij
  by_cases hj : j < k
  · have hi : i < k := lt_of_le_of_lt hij hj
    rw [fNat_of_lt f hi, fNat_of_lt f hj]
    exact f.monotone (show (⟨i, hi⟩ : Fin k) ≤ ⟨j, hj⟩ from hij)
  · rw [fNat_of_ge f (Nat.not_lt.1 hj)]
    exact fNat_le f i

/-- **The lower bound of the interval `J_f`,** in frame coordinates: `0` at the lower
endpoint, and `2·f(i) + 1` where `i` is the singular cell just below. -/
def loNat (f : Fin k →o Fin l) (a : ℕ) : ℕ := if a = 0 then 0 else 2 * fNat f ((a - 1) / 2) + 1

/-- **The upper bound of the interval `J_f`,** in frame coordinates: `2l` at the upper
endpoint, and `2·f(i) + 1` where `i` is the singular cell just above. -/
def hiNat (f : Fin k →o Fin l) (a : ℕ) : ℕ :=
  if 2 * k ≤ a then 2 * l else 2 * fNat f (a / 2) + 1

/-- At the lower endpoint the interval starts at the lower endpoint of `S`. -/
theorem loNat_zero (f : Fin k →o Fin l) : loNat f 0 = 0 := if_pos rfl

/-- Away from the lower endpoint the interval starts at the image of the singular cell below. -/
theorem loNat_of_pos (f : Fin k →o Fin l) {a : ℕ} (h : a ≠ 0) :
    loNat f a = 2 * fNat f ((a - 1) / 2) + 1 := if_neg h

/-- Away from the upper endpoint the interval ends at the image of the singular cell above. -/
theorem hiNat_of_lt (f : Fin k →o Fin l) {a : ℕ} (h : a < 2 * k) :
    hiNat f a = 2 * fNat f (a / 2) + 1 := if_neg (Nat.not_le.2 h)

/-- At the upper endpoint the interval ends at the upper endpoint of `S`. -/
theorem hiNat_of_ge (f : Fin k →o Fin l) {a : ℕ} (h : 2 * k ≤ a) : hiNat f a = 2 * l :=
  if_pos h

/-- The interval never leaves the carrier of `S`. -/
theorem hiNat_le (f : Fin k →o Fin l) (a : ℕ) : hiNat f a ≤ 2 * l := by
  by_cases h : 2 * k ≤ a
  · rw [hiNat_of_ge f h]
  · rw [hiNat_of_lt f (Nat.not_le.1 h)]
    have : fNat f (a / 2) < l := fNat_lt f (by omega)
    omega

/-- **The engine of (bimonotone):** the intervals `J_f` advance weakly with the frame
coordinate, in the strong sense that the interval at `a` ends where the interval at any
`a' > a` starts. -/
theorem hiNat_le_loNat (f : Fin k →o Fin l) {a a' : ℕ} (h : a < a') :
    hiNat f a ≤ loNat f a' := by
  have ha' : a' ≠ 0 := by omega
  rw [loNat_of_pos f ha']
  by_cases hk : 2 * k ≤ a
  · rw [hiNat_of_ge f hk, fNat_of_ge f (show k ≤ (a' - 1) / 2 by omega)]
    omega
  · rw [hiNat_of_lt f (Nat.not_le.1 hk)]
    have := fNat_mono f (show a / 2 ≤ (a' - 1) / 2 by omega)
    omega

/-- The interval `J_f` is nonempty. -/
theorem loNat_le_hiNat (f : Fin k →o Fin l) {a : ℕ} (h : a ≤ 2 * k) :
    loNat f a ≤ hiNat f a := by
  by_cases ha : a = 0
  · rw [ha, loNat_zero]; exact Nat.zero_le _
  · rw [loNat_of_pos f ha]
    by_cases hk : 2 * k ≤ a
    · rw [hiNat_of_ge f hk]
      have : fNat f ((a - 1) / 2) < l := fNat_lt f (by omega)
      omega
    · rw [hiNat_of_lt f (Nat.not_le.1 hk)]
      have := fNat_mono f (show (a - 1) / 2 ≤ a / 2 by omega)
      omega

/-- At a **singular** frame coordinate the interval degenerates to the single point
`2·f(i) + 1`: this is the `y = f(x)` clause of `proc:induced-truss-bordism`. -/
theorem loNat_eq_hiNat_of_odd (f : Fin k →o Fin l) {a : ℕ} (hodd : a % 2 = 1)
    (hle : a ≤ 2 * k) :
    loNat f a = 2 * fNat f (a / 2) + 1 ∧ hiNat f a = 2 * fNat f (a / 2) + 1 := by
  have h2 : (a - 1) / 2 = a / 2 := by omega
  exact ⟨by rw [loNat_of_pos f (by omega), h2], hiNat_of_lt f (by omega)⟩

/-! #### The coordinate regular cofunction

The (cofunctional) law of `induce f` says that a regular cell `2j'` of `S` lies in exactly one
interval `J_f(2j)`.  That unique `j` is the number of singular cells `i` with `f(i) < j'`,
which is realised here as a least element. -/

/-- The defining condition of `cvNat` always has a witness, namely `k`. -/
private theorem cvNat_ex (f : Fin k →o Fin l) (j' : ℕ) : ∃ j, k ≤ j ∨ j' ≤ fNat f j :=
  ⟨k, Or.inl le_rfl⟩

/-- **The regular cofunction of the induced bordism, in coordinates:** the least `j` with
`j' ≤ fNat f j`, equivalently the number of singular cells `i` of `T` with `f(i) < j'`. -/
def cvNat (f : Fin k →o Fin l) (j' : ℕ) : ℕ := Nat.find (cvNat_ex f j')

/-- `cvNat f j'` satisfies its defining condition. -/
theorem cvNat_spec (f : Fin k →o Fin l) (j' : ℕ) :
    k ≤ cvNat f j' ∨ j' ≤ fNat f (cvNat f j') := Nat.find_spec (cvNat_ex f j')

/-- `cvNat f j'` is least among the `j` satisfying its defining condition. -/
theorem cvNat_min (f : Fin k →o Fin l) {j' j : ℕ} (h : k ≤ j ∨ j' ≤ fNat f j) :
    cvNat f j' ≤ j := Nat.find_min' (cvNat_ex f j') h

/-- `cvNat` takes values in `[0, k]`. -/
theorem cvNat_le_k (f : Fin k →o Fin l) (j' : ℕ) : cvNat f j' ≤ k := cvNat_min f (Or.inl le_rfl)

/-- The defining characterisation of `cvNat`: it is the lower adjoint of `fNat`. -/
theorem cvNat_le_iff (f : Fin k →o Fin l) {j' j : ℕ} :
    cvNat f j' ≤ j ↔ (k ≤ j ∨ j' ≤ fNat f j) := by
  refine ⟨fun h => ?_, cvNat_min f⟩
  rcases cvNat_spec f j' with hs | hs
  · exact Or.inl (le_trans hs h)
  · exact Or.inr (le_trans hs (fNat_mono f h))

/-- The strict form of `cvNat_le_iff`. -/
theorem lt_cvNat_iff (f : Fin k →o Fin l) {j' j : ℕ} :
    j < cvNat f j' ↔ (j < k ∧ fNat f j < j') := by
  rw [← Nat.not_le, cvNat_le_iff, not_or, Nat.not_le, Nat.not_le]

/-- `cvNat f` is monotone. -/
theorem cvNat_mono (f : Fin k →o Fin l) : Monotone (cvNat f) := by
  intro j' j'' h
  rcases cvNat_spec f j'' with hs | hs
  · have hk : cvNat f j'' = k := le_antisymm (cvNat_le_k f j'') hs
    rw [hk]
    exact cvNat_le_k f j'
  · exact cvNat_min f (Or.inr (le_trans h hs))

/-- `cvNat` preserves the lower endpoint. -/
theorem cvNat_zero (f : Fin k →o Fin l) : cvNat f 0 = 0 :=
  Nat.le_zero.1 (cvNat_min f (Or.inr (Nat.zero_le _)))

/-- `cvNat` preserves the upper endpoint. -/
theorem cvNat_of_ge (f : Fin k →o Fin l) {j' : ℕ} (h : l ≤ j') : cvNat f j' = k := by
  refine le_antisymm (cvNat_le_k f j') ?_
  by_contra hc
  rcases cvNat_spec f j' with hs | hs
  · exact hc hs
  · exact absurd (lt_of_le_of_lt hs (fNat_lt f (Nat.not_le.1 hc))) (by omega)

/-- **The (cofunctional) computation.**  A regular cell `2j'` of `S` lies in the interval
`J_f` of the regular cell `2j` of `T` exactly when `j = cvNat f j'`. -/
theorem even_mem_iff (f : Fin k →o Fin l) {j j' : ℕ} (hj : j ≤ k) (hj' : j' ≤ l) :
    (loNat f (2 * j) ≤ 2 * j' ∧ 2 * j' ≤ hiNat f (2 * j)) ↔ j = cvNat f j' := by
  have hA : loNat f (2 * j) ≤ 2 * j' ↔ j ≤ cvNat f j' := by
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simp [loNat_zero]
    · have he : (2 * j - 1) / 2 = j - 1 := by omega
      rw [loNat_of_pos f (by omega), he]
      rw [show (j ≤ cvNat f j') ↔ (j - 1 < cvNat f j') from by omega, lt_cvNat_iff]
      constructor
      · exact fun h => ⟨by omega, by omega⟩
      · exact fun h => by omega
  have hB : 2 * j' ≤ hiNat f (2 * j) ↔ cvNat f j' ≤ j := by
    rw [cvNat_le_iff]
    rcases eq_or_lt_of_le hj with rfl | hlt
    · rw [hiNat_of_ge f le_rfl]
      exact ⟨fun _ => Or.inl le_rfl, fun _ => by omega⟩
    · rw [hiNat_of_lt f (by omega), show (2 * j) / 2 = j from by omega]
      constructor
      · exact fun h => Or.inr (by omega)
      · rintro (h | h)
        · omega
        · omega
  rw [hA, hB]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

/-- `loNat` is either `0` (at the lower endpoint) or odd (a singular frame coordinate). -/
theorem loNat_parity (f : Fin k →o Fin l) (a : ℕ) : loNat f a = 0 ∨ loNat f a % 2 = 1 := by
  unfold loNat
  split
  · exact Or.inl rfl
  · exact Or.inr (by omega)

/-- `hiNat` is either `2l` (the upper endpoint) or odd (a singular frame coordinate). -/
theorem hiNat_parity (f : Fin k →o Fin l) (a : ℕ) : hiNat f a = 2 * l ∨ hiNat f a % 2 = 1 := by
  unfold hiNat
  split
  · exact Or.inl rfl
  · exact Or.inr (by omega)

/-- **(functorial), in coordinates.**  The face order relates a regular cell only to its two
adjacent singular cells, which is what the two disjunctive hypotheses record. -/
theorem induce_functorial_nat (f : Fin k →o Fin l) {a a' b b' : ℕ}
    (ha : a ≤ 2 * k) (ha' : a' ≤ 2 * k) (hb'le : b' ≤ 2 * l)
    (hx : a' = a ∨ (a' % 2 = 0 ∧ a % 2 = 1 ∧ (a' = a + 1 ∨ a = a' + 1)))
    (hy : b = b' ∨ (b % 2 = 0 ∧ b' % 2 = 1 ∧ (b = b' + 1 ∨ b' = b + 1)))
    (h1 : loNat f a ≤ b) (h2 : b ≤ hiNat f a) :
    loNat f a' ≤ b' ∧ b' ≤ hiNat f a' := by
  rcases hx with rfl | ⟨-, hao, hcase⟩
  · rcases hy with rfl | ⟨hbe, hb'o, hbcase⟩
    · exact ⟨h1, h2⟩
    · rcases hbcase with hc | hc
      · refine ⟨?_, by omega⟩
        rcases loNat_parity f a' with h0 | hpar <;> omega
      · refine ⟨by omega, ?_⟩
        rcases hiNat_parity f a' with h0 | hpar <;> omega
  · obtain ⟨hlo, hhi⟩ := loNat_eq_hiNat_of_odd f hao ha
    have hb : b = 2 * fNat f (a / 2) + 1 := by omega
    have hbb' : b' = b := by
      rcases hy with h | ⟨hbe, -, -⟩
      · exact h.symm
      · omega
    have hnonempty := loNat_le_hiNat f ha'
    rcases hcase with hc | hc
    · have hlo' : loNat f a' = 2 * fNat f (a / 2) + 1 := by
        rw [loNat_of_pos f (by omega), show (a' - 1) / 2 = a / 2 from by omega]
      exact ⟨by omega, by omega⟩
    · have hhi' : hiNat f a' = 2 * fNat f (a / 2) + 1 := by
        rw [hiNat_of_lt f (by omega), show a' / 2 = a / 2 from by omega]
      exact ⟨by omega, by omega⟩

end Coords

/-! ### Cells of an open 1-truss by frame coordinate -/

namespace OpenTruss

/-- The carrier element of an open 1-truss at a given frame coordinate. -/
def elAt (T : OpenTruss) {a : ℕ} (h : a ≤ 2 * T.numSing) : T.toOneTruss.El :=
  ofIdx ⟨a, by have := T.len_eq; omega⟩

@[simp] theorem idx_elAt (T : OpenTruss) {a : ℕ} (h : a ≤ 2 * T.numSing) :
    (idx (T.elAt h)).val = a := rfl

/-- Every frame coordinate of an open 1-truss lies in `[0, 2k]`. -/
theorem idx_le (T : OpenTruss) (x : T.toOneTruss.El) : (idx x).val ≤ 2 * T.numSing := by
  have h := idx_le_upper x
  rw [idx_upper] at h
  have := T.len_eq
  omega

/-- A cell of an open 1-truss is determined by its frame coordinate. -/
theorem el_eq_of_idx_eq (T : OpenTruss) {x y : T.toOneTruss.El}
    (h : (idx x).val = (idx y).val) : x = y := idx_injective (Fin.ext h)

/-- **The face order of an open 1-truss in frame coordinates.**  A nonidentity comparison
runs from an even (regular) coordinate to an adjacent odd (singular) one. -/
theorem le_iff_nat (T : OpenTruss) {x y : T.toOneTruss.El} :
    x ≤ y ↔ ((idx x).val = (idx y).val ∨
      ((idx x).val % 2 = 0 ∧ (idx y).val % 2 = 1 ∧
        ((idx x).val = (idx y).val + 1 ∨ (idx y).val = (idx x).val + 1))) := by
  rw [le_iff_faceLE]
  unfold OneTruss.FaceLE
  constructor
  · rintro (rfl | ⟨h1, h2, h3⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨T.isRegular_iff_even.1 h1, T.isSingular_iff_odd.1 h2, h3⟩
  · rintro (h | ⟨h1, h2, h3⟩)
    · exact Or.inl (T.el_eq_of_idx_eq h)
    · exact Or.inr ⟨T.isRegular_iff_even.2 h1, T.isSingular_iff_odd.2 h2, h3⟩

end OpenTruss

/-! ### G06: the induced bordism -/

section Induce

variable {T S : OpenTruss}

/-- **Source: `proc:induced-truss-bordism` (Chapter 2), open case.**  The bordism induced by
an admissible singular function `f`, in coordinates.  Its relation is the single interval
formula `loNat f (idx x) ≤ idx y ≤ hiNat f (idx x)`, which specialises to `y = f(x)` at a
singular `x` and to the chapter's four cases of `J_f` at a regular `x`. -/
def induceOpen (f : Fin T.numSing →o Fin S.numSing) : Bord1 T.toOneTruss S.toOneTruss where
  rel x y := loNat f (idx x).val ≤ (idx y).val ∧ (idx y).val ≤ hiNat f (idx x).val
  nonempty := ⟨T.toOneTruss.lower, S.toOneTruss.lower, by simp [loNat_zero]⟩
  functorial {x x' y y'} hx hrel hy :=
    induce_functorial_nat f (T.idx_le x) (T.idx_le x') (S.idx_le y')
      (T.le_iff_nat.1 hx) (S.le_iff_nat.1 hy) hrel.1 hrel.2
  functional x hx := by
    have hax : (idx x).val % 2 = 1 := T.isSingular_iff_odd.1 hx
    have hale : (idx x).val ≤ 2 * T.numSing := T.idx_le x
    obtain ⟨hlo, hhi⟩ := loNat_eq_hiNat_of_odd f hax hale
    have hflt : fNat f ((idx x).val / 2) < S.numSing := fNat_lt f (by omega)
    have hc : 2 * fNat f ((idx x).val / 2) + 1 ≤ 2 * S.numSing := by omega
    refine ⟨S.elAt hc, ⟨S.isSingular_iff_odd.2 (by rw [S.idx_elAt]; omega), by
      rw [S.idx_elAt]; omega⟩, ?_⟩
    rintro z ⟨-, hz1, hz2⟩
    exact S.el_eq_of_idx_eq (by rw [S.idx_elAt]; omega)
  cofunctional y hy := by
    have hby : (idx y).val % 2 = 0 := S.isRegular_iff_even.1 hy
    have hble : (idx y).val ≤ 2 * S.numSing := S.idx_le y
    have hj' : (idx y).val / 2 ≤ S.numSing := by omega
    have hcv := cvNat_le_k f ((idx y).val / 2)
    have hj : 2 * cvNat f ((idx y).val / 2) ≤ 2 * T.numSing := by omega
    refine ⟨T.elAt hj, ⟨T.isRegular_iff_even.2 (by rw [T.idx_elAt]; omega), ?_⟩, ?_⟩
    · have hmem := (even_mem_iff f hcv hj').2 rfl
      rw [show 2 * ((idx y).val / 2) = (idx y).val from by omega] at hmem
      rw [T.idx_elAt]
      exact hmem
    · rintro z ⟨hzr, hz1, hz2⟩
      have hzp : (idx z).val % 2 = 0 := T.isRegular_iff_even.1 hzr
      have hzle : (idx z).val ≤ 2 * T.numSing := T.idx_le z
      have hz : (idx z).val / 2 = cvNat f ((idx y).val / 2) := by
        refine (even_mem_iff f (by omega : (idx z).val / 2 ≤ T.numSing) hj').1 ?_
        rw [show 2 * ((idx z).val / 2) = (idx z).val from by omega,
          show 2 * ((idx y).val / 2) = (idx y).val from by omega]
        exact ⟨hz1, hz2⟩
      exact T.el_eq_of_idx_eq (by rw [T.idx_elAt]; omega)
  bimonotone {x x' y y'} h h' hlt := by
    have := hiNat_le_loNat f hlt
    omega

@[simp] theorem induceOpen_rel (f : Fin T.numSing →o Fin S.numSing) (x : T.toOneTruss.El)
    (y : S.toOneTruss.El) :
    (induceOpen f).rel x y ↔
      (loNat f (idx x).val ≤ (idx y).val ∧ (idx y).val ≤ hiNat f (idx x).val) := Iff.rfl

end Induce

/-! ### Order-theoretic bookkeeping for the two enumerations -/

namespace OpenTruss

/-- `singAt` is an order embedding for the frame order. -/
theorem singAt_le_iff (T : OpenTruss) {k : ℕ} (hk : T.numSing = k) {i j : Fin k} :
    T.singAt hk i ≤ T.singAt hk j ↔ i ≤ j := by
  rw [Sing.le_iff, T.idx_singAt, T.idx_singAt, Fin.le_def]
  constructor <;> (intro h; omega)

/-- `regAt` is an order embedding for the frame order. -/
theorem regAt_le_iff (T : OpenTruss) {k : ℕ} (hk : T.numSing = k) {i j : Fin (k + 1)} :
    T.regAt hk i ≤ T.regAt hk j ↔ i ≤ j := by
  rw [Reg.le_iff, T.idx_regAt, T.idx_regAt, Fin.le_def]
  constructor <;> (intro h; omega)

/-- `singIdx` is an order embedding for the frame order. -/
theorem singIdx_le_iff (T : OpenTruss) {k : ℕ} (hk : T.numSing = k)
    {s t : Sing T.toOneTruss} : T.singIdx hk s ≤ T.singIdx hk t ↔ s ≤ t := by
  conv_rhs => rw [← T.singAt_singIdx hk s, ← T.singAt_singIdx hk t]
  exact (T.singAt_le_iff hk).symm

/-- `regIdx` is an order embedding for the frame order. -/
theorem regIdx_le_iff (T : OpenTruss) {k : ℕ} (hk : T.numSing = k)
    {r q : Reg T.toOneTruss} : T.regIdx hk r ≤ T.regIdx hk q ↔ r ≤ q := by
  conv_rhs => rw [← T.regAt_regIdx hk r, ← T.regAt_regIdx hk q]
  exact (T.regAt_le_iff hk).symm

/-- The frame coordinate of a singular cell is `2i+1` for its singular index `i`. -/
theorem idx_eq_singIdx (T : OpenTruss) (s : Sing T.toOneTruss) :
    (idx s.el).val = 2 * (T.singIdx rfl s).val + 1 := by
  conv_lhs => rw [← T.singAt_singIdx rfl s]
  exact T.idx_singAt rfl _

/-- The frame coordinate of a regular cell is `2j` for its regular index `j`. -/
theorem idx_eq_regIdx (T : OpenTruss) (r : Reg T.toOneTruss) :
    (idx r.el).val = 2 * (T.regIdx rfl r).val := by
  conv_lhs => rw [← T.regAt_regIdx rfl r]
  exact T.idx_regAt rfl _

/-- The lower endpoint of an open 1-truss is not singular. -/
theorem not_isSingular_lower (T : OpenTruss) :
    ¬ T.toOneTruss.IsSingular T.toOneTruss.lower :=
  fun h => absurd ((T.toOneTruss.not_isSingular_iff _).2 T.isOpen.1) (not_not.2 h)

/-- The upper endpoint of an open 1-truss is not singular. -/
theorem not_isSingular_upper (T : OpenTruss) :
    ¬ T.toOneTruss.IsSingular T.toOneTruss.upper :=
  fun h => absurd ((T.toOneTruss.not_isSingular_iff _).2 T.isOpen.2) (not_not.2 h)

end OpenTruss

/-! ### Extensionality for the structures of Chapter 2 -/

/-- Two admissible singular functions with the same underlying map are equal. -/
theorem Geometry.AdmSing.ext' {T S : OneTruss} {A B : AdmSing T S} (h : A.toFun = B.toFun) :
    A = B := by
  cases A; cases B; cases h; rfl

/-- Two admissible regular cofunctions with the same underlying map are equal. -/
theorem Geometry.AdmReg.ext' {T S : OneTruss} {A B : AdmReg T S} (h : A.toFun = B.toFun) :
    A = B := by
  cases A; cases B; cases h; rfl

/-- Two 1-truss bordisms with the same underlying relation are equal. -/
theorem Geometry.Bord1.ext' {T S : OneTruss} {R Q : Bord1 T S} (h : R.rel = Q.rel) : R = Q := by
  cases R; cases Q; cases h; rfl

/-! ### The open simplification of admissibility -/

section Adm

variable (T S : OpenTruss)

/-- **The pivot of the open setting.**  Both endpoints of an open 1-truss are regular, so
the two conditional endpoint laws of `AdmSing` are vacuous: an admissible singular function
between open 1-trusses is exactly a frame-nondecreasing map `Sing T → Sing S`, i.e. a
monotone `Fin k →o Fin l`. -/
def openAdmSingEquiv :
    AdmSing T.toOneTruss S.toOneTruss ≃ (Fin T.numSing →o Fin S.numSing) where
  toFun A :=
    ⟨fun i => S.singIdx rfl (A.toFun (T.singAt rfl i)),
      fun _ _ h => (S.singIdx_le_iff rfl).2 (A.mono ((T.singAt_le_iff rfl).2 h))⟩
  invFun f :=
    { toFun := fun x => S.singAt rfl (f (T.singIdx rfl x))
      mono := fun h => (S.singAt_le_iff rfl).2 (f.monotone ((T.singIdx_le_iff rfl).2 h))
      lower_preserving := fun h => absurd h T.not_isSingular_lower
      upper_preserving := fun h => absurd h T.not_isSingular_upper }
  left_inv A := by
    refine Geometry.AdmSing.ext' (funext fun x => ?_)
    show S.singAt rfl (S.singIdx rfl (A.toFun (T.singAt rfl (T.singIdx rfl x)))) = A.toFun x
    rw [T.singAt_singIdx, S.singAt_singIdx]
  right_inv f := by
    refine OrderHom.ext _ _ (funext fun i => ?_)
    show S.singIdx rfl (S.singAt rfl (f (T.singIdx rfl (T.singAt rfl i)))) = f i
    rw [T.singIdx_singAt, S.singIdx_singAt]

end Adm

/-! ### The singular function in coordinates -/

section SingHom

variable {T S : OpenTruss}

/-- **The singular function of a bordism, in coordinates.**  This is `f_R` transported
through the frame-order enumerations `singEquiv`. -/
noncomputable def singHom (R : Bord1 T.toOneTruss S.toOneTruss) :
    Fin T.numSing →o Fin S.numSing where
  toFun i := S.singIdx rfl (R.singFun (T.singAt rfl i))
  monotone' _ _ h := (S.singIdx_le_iff rfl).2 (R.singFun_mono ((T.singAt_le_iff rfl).2 h))

/-- The defining formula for `singHom`. -/
theorem singHom_apply (R : Bord1 T.toOneTruss S.toOneTruss) (i : Fin T.numSing) :
    singHom R i = S.singIdx rfl (R.singFun (T.singAt rfl i)) := rfl

/-- The frame coordinate of the image of the singular cell at `2i+1`. -/
theorem singFun_idx (R : Bord1 T.toOneTruss S.toOneTruss) {i : ℕ} (hi : i < T.numSing) :
    (idx (R.singFun (T.singAt rfl ⟨i, hi⟩)).el).val = 2 * fNat (singHom R) i + 1 := by
  rw [fNat_of_lt _ hi, singHom_apply]
  exact S.idx_eq_singIdx _

end SingHom

/-! ### G06: reconstruction from the singular function -/

section Reconstruct

variable {T S : OpenTruss}

/-- The singular cell at an odd frame coordinate, packaged with the frame coordinate of its
image under the singular function. -/
theorem exists_sing_cell (R : Bord1 T.toOneTruss S.toOneTruss) {i : ℕ} (hi : i < T.numSing) :
    ∃ s : Sing T.toOneTruss, (idx s.el).val = 2 * i + 1 ∧
      (idx (R.singFun s).el).val = 2 * fNat (singHom R) i + 1 :=
  ⟨T.singAt rfl ⟨i, hi⟩, T.idx_singAt rfl _, singFun_idx R hi⟩

/-- **Openness kills the mixed case.**  A singular cell of an open 1-truss is related only to
singular cells: a regular image would force the two distinct regular neighbours of the cell
to coincide, by (cofunctional). -/
theorem isSingular_of_rel (R : Bord1 T.toOneTruss S.toOneTruss) {x : T.toOneTruss.El}
    (hx : T.toOneTruss.IsSingular x) {y : S.toOneTruss.El} (hrel : R.rel x y) :
    S.toOneTruss.IsSingular y := by
  by_contra hreg
  rw [OneTruss.not_isSingular_iff] at hreg
  obtain ⟨xs, hxs, hxsreg, hxsle⟩ := T.exists_neighbour_succ hx
  obtain ⟨xp, hxp, hxpreg, hxple⟩ := T.exists_neighbour_pred hx
  obtain ⟨z, -, huniq⟩ := R.cofunctional y hreg
  have es := huniq xs ⟨hxsreg, R.functorial hxsle hrel le_rfl⟩
  have ep := huniq xp ⟨hxpreg, R.functorial hxple hrel le_rfl⟩
  have hidx : (idx xs).val = (idx xp).val := by rw [es, ep]
  omega

/-- At a singular cell the bordism relation is exactly the singular function. -/
theorem rel_singular_iff (R : Bord1 T.toOneTruss S.toOneTruss) {x : T.toOneTruss.El}
    (hx : T.toOneTruss.IsSingular x) {y : S.toOneTruss.El} :
    R.rel x y ↔ y = (R.singFun ⟨x, hx⟩).el := by
  refine ⟨fun h => R.singFun_unique ⟨x, hx⟩ (isSingular_of_rel R hx h) h, fun h => ?_⟩
  subst h
  exact R.singFun_rel ⟨x, hx⟩

/-- **The interval bound is necessary.**  If a regular cell `x` is related to `y`, then `y`
lies in the interval `J` cut out by the images of the singular neighbours of `x`. -/
theorem mem_of_rel_regular (R : Bord1 T.toOneTruss S.toOneTruss) {x : T.toOneTruss.El}
    (hx : T.toOneTruss.IsRegular x) {y : S.toOneTruss.El} (hrel : R.rel x y) :
    loNat (singHom R) (idx x).val ≤ (idx y).val ∧
      (idx y).val ≤ hiNat (singHom R) (idx x).val := by
  have hax : (idx x).val % 2 = 0 := T.isRegular_iff_even.1 hx
  have hale : (idx x).val ≤ 2 * T.numSing := T.idx_le x
  have hble : (idx y).val ≤ 2 * S.numSing := S.idx_le y
  constructor
  · rcases Nat.eq_zero_or_pos (idx x).val with h0 | hpos
    · rw [h0, loNat_zero]
      exact Nat.zero_le _
    · have hj1 : (idx x).val / 2 - 1 < T.numSing := by omega
      obtain ⟨sm, hsmidx, hsmimg⟩ := exists_sing_cell R hj1
      have hb := R.bimonotone (R.singFun_rel sm) hrel (by omega)
      rw [loNat_of_pos _ (by omega),
        show ((idx x).val - 1) / 2 = (idx x).val / 2 - 1 from by omega]
      omega
  · rcases eq_or_lt_of_le hale with heq | hlt
    · rw [hiNat_of_ge _ (by omega)]
      omega
    · have hj : (idx x).val / 2 < T.numSing := by omega
      obtain ⟨sp, hspidx, hspimg⟩ := exists_sing_cell R hj
      have hb := R.bimonotone hrel (R.singFun_rel sp) (by omega)
      rw [hiNat_of_lt _ (by omega)]
      omega

/-- **The interval bound is sufficient, at a regular cell of `S`.**  Here the (cofunctional)
law identifies the unique regular cell of `T` whose interval contains `y`. -/
theorem rel_of_mem_regular_even (R : Bord1 T.toOneTruss S.toOneTruss) {x : T.toOneTruss.El}
    (hx : T.toOneTruss.IsRegular x) {y : S.toOneTruss.El} (hy : S.toOneTruss.IsRegular y)
    (h1 : loNat (singHom R) (idx x).val ≤ (idx y).val)
    (h2 : (idx y).val ≤ hiNat (singHom R) (idx x).val) : R.rel x y := by
  have hax : (idx x).val % 2 = 0 := T.isRegular_iff_even.1 hx
  have hby : (idx y).val % 2 = 0 := S.isRegular_iff_even.1 hy
  have hale : (idx x).val ≤ 2 * T.numSing := T.idx_le x
  have hble : (idx y).val ≤ 2 * S.numSing := S.idx_le y
  obtain ⟨x0, hx0reg, hrel0⟩ : ∃ x0, T.toOneTruss.IsRegular x0 ∧ R.rel x0 y :=
    ⟨(R.regCofun ⟨y, hy⟩).el, (R.regCofun ⟨y, hy⟩).isRegular, R.regCofun_rel ⟨y, hy⟩⟩
  have hax0 : (idx x0).val % 2 = 0 := T.isRegular_iff_even.1 hx0reg
  have hale0 : (idx x0).val ≤ 2 * T.numSing := T.idx_le x0
  obtain ⟨h1', h2'⟩ := mem_of_rel_regular R hx0reg hrel0
  have e1 : (idx x).val / 2 = cvNat (singHom R) ((idx y).val / 2) := by
    refine (even_mem_iff _ (by omega) (by omega)).1 ?_
    rw [show 2 * ((idx x).val / 2) = (idx x).val from by omega,
      show 2 * ((idx y).val / 2) = (idx y).val from by omega]
    exact ⟨h1, h2⟩
  have e2 : (idx x0).val / 2 = cvNat (singHom R) ((idx y).val / 2) := by
    refine (even_mem_iff _ (by omega) (by omega)).1 ?_
    rw [show 2 * ((idx x0).val / 2) = (idx x0).val from by omega,
      show 2 * ((idx y).val / 2) = (idx y).val from by omega]
    exact ⟨h1', h2'⟩
  have : x = x0 := T.el_eq_of_idx_eq (by omega)
  rw [this]
  exact hrel0

/-- **The interval bound is sufficient, at a regular cell of `T`.** -/
theorem rel_of_mem_regular (R : Bord1 T.toOneTruss S.toOneTruss) {x : T.toOneTruss.El}
    (hx : T.toOneTruss.IsRegular x) {y : S.toOneTruss.El}
    (h1 : loNat (singHom R) (idx x).val ≤ (idx y).val)
    (h2 : (idx y).val ≤ hiNat (singHom R) (idx x).val) : R.rel x y := by
  rcases S.toOneTruss.isSingular_or_isRegular y with hy | hy
  swap
  · exact rel_of_mem_regular_even R hx hy h1 h2
  have hax : (idx x).val % 2 = 0 := T.isRegular_iff_even.1 hx
  have hby : (idx y).val % 2 = 1 := S.isSingular_iff_odd.1 hy
  have hale : (idx x).val ≤ 2 * T.numSing := T.idx_le x
  have hble : (idx y).val ≤ 2 * S.numSing := S.idx_le y
  by_cases hcase : loNat (singHom R) (idx x).val ≤ (idx y).val - 1
  · -- the regular cell just below `y` lies in the same interval
    have hy0le : (idx y).val - 1 ≤ 2 * S.numSing := by omega
    have hy0 : S.toOneTruss.IsRegular (S.elAt hy0le) :=
      S.isRegular_iff_even.2 (by rw [S.idx_elAt]; omega)
    have hrel0 : R.rel x (S.elAt hy0le) :=
      rel_of_mem_regular_even R hx hy0 (by rw [S.idx_elAt]; omega) (by rw [S.idx_elAt]; omega)
    refine R.functorial le_rfl hrel0 (S.le_iff_nat.2 (Or.inr ⟨?_, hby, Or.inr ?_⟩))
    · rw [S.idx_elAt]; omega
    · rw [S.idx_elAt]; omega
  · -- `y` is the image of the singular cell just below `x`
    have hlo : loNat (singHom R) (idx x).val = (idx y).val := by omega
    have hne : (idx x).val ≠ 0 := by
      intro h0
      rw [h0, loNat_zero] at hlo
      omega
    have hj1 : (idx x).val / 2 - 1 < T.numSing := by omega
    obtain ⟨sm, hsmidx, hsmimg⟩ := exists_sing_cell R hj1
    rw [loNat_of_pos _ hne, show ((idx x).val - 1) / 2 = (idx x).val / 2 - 1 from by omega]
      at hlo
    have hyeq : (R.singFun sm).el = y := S.el_eq_of_idx_eq (by omega)
    refine R.functorial (T.le_iff_nat.2 (Or.inr ⟨hax, ?_, Or.inl ?_⟩)) (R.singFun_rel sm) ?_
    · omega
    · omega
    · exact le_of_eq hyeq

/-- **Source: `prop:Reconstruction from the singular function` (Chapter 2), open case.**
Every bordism between open 1-trusses is the bordism induced by its own singular function. -/
theorem rel_iff_induce (R : Bord1 T.toOneTruss S.toOneTruss) (x : T.toOneTruss.El)
    (y : S.toOneTruss.El) :
    R.rel x y ↔ (loNat (singHom R) (idx x).val ≤ (idx y).val ∧
      (idx y).val ≤ hiNat (singHom R) (idx x).val) := by
  rcases T.toOneTruss.isSingular_or_isRegular x with hx | hx
  · have hax : (idx x).val % 2 = 1 := T.isSingular_iff_odd.1 hx
    have hale : (idx x).val ≤ 2 * T.numSing := T.idx_le x
    have hi : (idx x).val / 2 < T.numSing := by omega
    obtain ⟨sm, hsmidx, hsmimg⟩ := exists_sing_cell R hi
    have hsmx : sm.el = x := T.el_eq_of_idx_eq (by omega)
    have hsx : sm = ⟨x, hx⟩ := Sing.ext hsmx
    obtain ⟨hlo, hhi⟩ := loNat_eq_hiNat_of_odd (singHom R) hax hale
    rw [rel_singular_iff R hx, ← hsx, hlo, hhi]
    constructor
    · rintro rfl
      omega
    · intro h
      exact S.el_eq_of_idx_eq (by omega)
  · exact ⟨fun h => mem_of_rel_regular R hx h, fun h => rel_of_mem_regular R hx h.1 h.2⟩

end Reconstruct

/-! ### G06: the classification -/

section Classify

variable {T S : OpenTruss}

/-- **`f_{R_f} = f`:** the singular function of the induced bordism is the given one. -/
theorem singFun_induceOpen (f : Fin T.numSing →o Fin S.numSing) (i : Fin T.numSing) :
    (induceOpen f).singFun (T.singAt rfl i) = S.singAt rfl (f i) := by
  have hi : (i : ℕ) < T.numSing := i.isLt
  have hfl : (f i).val < S.numSing := (f i).isLt
  have hf : fNat f (i : ℕ) = (f i).val := fNat_of_lt f hi
  obtain ⟨hlo, hhi⟩ :=
    loNat_eq_hiNat_of_odd f (a := 2 * (i : ℕ) + 1) (by omega) (by omega)
  have hhalf : (2 * (i : ℕ) + 1) / 2 = (i : ℕ) := by omega
  refine Sing.ext (((induceOpen f).singFun_unique (T.singAt rfl i)
    (S.singAt rfl (f i)).isSingular ?_).symm)
  show loNat f (idx (T.singAt rfl i).el).val ≤ (idx (S.singAt rfl (f i)).el).val ∧
    (idx (S.singAt rfl (f i)).el).val ≤ hiNat f (idx (T.singAt rfl i).el).val
  rw [T.idx_singAt, S.idx_singAt, hlo, hhi, hhalf, hf]
  exact ⟨le_rfl, le_rfl⟩

/-- **`f_{R_f} = f` in coordinates.** -/
theorem singHom_induceOpen (f : Fin T.numSing →o Fin S.numSing) :
    singHom (induceOpen f) = f := by
  refine OrderHom.ext _ _ (funext fun i => ?_)
  show S.singIdx rfl ((induceOpen f).singFun (T.singAt rfl i)) = f i
  rw [singFun_induceOpen, S.singIdx_singAt]

/-- **`R_{f_R} = R`.** -/
theorem induceOpen_singHom (R : Bord1 T.toOneTruss S.toOneTruss) :
    induceOpen (singHom R) = R :=
  Geometry.Bord1.ext' (funext fun x => funext fun y => propext (rel_iff_induce R x y).symm)

/-- **Source: `prop:Reconstruction from the singular function` (Chapter 2), open case.**
`R ↦ f_R` and `f ↦ R_f` are mutually inverse, so a 1-truss bordism between open 1-trusses is
exactly a monotone map `Fin k →o Fin l` of singular indices. -/
noncomputable def openBordEquiv (T S : OpenTruss) :
    Bord1 T.toOneTruss S.toOneTruss ≃ (Fin T.numSing →o Fin S.numSing) where
  toFun := singHom
  invFun := induceOpen
  left_inv := induceOpen_singHom
  right_inv := singHom_induceOpen

end Classify

/-! ### The identity bordism and composition of bordisms -/

section Comp

/-- **Source: `Identity 1-bordism` (Chapter 2).**  The identity bordism of a 1-truss: its
relation is the face order.  No openness is needed. -/
def idBord (T : OneTruss) : Bord1 T T where
  rel x y := x ≤ y
  nonempty := ⟨T.lower, T.lower, le_rfl⟩
  functorial hx hrel hy := le_trans hx (le_trans hrel hy)
  functional x hx := by
    refine ⟨x, ⟨hx, le_rfl⟩, ?_⟩
    rintro z ⟨-, (h | ⟨h1, -, -⟩)⟩
    · exact h.symm
    · rw [hx] at h1
      exact absurd h1 (by decide)
  cofunctional y hy := by
    refine ⟨y, ⟨hy, le_rfl⟩, ?_⟩
    rintro z ⟨-, (h | ⟨-, h2, -⟩)⟩
    · exact h
    · rw [hy] at h2
      exact absurd h2 (by decide)
  bimonotone {x x' y y'} h h' hlt hcon := by
    have d1 := idx_dist_le_one (Or.inl h)
    have d2 := idx_dist_le_one (Or.inl h')
    have hbe : (idx y).val = (idx x).val + 1 ∧ (idx y').val = (idx x).val := by omega
    rcases h with heq | ⟨-, hy0, -⟩
    · have : (idx x).val = (idx y).val := by rw [heq]
      omega
    rcases h' with heq' | ⟨-, hy0', -⟩
    · have : (idx x').val = (idx y').val := by rw [heq']
      omega
    exact OneTruss.dim_ne_of_succ T (by omega) (hy0.trans hy0'.symm)

/-- The singular function of the identity bordism is the identity. -/
theorem singFun_idBord (T : OneTruss) (x : Sing T) : (idBord T).singFun x = x :=
  Sing.ext (((idBord T).singFun_unique x x.isSingular le_rfl).symm)

/-- The regular cofunction of the identity bordism is the identity. -/
theorem regCofun_idBord (T : OneTruss) (y : Reg T) : (idBord T).regCofun y = y :=
  Reg.ext (((idBord T).regCofun_unique y y.isRegular le_rfl).symm)

variable {T S U : OpenTruss}

/-- Dual form of `isSingular_of_rel`: only regular cells of `T` are related to a regular cell
of `S`. -/
theorem isRegular_of_rel (R : Bord1 T.toOneTruss S.toOneTruss) {x : T.toOneTruss.El}
    {y : S.toOneTruss.El} (hy : S.toOneTruss.IsRegular y) (hrel : R.rel x y) :
    T.toOneTruss.IsRegular x := by
  rw [← OneTruss.not_isSingular_iff]
  exact fun hx => (S.toOneTruss.not_isSingular_iff y).2 hy (isSingular_of_rel R hx hrel)

/-- An open 1-truss without singular cells has a single cell. -/
theorem OpenTruss.eq_of_numSing_zero (S : OpenTruss) (h : S.numSing = 0)
    (y y' : S.toOneTruss.El) : y = y' :=
  S.el_eq_of_idx_eq (by have := S.idx_le y; have := S.idx_le y'; omega)

/-- If an open 1-truss has a singular cell, every cell has a singular cell above it in the
face order. -/
theorem OpenTruss.exists_singular_ge (S : OpenTruss) (hk : 0 < S.numSing)
    (y : S.toOneTruss.El) : ∃ s : S.toOneTruss.El, S.toOneTruss.IsSingular s ∧ y ≤ s := by
  have hale := S.idx_le y
  by_cases hodd : (idx y).val % 2 = 1
  · exact ⟨y, S.isSingular_iff_odd.2 hodd, le_rfl⟩
  · by_cases hlt : (idx y).val < 2 * S.numSing
    · have hle : (idx y).val + 1 ≤ 2 * S.numSing := by omega
      exact ⟨S.elAt hle, S.isSingular_iff_odd.2 (by rw [S.idx_elAt]; omega),
        S.le_iff_nat.2 (Or.inr ⟨by omega, by rw [S.idx_elAt]; omega,
          Or.inr (by rw [S.idx_elAt])⟩)⟩
    · have hle : (idx y).val - 1 ≤ 2 * S.numSing := by omega
      exact ⟨S.elAt hle, S.isSingular_iff_odd.2 (by rw [S.idx_elAt]; omega),
        S.le_iff_nat.2 (Or.inr ⟨by omega, by rw [S.idx_elAt]; omega,
          Or.inl (by rw [S.idx_elAt]; omega)⟩)⟩

/-- Every cell of `S` is related to some cell of `T` by a bordism `T ⇸ S`. -/
theorem exists_rel_left (R : Bord1 T.toOneTruss S.toOneTruss) (y : S.toOneTruss.El) :
    ∃ x, R.rel x y := by
  rcases S.toOneTruss.isSingular_or_isRegular y with hy | hy
  · obtain ⟨r, -, hrreg, hrle⟩ := S.exists_neighbour_pred hy
    exact ⟨(R.regCofun ⟨r, hrreg⟩).el, R.functorial le_rfl (R.regCofun_rel ⟨r, hrreg⟩) hrle⟩
  · exact ⟨(R.regCofun ⟨y, hy⟩).el, R.regCofun_rel ⟨y, hy⟩⟩

/-- **Source: `def:bordism-composition` (Chapter 2), open case.**  The relational composite
of two bordisms is a bordism. -/
def compBord (R : Bord1 T.toOneTruss S.toOneTruss) (Q : Bord1 S.toOneTruss U.toOneTruss) :
    Bord1 T.toOneTruss U.toOneTruss where
  rel x z := ∃ y, R.rel x y ∧ Q.rel y z
  nonempty := by
    rcases Nat.eq_zero_or_pos S.numSing with h0 | hpos
    · obtain ⟨x, y₁, h₁⟩ := R.nonempty
      obtain ⟨y₂, z, h₂⟩ := Q.nonempty
      exact ⟨x, z, y₁, h₁, S.eq_of_numSing_zero h0 y₂ y₁ ▸ h₂⟩
    · obtain ⟨s, hs, -⟩ := S.exists_singular_ge hpos S.toOneTruss.lower
      obtain ⟨x, hx⟩ := exists_rel_left R s
      exact ⟨x, (Q.singFun ⟨s, hs⟩).el, s, hx, Q.singFun_rel ⟨s, hs⟩⟩
  functorial hx hrel hz := by
    obtain ⟨y, hR, hQ⟩ := hrel
    exact ⟨y, R.functorial hx hR le_rfl, Q.functorial le_rfl hQ hz⟩
  functional x hx := by
    have hy : S.toOneTruss.IsSingular (R.singFun ⟨x, hx⟩).el := (R.singFun ⟨x, hx⟩).isSingular
    refine ⟨(Q.singFun (R.singFun ⟨x, hx⟩)).el,
      ⟨(Q.singFun (R.singFun ⟨x, hx⟩)).isSingular,
        (R.singFun ⟨x, hx⟩).el, R.singFun_rel ⟨x, hx⟩, Q.singFun_rel _⟩, ?_⟩
    rintro z ⟨hzs, y', hR, hQ⟩
    have hy' : S.toOneTruss.IsSingular y' := isSingular_of_rel R hx hR
    have hye : (⟨y', hy'⟩ : Sing S.toOneTruss) = R.singFun ⟨x, hx⟩ :=
      Sing.ext (R.singFun_unique ⟨x, hx⟩ hy' hR)
    rw [← hye]
    exact Q.singFun_unique ⟨y', hy'⟩ hzs hQ
  cofunctional z hz := by
    have hy : S.toOneTruss.IsRegular (Q.regCofun ⟨z, hz⟩).el := (Q.regCofun ⟨z, hz⟩).isRegular
    refine ⟨(R.regCofun (Q.regCofun ⟨z, hz⟩)).el,
      ⟨(R.regCofun (Q.regCofun ⟨z, hz⟩)).isRegular,
        (Q.regCofun ⟨z, hz⟩).el, R.regCofun_rel _, Q.regCofun_rel ⟨z, hz⟩⟩, ?_⟩
    rintro x ⟨hxr, y', hR, hQ⟩
    have hy' : S.toOneTruss.IsRegular y' := isRegular_of_rel Q hz hQ
    have hye : (⟨y', hy'⟩ : Reg S.toOneTruss) = Q.regCofun ⟨z, hz⟩ :=
      Reg.ext (Q.regCofun_unique ⟨z, hz⟩ hy' hQ)
    rw [← hye]
    exact R.regCofun_unique ⟨y', hy'⟩ hxr hR
  bimonotone {x x' z z'} h h' hlt hcon := by
    obtain ⟨y, hR, hQ⟩ := h
    obtain ⟨y', hR', hQ'⟩ := h'
    rcases lt_trichotomy (idx y).val (idx y').val with hy | hy | hy
    · exact Q.bimonotone hQ hQ' hy hcon
    · -- `y = y'`: either it is regular, and `x = x'`, or singular, and `z = z'`
      have hyy : y = y' := S.el_eq_of_idx_eq hy
      subst hyy
      rcases S.toOneTruss.isSingular_or_isRegular y with hys | hyr
      · have hz1 := Q.singFun_unique ⟨y, hys⟩ (isSingular_of_rel Q hys hQ) hQ
        have hz2 := Q.singFun_unique ⟨y, hys⟩ (isSingular_of_rel Q hys hQ') hQ'
        rw [hz1, hz2] at hcon
        omega
      · have hx1 := R.regCofun_unique ⟨y, hyr⟩ (isRegular_of_rel R hyr hR) hR
        have hx2 := R.regCofun_unique ⟨y, hyr⟩ (isRegular_of_rel R hyr hR') hR'
        rw [hx1, hx2] at hlt
        omega
    · exact R.bimonotone hR hR' hlt hy

/-- The singular function of a composite is the composite of the singular functions. -/
theorem singFun_compBord (R : Bord1 T.toOneTruss S.toOneTruss)
    (Q : Bord1 S.toOneTruss U.toOneTruss) (x : Sing T.toOneTruss) :
    (compBord R Q).singFun x = Q.singFun (R.singFun x) :=
  Sing.ext (((compBord R Q).singFun_unique x (Q.singFun (R.singFun x)).isSingular
    ⟨(R.singFun x).el, R.singFun_rel x, Q.singFun_rel (R.singFun x)⟩).symm)

/-- The regular cofunction of a composite is the composite of the regular cofunctions, in the
reversed order. -/
theorem regCofun_compBord (R : Bord1 T.toOneTruss S.toOneTruss)
    (Q : Bord1 S.toOneTruss U.toOneTruss) (z : Reg U.toOneTruss) :
    (compBord R Q).regCofun z = R.regCofun (Q.regCofun z) :=
  Reg.ext (((compBord R Q).regCofun_unique z (R.regCofun (Q.regCofun z)).isRegular
    ⟨(Q.regCofun z).el, R.regCofun_rel (Q.regCofun z), Q.regCofun_rel z⟩).symm)

/-- **Functoriality of the classification, identity part.** -/
theorem singHom_idBord (T : OpenTruss) : singHom (idBord T.toOneTruss) = OrderHom.id := by
  refine OrderHom.ext _ _ (funext fun i => ?_)
  show T.singIdx rfl ((idBord T.toOneTruss).singFun (T.singAt rfl i)) = i
  rw [singFun_idBord, T.singIdx_singAt]

/-- **Functoriality of the classification, composition part.** -/
theorem singHom_compBord (R : Bord1 T.toOneTruss S.toOneTruss)
    (Q : Bord1 S.toOneTruss U.toOneTruss) :
    singHom (compBord R Q) = (singHom Q).comp (singHom R) := by
  refine OrderHom.ext _ _ (funext fun i => ?_)
  show U.singIdx rfl ((compBord R Q).singFun (T.singAt rfl i)) =
    U.singIdx rfl (Q.singFun (S.singAt rfl (S.singIdx rfl (R.singFun (T.singAt rfl i)))))
  rw [singFun_compBord, S.singAt_singIdx]

/-- **`singFun_id`.**  The identity bordism is classified by the identity monotone map; this
is `singHom_idBord` under the name used by the plan. -/
theorem singFun_id (T : OpenTruss) : singHom (idBord T.toOneTruss) = OrderHom.id :=
  singHom_idBord T

/-- **`singFun_comp`.**  A composite bordism is classified by the composite monotone map;
this is `singHom_compBord` under the name used by the plan. -/
theorem singFun_comp (R : Bord1 T.toOneTruss S.toOneTruss)
    (Q : Bord1 S.toOneTruss U.toOneTruss) :
    singHom (compBord R Q) = (singHom Q).comp (singHom R) := singHom_compBord R Q

/-- The identity bordism is induced by the identity monotone map. -/
theorem induceOpen_id (T : OpenTruss) :
    induceOpen (T := T) (S := T) OrderHom.id = idBord T.toOneTruss := by
  rw [← singHom_idBord T, induceOpen_singHom]

/-- The induced bordism of a composite is the composite of the induced bordisms. -/
theorem induceOpen_comp (f : Fin T.numSing →o Fin S.numSing)
    (g : Fin S.numSing →o Fin U.numSing) :
    induceOpen (g.comp f) = compBord (induceOpen f) (induceOpen g) := by
  rw [← singHom_induceOpen f, ← singHom_induceOpen g, ← singHom_compBord,
    induceOpen_singHom, singHom_induceOpen, singHom_induceOpen]

end Comp

/-! ### G07: the regular cofunction in coordinates -/

/-- **Admissible regular cofunctions between open 1-trusses, in coordinates.**  Both
endpoints of an open 1-truss are regular, so — unlike the two endpoint laws of `AdmSing` —
the two endpoint laws of `AdmReg` are **always active**: they say exactly that `g` preserves
the two ends. -/
structure OpenAdmReg (k l : ℕ) where
  /-- The underlying monotone map, running from the regular cells of `S` to those of `T`. -/
  toFun : Fin (l + 1) →o Fin (k + 1)
  /-- Lower-endpoint preservation. -/
  map_zero : toFun 0 = 0
  /-- Upper-endpoint preservation. -/
  map_last : toFun (Fin.last l) = Fin.last k

namespace OpenAdmReg

/-- Two admissible regular cofunctions with the same underlying map are equal. -/
theorem ext' {k l : ℕ} {A B : OpenAdmReg k l} (h : A.toFun = B.toFun) : A = B := by
  cases A; cases B; cases h; rfl

end OpenAdmReg

namespace OpenTruss

/-- The singular index of a singular cell is half its frame coordinate, rounded down. -/
theorem val_singIdx (T : OpenTruss) (s : Sing T.toOneTruss) :
    (T.singIdx rfl s).val = (idx s.el).val / 2 := rfl

/-- The regular index of a regular cell is half its frame coordinate. -/
theorem val_regIdx (T : OpenTruss) (r : Reg T.toOneTruss) :
    (T.regIdx rfl r).val = (idx r.el).val / 2 := rfl

/-- The lower endpoint as a regular cell. -/
theorem regAt_zero (T : OpenTruss) : (T.regAt rfl (0 : Fin (T.numSing + 1))).el =
    T.toOneTruss.lower := T.el_eq_of_idx_eq (by rw [T.idx_regAt]; simp)

/-- The upper endpoint as a regular cell. -/
theorem regAt_last (T : OpenTruss) : (T.regAt rfl (Fin.last T.numSing)).el =
    T.toOneTruss.upper := by
  refine T.el_eq_of_idx_eq ?_
  rw [T.idx_regAt, idx_upper, T.len_eq]
  rfl

end OpenTruss

section RegHom

variable {T S : OpenTruss}

/-- **The coordinate regular cofunction of an induced bordism,** i.e. the lower adjoint of
`f`.  Its endpoint equations are automatic. -/
def coarseHom {k l : ℕ} (f : Fin k →o Fin l) : OpenAdmReg k l where
  toFun :=
    ⟨fun j' => ⟨cvNat f j'.val, Nat.lt_succ_of_le (cvNat_le_k f j'.val)⟩,
      fun _ _ h => cvNat_mono f h⟩
  map_zero := Fin.ext (by
    show cvNat f (0 : Fin (l + 1)).val = (0 : Fin (k + 1)).val
    rw [Fin.val_zero, Fin.val_zero, cvNat_zero])
  map_last := Fin.ext (by
    show cvNat f (Fin.last l).val = (Fin.last k).val
    rw [Fin.val_last, Fin.val_last, cvNat_of_ge f le_rfl])

/-- The defining formula for `coarseHom`. -/
theorem coarseHom_apply {k l : ℕ} (f : Fin k →o Fin l) (j' : Fin (l + 1)) :
    ((coarseHom f).toFun j').val = cvNat f j'.val := rfl

/-- **The regular cofunction of a bordism, in coordinates.** -/
noncomputable def regHom (R : Bord1 T.toOneTruss S.toOneTruss) :
    OpenAdmReg T.numSing S.numSing where
  toFun :=
    ⟨fun j' => T.regIdx rfl (R.regCofun (S.regAt rfl j')),
      fun _ _ h => (T.regIdx_le_iff rfl).2 (R.regCofun_mono ((S.regAt_le_iff rfl).2 h))⟩
  map_zero := by
    refine Fin.ext ?_
    show (idx (R.regCofun (S.regAt rfl (0 : Fin (S.numSing + 1)))).el).val / 2 = 0
    have hr : S.regAt rfl (0 : Fin (S.numSing + 1)) = ⟨S.toOneTruss.lower, S.isOpen.1⟩ :=
      Reg.ext S.regAt_zero
    rw [hr, R.regCofun_lower S.isOpen.1, idx_lower]
  map_last := by
    refine Fin.ext ?_
    show (idx (R.regCofun (S.regAt rfl (Fin.last S.numSing))).el).val / 2 = _
    have hr : S.regAt rfl (Fin.last S.numSing) = ⟨S.toOneTruss.upper, S.isOpen.2⟩ :=
      Reg.ext S.regAt_last
    rw [hr, R.regCofun_upper S.isOpen.2, idx_upper]
    have := T.len_eq
    show T.toOneTruss.len / 2 = T.numSing
    omega

/-- The defining formula for `regHom`. -/
theorem regHom_apply (R : Bord1 T.toOneTruss S.toOneTruss) (j' : Fin (S.numSing + 1)) :
    (regHom R).toFun j' = T.regIdx rfl (R.regCofun (S.regAt rfl j')) := rfl


/-- The frame coordinate of the regular cofunction of an induced bordism. -/
theorem idx_regCofun_induceOpen (f : Fin T.numSing →o Fin S.numSing) (r : Reg S.toOneTruss) :
    (idx ((induceOpen f).regCofun r).el).val = 2 * cvNat f ((idx r.el).val / 2) := by
  have hby : (idx r.el).val % 2 = 0 := S.isRegular_iff_even.1 r.isRegular
  have hble : (idx r.el).val ≤ 2 * S.numSing := S.idx_le r.el
  have hcv := cvNat_le_k f ((idx r.el).val / 2)
  have hj : 2 * cvNat f ((idx r.el).val / 2) ≤ 2 * T.numSing := by omega
  have hx : T.toOneTruss.IsRegular (T.elAt hj) :=
    T.isRegular_iff_even.2 (by rw [T.idx_elAt]; omega)
  have hmem := (even_mem_iff f hcv (by omega : (idx r.el).val / 2 ≤ S.numSing)).2 rfl
  rw [show 2 * ((idx r.el).val / 2) = (idx r.el).val from by omega] at hmem
  have hrel : (induceOpen f).rel (T.elAt hj) r.el := by
    show loNat f (idx (T.elAt hj)).val ≤ (idx r.el).val ∧
      (idx r.el).val ≤ hiNat f (idx (T.elAt hj)).val
    rw [T.idx_elAt]
    exact hmem
  have heq := (induceOpen f).regCofun_unique r hx hrel
  rw [← heq, T.idx_elAt]

/-- **`g_{R_f}` is the lower adjoint `cvNat f`.** -/
theorem regHom_induceOpen (f : Fin T.numSing →o Fin S.numSing) :
    regHom (induceOpen f) = coarseHom f := by
  refine OpenAdmReg.ext' (OrderHom.ext _ _ (funext fun j' => Fin.ext ?_))
  show (T.regIdx rfl ((induceOpen f).regCofun (S.regAt rfl j'))).val = cvNat f j'.val
  rw [T.val_regIdx, idx_regCofun_induceOpen, S.idx_regAt,
    show 2 * (j' : ℕ) / 2 = (j' : ℕ) from by omega]
  omega

/-- The regular cofunction of a bordism is the lower adjoint of its singular function. -/
theorem regHom_eq_coarseHom (R : Bord1 T.toOneTruss S.toOneTruss) :
    regHom R = coarseHom (singHom R) := by
  conv_lhs => rw [← induceOpen_singHom R]
  exact regHom_induceOpen (singHom R)

end RegHom

/-! ### G07: the coinduced bordism -/

section Dual

variable {k l : ℕ}

/-- The ℕ-valued extension of an admissible regular cofunction, clamped to `[0, l]`. -/
def gNat (g : OpenAdmReg k l) (j' : ℕ) : ℕ := (g.toFun ⟨min j' l, by omega⟩).val

/-- `gNat` takes values in `[0, k]`. -/
theorem gNat_le_k (g : OpenAdmReg k l) (j' : ℕ) : gNat g j' ≤ k :=
  Nat.lt_succ_iff.1 (g.toFun _).isLt

/-- `gNat` is monotone on all of `ℕ`. -/
theorem gNat_mono (g : OpenAdmReg k l) : Monotone (gNat g) := fun _ _ h =>
  g.toFun.monotone (Fin.mk_le_mk.2 (by omega))

/-- The value of `gNat` inside the range. -/
theorem gNat_of_le (g : OpenAdmReg k l) {j' : ℕ} (h : j' ≤ l) :
    gNat g j' = (g.toFun ⟨j', Nat.lt_succ_of_le h⟩).val := by
  show (g.toFun ⟨min j' l, by omega⟩).val = _
  rw [show (⟨min j' l, by omega⟩ : Fin (l + 1)) = ⟨j', Nat.lt_succ_of_le h⟩ from
    Fin.ext (show min j' l = j' from by omega)]

/-- `gNat` preserves the lower endpoint; this is the first endpoint law of `OpenAdmReg`. -/
theorem gNat_zero (g : OpenAdmReg k l) : gNat g 0 = 0 := by
  rw [gNat_of_le g (Nat.zero_le l),
    show (⟨0, Nat.lt_succ_of_le (Nat.zero_le l)⟩ : Fin (l + 1)) = 0 from Fin.ext (by simp),
    g.map_zero, Fin.val_zero]

/-- `gNat` is constant equal to `k` from `l` onwards; this is the second endpoint law. -/
theorem gNat_of_ge (g : OpenAdmReg k l) {j' : ℕ} (h : l ≤ j') : gNat g j' = k := by
  show (g.toFun ⟨min j' l, by omega⟩).val = k
  rw [show (⟨min j' l, by omega⟩ : Fin (l + 1)) = Fin.last l from
    Fin.ext (show min j' l = l from by omega), g.map_last, Fin.val_last]

/-- The defining condition of `fineNat` always has a witness, namely `l`. -/
private theorem fineNat_ex (g : OpenAdmReg k l) (i : ℕ) : ∃ j', l ≤ j' ∨ i < gNat g j' :=
  ⟨l, Or.inl le_rfl⟩

/-- **The singular function recovered from a regular cofunction, in coordinates:** one less
than the least `j'` with `i < gNat g j'`, i.e. the greatest `j'` with `gNat g j' ≤ i`. -/
def fineNat (g : OpenAdmReg k l) (i : ℕ) : ℕ := Nat.find (fineNat_ex g i) - 1

/-- The defining characterisation of the least element underlying `fineNat`. -/
theorem find_le_iff (g : OpenAdmReg k l) {i j' : ℕ} :
    Nat.find (fineNat_ex g i) ≤ j' ↔ (l ≤ j' ∨ i < gNat g j') := by
  refine ⟨fun h => ?_, fun h => Nat.find_min' _ h⟩
  rcases Nat.find_spec (fineNat_ex g i) with hs | hs
  · exact Or.inl (le_trans hs h)
  · exact Or.inr (lt_of_lt_of_le hs (gNat_mono g h))

/-- The least element underlying `fineNat` is at most `l`. -/
theorem find_le_l (g : OpenAdmReg k l) (i : ℕ) : Nat.find (fineNat_ex g i) ≤ l :=
  Nat.find_min' _ (Or.inl le_rfl)

/-- Inside the range the least element underlying `fineNat` is positive. -/
theorem one_le_find (g : OpenAdmReg k l) {i : ℕ} (hi : i < k) :
    1 ≤ Nat.find (fineNat_ex g i) := by
  by_contra hc
  rcases (find_le_iff g).1 (show Nat.find (fineNat_ex g i) ≤ 0 by omega) with h | h
  · have hk : gNat g 0 = k := gNat_of_ge g (by omega)
    rw [gNat_zero] at hk
    omega
  · rw [gNat_zero] at h
    omega

/-- **The Galois characterisation of `fineNat`.** -/
theorem le_fineNat_iff (g : OpenAdmReg k l) {i j' : ℕ} (hi : i < k) :
    j' ≤ fineNat g i ↔ gNat g j' ≤ i := by
  have h1 := one_le_find g hi
  constructor
  · intro h
    have hnot : ¬ (Nat.find (fineNat_ex g i) ≤ j') := by unfold fineNat at h; omega
    obtain ⟨hl, hg⟩ := not_or.1 (fun hc => hnot ((find_le_iff g).2 hc))
    omega
  · intro h
    have hnot : ¬ (Nat.find (fineNat_ex g i) ≤ j') := by
      intro hc
      rcases (find_le_iff g).1 hc with hl | hg
      · have hk : gNat g j' = k := gNat_of_ge g hl
        omega
      · omega
    unfold fineNat
    omega

/-- `fineNat` takes values in `[0, l)` inside the range. -/
theorem fineNat_lt (g : OpenAdmReg k l) {i : ℕ} (hi : i < k) : fineNat g i < l := by
  have h1 := find_le_l g i
  have h2 := one_le_find g hi
  unfold fineNat
  omega

/-- `fineNat` is monotone. -/
theorem fineNat_mono (g : OpenAdmReg k l) : Monotone (fineNat g) := by
  intro i i' h
  have hfind : Nat.find (fineNat_ex g i) ≤ Nat.find (fineNat_ex g i') := by
    refine Nat.find_min' _ ?_
    rcases Nat.find_spec (fineNat_ex g i') with hs | hs
    · exact Or.inl hs
    · exact Or.inr (lt_of_le_of_lt h hs)
  unfold fineNat
  omega

/-- **The singular function recovered from a regular cofunction.** -/
def fineHom (g : OpenAdmReg k l) : Fin k →o Fin l where
  toFun i := ⟨fineNat g i.val, fineNat_lt g i.isLt⟩
  monotone' _ _ h := fineNat_mono g h

/-- `fNat` of `fineHom` is `fineNat`, inside the range. -/
theorem fNat_fineHom (g : OpenAdmReg k l) {i : ℕ} (hi : i < k) :
    fNat (fineHom g) i = fineNat g i := by rw [fNat_of_lt _ hi]; rfl

/-- **The two adjoints are mutually inverse, first equation.** -/
theorem coarseHom_fineHom (g : OpenAdmReg k l) : coarseHom (fineHom g) = g := by
  refine OpenAdmReg.ext' (OrderHom.ext _ _ (funext fun j' => Fin.ext ?_))
  show cvNat (fineHom g) j'.val = (g.toFun j').val
  have key : ∀ j, cvNat (fineHom g) j'.val ≤ j ↔ gNat g j'.val ≤ j := by
    intro j
    rw [cvNat_le_iff]
    constructor
    · rintro (h | h)
      · exact le_trans (gNat_le_k g _) h
      · by_cases hjk : j < k
        · rw [fNat_fineHom g hjk] at h
          exact (le_fineNat_iff g hjk).1 h
        · exact le_trans (gNat_le_k g _) (by omega)
    · intro h
      by_cases hjk : j < k
      · exact Or.inr (by rw [fNat_fineHom g hjk]; exact (le_fineNat_iff g hjk).2 h)
      · exact Or.inl (by omega)
  have h1 : cvNat (fineHom g) j'.val ≤ gNat g j'.val := (key _).2 le_rfl
  have h2 : gNat g j'.val ≤ cvNat (fineHom g) j'.val := (key _).1 le_rfl
  have hg : gNat g j'.val = (g.toFun j').val := gNat_of_le g (Nat.lt_succ_iff.1 j'.isLt)
  omega

/-- **The two adjoints are mutually inverse, second equation.** -/
theorem fineHom_coarseHom (f : Fin k →o Fin l) : fineHom (coarseHom f) = f := by
  refine OrderHom.ext _ _ (funext fun i => Fin.ext ?_)
  show fineNat (coarseHom f) i.val = (f i).val
  have hik := i.isLt
  have hg : ∀ j', gNat (coarseHom f) j' = cvNat f j' := by
    intro j'
    by_cases h : j' ≤ l
    · rw [gNat_of_le _ h]; rfl
    · rw [gNat_of_ge _ (by omega), cvNat_of_ge f (by omega)]
  have key : ∀ j', j' ≤ fineNat (coarseHom f) i.val ↔ j' ≤ fNat f i.val := by
    intro j'
    rw [le_fineNat_iff _ hik, hg, cvNat_le_iff]
    exact ⟨fun h => h.elim (fun hc => absurd hc (by omega)) id, fun h => Or.inr h⟩
  have h1 := (key (fineNat (coarseHom f) i.val)).1 le_rfl
  have h2 := (key (fNat f i.val)).2 le_rfl
  have hf : fNat f i.val = (f i).val := fNat_of_lt f hik
  omega

end Dual

section Coinduce

variable {T S : OpenTruss}

/-- **Source: `proc:coinduced-truss-bordism` (Chapter 2), open case.**  The bordism coinduced
by an admissible regular cofunction.  Rather than re-running the interval construction on the
other side, it is obtained from `induceOpen` through the adjoint `fineHom`, which is the
explicit correspondence `g ↦ f` between the two descriptions. -/
noncomputable def coinduceOpen (g : OpenAdmReg T.numSing S.numSing) :
    Bord1 T.toOneTruss S.toOneTruss := induceOpen (fineHom g)

/-- **`g_{R_g} = g`:** `prop:regular-reconstruction`, first equation. -/
theorem regHom_coinduceOpen (g : OpenAdmReg T.numSing S.numSing) :
    regHom (coinduceOpen g) = g := by
  show regHom (induceOpen (fineHom g)) = g
  rw [regHom_induceOpen, coarseHom_fineHom]

/-- **`R_{g_R} = R`:** `prop:regular-reconstruction`, second equation. -/
theorem coinduceOpen_regHom (R : Bord1 T.toOneTruss S.toOneTruss) :
    coinduceOpen (regHom R) = R := by
  show induceOpen (fineHom (regHom R)) = R
  rw [regHom_eq_coarseHom, fineHom_coarseHom, induceOpen_singHom]

/-- **Source: `prop:regular-reconstruction` (Chapter 2), open case.**  `R ↦ g_R` and
`g ↦ R_g` are mutually inverse. -/
noncomputable def openBordRegEquiv (T S : OpenTruss) :
    Bord1 T.toOneTruss S.toOneTruss ≃ OpenAdmReg T.numSing S.numSing where
  toFun := regHom
  invFun := coinduceOpen
  left_inv := coinduceOpen_regHom
  right_inv := regHom_coinduceOpen

end Coinduce

/-! ### The open simplification of `AdmReg` -/

namespace OpenTruss

/-- The regular index of the lower endpoint is `0`. -/
theorem regIdx_lower (T : OpenTruss) (h : T.toOneTruss.IsRegular T.toOneTruss.lower) :
    T.regIdx rfl ⟨T.toOneTruss.lower, h⟩ = 0 :=
  Fin.ext (show (idx T.toOneTruss.lower).val / 2 = (0 : Fin (T.numSing + 1)).val by simp)

/-- The regular index of the upper endpoint is the last one. -/
theorem regIdx_upper (T : OpenTruss) (h : T.toOneTruss.IsRegular T.toOneTruss.upper) :
    T.regIdx rfl ⟨T.toOneTruss.upper, h⟩ = Fin.last T.numSing := by
  refine Fin.ext ?_
  show (idx T.toOneTruss.upper).val / 2 = (Fin.last T.numSing).val
  rw [idx_upper, Fin.val_last]
  have := T.len_eq
  omega

end OpenTruss

section AdmRegPivot

variable (T S : OpenTruss)

/-- **The open form of `AdmReg`.**  Both endpoints of an open 1-truss are regular, so — in
contrast with `openAdmSingEquiv` — both endpoint laws of `AdmReg` are active, and an
admissible regular cofunction is a monotone `Fin (l+1) →o Fin (k+1)` preserving both ends. -/
def openAdmRegEquiv :
    AdmReg T.toOneTruss S.toOneTruss ≃ OpenAdmReg T.numSing S.numSing where
  toFun A :=
    { toFun :=
        ⟨fun j' => T.regIdx rfl (A.toFun (S.regAt rfl j')),
          fun _ _ h => (T.regIdx_le_iff rfl).2 (A.mono ((S.regAt_le_iff rfl).2 h))⟩
      map_zero := by
        obtain ⟨h', hA⟩ := A.lower_preserving S.isOpen.1
        show T.regIdx rfl (A.toFun (S.regAt rfl (0 : Fin (S.numSing + 1)))) = 0
        rw [show S.regAt rfl (0 : Fin (S.numSing + 1)) = ⟨S.toOneTruss.lower, S.isOpen.1⟩ from
          Reg.ext S.regAt_zero, hA, T.regIdx_lower]
      map_last := by
        obtain ⟨h', hA⟩ := A.upper_preserving S.isOpen.2
        show T.regIdx rfl (A.toFun (S.regAt rfl (Fin.last S.numSing))) = Fin.last T.numSing
        rw [show S.regAt rfl (Fin.last S.numSing) = ⟨S.toOneTruss.upper, S.isOpen.2⟩ from
          Reg.ext S.regAt_last, hA, T.regIdx_upper] }
  invFun g :=
    { toFun := fun r => T.regAt rfl (g.toFun (S.regIdx rfl r))
      mono := fun h => (T.regAt_le_iff rfl).2 (g.toFun.monotone ((S.regIdx_le_iff rfl).2 h))
      lower_preserving := fun h => ⟨T.isOpen.1, by
        show T.regAt rfl (g.toFun (S.regIdx rfl ⟨S.toOneTruss.lower, h⟩)) = _
        rw [S.regIdx_lower, g.map_zero]
        exact Reg.ext T.regAt_zero⟩
      upper_preserving := fun h => ⟨T.isOpen.2, by
        show T.regAt rfl (g.toFun (S.regIdx rfl ⟨S.toOneTruss.upper, h⟩)) = _
        rw [S.regIdx_upper, g.map_last]
        exact Reg.ext T.regAt_last⟩ }
  left_inv A := by
    refine Geometry.AdmReg.ext' (funext fun r => ?_)
    show T.regAt rfl (T.regIdx rfl (A.toFun (S.regAt rfl (S.regIdx rfl r)))) = A.toFun r
    rw [S.regAt_regIdx, T.regAt_regIdx]
  right_inv g := by
    refine OpenAdmReg.ext' (OrderHom.ext _ _ (funext fun j' => ?_))
    show T.regIdx rfl (T.regAt rfl (g.toFun (S.regIdx rfl (S.regAt rfl j')))) = g.toFun j'
    rw [S.regIdx_regAt, T.regIdx_regAt]

end AdmRegPivot

/-! ### T03: injective singular function versus surjective regular cofunction -/

section T03

variable {k l : ℕ}

/-- An injective monotone map of `Fin`s is strictly monotone, in ℕ coordinates. -/
private theorem fNat_strictMono (f : Fin k →o Fin l) (hinj : Function.Injective f)
    {i i' : ℕ} (hlt : i < i') (hi' : i' < k) : fNat f i < fNat f i' := by
  rcases eq_or_lt_of_le (fNat_mono f hlt.le) with heq | h
  · exfalso
    have hi : i < k := lt_trans hlt hi'
    rw [fNat_of_lt f hi, fNat_of_lt f hi'] at heq
    have hii : i = i' := congrArg Fin.val (hinj (Fin.ext heq))
    omega
  · exact h

/-- **Row T03 in coordinates.**  A monotone `f : Fin k →o Fin l` is injective exactly when
its lower adjoint `Fin (l+1) →o Fin (k+1)` is surjective. -/
theorem injective_iff_surjective_coarseHom (f : Fin k →o Fin l) :
    Function.Injective f ↔ Function.Surjective (coarseHom f).toFun := by
  constructor
  · intro hinj j
    have hjk : j.val ≤ k := Nat.lt_succ_iff.1 j.isLt
    rcases Nat.eq_zero_or_pos j.val with h0 | hpos
    · refine ⟨0, Fin.ext ?_⟩
      show cvNat f (0 : Fin (l + 1)).val = j.val
      rw [Fin.val_zero, cvNat_zero, h0]
    · have hj1 : j.val - 1 < k := by omega
      have hlt : fNat f (j.val - 1) < l := fNat_lt f hj1
      refine ⟨⟨fNat f (j.val - 1) + 1, by omega⟩, Fin.ext ?_⟩
      show cvNat f (fNat f (j.val - 1) + 1) = j.val
      have hle : cvNat f (fNat f (j.val - 1) + 1) ≤ j.val := by
        rw [cvNat_le_iff]
        by_cases hk : j.val = k
        · exact Or.inl (by omega)
        · exact Or.inr (by
            have := fNat_strictMono f hinj (show j.val - 1 < j.val by omega) (by omega)
            omega)
      have hge : ¬ (cvNat f (fNat f (j.val - 1) + 1) ≤ j.val - 1) := by
        rw [cvNat_le_iff]
        rintro (h | h) <;> omega
      omega
  · intro hsurj i i' heq
    by_contra hne
    have hvne : i.val ≠ i'.val := fun h => hne (Fin.ext h)
    have key : ∀ {a b : Fin k}, a.val < b.val → (f a).val = (f b).val → False := by
      intro a b hlt hab
      have hn : a.val + 1 < k + 1 := by have := b.isLt; omega
      obtain ⟨j', hj'⟩ := hsurj ⟨a.val + 1, hn⟩
      have hval : cvNat f j'.val = a.val + 1 := congrArg Fin.val hj'
      have h1 : cvNat f j'.val ≤ a.val + 1 := by omega
      have h2 : ¬ (cvNat f j'.val ≤ a.val) := by omega
      rw [cvNat_le_iff] at h1 h2
      obtain ⟨hk, hfa⟩ := not_or.1 h2
      have hb := b.isLt
      have hmono : fNat f (a.val + 1) ≤ fNat f b.val := fNat_mono f (by omega)
      have hfb : fNat f b.val = fNat f a.val := by
        rw [fNat_of_lt f hb, fNat_of_lt f (show a.val < k by omega), ← hab]
      rcases h1 with h | h
      · omega
      · omega
    rcases Nat.lt_or_ge i.val i'.val with h | h
    · exact key h (congrArg Fin.val heq)
    · exact key (show i'.val < i.val by omega) (congrArg Fin.val heq.symm)

variable {T S : OpenTruss}

/-- Injectivity of the singular function is a coordinate-free condition. -/
theorem injective_singHom_iff (R : Bord1 T.toOneTruss S.toOneTruss) :
    Function.Injective (singHom R) ↔ Function.Injective R.singFun := by
  constructor
  · intro h s t hst
    have hs : singHom R (T.singIdx rfl s) = singHom R (T.singIdx rfl t) := by
      show S.singIdx rfl (R.singFun (T.singAt rfl (T.singIdx rfl s))) =
        S.singIdx rfl (R.singFun (T.singAt rfl (T.singIdx rfl t)))
      rw [T.singAt_singIdx, T.singAt_singIdx, hst]
    calc s = T.singAt rfl (T.singIdx rfl s) := (T.singAt_singIdx rfl s).symm
      _ = T.singAt rfl (T.singIdx rfl t) := by rw [h hs]
      _ = t := T.singAt_singIdx rfl t
  · intro h i i' hii
    have h1 : S.singIdx rfl (R.singFun (T.singAt rfl i)) =
        S.singIdx rfl (R.singFun (T.singAt rfl i')) := hii
    have h2 : R.singFun (T.singAt rfl i) = R.singFun (T.singAt rfl i') := by
      calc R.singFun (T.singAt rfl i)
          = S.singAt rfl (S.singIdx rfl (R.singFun (T.singAt rfl i))) :=
            (S.singAt_singIdx rfl _).symm
        _ = S.singAt rfl (S.singIdx rfl (R.singFun (T.singAt rfl i'))) := by rw [h1]
        _ = R.singFun (T.singAt rfl i') := S.singAt_singIdx rfl _
    have h3 := congrArg (T.singIdx rfl) (h h2)
    rwa [T.singIdx_singAt, T.singIdx_singAt] at h3

/-- Surjectivity of the regular cofunction is a coordinate-free condition. -/
theorem surjective_regHom_iff (R : Bord1 T.toOneTruss S.toOneTruss) :
    Function.Surjective (regHom R).toFun ↔ Function.Surjective R.regCofun := by
  constructor
  · intro h r
    obtain ⟨j', hj'⟩ := h (T.regIdx rfl r)
    refine ⟨S.regAt rfl j', ?_⟩
    have hval : T.regIdx rfl (R.regCofun (S.regAt rfl j')) = T.regIdx rfl r := hj'
    calc R.regCofun (S.regAt rfl j')
        = T.regAt rfl (T.regIdx rfl (R.regCofun (S.regAt rfl j'))) :=
          (T.regAt_regIdx rfl _).symm
      _ = T.regAt rfl (T.regIdx rfl r) := by rw [hval]
      _ = r := T.regAt_regIdx rfl r
  · intro h j
    obtain ⟨r, hr⟩ := h (T.regAt rfl j)
    refine ⟨S.regIdx rfl r, ?_⟩
    change T.regIdx rfl (R.regCofun (S.regAt rfl (S.regIdx rfl r))) = j
    rw [S.regAt_regIdx, hr, T.regIdx_regAt]

/-- **Source: `prop:Singular functions and regular cofunctions` (draft chapter §5.3, row
T03), open case.**  A 1-truss bordism between open 1-trusses has an injective singular
function if and only if it has a surjective regular cofunction. -/
theorem injective_singFun_iff_surjective_regCofun (R : Bord1 T.toOneTruss S.toOneTruss) :
    Function.Injective R.singFun ↔ Function.Surjective R.regCofun := by
  rw [← injective_singHom_iff, ← surjective_regHom_iff, regHom_eq_coarseHom,
    injective_iff_surjective_coarseHom]

end T03

end Truss.Transfer
