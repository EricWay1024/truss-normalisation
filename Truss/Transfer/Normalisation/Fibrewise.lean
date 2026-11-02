/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.BundleLabel
import Truss.Transfer.Geometry.OpenBordism
import Truss.Transfer.Geometry.BordismRel
import Truss.Transfer.Normalisation.Retained

/-!
# The fibrewise characterisation of bundle coarsenings (§5.4, row B02)

This module proves the **converse** half of
`prop:fibrewise-characterisation-bundle-coarsenings`: a base-preserving bundle map whose
restriction to every 1-truss fibre is a coarsening *is* a coarsening of bundles.  Together
with `OpenBundle.isCoarsening_fibHom` (the forward half, in
`Truss.Transfer.Normalisation.BundleLabel`) this gives the full characterisation
`OpenBundle.isCoarsening_iff_fibrewise`.

## The shape of the proof

Everything is done in the frame coordinates of `Truss.Transfer.Geometry.OpenBordism` and
`Truss.Transfer.Normalisation.Retained`.  Write `σ = singHom (A.arr h)` for the singular
function of the arrow-fibre bordism of `A` over `h : b ≤ c`, `σ'` for that of `A'`, and
`U = ret q_b`, `V = ret q_c` for the retained sets of the two fibre coarsenings.  Then

* `Bord1.rel x y ↔ loNat σ (idx x) ≤ idx y ≤ hiNat σ (idx x)` (`rel_iff_induce`), and
* `idx (q_b x) = qUIdx U (idx x)` (`OpenTruss.coarsening_idx_eq`),

so every statement below is arithmetic in `ℕ`.

The **compatibility lemma** between `σ`, `σ'` and the retained sets is
`OpenBundle.cnt_cvNat_singHom`:

> `cnt U (cvNat σ t) = cvNat σ' (cnt V t)`  for `t ≤ numSing (A_c)`.

Conceptually it is the *naturality of the regular cofunctions*: `cvNat σ t` is the regular
index of the unique regular cell of `A_b` related to the regular cell `2t` of `A_c`, and
`cnt U` / `cnt V` are the fibre coarsenings read on regular indices.  Its proof is three
lines of geometry (`q.face` applied to the cofunction relation, then uniqueness of the
regular preimage downstairs) plus the coordinate dictionary.

From it, the two substantive clauses follow:

* **exact target lifting for the total map** — `OpenBundle.exists_rel_fibMap_eq`, obtained by
  computing both `(A.arr h)⁻¹(y)` and `(A'.arr h)⁻¹(q_c y)` as explicit frame intervals
  (`le_hiNat_iff`, `loNat_le_iff`) and matching their endpoints through `cnt`, then using the
  discrete intermediate value theorem `exists_eq_of_step_le` for the unit-step map `qUIdx U`;
* **connectivity of the arrow fibres** — `OpenBundle.arrowFibre_connected_of_fibrewise`,
  which follows the chapter's argument verbatim: lifts over a fixed target cell form a
  nonempty frame interval and are joined by source comparisons, and the target is then moved
  along a face zigzag in the point fibre of `q_c`.

## A tempting false simplification

One might hope for the stronger, more symmetric statement that the *interval endpoints*
themselves commute with the fibre coarsenings, i.e. `loNat σ' (qUIdx U n) = qUIdx V (loNat σ n)`
and likewise for `hiNat`; equivalently `q_c (R(x, -)) = R'(q_b x, -)` for every `x`.  **That is
false.**  Take `B = {b < c}`, `A_b = A_c = [3]` with one singular cell each and `σ = id`,
`A'_b` the point (so `U = ∅`) and `A'_c = A_c` (so `V = {0}`).  Then `q` is a bundle map with
both fibre maps coarsenings, but for `n = 1` (the singular cell of `A_b`) the left side is
`loNat σ' 0 = 0` while the right side is `qUIdx V 1 = 1`: the target bordism `R'` out of a
point is total, so it relates the image of `x` to strictly more than the image of `R(x, -)`.
Only the *regular cofunction* direction — `cnt_cvNat_singHom`, equivalently
`q_b (R⁻¹(y)) = R'⁻¹(q_c y)` — survives, and it is what openness actually needs.

## Main results

* `le_hiNat_iff`, `loNat_le_iff` — the two endpoints of the frame interval `R⁻¹(y)`.
* `exists_eq_of_step_le` — a discrete intermediate value theorem.
* `OpenTruss.qUIdx_div_two`, `OpenTruss.qUIdx_succ_div_two`, `OpenTruss.qUIdx_succ_le'` —
  arithmetic of the retained-set coarsening formula.
* `OpenBundle.cnt_cvNat_singHom` — **the compatibility lemma**.
* `OpenBundle.exists_rel_fibMap_eq` — exact target lifting.
* `OpenBundle.arrowFibre_connected_of_fibrewise` — arrow-fibre connectivity.
* `OpenBundle.isCoarsening_of_fibrewise`, `OpenBundle.isCoarsening_iff_fibrewise`.
-/

universe u

namespace Truss.Transfer

open CategoryTheory Geometry Geometry.OneTruss TrussLike

/-! ### The frame interval `R⁻¹(y)`, in ℕ coordinates -/

section Coords

variable {k l : ℕ}

/-- **The upper end of `R⁻¹(y)`.**  A frame coordinate `n` of the source has the frame
coordinate `a` of the target below the top of its interval exactly when `n` lies weakly above
`2·cvNat f (a/2)`.  Since `hiNat f` is constant on `{2j, 2j+1}`, that lower bound is even:
it is the regular cofunction of the regular cell just below `a`. -/
theorem le_hiNat_iff (f : Fin k →o Fin l) {a n : ℕ} (ha : a ≤ 2 * l) (hn : n ≤ 2 * k) :
    a ≤ hiNat f n ↔ 2 * cvNat f (a / 2) ≤ n := by
  rcases eq_or_lt_of_le hn with rfl | hlt
  · have := cvNat_le_k f (a / 2)
    rw [hiNat_of_ge f le_rfl]
    exact ⟨fun _ => by omega, fun _ => ha⟩
  · have hnk : n / 2 < k := by omega
    have hiff := lt_cvNat_iff f (j' := a / 2) (j := n / 2)
    rw [hiNat_of_lt f hlt]
    constructor
    · intro hle
      by_contra hc
      have h1 : n / 2 < cvNat f (a / 2) := by omega
      have := (hiff.1 h1).2
      omega
    · intro hge
      have h1 : ¬ (n / 2 < cvNat f (a / 2)) := by omega
      have h2 : ¬ (fNat f (n / 2) < a / 2) := fun hc => h1 (hiff.2 ⟨hnk, hc⟩)
      omega

/-- **The lower end of `R⁻¹(y)`.**  Dually, `n` has `a` above the bottom of its interval
exactly when `n` lies weakly below `2·cvNat f ((a+1)/2)`; `loNat f` is constant on
`{2j+1, 2j+2}`, so this upper bound is again even. -/
theorem loNat_le_iff (f : Fin k →o Fin l) {a n : ℕ} (hn : n ≤ 2 * k) :
    loNat f n ≤ a ↔ n ≤ 2 * cvNat f ((a + 1) / 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [loNat_zero]
  · have hnk : (n - 1) / 2 < k := by omega
    have hiff := lt_cvNat_iff f (j' := (a + 1) / 2) (j := (n - 1) / 2)
    rw [loNat_of_pos f (by omega)]
    constructor
    · intro hle
      have h1 : (n - 1) / 2 < cvNat f ((a + 1) / 2) := hiff.2 ⟨hnk, by omega⟩
      omega
    · intro hge
      have h1 : (n - 1) / 2 < cvNat f ((a + 1) / 2) := by omega
      have := (hiff.1 h1).2
      omega

end Coords

/-! ### A discrete intermediate value theorem -/

/-- A map of `ℕ` whose steps increase by at most one attains every value between two of its
values.  This is what makes a fibre coarsening surjective onto a frame interval. -/
theorem exists_eq_of_step_le {g : ℕ → ℕ} (hstep : ∀ n, g (n + 1) ≤ g n + 1) {p m : ℕ}
    (h1 : g p ≤ m) : ∀ {r : ℕ}, p ≤ r → m ≤ g r → ∃ n, p ≤ n ∧ n ≤ r ∧ g n = m := by
  intro r hpr
  induction r, hpr using Nat.le_induction with
  | base => intro h2; exact ⟨p, le_rfl, le_rfl, by omega⟩
  | succ r hpr ih =>
      intro h2
      by_cases hmr : m ≤ g r
      · obtain ⟨n, hn1, hn2, hn3⟩ := ih hmr
        exact ⟨n, hn1, by omega, hn3⟩
      · have := hstep r
        exact ⟨r + 1, by omega, le_rfl, by omega⟩

/-! ### Arithmetic of the retained-set coarsening -/

namespace OpenTruss

variable {k : ℕ}

/-- The regular index of the image of a frame coordinate: `q_U` sends the regular cell just
below `n` to the regular cell just below `q_U(n)`. -/
theorem qUIdx_div_two (U : Finset (Fin k)) (a : ℕ) : qUIdx U a / 2 = cnt U (a / 2) := by
  unfold qUIdx
  split <;> omega

/-- The companion of `qUIdx_div_two` for the regular cell just *above* `n`. -/
theorem qUIdx_succ_div_two (U : Finset (Fin k)) (a : ℕ) :
    (qUIdx U a + 1) / 2 = cnt U ((a + 1) / 2) := by
  rcases Nat.even_or_odd a with he | ho
  · have h0 : a % 2 = 0 := Nat.even_iff.1 he
    rw [show (a + 1) / 2 = a / 2 by omega]
    unfold qUIdx
    rw [if_neg (by rintro ⟨hc, -⟩; omega)]
    omega
  · have h1 : a % 2 = 1 := Nat.odd_iff.1 ho
    rw [show (a + 1) / 2 = a / 2 + 1 by omega, cnt_succ]
    unfold qUIdx
    by_cases hm : MemAt U (a / 2)
    · rw [if_pos ⟨h1, hm⟩, if_pos hm]; omega
    · rw [if_neg (fun hc => hm hc.2), if_neg hm]; omega

/-- The index formula of a retained-set coarsening increases by at most one per frame step. -/
theorem qUIdx_succ_le' (U : Finset (Fin k)) (n : ℕ) : qUIdx U (n + 1) ≤ qUIdx U n + 1 := by
  rcases Nat.even_or_odd n with he | ho
  · have h0 : n % 2 = 0 := Nat.even_iff.1 he
    obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j := ⟨n / 2, by omega⟩
    rw [qUIdx_even, qUIdx_odd]
    by_cases hm : MemAt U j <;> simp [hm]
  · have h1 : n % 2 = 1 := Nat.odd_iff.1 ho
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, qUIdx_even, qUIdx_odd, cnt_succ]
    by_cases hm : MemAt U m
    · simp only [if_pos hm]; omega
    · simp only [if_neg hm]; omega

end OpenTruss

/-! ### Preimages of a bordism are frame intervals -/

namespace Geometry.Bord1

variable {T S : OneTruss}

/-- `R⁻¹(y)` is a frame interval, in the non-strict form: it contains every cell whose frame
coordinate lies weakly between the frame coordinates of two of its members. -/
theorem preimage_frameInterval (R : Bord1 T S) {x z x' : T.El} {y : S.El}
    (h₁ : (idx x).val ≤ (idx z).val) (h₂ : (idx z).val ≤ (idx x').val)
    (hx : R.rel x y) (hx' : R.rel x' y) : R.rel z y := by
  rcases eq_or_lt_of_le h₁ with he | hlt₁
  · have hxz : x = z := OneTruss.idx_injective (Fin.ext he)
    rwa [hxz] at hx
  · rcases eq_or_lt_of_le h₂ with he | hlt₂
    · have hzx : z = x' := OneTruss.idx_injective (Fin.ext he)
      rwa [← hzx] at hx'
    · exact R.preimage_frameConvex hlt₁ hlt₂ hx hx'

end Geometry.Bord1

/-! ### Arrows of the total poset that lie over a fixed comparison of the base -/

variable {B : Type u} [PartialOrder B]

/-- The arrow of the total poset determined by a bordism-related pair of fibre cells. -/
def fibArr {A : OpenBundle B} {b c : B} {h : b ≤ c} {x : (A.fib b).toOneTruss.El}
    {y : (A.fib c).toOneTruss.El} (hr : (A.arr h).rel x y) : Arr A.Tot :=
  ⟨⟨b, x⟩, ⟨c, y⟩, ⟨h, hr⟩⟩

@[simp] theorem fibArr_src {A : OpenBundle B} {b c : B} {h : b ≤ c}
    {x : (A.fib b).toOneTruss.El} {y : (A.fib c).toOneTruss.El} (hr : (A.arr h).rel x y) :
    (fibArr hr).src = ⟨b, x⟩ := rfl

@[simp] theorem fibArr_tgt {A : OpenBundle B} {b c : B} {h : b ≤ c}
    {x : (A.fib b).toOneTruss.El} {y : (A.fib c).toOneTruss.El} (hr : (A.arr h).rel x y) :
    (fibArr hr).tgt = ⟨c, y⟩ := rfl

/-- Two such arrows are comparable as soon as their two components are. -/
theorem fibArr_le {A : OpenBundle B} {b c : B} {h : b ≤ c} {x x' : (A.fib b).toOneTruss.El}
    {y y' : (A.fib c).toOneTruss.El} (hr : (A.arr h).rel x y) (hr' : (A.arr h).rel x' y')
    (hx : x ≤ x') (hy : y ≤ y') : fibArr hr ≤ fibArr hr' :=
  ⟨⟨le_rfl, (A.arr_id b x x').2 hx⟩, ⟨le_rfl, (A.arr_id c y y').2 hy⟩⟩

variable [Finite B]

/-- Membership of such an arrow in an arrow fibre of the total map is fibrewise. -/
theorem fibArr_mem {A A' : OpenBundle B} {q : A ⟶ A'} {b c : B} {h : b ≤ c}
    {x : (A.fib b).toOneTruss.El} {y : (A.fib c).toOneTruss.El} (hr : (A.arr h).rel x y)
    {u : (A'.fib b).toOneTruss.El} {v : (A'.fib c).toOneTruss.El}
    (hx : q.fibMap b x = u) (hy : q.fibMap c y = v) :
    fibArr hr ∈ arrowFibre (TrussLike.totMap q) (⟨b, u⟩ : A'.Tot) ⟨c, v⟩ :=
  ⟨congrArg (fun z => (⟨b, z⟩ : A'.Tot)) hx, congrArg (fun z => (⟨c, z⟩ : A'.Tot)) hy⟩

/-! ### The compatibility of `σ`, `σ'` and the two retained sets -/

namespace OpenBundle

omit [Finite B] in
/-- **The heart of the matter: naturality of the regular cofunctions.**

For `h : b ≤ c`, let `σ = singHom (A.arr h)` and `σ' = singHom (A'.arr h)` be the singular
functions of the two arrow-fibre bordisms, and let `U = ret q_b`, `V = ret q_c` be the
retained sets of the two fibre coarsenings.  Then

> `cnt U (cvNat σ t) = cvNat σ' (cnt V t)`.

In words: `cvNat σ t` is the regular index of the unique regular cell of `A_b` related by
`A.arr h` to the regular cell of `A_c` at regular index `t`, and `cnt U` and `cnt V` read the
two fibre coarsenings on regular indices; the identity says the square of regular cofunctions
and fibre coarsenings commutes.  The proof is exactly that: transport the cofunction relation
along `q.face`, observe both endpoints stay regular, and invoke uniqueness of the regular
preimage in `A'`. -/
theorem cnt_cvNat_singHom {A A' : OpenBundle B} (q : A ⟶ A') {b c : B} (h : b ≤ c)
    (hb : IsCoarsening (fibHom q b)) (hc : IsCoarsening (fibHom q c)) {t : ℕ}
    (ht : t ≤ (A.fib c).numSing) :
    OpenTruss.cnt (OpenTruss.ret (fibHom q b)) (cvNat (singHom (A.arr h)) t)
      = cvNat (singHom (A'.arr h)) (OpenTruss.cnt (OpenTruss.ret (fibHom q c)) t) := by
  set σ := singHom (A.arr h) with hσ
  set σ' := singHom (A'.arr h) with hσ'
  set U := OpenTruss.ret (fibHom q b) with hU
  set V := OpenTruss.ret (fibHom q c) with hV
  set j := cvNat σ t with hj
  have hjk : j ≤ (A.fib b).numSing := cvNat_le_k σ t
  -- the two regular cells, chosen by their frame coordinates
  obtain ⟨x, hxidx⟩ : ∃ x : (A.fib b).toOneTruss.El, (idx x).val = 2 * j :=
    ⟨(A.fib b).elAt (by omega), OpenTruss.idx_elAt _ _⟩
  obtain ⟨y, hyidx⟩ : ∃ y : (A.fib c).toOneTruss.El, (idx y).val = 2 * t :=
    ⟨(A.fib c).elAt (by omega), OpenTruss.idx_elAt _ _⟩
  -- upstairs: `x` is the regular cofunction of `y`
  have hrel : (A.arr h).rel x y := by
    rw [rel_iff_induce, hxidx, hyidx, ← hσ]
    exact (even_mem_iff σ hjk ht).2 hj
  -- the images, in coordinates
  have hxq : (idx (q.fibMap b x)).val = 2 * OpenTruss.cnt U j := by
    have hco := OpenTruss.coarsening_idx_eq (T := A.fib b) rfl hb x
    rw [hxidx, OpenTruss.qUIdx_even] at hco
    exact hco
  have hyq : (idx (q.fibMap c y)).val = 2 * OpenTruss.cnt V t := by
    have hco := OpenTruss.coarsening_idx_eq (T := A.fib c) rfl hc y
    rw [hyidx, OpenTruss.qUIdx_even] at hco
    exact hco
  -- downstairs: the image pair is again a cofunction pair
  have hrel' := q.face h hrel
  rw [rel_iff_induce, hxq, hyq, ← hσ'] at hrel'
  have hcardU : (A'.fib b).numSing = U.card := OpenTruss.numSing_eq_card_ret rfl hb
  have hcardV : (A'.fib c).numSing = V.card := OpenTruss.numSing_eq_card_ret rfl hc
  refine (even_mem_iff σ' ?_ ?_).1 hrel'
  · rw [hcardU]; exact OpenTruss.cnt_le_card U j
  · rw [hcardV]; exact OpenTruss.cnt_le_card V t

/-! ### Exact target lifting for the total map -/

omit [Finite B] in
/-- **Source: `prop:fibrewise-characterisation-bundle-coarsenings` (§5.4), openness clause.**
Let `q` be a base-preserving bundle map with all fibre maps coarsenings, `h : b ≤ c`, and let
`u` be a cell of `A'_b` related by the arrow-fibre bordism of `A'` to the image of a cell `y`
of `A_c`.  Then `u` is the image of a cell of `A_b` related by the arrow-fibre bordism of `A`
to `y`; equivalently, `q_b (R⁻¹(y)) = R'⁻¹(q_c y)`.

In coordinates `R⁻¹(y)` is the frame interval `[2·cvNat σ (a/2), 2·cvNat σ ((a+1)/2)]` with
`a = idx y`, and `R'⁻¹(q_c y)` is the corresponding interval for `σ'`; the compatibility
lemma `cnt_cvNat_singHom` identifies the two pairs of endpoints, and the unit-step map
`qUIdx U` then hits every coordinate in between. -/
theorem exists_rel_fibMap_eq {A A' : OpenBundle B} (q : A ⟶ A')
    (hfib : ∀ b : B, IsCoarsening (fibHom q b)) {b c : B} (h : b ≤ c)
    {y : (A.fib c).toOneTruss.El} {u : (A'.fib b).toOneTruss.El}
    (hu : (A'.arr h).rel u (q.fibMap c y)) :
    ∃ x : (A.fib b).toOneTruss.El, (A.arr h).rel x y ∧ q.fibMap b x = u := by
  obtain ⟨σ, hσ⟩ : ∃ f, singHom (A.arr h) = f := ⟨_, rfl⟩
  obtain ⟨σ', hσ'⟩ : ∃ f, singHom (A'.arr h) = f := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ W, OpenTruss.ret (fibHom q b) = W := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ W, OpenTruss.ret (fibHom q c) = W := ⟨_, rfl⟩
  have hal : (idx y).val ≤ 2 * (A.fib c).numSing := (A.fib c).idx_le y
  have hml : (idx u).val ≤ 2 * (A'.fib b).numSing := (A'.fib b).idx_le u
  have hyq : (idx (q.fibMap c y)).val = OpenTruss.qUIdx V (idx y).val := by
    rw [← hV]; exact OpenTruss.coarsening_idx_eq (T := A.fib c) rfl (hfib c) y
  have hal' : OpenTruss.qUIdx V (idx y).val ≤ 2 * (A'.fib c).numSing := by
    rw [← hyq]; exact (A'.fib c).idx_le _
  rw [rel_iff_induce, hσ', hyq] at hu
  -- the two endpoints of the target interval `R'⁻¹(q_c y)`
  have h1 : 2 * cvNat σ' (OpenTruss.qUIdx V (idx y).val / 2) ≤ (idx u).val :=
    (le_hiNat_iff σ' hal' hml).1 hu.2
  have h2 : (idx u).val ≤ 2 * cvNat σ' ((OpenTruss.qUIdx V (idx y).val + 1) / 2) :=
    (loNat_le_iff σ' hml).1 hu.1
  rw [OpenTruss.qUIdx_div_two] at h1
  rw [OpenTruss.qUIdx_succ_div_two] at h2
  -- the compatibility lemma matches them with the images of the endpoints of `R⁻¹(y)`
  have key0 : OpenTruss.cnt U (cvNat σ ((idx y).val / 2))
      = cvNat σ' (OpenTruss.cnt V ((idx y).val / 2)) := by
    rw [← hσ, ← hσ', ← hU, ← hV]
    exact cnt_cvNat_singHom q h (hfib b) (hfib c) (by omega)
  have key1 : OpenTruss.cnt U (cvNat σ (((idx y).val + 1) / 2))
      = cvNat σ' (OpenTruss.cnt V (((idx y).val + 1) / 2)) := by
    rw [← hσ, ← hσ', ← hU, ← hV]
    exact cnt_cvNat_singHom q h (hfib b) (hfib c) (by omega)
  rw [← key0] at h1
  rw [← key1] at h2
  -- interpolate: `qUIdx U` has unit steps, so it attains `idx u` inside `R⁻¹(y)`
  have he0 := OpenTruss.qUIdx_even U (cvNat σ ((idx y).val / 2))
  have he1 := OpenTruss.qUIdx_even U (cvNat σ (((idx y).val + 1) / 2))
  have hmono : 2 * cvNat σ ((idx y).val / 2) ≤ 2 * cvNat σ (((idx y).val + 1) / 2) := by
    have := cvNat_mono σ (show (idx y).val / 2 ≤ ((idx y).val + 1) / 2 by omega)
    omega
  obtain ⟨n, hn0, hn1, hn2⟩ :=
    exists_eq_of_step_le (OpenTruss.qUIdx_succ_le' U)
      (p := 2 * cvNat σ ((idx y).val / 2)) (m := (idx u).val) (by omega) hmono (by omega)
  have hnk : n ≤ 2 * (A.fib b).numSing := by
    have := cvNat_le_k σ (((idx y).val + 1) / 2)
    omega
  refine ⟨(A.fib b).elAt hnk, ?_, ?_⟩
  · rw [rel_iff_induce, hσ, OpenTruss.idx_elAt]
    exact ⟨(loNat_le_iff σ hnk).2 hn1, (le_hiNat_iff σ hal hnk).2 hn0⟩
  · refine (A'.fib b).el_eq_of_idx_eq ?_
    have hco : (idx (q.fibMap b ((A.fib b).elAt hnk))).val = OpenTruss.qUIdx U n := by
      rw [← hU]
      have hc0 := OpenTruss.coarsening_idx_eq (T := A.fib b) rfl (hfib b) ((A.fib b).elAt hnk)
      rw [OpenTruss.idx_elAt] at hc0
      exact hc0
    rw [hco, hn2]

/-! ### Connectivity of the arrow fibres of the total map -/

/-- **Source: §5.4, "these lifts are therefore joined by source comparisons".**  Two lifts of
the *same* target cell are joined inside the arrow fibre by a zigzag of source comparisons:
the set of lifts is an intersection of two frame intervals (the preimage of `y` under the
bordism and the point fibre of `q_b`), so consecutive frame coordinates stay inside it and
are face comparable. -/
theorem zigzagIn_arrowFibre_dist {A A' : OpenBundle B} {q : A ⟶ A'} {b c : B} {h : b ≤ c}
    {u : (A'.fib b).toOneTruss.El} {v : (A'.fib c).toOneTruss.El}
    {y : (A.fib c).toOneTruss.El} (hy : q.fibMap c y = v) :
    ∀ (d : ℕ) {x x' : (A.fib b).toOneTruss.El} (hx : (A.arr h).rel x y)
      (_ : q.fibMap b x = u) (hx' : (A.arr h).rel x' y) (_ : q.fibMap b x' = u),
      (idx x').val = (idx x).val + d →
      ZigzagIn (arrowFibre (TrussLike.totMap q) (⟨b, u⟩ : A'.Tot) ⟨c, v⟩)
        (fibArr hx) (fibArr hx') := by
  intro d
  induction d with
  | zero =>
      intro x x' hx hqx hx' hqx' hd
      have hxx : x = x' := OneTruss.idx_injective (Fin.ext (by omega))
      subst hxx
      exact ZigzagIn.refl _
  | succ d ih =>
      intro x x' hx hqx hx' hqx' hd
      have hub : (idx x').val ≤ (A.fib b).toOneTruss.len := by
        simpa using OneTruss.idx_le_upper x'
      have hlt : (idx x).val < (A.fib b).toOneTruss.len := by omega
      have hzidx : (idx (frameSucc x hlt)).val = (idx x).val + 1 := idx_frameSucc x hlt
      have hzrel : (A.arr h).rel (frameSucc x hlt) y :=
        (A.arr h).preimage_frameInterval (by omega) (by omega) hx hx'
      have hzq : q.fibMap b (frameSucc x hlt) = u :=
        (OpenTruss.pointFibre_interval (fibHom q b) (i := x) (j := frameSucc x hlt) (k := x')
          (by omega) (by omega) (hqx.trans hqx'.symm)).trans hqx
      have hcomp : x ≤ frameSucc x hlt ∨ frameSucc x hlt ≤ x :=
        OneTruss.faceComparable_of_succ _ hzidx
      have hstep : ZigzagIn (arrowFibre (TrussLike.totMap q) (⟨b, u⟩ : A'.Tot) ⟨c, v⟩)
          (fibArr hx) (fibArr hzrel) := by
        rcases hcomp with hcx | hcx
        · exact ZigzagIn.of_le (fibArr_mem hx hqx hy) (fibArr_mem hzrel hzq hy)
            (fibArr_le hx hzrel hcx le_rfl)
        · exact ZigzagIn.of_ge (fibArr_mem hx hqx hy) (fibArr_mem hzrel hzq hy)
            (fibArr_le hzrel hx hcx le_rfl)
      exact hstep.trans (ih hzrel hzq hx' hqx' (by omega))

/-- The symmetric form of `zigzagIn_arrowFibre_dist`. -/
theorem zigzagIn_arrowFibre_sameTarget {A A' : OpenBundle B} {q : A ⟶ A'} {b c : B} {h : b ≤ c}
    {u : (A'.fib b).toOneTruss.El} {v : (A'.fib c).toOneTruss.El}
    {y : (A.fib c).toOneTruss.El} (hy : q.fibMap c y = v) {x x' : (A.fib b).toOneTruss.El}
    (hx : (A.arr h).rel x y) (hqx : q.fibMap b x = u) (hx' : (A.arr h).rel x' y)
    (hqx' : q.fibMap b x' = u) :
    ZigzagIn (arrowFibre (TrussLike.totMap q) (⟨b, u⟩ : A'.Tot) ⟨c, v⟩)
      (fibArr hx) (fibArr hx') := by
  rcases Nat.le_total (idx x).val (idx x').val with hle | hle
  · exact zigzagIn_arrowFibre_dist hy ((idx x').val - (idx x).val) hx hqx hx' hqx' (by omega)
  · exact (zigzagIn_arrowFibre_dist hy ((idx x).val - (idx x').val) hx' hqx' hx hqx
      (by omega)).symm

/-- **Source: `prop:fibrewise-characterisation-bundle-coarsenings` (§5.4), connectivity
clause.**  The arrow fibres of the total map of a fibrewise coarsening are zigzag connected.
The target is moved along a face zigzag in the point fibre `J = q_c⁻¹(v)`, which is available
because `q_c` is a coarsening; over each target cell the lifts are nonempty (exact target
lifting) and joined by source comparisons. -/
theorem arrowFibre_connected_of_fibrewise {A A' : OpenBundle B} (q : A ⟶ A')
    (hfib : ∀ b : B, IsCoarsening (fibHom q b)) (P P' : A'.Tot) (hPP' : P ≤ P') :
    IsZigzagConnected (arrowFibre (TrussLike.totMap q) P P') := by
  obtain ⟨b, u⟩ := P
  obtain ⟨c, v⟩ := P'
  obtain ⟨h, huv⟩ := hPP'
  -- exact target lifting, in the form needed below
  have lift : ∀ y : (A.fib c).toOneTruss.El, q.fibMap c y = v →
      ∃ x : (A.fib b).toOneTruss.El, (A.arr h).rel x y ∧ q.fibMap b x = u := by
    intro y hy
    refine exists_rel_fibMap_eq q hfib h ?_
    rw [hy]; exact huv
  rintro ⟨⟨b₁, x₁⟩, ⟨c₁, y₁⟩, hle₁⟩ hα ⟨⟨b₂, x₂⟩, ⟨c₂, y₂⟩, hle₂⟩ hβ
  have hb₁ : b = b₁ := congrArg (fun t : A'.Tot => t.1) hα.1.symm
  subst hb₁
  have hc₁ : c = c₁ := congrArg (fun t : A'.Tot => t.1) hα.2.symm
  subst hc₁
  have hb₂ : b = b₂ := congrArg (fun t : A'.Tot => t.1) hβ.1.symm
  subst hb₂
  have hc₂ : c = c₂ := congrArg (fun t : A'.Tot => t.1) hβ.2.symm
  subst hc₂
  have hq₁ : q.fibMap b x₁ = u := tot_mk_inj hα.1
  have hq₂ : q.fibMap b x₂ = u := tot_mk_inj hβ.1
  have hy₁ : q.fibMap c y₁ = v := tot_mk_inj hα.2
  have hy₂ : q.fibMap c y₂ = v := tot_mk_inj hβ.2
  have hrel₁ : (A.arr h).rel x₁ y₁ := by obtain ⟨h', hr'⟩ := hle₁; exact hr'
  have hrel₂ : (A.arr h).rel x₂ y₂ := by obtain ⟨h', hr'⟩ := hle₂; exact hr'
  change ZigzagIn (arrowFibre (TrussLike.totMap q) (⟨b, u⟩ : A'.Tot) ⟨c, v⟩)
    (fibArr hrel₁) (fibArr hrel₂)
  have key : ∀ y : (A.fib c).toOneTruss.El,
      ZigzagIn (pointFibre (TrussLike.totMap (fibHom q c)) v) y₁ y →
      ∀ (x : (A.fib b).toOneTruss.El) (hx : (A.arr h).rel x y), q.fibMap b x = u →
        ZigzagIn (arrowFibre (TrussLike.totMap q) (⟨b, u⟩ : A'.Tot) ⟨c, v⟩)
          (fibArr hrel₁) (fibArr hx) := by
    intro y hzy
    induction hzy with
    | refl =>
        intro x hx hqx
        exact zigzagIn_arrowFibre_sameTarget hy₁ hrel₁ hq₁ hx hqx
    | tail hprev hstep ih =>
        intro x hx hqx
        rcases hstep.2.2 with hc | hc
        · obtain ⟨x', hx'rel, hx'q⟩ := lift _ hstep.1
          have hx'' := (A.arr h).image_upClosed hx'rel hc
          refine (ih x' hx'rel hx'q).trans ?_
          refine (ZigzagIn.of_le (fibArr_mem hx'rel hx'q hstep.1)
            (fibArr_mem hx'' hx'q hstep.2.1) (fibArr_le hx'rel hx'' le_rfl hc)).trans ?_
          exact zigzagIn_arrowFibre_sameTarget hstep.2.1 hx'' hx'q hx hqx
        · have hxy' := (A.arr h).image_upClosed hx hc
          refine (ih x hxy' hqx).trans ?_
          exact ZigzagIn.of_ge (fibArr_mem hxy' hqx hstep.1) (fibArr_mem hx hqx hstep.2.1)
            (fibArr_le hx hxy' le_rfl hc)
  exact key y₂ (OpenTruss.pointFibre_zigzag (fibHom q c) v hy₁ hy₂) x₂ hrel₂ hq₂

/-! ### The characterisation -/

/-- **Source: `prop:fibrewise-characterisation-bundle-coarsenings` (§5.4), converse half
(row `B02`).**  A base-preserving bundle map of fibrewise-open 1-truss bundles whose
restriction to every 1-truss fibre is a coarsening is a coarsening of bundles.

Object-surjectivity and the dimension inequality are immediate, being fibrewise.  Exact
target lifting for the total map is `exists_rel_fibMap_eq` and connectivity of its arrow
fibres is `arrowFibre_connected_of_fibrewise`; both rest on the compatibility lemma
`cnt_cvNat_singHom`. -/
theorem isCoarsening_of_fibrewise {A A' : OpenBundle B} (q : A ⟶ A')
    (hfib : ∀ b : B, IsCoarsening (fibHom q b)) : IsCoarsening q where
  tot :=
    { surjective := by
        rintro ⟨b, w⟩
        obtain ⟨x, hx⟩ := ((isCoarsening_iff_surjective_regular (fibHom q b)).1 (hfib b)).1 w
        exact ⟨⟨b, x⟩, congrArg (fun z => (⟨b, z⟩ : A'.Tot)) hx⟩
      isOpen := by
        rw [isOpenPosetMap_iff_exists_le (TrussLike.totMap q).monotone]
        rintro ⟨c, y⟩ ⟨b, w⟩ ⟨h, hrel⟩
        obtain ⟨x, hx, hqx⟩ := exists_rel_fibMap_eq q hfib h hrel
        exact ⟨⟨b, x⟩, ⟨h, hx⟩, congrArg (fun z => (⟨b, z⟩ : A'.Tot)) hqx⟩
      arrowFibre_connected := fun P P' hPP' =>
        arrowFibre_connected_of_fibrewise q hfib P P' hPP' }
  dimsig_le := fun p i => (hfib p.1).dimsig_le p.2 i

/-- **Source: `prop:fibrewise-characterisation-bundle-coarsenings` (§5.4), row `B02`.**
*A coarsening in `K` is exactly a base-preserving bundle map whose restriction to every
1-truss fibre is a coarsening.*  The forward half is `isCoarsening_fibHom`. -/
theorem isCoarsening_iff_fibrewise {A A' : OpenBundle B} (q : A ⟶ A') :
    IsCoarsening q ↔ ∀ b : B, IsCoarsening (fibHom q b) :=
  ⟨fun hq b => isCoarsening_fibHom hq b, isCoarsening_of_fibrewise q⟩

end OpenBundle

end Truss.Transfer
