/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.BundleFibre
import Truss.Transfer.Geometry.OpenBordism
import Truss.Transfer.Normalisation.Retained

/-!
# The bundle quotient of a forward-stable singular family (§5.4, row B04)

The draft chapter's construction, just after `def:Forward-stable singular family`:

> *"Given a forward-stable family `U`, construct a coarsening `q_U : A → A'` by setting
> `(q_U)_b : A_b → A'_b` as the coarsening `q_(U_b)` given by
> `cons:retained-set-coarsening-1-truss`.  Forward stability guarantees that `q_U` is a
> well-defined coarsening."*

The saved review asked for the two things that sentence leaves implicit: an explicit
description of the *coarse* singular functions as restrictions `σ_(b,c)|_(U_b) : U_b → U_c`,
and a **proof** — not a hypothesis, not a structure field — that these restrictions preserve
identities and composition and that the fibrewise coarsenings assemble into a bundle map.
This module does exactly that.

## Main definitions

* `OpenBundle.IsForwardStableFam` — forward stability of a `Finset`-valued singular family,
  with `OpenBundle.isForwardStableFam_iff` the bridge to `StableFamily`'s `Set`-valued
  `Transport.IsForwardStable` (stated as an `Iff`, so both directions are available).
* `OpenTruss.nthNat` — the inverse of the counting function `cnt`: the `p`-th element of a
  `Finset (Fin k)`, in frame coordinates.  This is the monotone enumeration of `U_b` that the
  construction needs; it is built from `cnt` by `Nat.find` rather than from Mathlib's
  `Finset.orderEmbOfFin`, because every later step is an inequality between counts.
* `OpenBundle.restrictSigma` — the restriction `σ_(b,c)|_(U_b) : Fin |U_b| →o Fin |U_c|`,
  well defined exactly by forward stability.
* `OpenBundle.quotient` — the coarse bundle `A'`, with `A'_b = ofNumSing |U_b|` and arrow
  fibres the bordisms induced by the restricted singular functions.
* `OpenBundle.quotientMap` — the bundle map `q_U : A → A'`, fibrewise `q_(U_b)`.

## Main results

* `OpenBundle.restrictSigma_id`, `OpenBundle.restrictSigma_comp` — **preservation of
  identities and composition**, the first half of the review's request.  They are what make
  `quotient` a functor, i.e. a bundle at all.
* `OpenTruss.cnt_fNat_of_mem` — **the heart of the construction**: the enumerations of `U_b`
  and `U_c` intertwine `σ` with its restriction,
  `restrictSigma (cnt_(U_b) i) = cnt_(U_c) (σ i)` for `i ∈ U_b`.
* `OpenTruss.qUIdx_rel` — the resulting frame-coordinate compatibility, which is exactly the
  `face` field of the bundle map: the fibrewise retained-set coarsenings carry the interval
  `[lo_σ, hi_σ]` of an arrow fibre into the interval `[lo_(σ|U), hi_(σ|U)]` of the coarse one.
* `OpenBundle.ret_quotientMap` — `ret(q_U) = U`, fibrewise `ret_qU`.
* `OpenBundle.isCoarsening_fibMap_quotientMap` — every fibre map of `q_U` is a coarsening.

## Not proved here

`IsCoarsening (A.quotientMap U hU)` as a **bundle** coarsening is *not* proved: it needs the
converse half of `prop:fibrewise-characterisation-bundle-coarsenings` (fibrewise coarsenings
assemble to a bundle coarsening), which is a separate obligation.  Everything below stops at
the fibrewise statement.
-/

universe u

namespace Truss.Transfer

open CategoryTheory Geometry Geometry.OneTruss

namespace OpenTruss

/-! ### The inverse of the counting function

`cnt U j` counts the elements of `U` strictly below `j`.  Restricted to `U` it is a bijection
onto `Fin |U|` (`cnt_val_inj` gives injectivity); `nthNat U p` is the inverse, obtained as the
least frame position at which the count first exceeds `p`. -/

variable {k : ℕ}

/-- The search used to define `nthNat` always succeeds: `k` itself is a witness. -/
theorem nthNat_ex (V : Finset (Fin k)) (p : ℕ) : ∃ m : ℕ, p < cnt V (m + 1) ∨ k ≤ m :=
  ⟨k, Or.inr le_rfl⟩

/-- **The `p`-th element of `V`, in frame coordinates.**  The least `m` at which the count of
`V` first exceeds `p`; for `p < |V|` this is the unique `m ∈ V` with `cnt V m = p`. -/
def nthNat (V : Finset (Fin k)) (p : ℕ) : ℕ := Nat.find (nthNat_ex V p)

/-- **The defining property of `nthNat`.**  Below `|V|` the enumeration lands in `V` and
inverts the counting function. -/
theorem nthNat_spec (V : Finset (Fin k)) {p : ℕ} (hp : p < V.card) :
    MemAt V (nthNat V p) ∧ cnt V (nthNat V p) = p := by
  have hspec : p < cnt V (nthNat V p + 1) ∨ k ≤ nthNat V p := Nat.find_spec (nthNat_ex V p)
  have hmin : ∀ j : ℕ, j < nthNat V p → ¬ (p < cnt V (j + 1) ∨ k ≤ j) := fun j hj =>
    Nat.find_min (nthNat_ex V p) hj
  have hlow : cnt V (nthNat V p) ≤ p := by
    rcases Nat.eq_zero_or_pos (nthNat V p) with h0 | hpos
    · rw [h0, cnt_zero]; exact Nat.zero_le p
    · by_contra hcon
      exact hmin (nthNat V p - 1) (by omega)
        (Or.inl (by rw [show nthNat V p - 1 + 1 = nthNat V p by omega]; omega))
  have hhigh : p < cnt V (nthNat V p + 1) := by
    rcases hspec with h | h
    · exact h
    · rw [cnt_of_card_le V (by omega)]; exact hp
  rw [cnt_succ] at hhigh
  by_cases hmem : MemAt V (nthNat V p)
  · rw [if_pos hmem] at hhigh
    exact ⟨hmem, by omega⟩
  · rw [if_neg hmem] at hhigh
    omega

/-- The `p`-th element of `V` really is an element of `V`. -/
theorem memAt_nthNat (V : Finset (Fin k)) {p : ℕ} (hp : p < V.card) : MemAt V (nthNat V p) :=
  (nthNat_spec V hp).1

/-- The counting function inverts the enumeration. -/
theorem cnt_nthNat (V : Finset (Fin k)) {p : ℕ} (hp : p < V.card) :
    cnt V (nthNat V p) = p := (nthNat_spec V hp).2

/-- The `p`-th element of `V` is a legitimate index. -/
theorem nthNat_lt (V : Finset (Fin k)) {p : ℕ} (hp : p < V.card) : nthNat V p < k :=
  lt_of_memAt (memAt_nthNat V hp)

/-- The enumeration inverts the counting function on `V`. -/
theorem nthNat_cnt {V : Finset (Fin k)} {m : ℕ} (hm : MemAt V m) : nthNat V (cnt V m) = m := by
  have hp : cnt V m < V.card := cnt_lt_card_of_memAt hm
  obtain ⟨hmem, hcnt⟩ := nthNat_spec V hp
  rcases lt_trichotomy (nthNat V (cnt V m)) m with h | h | h
  · exact absurd hcnt (Nat.ne_of_lt (cnt_lt_cnt_of_memAt hmem h))
  · exact h
  · exact absurd hcnt.symm (Nat.ne_of_lt (cnt_lt_cnt_of_memAt hm h))

/-- The enumeration is monotone. -/
theorem nthNat_mono (V : Finset (Fin k)) : Monotone (nthNat V) := fun _ _ hpq =>
  Nat.find_mono fun _ hm => hm.imp (fun h => lt_of_le_of_lt hpq h) id

/-- If the count at `m` does not exceed `p`, the `p`-th element of `V` is at least `m`. -/
theorem le_nthNat {V : Finset (Fin k)} {m p : ℕ} (hp : p < V.card) (h : cnt V m ≤ p) :
    m ≤ nthNat V p := by
  by_contra hcon
  have hlt := cnt_lt_cnt_of_memAt (memAt_nthNat V hp) (Nat.not_le.1 hcon)
  rw [cnt_nthNat V hp] at hlt
  omega

/-- If `p` is below the count at `m + 1`, the `p`-th element of `V` is at most `m`. -/
theorem nthNat_le_of_lt_cnt {V : Finset (Fin k)} {m p : ℕ} (h : p < cnt V (m + 1)) :
    p < V.card ∧ nthNat V p ≤ m := by
  have hp : p < V.card := lt_of_lt_of_le h (cnt_le_card V (m + 1))
  refine ⟨hp, ?_⟩
  by_contra hcon
  have hle : cnt V (m + 1) ≤ cnt V (nthNat V p) := cnt_mono V (by omega)
  rw [cnt_nthNat V hp] at hle
  omega

/-! ### Two arithmetic identities for `qUIdx` -/

/-- Halving the retained-set index formula returns the count. -/
theorem qUIdx_div_two (V : Finset (Fin k)) (a : ℕ) : qUIdx V a / 2 = cnt V (a / 2) := by
  unfold qUIdx
  split <;> omega

/-- Past the carrier of `T` the retained-set index formula is constant at the upper
endpoint of `S_V`. -/
theorem qUIdx_of_ge (V : Finset (Fin k)) {a : ℕ} (h : 2 * k ≤ a) : qUIdx V a = 2 * V.card := by
  have h1 : cnt V (a / 2) = V.card := cnt_of_card_le V (by omega)
  have h2 : ¬ MemAt V (a / 2) := fun hm => absurd (lt_of_memAt hm) (by omega)
  unfold qUIdx
  rw [if_neg (fun hc => h2 hc.2), h1, Nat.add_zero]

/-! ### The coarse singular function, in the abstract

The whole of §5.4's construction is the following piece of arithmetic.  `f` is the singular
function of an arrow fibre, `V ⊆ Fin kb` and `W ⊆ Fin kc` the retained families over the two
base points, `f V ⊆ W` is forward stability, and `g` is *any* monotone map that computes the
transported counts — for the bundle quotient it is `restrictSigma`. -/

section Face

variable {kb kc kb' kc' : ℕ} {f : Fin kb →o Fin kc} {g : Fin kb' →o Fin kc'}
  {V : Finset (Fin kb)} {W : Finset (Fin kc)}

/-- **The key identity of the construction.**  On elements of `V` the enumeration of `W`
intertwines `f` with `g`: the count of `W` below `f i` is the value of `g` at the count of
`V` below `i`.  (Off `V` this fails — `g` is only defined on the retained indices — and the
two inequalities below are what survive.) -/
theorem cnt_fNat_of_mem (hg : ∀ p : ℕ, p < V.card → fNat g p = cnt W (fNat f (nthNat V p)))
    {i : Fin kb} (hi : i ∈ V) : fNat g (cnt V i.val) = cnt W (fNat f i.val) := by
  have hmem : MemAt V i.val := (memAt_val V i).2 hi
  rw [hg _ (cnt_lt_card_of_memAt hmem), nthNat_cnt hmem]

/-- **The one-sided comparison off `V`.**  Transporting first and counting afterwards can
only lose elements: `g` is evaluated at a count that is at least the count at `m`. -/
theorem cnt_fNat_le (hb : kb' = V.card) (hc : kc' = W.card)
    (hg : ∀ p : ℕ, p < V.card → fNat g p = cnt W (fNat f (nthNat V p)))
    {m p : ℕ} (hmp : cnt V m ≤ p) : cnt W (fNat f m) ≤ fNat g p := by
  by_cases hp : p < V.card
  · rw [hg _ hp]
    exact cnt_mono W (fNat_mono f (le_nthNat hp hmp))
  · rw [fNat_of_ge g (by omega), hc]
    exact cnt_le_card W _

/-- **The comparison at a singular coarse cell.**  If `p` is below the count at `m + 1` then
the coarse singular cell `2·g(p)+1` is at most the image of the singular cell `2·f(m)+1`.
This is the inequality the *lower* endpoint of an arrow-fibre interval needs. -/
theorem qUIdx_odd_bound (hstab : ∀ i ∈ V, f i ∈ W)
    (hg : ∀ p : ℕ, p < V.card → fNat g p = cnt W (fNat f (nthNat V p)))
    {m p : ℕ} (hp : p < cnt V (m + 1)) :
    2 * fNat g p + 1 ≤ qUIdx W (2 * fNat f m + 1) := by
  obtain ⟨hpc, hle⟩ := nthNat_le_of_lt_cnt hp
  obtain ⟨i, hiV, hiv⟩ := memAt_nthNat V hpc
  have hu : fNat f (nthNat V p) = (f i).val := by rw [← hiv, fNat_of_lt f i.isLt]
  have huW : MemAt W (fNat f (nthNat V p)) := ⟨f i, hstab i hiV, hu.symm⟩
  have hut : fNat f (nthNat V p) ≤ fNat f m := fNat_mono f hle
  rw [hg _ hpc, qUIdx_odd]
  rcases eq_or_lt_of_le hut with heq | hlt
  · rw [heq] at huW ⊢
    rw [if_pos huW]
  · have hcc := cnt_lt_cnt_of_memAt huW hlt
    by_cases hW : MemAt W (fNat f m)
    · rw [if_pos hW]; omega
    · rw [if_neg hW]; omega

/-- **The frame-coordinate compatibility of the fibrewise retained-set coarsenings.**
If `a'` lies in the interval `J_f(a)` of the arrow-fibre bordism induced by `f`, then the
image of `a'` under `q_W` lies in the interval `J_g` of the image of `a` under `q_V`.  This
is precisely the `face` clause of the bundle map `q_U`. -/
theorem qUIdx_rel (hb : kb' = V.card) (hc : kc' = W.card) (hstab : ∀ i ∈ V, f i ∈ W)
    (hg : ∀ p : ℕ, p < V.card → fNat g p = cnt W (fNat f (nthNat V p)))
    {a a' : ℕ} (hlo : loNat f a ≤ a') (hhi : a' ≤ hiNat f a) :
    loNat g (qUIdx V a) ≤ qUIdx W a' ∧ qUIdx W a' ≤ hiNat g (qUIdx V a) := by
  constructor
  · by_cases hA : qUIdx V a = 0
    · rw [hA, loNat_zero]
      exact Nat.zero_le _
    · have ha : a ≠ 0 := by rintro rfl; exact hA (qUIdx_zero V)
      rw [loNat_of_pos g hA]
      have hstep : qUIdx W (2 * fNat f ((a - 1) / 2) + 1) ≤ qUIdx W a' := by
        rw [← loNat_of_pos f ha]
        exact qUIdx_mono W hlo
      refine le_trans (qUIdx_odd_bound hstab hg ?_) hstep
      rcases Nat.even_or_odd a with he | ho
      · have hn : a % 2 = 0 := Nat.even_iff.1 he
        obtain ⟨j, rfl⟩ : ∃ j, a = 2 * j := ⟨a / 2, by omega⟩
        rw [qUIdx_even] at hA ⊢
        have hcj : cnt V j ≠ 0 := by omega
        have hj : j ≠ 0 := by rintro rfl; exact hcj (cnt_zero V)
        rw [show (2 * j - 1) / 2 + 1 = j by omega]
        omega
      · have hn : a % 2 = 1 := Nat.odd_iff.1 ho
        obtain ⟨t, rfl⟩ : ∃ t, a = 2 * t + 1 := ⟨a / 2, by omega⟩
        rw [qUIdx_odd] at hA
        rw [show (2 * t + 1 - 1) / 2 = t by omega, qUIdx_odd, cnt_succ]
        by_cases hm : MemAt V t
        · rw [if_pos hm] at hA ⊢
          omega
        · rw [if_neg hm] at hA ⊢
          omega
  · by_cases hAge : 2 * kb' ≤ qUIdx V a
    · rw [hiNat_of_ge g hAge, hc]
      exact qUIdx_le W a'
    · rw [hiNat_of_lt g (Nat.not_le.1 hAge)]
      refine le_trans (qUIdx_mono W hhi) ?_
      by_cases hage : 2 * kb ≤ a
      · exfalso
        rw [qUIdx_of_ge V hage] at hAge
        omega
      · rw [hiNat_of_lt f (Nat.not_le.1 hage), qUIdx_odd, qUIdx_div_two]
        have key : cnt W (fNat f (a / 2)) ≤ fNat g (cnt V (a / 2)) :=
          cnt_fNat_le hb hc hg le_rfl
        by_cases hm : MemAt W (fNat f (a / 2))
        · rw [if_pos hm]; omega
        · rw [if_neg hm]; omega

end Face

end OpenTruss

/-! ### Forward-stable families of a bundle -/

variable {B : Type u} [PartialOrder B]

namespace OpenBundle

/-- **Source: `def:Forward-stable singular family` (§5.4), `Finset` form.**  A family of
subsets of the singular cells of the fibres, stable under the singular functions. -/
def IsForwardStableFam (A : OpenBundle B) (U : ∀ b : B, Finset (Fin (A.fib b).numSing)) :
    Prop := ∀ ⦃b c : B⦄ (h : b ≤ c), ∀ i ∈ U b, A.sigma h i ∈ U c

/-- **The bridge to `StableFamily`.**  The `Finset` form of forward stability is the
`Set`-valued `Transport.IsForwardStable` of `A.singTransport`, applied to the coercion of the
family.  Stated as an `Iff`, so both directions are available: `retFam_isForwardStable` lands
on the right-hand side, the construction below uses the left. -/
theorem isForwardStableFam_iff (A : OpenBundle B)
    (U : ∀ b : B, Finset (Fin (A.fib b).numSing)) :
    A.IsForwardStableFam U ↔
      A.singTransport.IsForwardStable (fun b => (↑(U b) : Set (Fin (A.fib b).numSing))) := by
  rw [Transport.isForwardStable_iff]
  constructor
  · intro h b c hbc i hi
    exact Finset.mem_coe.2 (h hbc i (Finset.mem_coe.1 hi))
  · intro h b c hbc i hi
    exact Finset.mem_coe.1 (h hbc i (Finset.mem_coe.2 hi))

/-- The singular function of an arrow fibre, as a monotone map of singular indices. -/
noncomputable def sigmaHom (A : OpenBundle B) {b c : B} (h : b ≤ c) :
    Fin (A.fib b).numSing →o Fin (A.fib c).numSing := singHom (A.arr h)

@[simp] theorem sigmaHom_apply (A : OpenBundle B) {b c : B} (h : b ≤ c)
    (i : Fin (A.fib b).numSing) : A.sigmaHom h i = A.sigma h i := rfl

section Restrict

variable {A : OpenBundle B} {U : ∀ b : B, Finset (Fin (A.fib b).numSing)}
  (hU : A.IsForwardStableFam U)

/-- The `p`-th retained singular cell of the fibre over `b`. -/
def stableIdx (b : B) (p : Fin (U b).card) : Fin (A.fib b).numSing :=
  ⟨OpenTruss.nthNat (U b) p.val, OpenTruss.nthNat_lt _ p.isLt⟩

/-- The enumeration lands in `U b`. -/
theorem mem_stableIdx (b : B) (p : Fin (U b).card) : stableIdx b p ∈ U b :=
  (OpenTruss.memAt_val (U b) _).1 (OpenTruss.memAt_nthNat (U b) p.isLt)

/-- The enumeration inverts the counting function. -/
theorem cnt_stableIdx (b : B) (p : Fin (U b).card) :
    OpenTruss.cnt (U b) (stableIdx b p).val = p.val := OpenTruss.cnt_nthNat _ p.isLt

/-- The counting function inverts the enumeration on `U b`. -/
theorem stableIdx_of_mem {b : B} {i : Fin (A.fib b).numSing} (hi : i ∈ U b)
    {p : Fin (U b).card} (hp : p.val = OpenTruss.cnt (U b) i.val) : stableIdx b p = i :=
  Fin.ext (by
    change OpenTruss.nthNat (U b) p.val = i.val
    rw [hp, OpenTruss.nthNat_cnt ((OpenTruss.memAt_val _ _).2 hi)])

/-- **Source: §5.4, the construction after `def:Forward-stable singular family`.**
The restricted singular function `σ_(b,c)|_(U_b) : U_b → U_c`, in the counting coordinates of
the two retained families.  **Forward stability is exactly what makes it well defined**: it is
what places `σ_(b,c)(i)` in `U_c`, so that its count is below `|U_c|`. -/
noncomputable def restrictSigma {b c : B} (h : b ≤ c) : Fin (U b).card →o Fin (U c).card where
  toFun p := ⟨OpenTruss.cnt (U c) (A.sigma h (stableIdx b p)).val,
    OpenTruss.cnt_lt_card_of_memAt
      ((OpenTruss.memAt_val _ _).2 (hU h _ (mem_stableIdx b p)))⟩
  monotone' p q hpq := by
    refine OpenTruss.cnt_mono (U c) ?_
    refine (A.sigmaHom h).monotone ?_
    exact OpenTruss.nthNat_mono (U b) hpq

@[simp] theorem restrictSigma_val {b c : B} (h : b ≤ c) (p : Fin (U b).card) :
    (restrictSigma hU h p).val = OpenTruss.cnt (U c) (A.sigma h (stableIdx b p)).val := rfl

/-- **Preservation of identities.**  The restriction of the identity singular function is the
identity: the two enumerations of `U b` are inverse to the same counting function. -/
theorem restrictSigma_id (b : B) : restrictSigma hU (le_refl b) = OrderHom.id := by
  refine OrderHom.ext _ _ (funext fun p => Fin.ext ?_)
  rw [restrictSigma_val, A.sigma_id, cnt_stableIdx]
  rfl

/-- The enumeration of `U c` recovers the transported cell. -/
theorem stableIdx_restrictSigma {b c : B} (h : b ≤ c) (p : Fin (U b).card) :
    stableIdx c (restrictSigma hU h p) = A.sigma h (stableIdx b p) :=
  stableIdx_of_mem (hU h _ (mem_stableIdx b p)) rfl

/-- **Preservation of composition**, pointwise. -/
theorem restrictSigma_comp_apply {b c d : B} (h₁ : b ≤ c) (h₂ : c ≤ d) (p : Fin (U b).card) :
    restrictSigma hU h₂ (restrictSigma hU h₁ p) = restrictSigma hU (h₁.trans h₂) p := by
  refine Fin.ext ?_
  rw [restrictSigma_val, restrictSigma_val, stableIdx_restrictSigma, A.sigma_comp]

/-- **Preservation of composition.**  The restriction of a composite singular function is the
composite of the restrictions. -/
theorem restrictSigma_comp {b c d : B} (h₁ : b ≤ c) (h₂ : c ≤ d) :
    (restrictSigma hU h₂).comp (restrictSigma hU h₁) = restrictSigma hU (h₁.trans h₂) :=
  OrderHom.ext _ _ (funext fun p => restrictSigma_comp_apply hU h₁ h₂ p)

/-! ### Transporting the restriction to the coarse fibres -/

/-- Reindexing `Fin` along an equality of naturals, monotonically. -/
def finCastHom {m n : ℕ} (h : m = n) : Fin m →o Fin n where
  toFun := Fin.cast h
  monotone' _ _ hij := hij

/-- The restricted singular function, read in the singular indices of the coarse fibres
`ofNumSing |U_b|`.  The only difference from `restrictSigma` is the identification
`(ofNumSing k).numSing = k`, which is a propositional equality of naturals. -/
noncomputable def quotientHom {b c : B} (h : b ≤ c) :
    Fin (OpenTruss.ofNumSing (U b).card).numSing →o
      Fin (OpenTruss.ofNumSing (U c).card).numSing :=
  (finCastHom (OpenTruss.numSing_ofNumSing (U c).card).symm).comp
    ((restrictSigma hU h).comp (finCastHom (OpenTruss.numSing_ofNumSing (U b).card)))

@[simp] theorem quotientHom_val {b c : B} (h : b ≤ c)
    (p : Fin (OpenTruss.ofNumSing (U b).card).numSing) :
    (quotientHom hU h p).val =
      (restrictSigma hU h (Fin.cast (OpenTruss.numSing_ofNumSing (U b).card) p)).val := rfl

/-- `quotientHom` preserves identities. -/
theorem quotientHom_id (b : B) : quotientHom hU (le_refl b) = OrderHom.id := by
  refine OrderHom.ext _ _ (funext fun p => Fin.ext ?_)
  rw [quotientHom_val, restrictSigma_id]
  rfl

/-- `quotientHom` preserves composition. -/
theorem quotientHom_comp {b c d : B} (h₁ : b ≤ c) (h₂ : c ≤ d) :
    quotientHom hU (h₁.trans h₂) = (quotientHom hU h₂).comp (quotientHom hU h₁) := by
  refine OrderHom.ext _ _ (funext fun p => Fin.ext ?_)
  change (restrictSigma hU (h₁.trans h₂)
      (Fin.cast (OpenTruss.numSing_ofNumSing (U b).card) p)).val
    = (restrictSigma hU h₂ (restrictSigma hU h₁
      (Fin.cast (OpenTruss.numSing_ofNumSing (U b).card) p))).val
  rw [restrictSigma_comp_apply]

/-- The `ℕ`-level extension of `quotientHom` is computed by the counting formula. -/
theorem fNat_quotientHom {b c : B} (h : b ≤ c) {p : ℕ} (hp : p < (U b).card) :
    fNat (quotientHom hU h) p
      = OpenTruss.cnt (U c) (fNat (A.sigmaHom h) (OpenTruss.nthNat (U b) p)) := by
  have hp' : p < (OpenTruss.ofNumSing (U b).card).numSing := by
    rw [OpenTruss.numSing_ofNumSing]; exact hp
  rw [fNat_of_lt _ hp', fNat_of_lt _ (OpenTruss.nthNat_lt _ hp)]
  rfl

end Restrict

/-! ### The coarse bundle and the quotient map -/

/-- **Source: §5.4, the construction after `def:Forward-stable singular family`.**
The bundle quotient of a forward-stable family: fibrewise the open 1-truss on the retained
singular cells, with arrow fibres the bordisms induced by the restricted singular functions.
The two functoriality clauses are *proved*, from `restrictSigma_id` / `restrictSigma_comp`
together with `induceOpen_id` / `induceOpen_comp`. -/
noncomputable def quotient (A : OpenBundle B) (U : ∀ b : B, Finset (Fin (A.fib b).numSing))
    (hU : A.IsForwardStableFam U) : OpenBundle B where
  fib b := OpenTruss.ofNumSing (U b).card
  arr h := induceOpen (quotientHom hU h)
  arr_id b x y := by
    rw [quotientHom_id hU b, induceOpen_id]
    exact Iff.rfl
  arr_comp h₁ h₂ x z := by
    rw [quotientHom_comp hU h₁ h₂, induceOpen_comp]
    exact Iff.rfl

@[simp] theorem quotient_fib (A : OpenBundle B)
    (U : ∀ b : B, Finset (Fin (A.fib b).numSing)) (hU : A.IsForwardStableFam U) (b : B) :
    (A.quotient U hU).fib b = OpenTruss.ofNumSing (U b).card := rfl

/-- **Source: §5.4, `q_U : A → A'`.**  The bundle map onto the quotient, fibrewise the
retained-set coarsening `q_(U_b)` of `cons:retained-set-coarsening-1-truss`.  The `face`
clause — that the fibrewise coarsenings are compatible with the arrow-fibre bordisms — is the
content of `OpenTruss.qUIdx_rel`, and is where forward stability is used. -/
noncomputable def quotientMap (A : OpenBundle B)
    (U : ∀ b : B, Finset (Fin (A.fib b).numSing)) (hU : A.IsForwardStableFam U) :
    A ⟶ A.quotient U hU where
  fibMap b := OpenTruss.qU (A.fib b) (U b)
  face := by
    intro b c h x y hrel
    rw [← induceOpen_singHom (A.arr h), induceOpen_rel] at hrel
    change (induceOpen (quotientHom hU h)).rel _ _
    rw [induceOpen_rel]
    simp only [OpenTruss.idx_qU]
    exact OpenTruss.qUIdx_rel (OpenTruss.numSing_ofNumSing (U b).card)
      (OpenTruss.numSing_ofNumSing (U c).card) (fun i hi => hU h i hi)
      (fun p hp => fNat_quotientHom hU h hp) hrel.1 hrel.2

@[simp] theorem quotientMap_fibMap (A : OpenBundle B)
    (U : ∀ b : B, Finset (Fin (A.fib b).numSing)) (hU : A.IsForwardStableFam U) (b : B) :
    (A.quotientMap U hU).fibMap b = OpenTruss.qU (A.fib b) (U b) := rfl

/-! ### The retained family of the quotient map is the given family -/

/-- **Source: §5.4.**  The retained singular family of `q_U` is `U` itself; fibrewise this is
`ret_qU`. -/
theorem ret_quotientMap (A : OpenBundle B)
    (U : ∀ b : B, Finset (Fin (A.fib b).numSing)) (hU : A.IsForwardStableFam U) :
    retFam (A.quotientMap U hU) = fun b => (↑(U b) : Set (Fin (A.fib b).numSing)) := by
  funext b
  ext i
  rw [mem_retFam, Finset.mem_coe, ← OpenTruss.ret_qU (A.fib b) rfl (U b),
    OpenTruss.mem_retOf rfl (OpenTruss.qU (A.fib b) (U b)) i]
  exact Iff.rfl

/-- **Source: `prop:fibrewise-characterisation-bundle-coarsenings` (§5.4), fibrewise half.**
Every fibre map of `q_U` is a coarsening of open 1-trusses.  (That these assemble into a
*bundle* coarsening is the converse of the fibrewise characterisation and is **not** proved
here.) -/
theorem isCoarsening_fibMap_quotientMap (A : OpenBundle B)
    (U : ∀ b : B, Finset (Fin (A.fib b).numSing)) (hU : A.IsForwardStableFam U) (b : B) :
    IsCoarsening (show A.fib b ⟶ (A.quotient U hU).fib b from
      (A.quotientMap U hU).fibMap b) :=
  OpenTruss.qU_isCoarsening (A.fib b) rfl (U b)

end OpenBundle

end Truss.Transfer
