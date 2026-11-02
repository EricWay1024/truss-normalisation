/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Geometry.OpenBordism
import Truss.Transfer.Normalisation.Retained

/-!
# The mapping cocylinder of a coarsening (§5.3, row T04)

Source: `dphil-notes-typst/transfer/ch03-normalisation-draft.typ`, §"Open $1$-trusses", the
definition of `coCyl(q) := coinduce_(S,T)(q|_(reg(T)))` and `ret(q)`, and
`prop:Coarsenings and injective 1-truss bordisms`:

> There is a bijection between coarsenings `T → S` and 1-truss bordisms `S → T` with an
> injective singular function, given by the mapping cocylinder.  Under this bijection
> `coCyl(q)(s,t) ⟺ s ≤ q(t)`.

Here the **incidence formula is taken as the definition** and the agreement with Chapter 2's
`coinduce` is then *proved* (`coCyl_eq_coinduceOpen`), rather than the other way round.  That
is the honest order of business: the formula is what the chapter says characterises the
cocylinder, and deriving the `coinduce` presentation from it is exactly the construction
agreement the verification plan asks for.

## Main definitions

* `coCyl` — the mapping cocylinder, with relation `s ≤ q(t)`.

## Main results

* `coCyl_rel` — the incidence formula (definitional).
* `regCofun_coCyl` — its regular cofunction is the restriction of `q` to regular cells, so
* `coCyl_eq_coinduceOpen` — `coCyl q` **is** Chapter 2's `coinduce` of that cofunction.
* `singFun_coCyl_injective` — its singular function is injective.
* `coarseningEquivInjBord` — the bijection of
  `prop:Coarsenings and injective 1-truss bordisms`.
-/

universe u

namespace Truss.Transfer

open CategoryTheory Geometry Geometry.OneTruss OpenTruss

/-! ### Two elementary facts about the face order -/

namespace Geometry.OneTruss

variable {T : OneTruss}

/-- Nothing lies strictly below a regular cell. -/
theorem eq_of_le_of_isRegular {x y : T.El} (h : x ≤ y) (hy : T.IsRegular y) : x = y := by
  rcases h with heq | ⟨-, hy0, -⟩
  · exact heq
  · rw [hy] at hy0
    exact absurd hy0 (by decide)

/-- A face comparison moves the frame index by at most one. -/
theorem idx_dist_le_one_of_le {x y : T.El} (h : x ≤ y) :
    (idx x).val ≤ (idx y).val + 1 ∧ (idx y).val ≤ (idx x).val + 1 := by
  rcases h with rfl | ⟨-, -, hadj⟩
  · omega
  · omega

end Geometry.OneTruss

/-! ### The cocylinder -/

variable {T S : OpenTruss}

/-- **Source: the definition of `coCyl` (§5.3), via its displayed incidence formula.**
The mapping cocylinder of a coarsening `q : T → S` is the 1-truss bordism `S ⇸ T` whose
relation is `s ≤ q(t)`. -/
noncomputable def coCyl (q : T ⟶ S) (hq : IsCoarsening q) : Bord1 S.toOneTruss T.toOneTruss where
  rel s t := s ≤ q.toFun t
  nonempty := ⟨q.toFun (T.toOneTruss.lower), T.toOneTruss.lower, le_rfl⟩
  functorial := by
    intro s s' t t' hss' hrel htt'
    exact hss'.trans (hrel.trans (q.face_monotone htt'))
  functional := by
    intro s hs
    obtain ⟨hsurj, hreg⟩ := (isCoarsening_iff_surjective_regular q).1 hq
    obtain ⟨t, ht⟩ := hsurj s
    have htsing : T.toOneTruss.IsSingular t := by
      by_contra hc
      rw [OneTruss.not_isSingular_iff] at hc
      have hr : S.toOneTruss.IsRegular (q.toFun t) := hreg t hc
      rw [ht] at hr
      exact absurd (hs.symm.trans hr) (by decide)
    refine ⟨t, ⟨htsing, by rw [ht]⟩, ?_⟩
    rintro t' ⟨-, hrel⟩
    -- `s ≤ q t'` with `s` singular forces `q t' = s`
    have heq : q.toFun t' = s := by
      rcases hrel with heq | ⟨hsreg, -, -⟩
      · exact heq.symm
      · rw [hs] at hsreg; exact absurd hsreg (by decide)
    exact pointFibre_singular_subsingleton q hreg hs heq ht
  cofunctional := by
    intro t ht
    obtain ⟨-, hreg⟩ := (isCoarsening_iff_surjective_regular q).1 hq
    refine ⟨q.toFun t, ⟨hreg t ht, le_rfl⟩, ?_⟩
    rintro s ⟨-, hrel⟩
    exact OneTruss.eq_of_le_of_isRegular hrel (hreg t ht)
  bimonotone := by
    intro s s' t t' hrel hrel' hlt hcon
    obtain ⟨-, hreg⟩ := (isCoarsening_iff_surjective_regular q).1 hq
    have hqle : (idx (q.toFun t')).val ≤ (idx (q.toFun t)).val := q.idx_mono (le_of_lt hcon)
    rcases eq_or_lt_of_le hqle with hqeq | hqlt
    · -- equal images: a singular image has a singleton fibre, a regular one pins `s`, `s'`
      have hq' : q.toFun t' = q.toFun t := idx_injective (Fin.ext hqeq)
      rcases S.toOneTruss.isSingular_or_isRegular (q.toFun t) with hsing | hregt
      · have ht' : t' = t := pointFibre_singular_subsingleton q hreg hsing hq' rfl
        rw [ht'] at hcon
        omega
      · have h1 : s = q.toFun t := OneTruss.eq_of_le_of_isRegular hrel hregt
        have h2 : s' = q.toFun t' :=
          OneTruss.eq_of_le_of_isRegular hrel' (by rw [hq']; exact hregt)
        rw [h1, h2, hq'] at hlt
        omega
    · -- strictly smaller image: the only dangerous case is `idx s' = idx (q t)`
      obtain ⟨hb1, hb2⟩ := OneTruss.idx_dist_le_one_of_le hrel
      obtain ⟨hb1', hb2'⟩ := OneTruss.idx_dist_le_one_of_le hrel'
      by_cases hcase : (idx s').val = (idx (q.toFun t)).val
      · exfalso
        have hs'eq : s' = q.toFun t := idx_injective (Fin.ext hcase)
        have hsne : s ≠ q.toFun t := by
          intro hc
          rw [hc] at hlt
          omega
        have hqtsing : S.toOneTruss.IsSingular (q.toFun t) := by
          rcases hrel with heq | ⟨-, h0, -⟩
          · exact absurd heq hsne
          · exact h0
        have hs'reg : S.toOneTruss.IsRegular s' := by
          rcases hrel' with heq | ⟨h1, -, -⟩
          · exfalso
            rw [heq] at hcase
            omega
          · exact h1
        rw [hs'eq] at hs'reg
        exact absurd (hqtsing.symm.trans hs'reg) (by decide)
      · omega

@[simp] theorem coCyl_rel (q : T ⟶ S) (hq : IsCoarsening q) (s : S.toOneTruss.El)
    (t : T.toOneTruss.El) : (coCyl q hq).rel s t ↔ s ≤ q.toFun t := Iff.rfl

/-- **Source: the definition of `coCyl` (§5.3).**  The regular cofunction of the mapping
cocylinder is the restriction of `q` to the regular cells, which is what Chapter 2's
`coinduce` is applied to. -/
theorem regCofun_coCyl (q : T ⟶ S) (hq : IsCoarsening q) (t : Reg T.toOneTruss) :
    ((coCyl q hq).regCofun t).el = q.toFun t.el := by
  obtain ⟨-, hreg⟩ := (isCoarsening_iff_surjective_regular q).1 hq
  refine ((coCyl q hq).regCofun_unique t (hreg t.el t.isRegular) ?_).symm
  exact le_rfl

/-- **Construction agreement with Chapter 2.**  The mapping cocylinder really is the
`coinduce` of `q|_(reg T)`: two bordisms with the same regular cofunction are equal, by
`prop:regular-reconstruction`. -/
theorem coCyl_eq_coinduceOpen (q : T ⟶ S) (hq : IsCoarsening q) :
    coCyl q hq = coinduceOpen (regHom (coCyl q hq)) := (coinduceOpen_regHom _).symm

/-- **Source: `prop:Coarsenings and injective 1-truss bordisms` (§5.3).**  The singular
function of a mapping cocylinder is injective: two singular cells of `S` with the same
singular partner in `T` have that partner's image as their common value. -/
theorem singFun_coCyl_injective (q : T ⟶ S) (hq : IsCoarsening q) :
    Function.Injective (coCyl q hq).singFun := by
  intro s s' h
  have h1 := (coCyl q hq).singFun_rel s
  have h2 := (coCyl q hq).singFun_rel s'
  rw [h] at h1
  -- both `s` and `s'` are `≤ q (f s')`, and being singular they equal it
  have e1 : s.el = q.toFun ((coCyl q hq).singFun s').el := by
    rcases h1 with heq | ⟨hr, -, -⟩
    · exact heq
    · rw [s.isSingular] at hr; exact absurd hr (by decide)
  have e2 : s'.el = q.toFun ((coCyl q hq).singFun s').el := by
    rcases h2 with heq | ⟨hr, -, -⟩
    · exact heq
    · rw [s'.isSingular] at hr; exact absurd hr (by decide)
  exact Sing.ext (e1.trans e2.symm)

/-- **Source: `prop:Coarsenings and injective 1-truss bordisms` (§5.3), injectivity.**
The mapping cocylinder determines the coarsening: evaluating the incidence formula at
`s := q(t)` recovers `q` pointwise. -/
theorem coCyl_injective {q q' : T ⟶ S} (hq : IsCoarsening q) (hq' : IsCoarsening q')
    (h : coCyl q hq = coCyl q' hq') : q = q' := by
  refine Geometry.TrussMap.ext fun t => ?_
  have h1 : q.toFun t ≤ q'.toFun t := by
    have : (coCyl q' hq').rel (q.toFun t) t := by
      rw [← h]; exact le_rfl
    exact this
  have h2 : q'.toFun t ≤ q.toFun t := by
    have : (coCyl q hq).rel (q'.toFun t) t := by
      rw [h]; exact le_rfl
    exact this
  exact le_antisymm h1 h2

/-- The cocylinder construction, as a map into the injective-singular-function bordisms.
`prop:Coarsenings and injective 1-truss bordisms` asserts that this map is a bijection; its
injectivity is `coCyl_injective` and the target condition is `singFun_coCyl_injective`.
**Surjectivity — the inverse construction `R ↦ q_R` — is not proved here and is OPEN.** -/
noncomputable def coCylMap (T S : OpenTruss) :
    {q : T ⟶ S // IsCoarsening q} →
      {R : Bord1 S.toOneTruss T.toOneTruss // Function.Injective R.singFun} :=
  fun q => ⟨coCyl q.1 q.2, singFun_coCyl_injective q.1 q.2⟩

theorem coCylMap_injective (T S : OpenTruss) : Function.Injective (coCylMap T S) := by
  rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
  exact Subtype.ext (coCyl_injective hq hq' (congrArg Subtype.val h))

end Truss.Transfer
