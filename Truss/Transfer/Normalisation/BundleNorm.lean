/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.BundleQuotient
import Truss.Transfer.Normalisation.BundleLabel
import Truss.Transfer.Normalisation.BundlePullback
import Truss.Transfer.Normalisation.Classification

/-!
# Normalisation of labelled open 1-truss bundles (§5.4, rows B05, B09, B10, B11)

This module finishes §5.4 of the draft normalisation chapter
(`transfer/ch03-normalisation-draft.typ`), from
`prop:draft-outcoarse-1-bundle-poset-iso` to the end of the section.

Everything here is **conditional on one explicit hypothesis**, `FibrewiseThm B`: the converse
half of `prop:fibrewise-characterisation-bundle-coarsenings`, i.e. that a base-preserving
bundle map whose fibre maps are all coarsenings is itself a coarsening.  That converse is the
substantive geometric input of the section and is proved elsewhere; it is taken as a
hypothesis so that every result below becomes unconditional the moment it lands.  It is never
assumed in any other form and never `sorry`'d.

## Main definitions

* `FibrewiseThm` — the converse of the fibrewise characterisation, as a `Prop`.
* `OpenBundle.mediatorMap` — the assembly of fibrewise mediators into a bundle map.  The
  `face` clause is `OpenBundle.face_of_fibrewise`, which is where the poset-coarsening
  hypothesis on the source is used: an arrow of `Tot(Y)` lifts to an arrow of `Tot(A)`.
* `OpenBundle.closureFinset` — `\overline{NonTriv(A,L)}` as a **`Finset`**-valued family.
* `OpenBundle.normQuotient`, `OpenBundle.normQuotientMap` — steps 2 and 3 of the algorithm.
* `OpenBundle.outClassification` — the `OutClassification` of §5.4 (row `B09`), with
  `inv q := ret(q)`, `least := \overline{NonTriv(A,L)}`.
* `OpenBundle.bundleNormalise`, `OpenBundle.bundleNormaliseMap` — step 4 of the algorithm.
* `OpenBundle.labReindex` — the reindexed **labelled** bundle coarsening of row `B11`.

## Main results

* `OpenBundle.isCoarsening_quotientMap` — `q_U` is a bundle coarsening (row `B05`).
* `OpenBundle.exists_mediator_iff_retFam_le` — the order-reversal clause of
  `prop:draft-outcoarse-1-bundle-poset-iso`.
* `OpenBundle.isNormalising_iff_retFam_eq_closure`, `OpenBundle.isNormal_iff_sing_eq_closure`
  — `cor:coarsening-normalising-iff-return-equals-nontrivial` (row `B09`).
* `OpenBundle.bundleNormaliseMap_isNormalising` — **the existence theorem for §5.4** (row
  `B10`): every labelled fibrewise-open 1-truss bundle admits a normalising coarsening.
* `OpenBundle.isNormalising_reindex` — `prop:open-pullbacks-preserve-normalisation` (row
  `B11`).

## The `Set` / `Finset` mismatch

`OpenBundle.nonTrivClosure` is `Set`-valued (it is a `Transport.Family`), while
`OpenBundle.IsForwardStableFam` and `OpenBundle.quotient` are `Finset`-valued.  The bridge is
`OpenBundle.closureFinset`, defined as `(Set.toFinite _).toFinset` fibrewise — the ambient
type `Fin (A.fib b).numSing` is finite, so `Set.toFinite` applies with no decidability
hypothesis, and `Set.Finite.coe_toFinset` returns the original set.  `closureFinset` is
therefore noncomputable, which is harmless: `nonTrivClosure` is already noncomputable.
-/

universe u v w

namespace Truss.Transfer

open CategoryTheory Geometry Geometry.OneTruss TrussLike

/-- The converse of `prop:fibrewise-characterisation-bundle-coarsenings`, taken as an
explicit hypothesis. -/
abbrev FibrewiseThm (B : Type u) [PartialOrder B] [Finite B] : Prop :=
  ∀ {A A' : OpenBundle B} (q : A ⟶ A'), (∀ b : B, IsCoarsening (OpenBundle.fibHom q b)) →
    IsCoarsening q

variable {B : Type u} [PartialOrder B] [Finite B]

namespace OpenBundle

/-! ### The retained family, fibrewise -/

omit [Finite B] in
/-- The retained family of a bundle map is fibrewise the retained set of §5.3. -/
theorem mem_retFam_iff {A A' : OpenBundle B} (q : A ⟶ A') (b : B)
    (i : Fin (A.fib b).numSing) :
    i ∈ retFam q b ↔ i ∈ OpenTruss.retOf (rfl : (A.fib b).numSing = (A.fib b).numSing)
      (fibHom q b) :=
  mem_retFam.trans (OpenTruss.mem_retOf rfl (fibHom q b) i).symm

omit [Finite B] in
/-- The retained family, fibrewise, as an equality of sets. -/
theorem retFam_eq_coe_retOf {A A' : OpenBundle B} (q : A ⟶ A') (b : B) :
    retFam q b = ↑(OpenTruss.retOf (rfl : (A.fib b).numSing = (A.fib b).numSing)
      (fibHom q b)) :=
  Set.ext fun i => (mem_retFam_iff q b i).trans Finset.mem_coe.symm

omit [Finite B] in
/-- The retained family of the identity is everything: a singular cell is singular. -/
theorem retFam_id (A : OpenBundle B) :
    retFam (𝟙 A) = fun b => (Set.univ : Set (Fin (A.fib b).numSing)) := by
  funext b
  ext i
  exact iff_of_true (OpenTruss.isSingular_singEl (T := A.fib b) rfl i) (Set.mem_univ i)

/-! ### `B05`: the quotient map is a bundle coarsening -/

/-- **Source: `prop:draft-outcoarse-1-bundle-poset-iso` (§5.4), the section clause.**
The bundle quotient map of a forward-stable family is a coarsening.  `BundleQuotient.lean`
proves this fibrewise; the fibrewise theorem assembles it. -/
theorem isCoarsening_quotientMap (hFib : FibrewiseThm B) (A : OpenBundle B)
    (U : ∀ b : B, Finset (Fin (A.fib b).numSing)) (hU : A.IsForwardStableFam U) :
    IsCoarsening (A.quotientMap U hU) :=
  hFib _ fun b => isCoarsening_fibMap_quotientMap A U hU b

/-! ### Assembling fibrewise mediators -/

/-- **The `face` clause of a fibrewise mediator.**  Let `r : A ⟶ Y` be a bundle coarsening,
`q : A ⟶ Z` any bundle map, and `g` a family of fibre maps with `g_b ∘ r_b = q_b`.  Then `g`
is compatible with the arrow-fibre bordisms.

This is where the poset-coarsening hypothesis on `r` is used, and it is used exactly once: an
arrow of `Tot(Y)` inside a single base fibre-pair lifts to an arrow of `Tot(A)`, because a
poset coarsening has nonempty arrow fibres. -/
theorem face_of_fibrewise {A Y Z : OpenBundle B} {r : A ⟶ Y} (hr : IsCoarsening r)
    (q : A ⟶ Z) (g : ∀ b : B, Y.fib b ⟶ Z.fib b)
    (hg : ∀ (b : B) (x : (A.fib b).toOneTruss.El), (g b).toFun (r.fibMap b x) = q.fibMap b x)
    {b c : B} (h : b ≤ c) {x : (Y.fib b).toOneTruss.El} {y : (Y.fib c).toOneTruss.El}
    (hrel : (Y.arr h).rel x y) : (Z.arr h).rel ((g b).toFun x) ((g c).toFun y) := by
  have hle : @LE.le Y.Tot _ ⟨b, x⟩ ⟨c, y⟩ := ⟨h, hrel⟩
  obtain ⟨a, hsrc, htgt⟩ := hr.tot.arrowFibre_nonempty hle
  obtain ⟨⟨b₀, x₀⟩, ⟨c₀, y₀⟩, hale⟩ := a
  have hsrc' : (⟨b₀, r.fibMap b₀ x₀⟩ : Y.Tot) = ⟨b, x⟩ := hsrc
  have htgt' : (⟨c₀, r.fibMap c₀ y₀⟩ : Y.Tot) = ⟨c, y⟩ := htgt
  rw [Sigma.mk.injEq] at hsrc' htgt'
  obtain ⟨rfl, hx⟩ := hsrc'
  obtain ⟨rfl, hy⟩ := htgt'
  have hx' : r.fibMap b₀ x₀ = x := eq_of_heq hx
  have hy' : r.fibMap c₀ y₀ = y := eq_of_heq hy
  obtain ⟨h', hrel'⟩ := hale
  have := q.face h' hrel'
  rw [← hg b₀ x₀, ← hg c₀ y₀, hx', hy'] at this
  exact this

/-- **Source: `prop:draft-outcoarse-1-bundle-poset-iso` (§5.4), the mediator construction.**
Fibrewise mediators over a bundle coarsening assemble into a bundle map. -/
def mediatorMap {A Y Z : OpenBundle B} {r : A ⟶ Y} (hr : IsCoarsening r) (q : A ⟶ Z)
    (g : ∀ b : B, Y.fib b ⟶ Z.fib b)
    (hg : ∀ (b : B) (x : (A.fib b).toOneTruss.El), (g b).toFun (r.fibMap b x) = q.fibMap b x) :
    Y ⟶ Z where
  fibMap b := g b
  face := fun {_ _} h {_ _} hrel => face_of_fibrewise hr q g hg h hrel

@[simp] theorem mediatorMap_fibMap {A Y Z : OpenBundle B} {r : A ⟶ Y} (hr : IsCoarsening r)
    (q : A ⟶ Z) (g : ∀ b : B, Y.fib b ⟶ Z.fib b)
    (hg : ∀ (b : B) (x : (A.fib b).toOneTruss.El), (g b).toFun (r.fibMap b x) = q.fibMap b x)
    (b : B) : (mediatorMap hr q g hg).fibMap b = g b := rfl

/-! ### `B05`: order reversal -/

/-- **Source: `prop:draft-outcoarse-1-bundle-poset-iso` (§5.4), order reversal.**
A mediating bundle coarsening `h : Y ⟶ Z` with `q = r ≫ h` exists exactly when
`ret(q) ⊆ ret(r)`.

Forward: restrict to a fibre and apply §5.3's `exists_mediator_iff_ret_subset`.  Backward:
take the 1-truss mediator in each fibre, assemble it with `mediatorMap`, and apply the
fibrewise theorem to see that the assembly is a bundle coarsening. -/
theorem exists_mediator_iff_retFam_le (hFib : FibrewiseThm B) {A Y Z : OpenBundle B}
    {r : A ⟶ Y} {q : A ⟶ Z} (hr : IsCoarsening r) (hq : IsCoarsening q) :
    (∃ h : Y ⟶ Z, IsCoarsening h ∧ q = r ≫ h) ↔ retFam q ≤ retFam r := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    intro b i hi
    have hmed : (∃ m : Y.fib b ⟶ Z.fib b, IsCoarsening m ∧
        fibHom (r ≫ h) b = fibHom r b ≫ m) := ⟨fibHom h b, isCoarsening_fibHom hh b, rfl⟩
    have hsub := (OpenTruss.exists_mediator_iff_ret_subset
      (rfl : (A.fib b).numSing = (A.fib b).numSing) (isCoarsening_fibHom hr b)
      (isCoarsening_fibHom (hr.comp hh) b)).1 hmed
    exact (mem_retFam_iff r b i).2 (hsub ((mem_retFam_iff (r ≫ h) b i).1 hi))
  · intro hle
    have hfib : ∀ b : B, ∃ m : Y.fib b ⟶ Z.fib b, IsCoarsening m ∧
        fibHom q b = fibHom r b ≫ m := by
      intro b
      refine (OpenTruss.exists_mediator_iff_ret_subset
        (rfl : (A.fib b).numSing = (A.fib b).numSing) (isCoarsening_fibHom hr b)
        (isCoarsening_fibHom hq b)).2 ?_
      intro i hi
      exact (mem_retFam_iff r b i).1 (hle b ((mem_retFam_iff q b i).2 hi))
    choose g hgc hgcomp using hfib
    have hg : ∀ (b : B) (x : (A.fib b).toOneTruss.El),
        (g b).toFun (r.fibMap b x) = q.fibMap b x := by
      intro b x
      exact (congrArg (fun m : A.fib b ⟶ Z.fib b => m.toFun x) (hgcomp b)).symm
    refine ⟨mediatorMap hr q g hg, hFib _ fun b => hgc b, ?_⟩
    exact BundleMap.ext fun b x => (hg b x).symm

/-! ### The forward-stable closure as a `Finset`-valued family -/

section Labelled

variable {C : Type v} [Category.{w} C]

/-- `\overline{NonTriv(A,L)}` as a **`Finset`**-valued family.  The ambient type
`Fin (A.fib b).numSing` is finite, so `Set.toFinite` applies with no decidability
hypothesis. -/
noncomputable def closureFinset (A : OpenBundle B) (L : A.Tot ⥤ C) (b : B) :
    Finset (Fin (A.fib b).numSing) :=
  (Set.toFinite (A.nonTrivClosure L b)).toFinset

omit [Finite B] in
@[simp] theorem coe_closureFinset (A : OpenBundle B) (L : A.Tot ⥤ C) (b : B) :
    ↑(closureFinset A L b) = A.nonTrivClosure L b :=
  Set.Finite.coe_toFinset _

omit [Finite B] in
/-- The `Finset` form of the closure is forward-stable, in the `Finset` sense that
`OpenBundle.quotient` requires. -/
theorem closureFinset_isForwardStableFam (A : OpenBundle B) (L : A.Tot ⥤ C) :
    A.IsForwardStableFam (closureFinset A L) := by
  rw [A.isForwardStableFam_iff]
  have hcoe : (fun b => (↑(closureFinset A L b) : Set (Fin (A.fib b).numSing)))
      = A.nonTrivClosure L := funext fun b => coe_closureFinset A L b
  rw [hcoe]
  exact fun {_ _} h => A.nonTrivClosure_isForwardStable L h

/-! ### `B10`: steps 2 and 3 of the algorithm -/

/-- **Source: the algorithm of §5.4, steps 2 and 3.**  The bundle quotient at
`U := \overline{NonTriv(A,L)}`. -/
noncomputable def normQuotient (A : OpenBundle B) (L : A.Tot ⥤ C) : OpenBundle B :=
  A.quotient (closureFinset A L) (closureFinset_isForwardStableFam A L)

/-- **Source: the algorithm of §5.4, step 3.**  The bundle coarsening `q_U`. -/
noncomputable def normQuotientMap (A : OpenBundle B) (L : A.Tot ⥤ C) : A ⟶ normQuotient A L :=
  A.quotientMap (closureFinset A L) (closureFinset_isForwardStableFam A L)

omit [Finite B] in
/-- `ret(q_U) = \overline{NonTriv(A,L)}`. -/
theorem retFam_normQuotientMap (A : OpenBundle B) (L : A.Tot ⥤ C) :
    retFam (normQuotientMap A L) = A.nonTrivClosure L := by
  rw [normQuotientMap, ret_quotientMap]
  funext b
  exact coe_closureFinset A L b

/-- `q_U` is a bundle coarsening. -/
theorem isCoarsening_normQuotientMap (hFib : FibrewiseThm B) (A : OpenBundle B)
    (L : A.Tot ⥤ C) : IsCoarsening (normQuotientMap A L) :=
  isCoarsening_quotientMap hFib A _ _

/-- **Source: the algorithm of §5.4, step 4.**  `L` descends along `q_U`, because
`ret(q_U)` is exactly the closure. -/
theorem descendsAlong_normQuotientMap (hFib : FibrewiseThm B) (A : OpenBundle B)
    (L : A.Tot ⥤ C) : DescendsAlong (normQuotientMap A L) L := by
  rw [descendsAlong_iff_nonTrivClosure_le _ (isCoarsening_normQuotientMap hFib A L) L,
    retFam_normQuotientMap]

/-- **Source: the algorithm of §5.4, step 4.**  The normalised labelled bundle. -/
noncomputable def bundleNormalise (hFib : FibrewiseThm B) (A : OpenBundle B)
    (L : A.Tot ⥤ C) : LabObj 1 (OpenBundle B) C :=
  ⟨normQuotient A L, descendedLabel (isCoarsening_normQuotientMap hFib A L)
    (descendsAlong_normQuotientMap hFib A L)⟩

/-- **Source: the algorithm of §5.4, step 4.**  The labelled bundle coarsening
`q_U : (A,L) → (A^U, \overline{L})`. -/
noncomputable def bundleNormaliseMap (hFib : FibrewiseThm B) (A : OpenBundle B)
    (L : A.Tot ⥤ C) :
    (⟨A, L⟩ : LabObj 1 (OpenBundle B) C) ⟶ bundleNormalise hFib A L :=
  ⟨normQuotientMap A L, (descendedLabel_spec (isCoarsening_normQuotientMap hFib A L)
    (descendsAlong_normQuotientMap hFib A L)).symm⟩

theorem bundleNormaliseMap_isCoarsening (hFib : FibrewiseThm B) (A : OpenBundle B)
    (L : A.Tot ⥤ C) : IsCoarsening (bundleNormaliseMap hFib A L).1 :=
  isCoarsening_normQuotientMap hFib A L

theorem retFam_bundleNormaliseMap (hFib : FibrewiseThm B) (A : OpenBundle B)
    (L : A.Tot ⥤ C) : retFam (bundleNormaliseMap hFib A L).1 = A.nonTrivClosure L :=
  retFam_normQuotientMap A L

/-! ### `B09`: the classification -/

/-- **Source: `prop:Outgoing labelled bundle coarsenings` (§5.4).**  The retained-family
classification of the outgoing labelled coarsenings of `(A,L)`.

`least_le` is `descendsAlong_iff_nonTrivClosure_le`, `exists_least` is the algorithm of
`B10`, and `mediator_iff` is `exists_mediator_iff_retFam_le` together with the fullness
lemma `descendedLabel_comp` of §5.2. -/
noncomputable def outClassification (hFib : FibrewiseThm B) (A : OpenBundle B)
    (L : A.Tot ⥤ C) :
    OutClassification (⟨A, L⟩ : LabObj 1 (OpenBundle B) C) A.singTransport.Family where
  inv q := retFam q.1
  mediator_iff := by
    intro D E r q hr hq
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact (exists_mediator_iff_retFam_le hFib hr hq).1 ⟨h.1, hh, rfl⟩
    · intro hle
      obtain ⟨h₀, hh₀, hcomp⟩ := (exists_mediator_iff_retFam_le hFib hr hq).2 hle
      have hlab : posetFunctor (totMap h₀) ⋙ E.label = D.label :=
        descendedLabel_comp hr hcomp r.2.symm q.2.symm
      exact ⟨⟨h₀, hlab.symm⟩, hh₀, Subtype.ext hcomp⟩
  least := A.nonTrivClosure L
  least_le := by
    intro D r hr
    exact (descendsAlong_iff_nonTrivClosure_le r.1 hr L).1
      ((descendsAlong_iff hr L).2 ⟨D.label, r.2.symm⟩)
  exists_least :=
    ⟨bundleNormalise hFib A L, bundleNormaliseMap hFib A L,
      bundleNormaliseMap_isCoarsening hFib A L, retFam_bundleNormaliseMap hFib A L⟩

/-- **Source: `cor:coarsening-normalising-iff-return-equals-nontrivial` (§5.4).**
A labelled bundle coarsening out of `(A,L)` is normalising exactly when its retained family
is the forward-stable closure of `NonTriv(A,L)`. -/
theorem isNormalising_iff_retFam_eq_closure (hFib : FibrewiseThm B) {A : OpenBundle B}
    {L : A.Tot ⥤ C} {D : LabObj 1 (OpenBundle B) C}
    (q : (⟨A, L⟩ : LabObj 1 (OpenBundle B) C) ⟶ D) (hq : IsCoarsening q.1) :
    IsNormalising q ↔ retFam q.1 = A.nonTrivClosure L :=
  (outClassification hFib A L).isNormalising_iff_inv_eq_least q hq

/-- **Source: `cor:coarsening-normalising-iff-return-equals-nontrivial` (§5.4).**
`(A,L)` is normal exactly when every singular cell of every fibre lies in the forward-stable
closure of `NonTriv(A,L)`. -/
theorem isNormal_iff_sing_eq_closure (hFib : FibrewiseThm B) (A : OpenBundle B)
    (L : A.Tot ⥤ C) :
    IsNormal (⟨A, L⟩ : LabObj 1 (OpenBundle B) C) ↔
      (fun b => (Set.univ : Set (Fin (A.fib b).numSing))) = A.nonTrivClosure L := by
  rw [IsNormal, isNormalising_iff_retFam_eq_closure hFib (𝟙 _) (IsCoarsening.id _),
    LabObj.id_coe, retFam_id]

/-- **The existence theorem for §5.4.**  Every labelled fibrewise-open 1-truss bundle admits
a normalising coarsening, namely the one produced by the chapter's algorithm. -/
theorem bundleNormaliseMap_isNormalising (hFib : FibrewiseThm B) (A : OpenBundle B)
    (L : A.Tot ⥤ C) : IsNormalising (bundleNormaliseMap hFib A L) :=
  (isNormalising_iff_retFam_eq_closure hFib _ (bundleNormaliseMap_isCoarsening hFib A L)).2
    (retFam_bundleNormaliseMap hFib A L)

/-- The target of the algorithm's coarsening is normal (§5.2's `C10`). -/
theorem bundleNormalise_isNormal (hFib : FibrewiseThm B) (A : OpenBundle B)
    (L : A.Tot ⥤ C) : IsNormal (bundleNormalise hFib A L) :=
  (bundleNormaliseMap_isNormalising hFib A L).target_isNormal

end Labelled

/-! ### `B11`: open pullbacks preserve normalisation

`BundlePullback.lean` states `pullbackLabel` and `nonTrivClosure_reindex` for a **small**
label category (`Category.{v} C`), so this last part inherits that restriction; `B05`-`B10`
above are stated for an arbitrary `Category.{w} C`. -/

section Pullback

variable {C : Type v} [Category.{v} C]
variable {B' : Type u} [PartialOrder B'] [Finite B']

/-- **Source: `prop:open-pullbacks-preserve-normalisation` (§5.4).**  The reindexing of a
labelled bundle coarsening along a monotone base map.  The label equation pulls back by
`descendsAlong_reindex`; no openness is needed for this. -/
def labReindex (f : B' →o B) {A A' : OpenBundle B} {L : A.Tot ⥤ C} {M : A'.Tot ⥤ C}
    (q : (⟨A, L⟩ : LabObj 1 (OpenBundle B) C) ⟶ ⟨A', M⟩) :
    (⟨reindex f A, pullbackLabel f A L⟩ : LabObj 1 (OpenBundle B') C) ⟶
      ⟨reindex f A', pullbackLabel f A' M⟩ :=
  ⟨BundleMap.reindex f q.1,
    (congrArg (pullbackLabel f A) q.2).trans (descendsAlong_reindex f q.1 M)⟩

@[simp] theorem labReindex_coe (f : B' →o B) {A A' : OpenBundle B} {L : A.Tot ⥤ C}
    {M : A'.Tot ⥤ C} (q : (⟨A, L⟩ : LabObj 1 (OpenBundle B) C) ⟶ ⟨A', M⟩) :
    (labReindex f q).1 = BundleMap.reindex f q.1 := rfl

/-- **Source: `prop:open-pullbacks-preserve-normalisation` (§5.4).**  Pulling a normalising
coarsening of labelled fibrewise-open 1-truss bundles back along an **open** monotone base
map again gives a normalising coarsening.

The proof is the chapter's: `ret(f^*q)_p = ret(q)_{f p}` is definitional, the closure of the
pulled-back non-trivially labelled family is the pullback of the closure
(`nonTrivClosure_reindex`, which is where openness of `f` is used), and
`cor:coarsening-normalising-iff-return-equals-nontrivial` applies at both ends. -/
theorem isNormalising_reindex (hFib : FibrewiseThm B) (hFib' : FibrewiseThm B')
    (f : B' →o B) (hf : IsOpenPosetMap f) {A A' : OpenBundle B} {L : A.Tot ⥤ C}
    {M : A'.Tot ⥤ C} (q : (⟨A, L⟩ : LabObj 1 (OpenBundle B) C) ⟶ ⟨A', M⟩)
    (hq : IsNormalising q) : IsNormalising (labReindex f q) := by
  have hqc : IsCoarsening q.1 := hq.1
  have hret : retFam q.1 = A.nonTrivClosure L :=
    (isNormalising_iff_retFam_eq_closure hFib q hqc).1 hq
  have hc' : IsCoarsening (labReindex f q).1 :=
    hFib' _ fun p => isCoarsening_fibHom hqc (f p)
  refine (isNormalising_iff_retFam_eq_closure hFib' (labReindex f q) hc').2 ?_
  funext p
  rw [nonTrivClosure_reindex f hf A L p, ← hret]
  rfl

end Pullback

end OpenBundle

end Truss.Transfer
