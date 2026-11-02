/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.BundleNorm
import Truss.Transfer.Normalisation.Fibrewise

/-!
# §5.4 unconditionally

`BundleNorm.lean` develops the end of §5.4 against the fibrewise characterisation of bundle
coarsenings, taken there as an explicit hypothesis `FibrewiseThm` rather than as a `sorry`.
`Fibrewise.lean` proves that characterisation.  This module discharges the hypothesis and
restates the results unconditionally.

## Main results

* `fibrewiseThm` — the hypothesis, discharged.
* `OpenBundle.isNormalising_iff_retFam_eq_closure'` —
  `cor:coarsening-normalising-iff-return-equals-nontrivial` (row `B09`).
* `OpenBundle.bundleNormaliseMap_isNormalising'` — **the existence theorem for §5.4**
  (row `B10`): every labelled fibrewise-open 1-truss bundle over a finite poset admits a
  normalising coarsening.
* `OpenBundle.isNormalising_reindex'` — `prop:open-pullbacks-preserve-normalisation`
  (row `B11`).

## `prop:draft-outcoarse-1-bundle-poset-iso`

The section `U ↦ q_U` with `ret(q_U) = U` and the order-reversal clause are here; the
**retraction** half — that every bundle coarsening *is* `q_(ret q)` — is in
`BundleRetract.lean`, so the proposition is complete.
-/

universe u v w

namespace Truss.Transfer

open CategoryTheory TrussLike

/-- **`prop:fibrewise-characterisation-bundle-coarsenings`, in the form `BundleNorm.lean`
consumes it.**  This is the discharge: the hypothesis is a theorem. -/
theorem fibrewiseThm (B : Type u) [PartialOrder B] [Finite B] : FibrewiseThm B :=
  fun q hfib => OpenBundle.isCoarsening_of_fibrewise q hfib

namespace OpenBundle

variable {B : Type u} [PartialOrder B] [Finite B]
variable {C : Type v} [Category.{w} C]

/-- **Row `B05`, the part the criterion needs**: a mediator between bundle coarsenings exists
exactly when the retained families are reverse-ordered. -/
theorem exists_mediator_iff_retFam_le' {A Y Z : OpenBundle B} {r : A ⟶ Y} {q : A ⟶ Z}
    (hr : IsCoarsening r) (hq : IsCoarsening q) :
    (∃ h : Y ⟶ Z, IsCoarsening h ∧ q = r ≫ h) ↔ retFam q ≤ retFam r :=
  exists_mediator_iff_retFam_le (fibrewiseThm B) hr hq

/-- **Row `B09` — `cor:coarsening-normalising-iff-return-equals-nontrivial`.**  A labelled
bundle coarsening is normalising exactly when its retained family is the forward-stable
closure of the non-trivially labelled family. -/
theorem isNormalising_iff_retFam_eq_closure' {A : OpenBundle B} {L : A.Tot ⥤ C}
    {D : LabObj 1 (OpenBundle B) C} (q : (⟨A, L⟩ : LabObj 1 (OpenBundle B) C) ⟶ D)
    (hq : IsCoarsening q.1) : IsNormalising q ↔ retFam q.1 = A.nonTrivClosure L :=
  isNormalising_iff_retFam_eq_closure (fibrewiseThm B) q hq

/-- **Row `B09`, normality.**  `(A,L)` is normal exactly when every singular cell is in the
closure of the non-trivially labelled family. -/
theorem isNormal_iff_sing_eq_closure' (A : OpenBundle B) (L : A.Tot ⥤ C) :
    IsNormal (⟨A, L⟩ : LabObj 1 (OpenBundle B) C) ↔
      (fun b => (Set.univ : Set (Fin (A.fib b).numSing))) = A.nonTrivClosure L :=
  isNormal_iff_sing_eq_closure (fibrewiseThm B) A L

/-- **Row `B10` — THE EXISTENCE THEOREM FOR §5.4.**  The chapter's algorithm returns a
normalising coarsening for every labelled fibrewise-open 1-truss bundle over a finite
poset. -/
theorem bundleNormaliseMap_isNormalising' (A : OpenBundle B) (L : A.Tot ⥤ C) :
    IsNormalising (bundleNormaliseMap (fibrewiseThm B) A L) :=
  bundleNormaliseMap_isNormalising (fibrewiseThm B) A L

/-- Its target is normal. -/
theorem bundleNormalise_isNormal' (A : OpenBundle B) (L : A.Tot ⥤ C) :
    IsNormal (bundleNormalise (fibrewiseThm B) A L) :=
  bundleNormalise_isNormal (fibrewiseThm B) A L

/-- **Row `B10`, existence in bare form.**  Every labelled fibrewise-open 1-truss bundle over
a finite poset admits a normalising coarsening. -/
theorem exists_isNormalising_bundle (A : OpenBundle B) (L : A.Tot ⥤ C) :
    ∃ (D : LabObj 1 (OpenBundle B) C) (r : (⟨A, L⟩ : LabObj 1 (OpenBundle B) C) ⟶ D),
      IsNormalising r :=
  ⟨_, _, bundleNormaliseMap_isNormalising' A L⟩

end OpenBundle

/-! ### Row `B11`, at the universe level `BundlePullback.lean` supports -/

namespace OpenBundle

variable {B : Type u} {B' : Type u} [PartialOrder B] [PartialOrder B'] [Finite B] [Finite B']
variable {C : Type v} [Category.{v} C]

/-- **Row `B11` — `prop:open-pullbacks-preserve-normalisation`.**  Pulling a normalising
coarsening of labelled 1-truss bundles back along an **open** base map gives a normalising
coarsening.  Surjectivity and connected fibres of the base map are not required. -/
theorem isNormalising_reindex' (f : B' →o B) (hf : IsOpenPosetMap f) {A A' : OpenBundle B}
    {L : A.Tot ⥤ C} {M : A'.Tot ⥤ C} (q : (⟨A, L⟩ : LabObj 1 (OpenBundle B) C) ⟶ ⟨A', M⟩)
    (hq : IsNormalising q) : IsNormalising (labReindex f q) :=
  isNormalising_reindex (fibrewiseThm B) (fibrewiseThm B') f hf q hq

end OpenBundle

end Truss.Transfer
