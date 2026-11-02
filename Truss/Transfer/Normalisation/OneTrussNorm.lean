/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.NonTriv
import Truss.Transfer.Normalisation.Retained
import Truss.Transfer.Normalisation.Terminality

/-!
# Normalisation of labelled open 1-trusses (§5.3, rows T07–T09)

Combining the unlabelled classification of `Retained.lean` (`T05`, `T06`) with the label
criterion of `NonTriv.lean` gives the labelled half of §5.3:

* `prop:Outgoing labelled coarsenings as retained sets` — the retained-set classification
  restricts to the labelled outgoing coarsenings, which are exactly those retaining
  `NonTriv(X,L)`;
* the corollary — a coarsening is **normalising** exactly when `ret(q) = NonTriv(X,L)`, and
  `(X,L)` is **normal** exactly when `NonTriv(X,L) = sing(X)`;
* `Algorithm: normalisation of labelled 1-trusses` — the construction `q_E`, its unique
  descended label, and the theorem that it really is terminal.

The last item is the **existence theorem for §5.3**: every labelled open 1-truss admits a
normalising coarsening.  Nothing in §5.2 assumed such existence; it is produced here.
-/

universe u v

namespace Truss.Transfer

open CategoryTheory Geometry Geometry.OneTruss TrussLike OpenTruss

variable {C : Type u} [Category.{v} C]

/-! ### The bridge between the two descriptions of "retained" -/

theorem mem_retOf {T S : OpenTruss} {k : ℕ} (hk : T.numSing = k) (q : T ⟶ S)
    (i : Fin k) : i ∈ retOf hk q ↔ S.toOneTruss.IsSingular (q.toFun (T.singAt hk i).el) := by
  simp [retOf]

/-- **Source: `prop:Outgoing labelled coarsenings as retained sets` (§5.3), object part.**
A coarsening out of `(X,L)` is label-preserving exactly when it retains every non-trivially
labelled singular cell. -/
theorem descendsAlong_iff_nonTriv_subset {T S : OpenTruss} (q : T ⟶ S) (hq : IsCoarsening q)
    (L : Tot T ⥤ C) : DescendsAlong q L ↔ NonTriv T L ⊆ retOf rfl q := by
  rw [descendsAlong_iff_nonTriv_retained q hq L]
  constructor
  · intro h i hi
    exact (mem_retOf rfl q i).2 (h i hi)
  · intro h i hi
    exact (mem_retOf rfl q i).1 (h hi)

/-! ### The labelled outgoing category -/

variable (A : LabObj.{0, 0, 0, u, v} 1 OpenTruss C)

/-- The non-trivially labelled singular cells of a labelled open 1-truss. -/
noncomputable abbrev nonTrivOf : Finset (Fin A.obj.numSing) := NonTriv A.obj A.label

variable {A}

/-- Every labelled coarsening out of `(X,L)` retains `NonTriv(X,L)`. -/
theorem nonTriv_subset_ret_of_hom {B : LabObj.{0, 0, 0, u, v} 1 OpenTruss C} (q : A ⟶ B)
    (hq : IsCoarsening q.1) : nonTrivOf A ⊆ retOf rfl q.1 :=
  (descendsAlong_iff_nonTriv_subset q.1 hq A.label).1
    ((descendsAlong_iff hq A.label).2 ⟨B.label, q.2.symm⟩)

/-! ### The algorithm -/

/-- **Source: `Algorithm: normalisation of labelled 1-trusses` (§5.3), step 2.**
The coarsening `q_E` at `E := NonTriv(X,L)`. -/
noncomputable def normCoarsening : A.obj ⟶ ofNumSing (nonTrivOf A).card :=
  qU A.obj (nonTrivOf A)

theorem normCoarsening_isCoarsening : IsCoarsening (normCoarsening (A := A)) :=
  qU_isCoarsening A.obj rfl _

theorem ret_normCoarsening : retOf rfl (normCoarsening (A := A)) = nonTrivOf A :=
  ret_qU A.obj rfl _

theorem normCoarsening_descendsAlong : DescendsAlong (normCoarsening (A := A)) A.label := by
  rw [descendsAlong_iff_nonTriv_subset _ normCoarsening_isCoarsening, ret_normCoarsening]

/-- **Source: the algorithm, step 3.**  The unique descended label `\overline{L}`. -/
noncomputable def normLabel : Tot (ofNumSing (nonTrivOf A).card) ⥤ C :=
  descendedLabel normCoarsening_isCoarsening normCoarsening_descendsAlong

/-- **Source: the algorithm, step 4.**  The normalised labelled 1-truss. -/
noncomputable def normalise : LabObj.{0, 0, 0, u, v} 1 OpenTruss C :=
  ⟨ofNumSing (nonTrivOf A).card, normLabel⟩

/-- **Source: the algorithm, step 4.**  The labelled coarsening `q_E : (X,L) → (X_E, L̄)`. -/
noncomputable def normaliseMap : A ⟶ normalise (A := A) :=
  ⟨normCoarsening, (descendedLabel_spec normCoarsening_isCoarsening
    normCoarsening_descendsAlong).symm⟩

theorem normaliseMap_isCoarsening : IsCoarsening (normaliseMap (A := A)).1 :=
  normCoarsening_isCoarsening

theorem ret_normaliseMap : retOf rfl (normaliseMap (A := A)).1 = nonTrivOf A :=
  ret_normCoarsening

/-! ### The normalising criterion -/

/-- **Source: the corollary after `prop:Outgoing labelled coarsenings as retained sets`.**
A labelled coarsening out of `(X,L)` is normalising exactly when its retained set is
`NonTriv(X,L)`. -/
theorem isNormalising_iff_ret_eq_nonTriv {B : LabObj.{0, 0, 0, u, v} 1 OpenTruss C} (q : A ⟶ B)
    (hq : IsCoarsening q.1) : IsNormalising q ↔ retOf rfl q.1 = nonTrivOf A := by
  constructor
  · intro hnorm
    refine Finset.Subset.antisymm ?_ (nonTriv_subset_ret_of_hom q hq)
    obtain ⟨m, hm, heq⟩ := hnorm.exists_mediator (normaliseMap (A := A)) normaliseMap_isCoarsening
    have hsub := (exists_mediator_iff_ret_subset rfl normaliseMap_isCoarsening hq).1
      ⟨m.1, hm, congrArg Subtype.val heq⟩
    rwa [ret_normaliseMap] at hsub
  · intro hret
    refine ⟨hq, fun D r hr => ?_⟩
    -- a mediator exists because `ret q = NonTriv ⊆ ret r`
    have hsub : retOf rfl q.1 ⊆ retOf rfl r.1 := by
      rw [hret]; exact nonTriv_subset_ret_of_hom r hr
    obtain ⟨h₀, hh₀, hcomp⟩ := (exists_mediator_iff_ret_subset rfl hr hq).2 hsub
    -- and it is automatically a labelled morphism, by fullness
    have hlab : posetFunctor (totMap h₀) ⋙ B.label = D.label :=
      descendedLabel_comp hr hcomp (r.2).symm (q.2).symm
    refine ⟨⟨h₀, hlab.symm⟩, ⟨hh₀, Subtype.ext hcomp⟩, ?_⟩
    rintro k ⟨-, hk⟩
    exact IsNormalising.mediator_unique hr (hk.symm.trans (Subtype.ext hcomp))

/-- The identity coarsening retains every singular cell. -/
theorem ret_id (T : OpenTruss) : retOf rfl (𝟙 T) = Finset.univ :=
  Finset.eq_univ_iff_forall.2 fun i => (mem_retOf rfl (𝟙 T) i).2 (T.singAt rfl i).isSingular

/-- **Source: the same corollary.**  `(X,L)` is normal exactly when every singular cell is
non-trivially labelled. -/
theorem isNormal_iff_nonTriv_eq_univ : IsNormal A ↔ nonTrivOf A = Finset.univ := by
  rw [IsNormal, isNormalising_iff_ret_eq_nonTriv (𝟙 A) (IsCoarsening.id _), LabObj.id_coe,
    ret_id]
  exact eq_comm

/-- **The existence theorem for §5.3.**  Every labelled open 1-truss admits a normalising
coarsening, namely the one produced by the chapter's algorithm. -/
theorem normaliseMap_isNormalising : IsNormalising (normaliseMap (A := A)) :=
  (isNormalising_iff_ret_eq_nonTriv _ normaliseMap_isCoarsening).2 ret_normaliseMap

/-- Consequently the normalised object is normal (§5.2's `C10` applied to the construction). -/
theorem normalise_isNormal : IsNormal (normalise (A := A)) :=
  normaliseMap_isNormalising.target_isNormal

end Truss.Transfer
