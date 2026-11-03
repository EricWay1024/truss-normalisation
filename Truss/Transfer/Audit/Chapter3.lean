/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.OneTrussNorm
import Truss.Transfer.Normalisation.CoCylBij
import Truss.Transfer.Normalisation.BundlePullback
import Truss.Transfer.Normalisation.Fibrewise
import Truss.Transfer.Normalisation.NoAut
import Truss.Transfer.Normalisation.Classification
import Truss.Transfer.Normalisation.LayerNormality
import Truss.Transfer.Normalisation.BlockNormality
import Truss.Transfer.Normalisation.OneTrussOrder
import Truss.Transfer.Normalisation.BundleOrder

/-!
# Audit: exact-typed witnesses for the draft normalisation chapter

[`plan/DraftNormalisationVerification.md`](../../../plan/DraftNormalisationVerification.md)
§11 requires, for every accepted result, that its **full type** be inspected against the
source's quantifiers, hypotheses and direction of maps.  This module makes that check
machine-enforced: each witness below **restates** the result from scratch and then supplies
the proved declaration.  A refactor that quietly changes a statement breaks this file.

Witnesses are grouped by the plan's coverage IDs.  Rows that are still **OPEN** are listed in
the closing comment, not witnessed here — an audit module contains no new assumptions.
-/

universe u v w u₂ v₂

namespace Truss.Transfer.Audit

open CategoryTheory Truss.Transfer Truss.Transfer.Geometry Truss.Transfer.TrussLike

section Chapter3

variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
variable {C : Type u} [Category.{v} C]

/-! ### §5.1 — the poset preamble -/

/-- `P01` — `prop:draft-open-exact`: openness is exact target lifting. -/
theorem w_P01 (q : P → Q) (hq : Monotone q) :
    (∀ y : P, q '' Set.Iic y = Set.Iic (q y)) ↔ ∀ (y : P) (z : Q), z ≤ q y → ∃ x ≤ y, q x = z :=
  isOpenPosetMap_iff_exists_le hq

/-- `P02` — `lem:draft-identity-arrow-fibre`: the arrow fibre over an identity arrow is the
arrow poset of the point fibre. -/
noncomputable def w_P02 (q : P →o Q) (y : Q) :
    ↥(arrowFibre q y y) ≃o Arr ↥(pointFibre q y) := arrowFibre_self_orderIso q y

/-- `P03` — the remark after `Poset coarsening`: nonemptiness of arrow fibres is *derived*
from object-surjectivity and openness, and arrow-fibre connectivity implies point-fibre
connectivity. -/
theorem w_P03 {q : P →o Q} (hq : IsPosetCoarsening q) :
    (∀ {y y' : Q}, y ≤ y' → (arrowFibre q y y').Nonempty) ∧
      ∀ y : Q, IsZigzagConnected (pointFibre q y) :=
  by
  refine ⟨?_, hq.pointFibre_connected⟩
  intro y y' h
  exact hq.arrowFibre_nonempty h

/-- `P04` — `prop:draft-poset-coarsening-properties`, all three clauses: epi, wide
subcategory, and pullback along an **arbitrary** monotone map. -/
theorem w_P04 :
    (∀ {R : Type u} [PartialOrder R] {q : P →o Q} (_ : IsPosetCoarsening q) {g h : Q →o R},
        g.comp q = h.comp q → g = h) ∧
      IsPosetCoarsening (OrderHom.id : P →o P) ∧
      (∀ {R : Type u} [PartialOrder R] {q : P →o Q} {r : Q →o R}, IsPosetCoarsening q →
        IsPosetCoarsening r → IsPosetCoarsening (r.comp q)) ∧
      (∀ {Z : Type u} [PartialOrder Z] {q : P →o Q} (_ : IsPosetCoarsening q) (f : Z →o Q),
        IsPosetCoarsening (pullbackSnd q f)) :=
  by
  refine ⟨?_, IsPosetCoarsening.id, ?_, ?_⟩
  · intro R _ q hq g h heq
    exact hq.cancel_right heq
  · intro R _ q r hq hr
    exact hq.comp hr
  · intro Z _ q hq f
    exact hq.pullback_proj f

/-- `P05` — `prop:draft-label-descent`: a **category-valued** label descends along a poset
coarsening exactly when it sends every collapsed arrow to an identity, and the descended
functor is unique. -/
theorem w_P05 {q : P →o Q} (hq : IsPosetCoarsening q) (L : P ⥤ C) :
    ((∃ K : Q ⥤ C, posetFunctor q ⋙ K = L) ↔
        ∀ (x y : P) (h : x ≤ y), q x = q y →
          ∃ e : L.obj x = L.obj y, L.map (homOfLE h) = eqToHom e) ∧
      ∀ K K' : Q ⥤ C, posetFunctor q ⋙ K = posetFunctor q ⋙ K' → K = K' :=
  ⟨label_descent hq L, fun _ _ hKK' => label_descent_unique hq hKK'⟩

end Chapter3

/-! ### §5.2 — the common interface -/

section Common

variable {n : ℕ} {K : Type u} [Category.{v} K] [TrussLike.{u, v, u} n K]
variable {C : Type u} [Category.{v} C]

/-- `C02` — `def:draft-coarsening`: the primitive lax comparison and the coordinatewise
numerical inequality agree. -/
theorem w_C02 {X Y : K} (q : X ⟶ Y) :
    (IsPosetCoarsening (totMap q) ∧
        Nonempty ((totMap q).monotone.functor ⋙ dimsigFunctor Y ⟶ dimsigFunctor X)) ↔
      IsCoarsening q :=
  isCoarsening_iff_exists_dimsigNatTrans q

/-- `C02`/`C03` — coarsenings are epi and form a wide subcategory; outgoing coarsenings are
thin. -/
theorem w_C03 :
    (∀ {X Y : K} {q : X ⟶ Y}, IsCoarsening q → Epi q) ∧
      (∀ X : K, IsCoarsening (𝟙 X)) ∧
      (∀ {X Y Z : K} {f : X ⟶ Y} {g : Y ⟶ Z}, IsCoarsening f → IsCoarsening g →
        IsCoarsening (f ≫ g)) :=
  by
  refine ⟨?_, IsCoarsening.id, ?_⟩
  · intro X Y q hq
    exact hq.epi
  · intro X Y Z f g hf hg
    exact hf.comp hg

/-- `C05` — `lem:draft-labelled-outcoarse-full`: every *structural* mediator between
label-preserving coarsenings is already a labelled one. -/
theorem w_C05 {X Y Z : K} {L : Tot X ⥤ C} {r : X ⟶ Y} {q : X ⟶ Z} {h : Y ⟶ Z}
    (hr : IsCoarsening r) (hcomp : q = r ≫ h) {M : Tot Y ⥤ C} {N : Tot Z ⥤ C}
    (hM : posetFunctor (totMap r) ⋙ M = L) (hN : posetFunctor (totMap q) ⋙ N = L) :
    posetFunctor (totMap h) ⋙ N = M :=
  descendedLabel_comp hr hcomp hM hN

/-- `C06` — `Structural uniqueness`: two normalising coarsenings out of one labelled object
are related by a compatible isomorphism **whose inverse is again a coarsening**. -/
theorem w_C06 {A B D : LabObj.{u, v, u, u, v} n K C} {q : A ⟶ B} {q' : A ⟶ D}
    (h : IsNormalising q) (h' : IsNormalising q') :
    ∃ e : B ⟶ D, ∃ e' : D ⟶ B, IsCoarsening e.1 ∧ IsCoarsening e'.1 ∧
      q' = q ≫ e ∧ q = q' ≫ e' ∧ e ≫ e' = 𝟙 B ∧ e' ≫ e = 𝟙 D :=
  h.unique_iso h'

/-- `C08` — `prop:draft-terminal-factors`. -/
theorem w_C08 {A B D : LabObj.{u, v, u, u, v} n K C} {c : A ⟶ B} {e : B ⟶ D}
    (hc : IsCoarsening c.1) (he : IsCoarsening e.1) (h : IsNormalising (c ≫ e)) :
    IsNormalising e := terminal_factors hc he h

/-- `C09` — `lem:draft-normalisation-precomposition`, with the source's existence hypothesis
kept **explicit**. -/
theorem w_C09 {A B D : LabObj.{u, v, u, u, v} n K C} {a : A ⟶ B} {d : B ⟶ D}
    (ha : IsCoarsening a.1) (hd : IsCoarsening d.1)
    (hex : ∃ (W : LabObj.{u, v, u, u, v} n K C) (q : A ⟶ W), IsNormalising q) :
    IsNormalising (a ≫ d) ↔ IsNormalising d := normalising_precomp ha hd hex

/-- `C10` — the target of a normalising coarsening is normal.  Its converse is **not**
asserted anywhere. -/
theorem w_C10 {A B : LabObj.{u, v, u, u, v} n K C} {q : A ⟶ B} (h : IsNormalising q) :
    IsNormal B := h.target_isNormal

/-- The `Label comparisons` remark: the invertible natural comparison is unique. -/
theorem w_C04c (hC : NoAut C) {X Y : K} (q : X ⟶ Y) (L : Tot X ⥤ C) (M : Tot Y ⥤ C)
    (α β : L ≅ posetFunctor (totMap q) ⋙ M) : α = β := labelComparison_unique hC q L M α β

end Common

/-! ### §5.3 — open 1-trusses -/

section OneTruss

variable {C : Type u} [Category.{v} C]

/-- `T01` — the construction bridges: `Tot` really is the face-poset functor and `dimsig`
really is `dim`, not look-alikes. -/
theorem w_T01 {T S : OpenTruss} (q : T ⟶ S) (x : Tot T) (i : Fin 1) :
    totMap q x = q.toFun x ∧ TrussLike.dimsig T x i = T.toOneTruss.dim x :=
  ⟨rfl, rfl⟩

/-- `T02` — `prop:characterisation-of-open-1-truss-coarsenings`. -/
theorem w_T02 {T S : OpenTruss} (q : T ⟶ S) :
    IsCoarsening q ↔ Function.Surjective q.toFun ∧
      ∀ i, T.toOneTruss.IsRegular i → S.toOneTruss.IsRegular (q.toFun i) :=
  isCoarsening_iff_surjective_regular q

/-- `T03` — `prop:Singular functions and regular cofunctions`, in the open setting. -/
theorem w_T03 {T S : OpenTruss} (R : Bord1 T.toOneTruss S.toOneTruss) :
    Function.Injective R.singFun ↔ Function.Surjective R.regCofun :=
  injective_singFun_iff_surjective_regCofun R

/-- `T04` — the mapping cocylinder's incidence formula, and its agreement with Chapter 2's
`coinduce`. -/
theorem w_T04 {T S : OpenTruss} (q : T ⟶ S) (hq : IsCoarsening q) :
    (∀ (s : S.toOneTruss.El) (t : T.toOneTruss.El), (coCyl q hq).rel s t ↔ s ≤ q.toFun t) ∧
      coCyl q hq = coinduceOpen (regHom (coCyl q hq)) :=
  ⟨coCyl_rel q hq, coCyl_eq_coinduceOpen q hq⟩

/-- `T04` — `prop:Coarsenings and injective 1-truss bordisms` **in full**: the bijection
between coarsenings `T → S` and 1-truss bordisms `S ⇸ T` with injective singular function,
given by the mapping cocylinder. -/
noncomputable def w_T04_bij (T S : OpenTruss) :
    {q : T ⟶ S // IsCoarsening q} ≃
      {R : Bord1 S.toOneTruss T.toOneTruss // Function.Injective R.singFun} := coCylEquiv T S

theorem w_T04_bij_is_coCyl (T S : OpenTruss) (q : {q : T ⟶ S // IsCoarsening q}) :
    (w_T04_bij T S q).1 = coCyl q.1 q.2 := rfl

/-- `T05` — `cons:retained-set-coarsening-1-truss`: `q_U` is a coarsening and retains
exactly `U`. -/
theorem w_T05 (T : OpenTruss) {k : ℕ} (hk : T.numSing = k) (U : Finset (Fin k)) :
    IsCoarsening (OpenTruss.qU T U) ∧ OpenTruss.retOf hk (OpenTruss.qU T U) = U :=
  ⟨OpenTruss.qU_isCoarsening T hk U, OpenTruss.ret_qU T hk U⟩

/-- `T06` — `prop:draft-outcoarse-poset-iso`: the order-reversal half, and the invertibility
criterion. -/
theorem w_T06 {T Y Z : OpenTruss} {k : ℕ} (hk : T.numSing = k) {r : T ⟶ Y} {q : T ⟶ Z}
    (hr : IsCoarsening r) (hq : IsCoarsening q) :
    ((∃ h : Y ⟶ Z, IsCoarsening h ∧ q = r ≫ h) ↔ OpenTruss.retOf hk q ⊆ OpenTruss.retOf hk r)
      ∧ (IsIso q ↔ OpenTruss.retOf hk q = Finset.univ) :=
  ⟨OpenTruss.exists_mediator_iff_ret_subset hk hr hq, OpenTruss.isIso_iff_ret_eq_univ hk hq⟩

/-- `T08` — the corollary: normalising exactly when the retained set is `NonTriv`, and normal
exactly when every singular cell is non-trivially labelled. -/
theorem w_T08 {A B : LabObj.{0, 0, 0, u, v} 1 OpenTruss C} (q : A ⟶ B)
    (hq : IsCoarsening q.1) :
    (IsNormalising q ↔ OpenTruss.retOf rfl q.1 = nonTrivOf A) ∧
      (IsNormal A ↔ nonTrivOf A = Finset.univ) :=
  ⟨isNormalising_iff_ret_eq_nonTriv q hq, isNormal_iff_nonTriv_eq_univ⟩

/-- `T09` — **the existence theorem for §5.3**: the chapter's algorithm returns a normalising
coarsening, and its target is normal.  This is the §11 capstone shape for `n = 1`: for every
labelled structural coarsening `R` out of `(X,L)` there is a **unique** labelled structural
coarsening `H` with `R ≫ H = Q`. -/
theorem w_T09 (A : LabObj.{0, 0, 0, u, v} 1 OpenTruss C) :
    IsNormalising (normaliseMap (A := A)) ∧ IsNormal (normalise (A := A)) ∧
      ∀ (D : LabObj.{0, 0, 0, u, v} 1 OpenTruss C) (R : A ⟶ D), IsCoarsening R.1 →
        ∃! H : D ⟶ normalise (A := A), IsCoarsening H.1 ∧ normaliseMap (A := A) = R ≫ H :=
  ⟨normaliseMap_isNormalising, normalise_isNormal,
    fun D R hR => (normaliseMap_isNormalising).2 D R hR⟩

end OneTruss

/-! ### §5.4 — open 1-truss bundles -/

section Bundle

variable {B : Type u} [PartialOrder B] [Finite B] {C : Type u} [Category.{v} C]

/-- `B01` — the construction bridges for the bundle category: `Tot` is the total poset of
`def:total-poset-bundle` and `dimsig` is the fibrewise dimension. -/
theorem w_B01 {A A' : OpenBundle B} (q : A ⟶ A') (p : A.Tot) (i : Fin 1) :
    totMap q p = ⟨p.1, q.fibMap p.1 p.2⟩ ∧
      TrussLike.dimsig A p i = (A.fib p.1).toOneTruss.dim p.2 := ⟨rfl, rfl⟩

/-- `B02` — `prop:fibrewise-characterisation-bundle-coarsenings`, **both directions**: a
coarsening of fibrewise-open 1-truss bundles is exactly a base-preserving bundle map whose
restriction to every fibre is a coarsening. -/
theorem w_B02 {A A' : OpenBundle B} (q : A ⟶ A') :
    IsCoarsening q ↔ ∀ b : B, IsCoarsening (OpenBundle.fibHom q b) :=
  OpenBundle.isCoarsening_iff_fibrewise q

omit [Finite B] in
/-- `B03` — the retained family of *any* base-preserving bundle map is forward-stable. -/
theorem w_B03 {A A' : OpenBundle B} (q : A ⟶ A') :
    A.singTransport.IsForwardStable (OpenBundle.retFam q) :=
  OpenBundle.retFam_isForwardStable q

omit [Finite B] in
/-- `B06` — `def:Forward-stable closure` and its two "clearly"s: the closure is extensive,
forward-stable, and least. -/
theorem w_B06 {E : B → Type u} (σ : Transport E) (U : σ.Family) :
    U ≤ σ.closure U ∧ σ.IsForwardStable (σ.closure U) ∧
      ∀ V : σ.Family, U ≤ V → σ.IsForwardStable V → σ.closure U ≤ V :=
  ⟨σ.le_closure U, σ.closure_isForwardStable U, fun _ h hV => σ.closure_le h hV⟩

/-- `B08` — `prop:Outgoing labelled bundle coarsenings`: label-preserving exactly when the
non-trivially labelled family is retained, equivalently when its closure is. -/
theorem w_B08 {A A' : OpenBundle B} (q : A ⟶ A') (hq : IsCoarsening q) (L : A.Tot ⥤ C) :
    (DescendsAlong q L ↔ A.nonTrivFam L ≤ OpenBundle.retFam q) ∧
      (DescendsAlong q L ↔ A.nonTrivClosure L ≤ OpenBundle.retFam q) :=
  ⟨OpenBundle.descendsAlong_iff_nonTrivFam_le q hq L,
    OpenBundle.descendsAlong_iff_nonTrivClosure_le q hq L⟩

end Bundle

section BundlePullbackAudit

variable {B : Type u} {B' : Type u} [PartialOrder B] [PartialOrder B'] [Finite B]
variable {C : Type v} [Category.{v} C]

omit [Finite B] in
/-- `B11`, key equality — the chapter's displayed union identity, holding because
`f(↓p) = ↓f(p)`.  Surjectivity and connected fibres of `f` are **not** used. -/
theorem w_B11key (f : B' →o B) (hf : IsOpenPosetMap f)
    (A : OpenBundle B) (L : A.Tot ⥤ C) (p : B') :
    (OpenBundle.reindex f A).nonTrivClosure (OpenBundle.pullbackLabel f A L) p
      = A.nonTrivClosure L (f p) :=
  OpenBundle.nonTrivClosure_reindex f hf A L p


end BundlePullbackAudit

section Section55Audit

variable {P : FPoset.{u}} {m : ℕ} {C : Type v} [Category.{v} C]

/-- `N02`, `thm:draft-successor-coarsening` — the three-way equivalence at a successor
height, as a genuine `List.TFAE`.  Unconditional: the fibrewise theorem is discharged. -/
theorem w_N02 {T S : Tower P (m + 1)} (Q : T ⟶ S) :
    [IsCoarsening Q,
      Function.Surjective (TowerMap.totHom Q) ∧
        ∀ x, Tower.dimsig P (m + 1) T x ≤ Tower.dimsig P (m + 1) S (TowerMap.totHom Q x),
      IsCoarsening (K := Tower P m) Q.lower ∧
        IsCoarsening (K := OpenBundle (towerTot P m T.lower).carrier) Q.topMap].TFAE :=
  successor_tfae' Q

/-- `N03`, `thm:draft-successor-normalising` — a morphism of labelled towers at a successor
height is normalising exactly when both of its components are. -/
theorem w_N03 {T S : Tower P (m + 1)} {L : (towerTot P (m + 1) T).carrier ⥤ C}
    {M : (towerTot P (m + 1) S).carrier ⥤ C}
    (Q : (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ⟶ ⟨S, M⟩) :
    IsNormalising Q ↔ IsNormalising (topLab Q) ∧ IsNormalising (lowLab Q) :=
  succ_isNormalising_iff Q

/-- `N04`, `cor:draft-successor-normality` — normality at a successor height splits into
normality of the lower tower (labelled by the classifying functor of the top bundle) and
normality of the top labelled bundle. -/
theorem w_N04 (T : Tower P (m + 1)) (L : (towerTot P (m + 1) T).carrier ⥤ C) :
    IsNormal (⟨T, L⟩ : LabObj (m + 1) (Tower P (m + 1)) C) ↔
      IsNormal (⟨T.lower, OpenBundle.classify T.top L⟩ :
          LabObj m (Tower P m) (LabOneTruss C)) ∧
        IsNormal (⟨T.top, L⟩ :
          LabObj 1 (OpenBundle (towerTot P m T.lower).carrier) C) :=
  succ_isNormal_iff T L

/-- `N05`, `cons:draft-recursive-normalisation` — the recursion itself: for every labelled
tower it produces a labelled tower and a morphism into it, and that morphism is
normalising. -/
theorem w_N05 (T : Tower P m) (L : (towerTot P m T).carrier ⥤ C) :
    IsNormalising (towerNormalise P m T L).2 :=
  towerNormalise_isNormalising P m T L

/-- `N06`, existence — every labelled tower admits a normalising morphism. -/
theorem w_N06exist (T : Tower P m) (L : (towerTot P m T).carrier ⥤ C) :
    ∃ (D : LabObj m (Tower P m) C) (r : (⟨T, L⟩ : LabObj m (Tower P m) C) ⟶ D),
      IsNormalising r :=
  exists_isNormalising_tower (P := P) (m := m) (T := T) (L := L)

/-- `N06`, normality of the target — the tower the recursion produces is normal. -/
theorem w_N06normal (T : Tower P m) (L : (towerTot P m T).carrier ⥤ C) :
    IsNormal (towerNormalise P m T L).1 :=
  towerNormalise_target_isNormal (T := T) (L := L)

/-- `N06`, the universal property — the normalisation is terminal among coarsenings: every
coarsening out of `(T,L)` factors through it, uniquely and by a coarsening. -/
theorem w_N06universal (T : Tower P m) (L : (towerTot P m T).carrier ⥤ C)
    (D : LabObj m (Tower P m) C) (R : (⟨T, L⟩ : LabObj m (Tower P m) C) ⟶ D)
    (hR : IsCoarsening R.1) :
    ∃! H : D ⟶ (towerNormalise P m T L).1,
      IsCoarsening H.1 ∧ R ≫ H = (towerNormalise P m T L).2 :=
  towerNormalise_universal (T := T) (L := L) D R hR

end Section55Audit

/-! ### Current chapter additions, reviewed 3 November 2026 -/

section CurrentPoset

variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]

/-- Current `lem:draft-poset-coarsening-basics` (1): object and arrow surjectivity. -/
theorem w_current_poset_surjective {q : P →o Q} (hq : IsPosetCoarsening q) :
    Function.Surjective q ∧ Function.Surjective (Arr.map q) :=
  ⟨hq.surjective, hq.arr_surjective⟩

/-- Current clause (3), in its stronger form requiring only openness. -/
theorem w_current_open_chain {q : P →o Q} (hq : IsOpenPosetMap q) {n : ℕ}
    (y : Fin (n + 1) → Q) (hy : Monotone y) (last : P)
    (hlast : q last = y (Fin.last n)) :
    ∃ x : Fin (n + 1) → P, Monotone x ∧ x (Fin.last n) = last ∧ ∀ i, q (x i) = y i :=
  hq.exists_monotone_lift y hy last hlast

/-- Current clause (3): every finite chain lifts with its prescribed final element. -/
theorem w_current_coarsening_chain {q : P →o Q} (hq : IsPosetCoarsening q) {n : ℕ}
    (y : Fin (n + 1) → Q) (hy : Monotone y) (last : P)
    (hlast : q last = y (Fin.last n)) :
    ∃ x : Fin (n + 1) → P, Monotone x ∧ x (Fin.last n) = last ∧ ∀ i, q (x i) = y i :=
  hq.exists_monotone_lift y hy last hlast

end CurrentPoset

section CurrentLabelledOutgoing

variable {n : ℕ} {K : Type u} [Category.{v} K] [TrussLike.{u, v, w} n K]
variable {C : Type u₂} [Category.{v₂} C] {A : LabObj n K C}

/-- Forgetting the uniquely descended target label is injective. -/
theorem w_current_forget_injective :
    Function.Injective (fun r : LabOutCoarse A =>
      (⟨r.tgt.obj, r.map.1, r.isCoarsening⟩ : OutCoarse A.obj)) :=
  LabOutCoarse.forgetObj_injective

/-- The labelled factorisation order is the structural factorisation order. -/
theorem w_current_labelled_mediator (r q : LabOutCoarse A) :
    Nonempty (r ⟶ q) ↔
      ∃ h : r.tgt.obj ⟶ q.tgt.obj, IsCoarsening h ∧ q.map.1 = r.map.1 ≫ h :=
  LabOutCoarse.nonempty_hom_iff r q

end CurrentLabelledOutgoing

section CurrentOneTrussOrder

variable {C : Type u} [Category.{v} C]

/-- `prop:draft-labelled-outcoarse-1-truss-poset-iso`, as a literal order isomorphism. -/
noncomputable def w_current_labelled_truss_iso (A : LabObj 1 OpenTruss C) :
    OpenTruss.LabOutCoarsePoset A ≃o
      {U : Finset (Fin A.obj.numSing) // NonTriv A.obj A.label ⊆ U}ᵒᵈ :=
  OpenTruss.labelledRetOrderIso A

/-- The source order of the labelled one-truss isomorphism is labelled factorisation. -/
theorem w_current_labelled_truss_order (A : LabObj 1 OpenTruss C)
    (r q : OpenTruss.LabOutCoarsePoset A) :
    r ≤ q ↔ Nonempty (r.out ⟶ q.out) := OpenTruss.LabOutCoarsePoset.le_iff r q

/-- The labelled one-truss map is the restriction of the unlabelled retained-set map. -/
theorem w_current_labelled_truss_restriction (A : LabObj 1 OpenTruss C)
    (r : OpenTruss.LabOutCoarsePoset A) :
    (OrderDual.ofDual (OpenTruss.labelledRetOrderIso A r)).val =
      OrderDual.ofDual (OpenTruss.retOrderIso A.obj
        (OpenTruss.OutCoarsePoset.of r.out.forgetObj)) :=
  OpenTruss.labelledRetOrderIso_forget A r

end CurrentOneTrussOrder

section CurrentBundleOrder

variable {B : Type u} [PartialOrder B] [Finite B]
variable {C : Type v} [Category.{w} C]

/-- Equality of retained families determines the actual outgoing coarsening. -/
theorem w_current_bundle_ext {A : OpenBundle B} {r s : OutCoarse A}
    (h : OpenBundle.retFinset r.map = OpenBundle.retFinset s.map) : r = s :=
  OpenBundle.outCoarse_ext h

omit [Finite B] in
/-- The two presentations of family inclusion agree. -/
theorem w_current_bundle_retained_le {A Y Z : OpenBundle B} (r : A ⟶ Y) (q : A ⟶ Z) :
    OpenBundle.retFinset q ≤ OpenBundle.retFinset r ↔
      OpenBundle.retFam q ≤ OpenBundle.retFam r := OpenBundle.retFinset_le_iff r q

/-- `prop:draft-outcoarse-1-bundle-poset-iso`, as a literal order isomorphism. -/
noncomputable def w_current_bundle_iso (A : OpenBundle B) :
    OpenBundle.OutCoarsePoset A ≃o
      {U : ∀ b : B, Finset (Fin (A.fib b).numSing) // A.IsForwardStableFam U}ᵒᵈ :=
  OpenBundle.retOrderIso A

/-- The unlabelled bundle order is mediating-coarsening existence. -/
theorem w_current_bundle_order (A : OpenBundle B) (r q : OpenBundle.OutCoarsePoset A) :
    r ≤ q ↔ ∃ h : r.out.tgt ⟶ q.out.tgt,
      IsCoarsening h ∧ q.out.map = r.out.map ≫ h := OpenBundle.OutCoarsePoset.le_iff r q

/-- The bundle classification maps a coarsening to its actual retained family. -/
theorem w_current_bundle_iso_apply (A : OpenBundle B) (r : OpenBundle.OutCoarsePoset A) :
    (OrderDual.ofDual (OpenBundle.retOrderIso A r)).val = OpenBundle.retFinset r.out.map :=
  OpenBundle.retOrderIso_apply A r

/-- Its inverse is the actual canonical quotient map. -/
theorem w_current_bundle_iso_symm (A : OpenBundle B)
    (U : (OpenBundle.StableRetainedFamily A)ᵒᵈ) :
    ((OpenBundle.retOrderIso A).symm U).out.map =
      A.quotientMap (OrderDual.ofDual U).val (OrderDual.ofDual U).property :=
  OpenBundle.retOrderIso_symm_map A U

/-- Non-trivial labels are retained by a labelled bundle coarsening. -/
theorem w_current_bundle_nontriv (A : LabObj 1 (OpenBundle B) C) (r : LabOutCoarse A) :
    A.obj.nonTrivFam A.label ≤ fun b => (↑(OpenBundle.retFinset r.map.1 b) : Set _) :=
  OpenBundle.nonTrivFam_le_retFinset r

/-- `prop:draft-labelled-outcoarse-1-bundle-poset-iso`, with the inclusion bound explicit. -/
noncomputable def w_current_labelled_bundle_iso (A : LabObj 1 (OpenBundle B) C) :
    OpenBundle.LabOutCoarsePoset A ≃o
      {U : OpenBundle.StableRetainedFamily A.obj //
        A.obj.nonTrivFam A.label ≤ fun b =>
          (↑(U.val b) : Set (Fin (A.obj.fib b).numSing))}ᵒᵈ :=
  OpenBundle.labelledRetOrderIso A

/-- The labelled bundle order is labelled factorisation. -/
theorem w_current_labelled_bundle_order (A : LabObj 1 (OpenBundle B) C)
    (r q : OpenBundle.LabOutCoarsePoset A) :
    r ≤ q ↔ Nonempty (r.out ⟶ q.out) := OpenBundle.LabOutCoarsePoset.le_iff r q

/-- The labelled bundle map restricts the unlabelled retained-family map. -/
theorem w_current_labelled_bundle_restriction (A : LabObj 1 (OpenBundle B) C)
    (r : OpenBundle.LabOutCoarsePoset A) :
    (OrderDual.ofDual (OpenBundle.labelledRetOrderIso A r)).val =
      OrderDual.ofDual (OpenBundle.retOrderIso A.obj
        (OpenBundle.OutCoarsePoset.of r.out.forgetObj)) :=
  OpenBundle.labelledRetOrderIso_forget A r

end CurrentBundleOrder

section CurrentLayerNormality

variable {P : FPoset.{u}} {C : Type v} [Category.{v} C]

/-- The alternative layer predicate's successor clause, with all labels explicit. -/
theorem w_current_layers_succ {n : ℕ} (T : Tower P (n + 1))
    (L : (towerTot P (n + 1) T).carrier ⥤ C) :
    HasNormalLayers (n + 1) T L ↔
      IsNormal (⟨T.top, L⟩ : LabObj 1 (OpenBundle (towerTot P n T.lower).carrier) C) ∧
      IsNormal (⟨T.lower, OpenBundle.classify T.top L⟩ :
        LabObj n (Tower P n) (LabOneTruss C)) ∧
      HasNormalLayers n T.lower (OpenBundle.classify T.top L) := Iff.rfl

/-- The iterated normality criterion; this does not state arbitrary middle-block normality. -/
theorem w_current_layer_normality {n : ℕ} (T : Tower P n)
    (L : (towerTot P n T).carrier ⥤ C) :
    IsNormal (⟨T, L⟩ : LabObj n (Tower P n) C) ↔ HasNormalLayers n T L :=
  isNormal_iff_hasNormalLayers n T L

/-- The forward consequence exposes all individual layers and classified lower prefixes. -/
theorem w_current_normal_layers {n : ℕ} (T : Tower P n)
    (L : (towerTot P n T).carrier ⥤ C)
    (h : IsNormal (⟨T, L⟩ : LabObj n (Tower P n) C)) : HasNormalLayers n T L :=
  h.hasNormalLayers

/-- Normality splits across an arbitrary cut, in both directions and in every label category. -/
theorem w_current_blocks_iff (k j : ℕ) (T : Tower P (k + j))
    (L : (towerTot P (k + j) T).carrier ⥤ C) :
    letI := (iterLab C j).2
    IsNormal (⟨T, L⟩ : LabObj (k + j) (Tower P (k + j)) C) ↔
      IsNormal (⟨Tower.suffix k j T, Tower.suffixLabel k j T L⟩ :
        LabObj j (Tower (towerTot P k (Tower.prefix k j T)) j) C) ∧
      IsNormal (⟨Tower.prefix k j T,
        towerClassify (Tower.suffix k j T) (Tower.suffixLabel k j T L)⟩ :
        LabObj k (Tower P k) (iterLab C j).1) :=
  isNormal_iff_blocks k j T L

/-- `cor:draft-layer-normality`: the literal middle tower and lower classified tower.
Both height and category transports are explicit; all zero heights are in scope. -/
theorem w_current_middle_block_normality {n : ℕ} (T : Tower P n)
    (L : (towerTot P n T).carrier ⥤ C) (j k : ℕ) (hjk : j + k ≤ n)
    (hN : IsNormal (⟨T, L⟩ : LabObj n (Tower P n) C)) :
    let r := n - j - k
    let hheight : n = (k + j) + r := by omega
    let T' := Tower.castHeight hheight T
    let L' := Tower.castHeightLabel hheight T L
    let S := Tower.prefix (k + j) r T'
    letI := (iterLab C r).2
    let U := towerClassify (Tower.suffix (k + j) r T')
      (Tower.suffixLabel (k + j) r T' L')
    let T_low := Tower.prefix k j S
    let M := Tower.suffix k j S
    let U_M := Tower.suffixLabel k j S U
    letI := (iterLab C (n - k)).2
    letI := (@iterLab (iterLab C r).1 (iterLab C r).2 j).2
    let hCategory : @iterLab (iterLab C r).1 (iterLab C r).2 j = iterLab C (n - k) :=
      (iterLab_add C r j).trans (congrArg (iterLab C) (by omega))
    let V := (towerClassify M U_M).comp (categoryTransport hCategory)
    IsNormal (⟨M, U_M⟩ : LabObj j (Tower (towerTot P k T_low) j) (iterLab C r).1) ∧
      IsNormal (⟨T_low, V⟩ : LabObj k (Tower P k) (iterLab C (n - k)).1) :=
  normality_of_tower_layers T L j k hjk hN

end CurrentLayerNormality

/-!
## Specific source correspondence still missing

The arbitrary middle-block normality statement (`cor:draft-layer-normality`) is
restated by `w_current_middle_block_normality`, including explicit category transports.
The cross-framework comparison (`rem:draft-normalisation-comparison`) has no witness.
The coordinate tower results still lack the intrinsic Chapter 2 object/map comparison.
See `plan/CurrentChapterCoverage.md` for the current per-label correspondence; the
September coverage ledger is a historical snapshot.
-/

end Truss.Transfer.Audit
