/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.RecursiveNorm
import Truss.Transfer.Normalisation.OneTrussNorm
import Truss.Transfer.Audit.OpenTrussProbe
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.Tactic.FinCases
import Mathlib.CategoryTheory.SingleObj

/-!
# Concrete non-vacuity probes for reflection-based normalisation (§5.4–§5.5)

Bounded examples for the reflection-based normalisation of labelled open `n`-truss bundles
(`succ_isNormal_iff`, `towerNormalise`, `towerNormalise_isNormalising`).  They certify
nothing universal; they show that the theorems are not vacuous, that both normal and
non-normal objects occur, and that the recursion's output behaves as the mathematics
predicts on small inputs.  Every hypothesis (openness of the trusses, the bundle laws,
functoriality of the labels, the coarsening property of the witnesses) is proved, not
assumed.  Face-order convention: regular cells lie *below* singular cells, so label arrows
run regular → singular.

Throughout, `[3] = reg < sing > reg` is `Truss.Transfer.Audit.iv` and `[1]` is
`Truss.Transfer.Audit.pt`.  At height one, `isNormal_towerOf_iff` combines
`succ_isNormal_iff`, `isNormal_zero` and the §5.4 criterion
`OpenBundle.isNormal_iff_sing_eq_closure'`: normality is "every singular cell lies in the
forward-stable closure of the non-trivially labelled family".

## Probes

* **(A) Removable identity.**  The constant `[3]`-bundle over a point, labelled constantly in
  `Discrete PUnit`.  `not_isNormal_A_criterion` (via the criterion) and `not_isNormal_A`
  (via an explicit labelled coarsening `collapseLab` to `[1]`, which cannot be invertible
  because it identifies the two regular cells).  `towerNormalise_A_not_injective`: the
  normalising coarsening built by the recursion is not injective on total posets.
* **(B) A parallel-pair label keeps the singular cell.**  The same bundle labelled in the
  gaunt category `WalkingParallelPair`, the two incoming arrows of the singular cell going to
  the parallel arrows `left` and `right` (`labB_map_low`, `labB_map_high`).  `isNormal_B`,
  and `towerNormalise_B_bijective`: the recursion's output is a bijection on total posets.
  Here the object labels of the two ends already differ (`zero ≠ one`).
* **(B') An arrow-only label.**  The same bundle labelled in the one-object category of the
  idempotent monoid `{1, e}` (gaunt: `Idem.eq_one_of_mul_eq_one`; not thin).  All object
  labels agree; only the arrows are non-identity.  `isNormal_B'`.
* **(C) Cross-fibre forcing.**  The constant `[3]`-bundle over the chain `0 < 1` (identity
  bordism over `0 ≤ 1`), labelled in the poset `Fin 2`.
  - `labC1`: non-trivial over `0`, constant over `1`.  The fibre over `1` alone is not normal
    (`not_isNormal_C1_fibre_one`, §5.3), its singular cell is trivially labelled
    (`s0_not_mem_nonTrivFam_C1_one`), yet it lies in the forward-stable closure
    (`s0_mem_nonTrivClosure_C1_one`), and the bundle is normal (`isNormal_C1`).
  - `labC2`: the reverse arrangement.  Closure only transports forwards, so nothing forces
    the cell over `0` (`s0_not_mem_nonTrivClosure_C2_zero`) and the bundle is not normal
    (`not_isNormal_C2`).
* **(D) Height two.**  `towA` with the constant `[3]`-bundle appended over `Tot(towA)`,
  labelled by the parallel-pair label of the top fibre coordinate only.  The top labelled
  1-truss bundle is normal (`isNormal_D_top`), yet the tower is not (`not_isNormal_D`,
  witnessed by lifting the lower collapse).  By `succ_isNormal_iff` the obstruction is the
  lower level labelled in `LabOneTruss WalkingParallelPair` by the classifier
  (`not_isNormal_D_lower`), and the recursion collapses it
  (`towerNormalise_D_not_injective`).
-/

namespace Truss.Transfer.Audit.ReflectionExamples

open CategoryTheory CategoryTheory.Limits Geometry TrussLike

/-- The one-point base poset. -/
abbrev P1 : FPoset.{0} := ⟨Fin 1⟩

/-- The two-element chain `0 < 1`. -/
abbrev P2 : FPoset.{0} := ⟨Fin 2⟩

/-- The constant bundle with fibre `F` over `B`. -/
def constBundle (B : Type) [PartialOrder B] (F : OpenTruss) : OpenBundle B where
  fib _ := F
  arr _ := idBord F.toOneTruss
  arr_id _ _ _ := Iff.rfl
  arr_comp _ _ x _ := ⟨fun h => ⟨x, le_rfl, h⟩, fun ⟨_, h1, h2⟩ => le_trans h1 h2⟩

/-- The height-one tower over `B` with final bundle `A`. -/
def towerOf (B : FPoset.{0}) (A : OpenBundle B.carrier) : Tower B 1 :=
  Tower.succ (P := B) (n := 0) PUnit.unit A

/-- Normality at height one is §5.4 normality of the final bundle. -/
theorem isNormal_towerOf_iff (B : FPoset.{0}) (A : OpenBundle B.carrier) {C : Type}
    [Category.{0} C] (L : A.Tot ⥤ C) :
    IsNormal (⟨towerOf B A, L⟩ : LabObj 1 (Tower B 1) C) ↔
      (fun b => (Set.univ : Set (Fin (A.fib b).numSing))) = A.nonTrivClosure L := by
  rw [succ_isNormal_iff]
  exact (and_iff_right (isNormal_zero _ _)).trans (OpenBundle.isNormal_iff_sing_eq_closure' A L)

/-- `[3]` has exactly one singular cell. -/
theorem iv_numSing : iv.numSing = 1 := rfl

/-- The singular-cell index `0` of `[3]`. -/
def s0 : Fin iv.numSing := ⟨0, by decide⟩

/-- The singular-cell index set of `[3]` is the singleton `{s0}`. -/
theorem eq_s0 (i : Fin iv.numSing) : i = s0 := by
  have h : i.val < 1 := i.isLt
  exact Fin.ext (by change i.val = 0; omega)

/-! ### (A) Removable identity -/

/-- (A) The constant `[3]`-bundle over the point. -/
def bunA : OpenBundle (Fin 1) := constBundle (Fin 1) iv

/-- (A) The height-one tower of `bunA`. -/
def towA : Tower P1 1 := towerOf P1 bunA

/-- (A) The constant label into the one-object category. -/
def labA : bunA.Tot ⥤ Discrete PUnit.{1} := (Functor.const _).obj ⟨PUnit.unit⟩

/-- Every arrow is identity-labelled by a label into `Discrete PUnit.{1}`. -/
theorem isIdLabelled_discrete {T : OpenTruss} (L : Tot T ⥤ Discrete PUnit.{1})
    {x y : T.toOneTruss.El} (h : x ≤ y) : IsIdLabelled L h :=
  ⟨Discrete.ext (Subsingleton.elim _ _), Subsingleton.elim _ _⟩

/-- (A) The singular cell of the fibre is not in the closure of the non-trivial family. -/
theorem s0_not_mem_closure_A : s0 ∉ bunA.nonTrivClosure labA 0 := by
  rintro ⟨a, -, x, hx, -⟩
  exact OpenBundle.mem_nonTrivFam.1 hx
    ⟨isIdLabelled_discrete _ _, isIdLabelled_discrete _ _⟩

/-- **(A), via the §5.4 criterion.**  The constant-labelled `[3]` over a point is not normal. -/
theorem not_isNormal_A_criterion :
    ¬ IsNormal (⟨towA, labA⟩ : LabObj 1 (Tower P1 1) (Discrete PUnit.{1})) := by
  intro h
  have h' := congrFun ((isNormal_towerOf_iff P1 bunA labA).1 h) 0
  have hs : s0 ∈ bunA.nonTrivClosure labA 0 := h' ▸ Set.mem_univ s0
  exact s0_not_mem_closure_A hs

/-- (A) The constant `[1]`-bundle over the point, the collapse target. -/
def bunPt : OpenBundle (Fin 1) := constBundle (Fin 1) pt

/-- (A) The height-one tower of `bunPt`. -/
def towPt : Tower P1 1 := towerOf P1 bunPt

/-- (A) The constant label on the collapse target. -/
def labPt : bunPt.Tot ⥤ Discrete PUnit.{1} := (Functor.const _).obj ⟨PUnit.unit⟩

/-- (A) The fibrewise collapse `[3] → [1]`, as a bundle map. -/
def collapseTop : BundleMap bunA bunPt where
  fibMap _ := collapse
  face := fun {_ _} _ {_ _} _ => le_rfl

/-- (A) The collapse as a map of height-one towers: identity below, `collapseTop` on top. -/
def collapseTower : towA ⟶ towPt :=
  TowerMap.succ (P := P1) (n := 0) (TowerMap.id towA.lower) collapseTop

/-- (A) The collapse as a labelled map. -/
def collapseLab : (⟨towA, labA⟩ : LabObj 1 (Tower P1 1) (Discrete PUnit.{1})) ⟶
    ⟨towPt, labPt⟩ := ⟨collapseTower, rfl⟩

/-- (A) The collapse is a genuine coarsening of towers. -/
theorem collapseTower_isCoarsening : IsCoarsening collapseTower :=
  isCoarsening_of_parts collapseTower (IsCoarsening.id _)
    (OpenBundle.isCoarsening_of_fibrewise collapseTop fun _ => collapse_isCoarsening)

/-- The lower regular cell of the fibre of `towA`. -/
def x0 : (towerTot P1 1 towA).carrier := (⟨(0 : Fin 1), OneTruss.ofIdx 0⟩ : bunA.Tot)

/-- The upper regular cell of the fibre of `towA`. -/
def x2 : (towerTot P1 1 towA).carrier := (⟨(0 : Fin 1), OneTruss.ofIdx 2⟩ : bunA.Tot)

/-- The two regular cells are distinct. -/
theorem x0_ne_x2 : x0 ≠ x2 := by
  intro h
  have := congrArg (fun p : (towerTot P1 1 towA).carrier => (OneTruss.idx p.2).val) h
  exact absurd this (by decide)

/-- The collapse identifies the two regular cells. -/
theorem collapse_x0_x2 : totMap collapseTower x0 = totMap collapseTower x2 := rfl

/-- **(A), via a witness.**  The constant-labelled `[3]` over a point is not normal: the
collapse to `[1]` is a labelled coarsening, and it cannot be invertible because it identifies
the two regular cells. -/
theorem not_isNormal_A :
    ¬ IsNormal (⟨towA, labA⟩ : LabObj 1 (Tower P1 1) (Discrete PUnit.{1})) := by
  intro h
  obtain ⟨p, -, hqp, -⟩ := h.isIso_of_isCoarsening (q := collapseLab) collapseTower_isCoarsening
  have hid : ∀ x, totMap p.1 (totMap collapseTower x) = x := by
    intro x
    have := congrArg (fun k => totMap (k.1 : towA ⟶ towA) x) hqp
    simpa [LabObj.comp_coe, totMap_comp] using this
  exact x0_ne_x2 ((hid x0).symm.trans ((congrArg _ collapse_x0_x2).trans (hid x2)))

/-- **(A), the recursion really collapses.**  The total map of the normalising coarsening
returned by `towerNormalise` is not injective: it factors through the collapse. -/
theorem towerNormalise_A_not_injective :
    ¬ Function.Injective (totMap (towerNormalise P1 1 towA labA).2.1) := by
  intro hinj
  obtain ⟨m, -, hm⟩ := (towerNormalise_isNormalising P1 1 towA labA).exists_mediator
    collapseLab collapseTower_isCoarsening
  have hfac : ∀ x, totMap (towerNormalise P1 1 towA labA).2.1 x
      = totMap m.1 (totMap collapseTower x) := by
    intro x
    rw [hm, LabObj.comp_coe, totMap_comp]
    rfl
  exact x0_ne_x2 (hinj ((hfac x0).trans ((congrArg _ collapse_x0_x2).trans (hfac x2).symm)))

/-! ### (B) A parallel-arrow label keeps the singular cell -/

/-- (B) Object part of the label on `[3]`: the singular cell `1` goes to `one`, the regular
cells to `zero`. -/
def wppObj : Fin 3 → WalkingParallelPair
  | 1 => .one
  | _ => .zero

/-- A non-comparison in the face order of `[3]`: two distinct cells neither of which is
the singular cell `1` above a regular one. -/
theorem iv_not_le {x y : Fin 3} (h : x ≠ y ∧ (y = 1 → x = 1)) :
    ¬ @LE.le iv.toOneTruss.El _ x y := by
  rintro (hxy | ⟨h1, h2, -⟩)
  · exact h.1 hxy
  · have key : ∀ z : Fin 3, iv.toOneTruss.dim z = 0 → z = 1 := by decide
    have hx : x = 1 := h.2 (key y h2)
    subst hx
    exact absurd h1 (by decide)

/-- (B) Arrow part: the two incoming arrows of the singular cell go to the two parallel
arrows `left` and `right`; identities go to identities. -/
def wppMap : ∀ x y : Fin 3, @LE.le iv.toOneTruss.El _ x y → (wppObj x ⟶ wppObj y)
  | 0, 0, _ => 𝟙 _
  | 1, 1, _ => 𝟙 _
  | 2, 2, _ => 𝟙 _
  | 0, 1, _ => WalkingParallelPairHom.left
  | 2, 1, _ => WalkingParallelPairHom.right
  | 0, 2, h => absurd h (iv_not_le (by decide))
  | 1, 0, h => absurd h (iv_not_le (by decide))
  | 1, 2, h => absurd h (iv_not_le (by decide))
  | 2, 0, h => absurd h (iv_not_le (by decide))

/-- (B) `wppMap` sends identities to identities. -/
theorem wppMap_id : ∀ (x : Fin 3) (h : @LE.le iv.toOneTruss.El _ x x), wppMap x x h = 𝟙 _ := by
  intro x; fin_cases x <;> intro h <;> rfl

/-- (B) `wppMap` is functorial: the only non-identity arrows run into the singular cell, so
every composable pair contains an identity. -/
theorem wppMap_comp : ∀ (x y z : Fin 3) (hxy : @LE.le iv.toOneTruss.El _ x y)
    (hyz : @LE.le iv.toOneTruss.El _ y z) (hxz : @LE.le iv.toOneTruss.El _ x z),
    wppMap x z hxz = wppMap x y hxy ≫ wppMap y z hyz := by
  intro x y z
  fin_cases x <;> fin_cases y <;> fin_cases z <;> intro h1 h2 _ <;>
    first
      | rfl
      | exact absurd h1 (iv_not_le (by decide))
      | exact absurd h2 (iv_not_le (by decide))

/-- A face comparison in the total poset of a constant `[3]`-bundle is a face comparison of
fibre cells. -/
theorem constIv_le {B : Type} [PartialOrder B] {p q : (constBundle B iv).Tot} (h : p ≤ q) :
    @LE.le iv.toOneTruss.El _ p.2 q.2 :=
  h.elim fun _ hr => hr

/-- The parallel-pair label on any constant `[3]`-bundle, depending only on the fibre
coordinate: regular cells to `zero`, the singular cell to `one`, its lower incoming arrow to
`left` and its upper incoming arrow to `right`. -/
def wppLabel (B : Type) [PartialOrder B] : (constBundle B iv).Tot ⥤ WalkingParallelPair where
  obj p := wppObj p.2
  map {p q} h := wppMap p.2 q.2 (constIv_le (leOfHom h))
  map_id p := wppMap_id p.2 _
  map_comp {p q r} f g :=
    wppMap_comp p.2 q.2 r.2 (constIv_le (leOfHom f)) (constIv_le (leOfHom g)) _

/-- (B) The label `Tot(bunA) ⥤ WalkingParallelPair`, the parallel-pair label over the
point. -/
def labB : bunA.Tot ⥤ WalkingParallelPair := wppLabel (Fin 1)

/-- (B) The lower regular neighbour of the singular cell, in `Tot(bunA)`. -/
def pLow : bunA.Tot := ⟨0, iv.regLow rfl s0⟩

/-- (B) The upper regular neighbour of the singular cell, in `Tot(bunA)`. -/
def pHigh : bunA.Tot := ⟨0, iv.regHigh rfl s0⟩

/-- (B) The singular cell, in `Tot(bunA)`. -/
def pSing : bunA.Tot := ⟨0, iv.singEl rfl s0⟩

/-- (B) The lower incoming arrow of the singular cell is labelled `left`. -/
theorem labB_map_low :
    labB.map (homOfLE (show pLow ≤ pSing from ⟨le_rfl, iv.regLow_le_singEl rfl s0⟩))
      = (WalkingParallelPairHom.left : labB.obj pLow ⟶ labB.obj pSing) := rfl

/-- (B) The upper incoming arrow of the singular cell is labelled `right`. -/
theorem labB_map_high :
    labB.map (homOfLE (show pHigh ≤ pSing from ⟨le_rfl, iv.regHigh_le_singEl rfl s0⟩))
      = (WalkingParallelPairHom.right : labB.obj pHigh ⟶ labB.obj pSing) := rfl

/-- (B) The singular cell is non-trivially labelled. -/
theorem s0_mem_nonTrivFam_B : s0 ∈ bunA.nonTrivFam labB 0 := by
  rw [OpenBundle.mem_nonTrivFam]
  rintro ⟨⟨e, -⟩, -⟩
  exact absurd e (by decide)

/-- **(B) The parallel-pair label makes the bundle normal.** -/
theorem isNormal_B : IsNormal (⟨towA, labB⟩ : LabObj 1 (Tower P1 1) WalkingParallelPair) := by
  refine (isNormal_towerOf_iff P1 bunA labB).2 (funext fun b => Set.ext fun i => ?_)
  refine iff_of_true (Set.mem_univ i) ?_
  obtain rfl : b = 0 := Subsingleton.elim _ _
  obtain rfl : i = s0 := eq_s0 _
  exact bunA.singTransport.le_closure _ 0 s0_mem_nonTrivFam_B

/-- **(B) The recursion changes nothing.**  The total map of the normalising coarsening
returned by `towerNormalise` is a bijection. -/
theorem towerNormalise_B_bijective :
    Function.Bijective (totMap (towerNormalise P1 1 towA labB).2.1) := by
  have hq := towerNormalise_isNormalising P1 1 towA labB
  obtain ⟨p, -, hqp, -⟩ := isNormal_B.isIso_of_isCoarsening hq.1
  refine ⟨fun x y hxy => ?_, hq.1.tot.surjective⟩
  have hid : ∀ x, totMap p.1 (totMap (towerNormalise P1 1 towA labB).2.1 x) = x := by
    intro x
    have := congrArg (fun k => totMap (k.1 : towA ⟶ towA) x) hqp
    simpa [LabObj.comp_coe, totMap_comp] using this
  rw [← hid x, hxy, hid y]

/-- The face order of `[3]` in coordinates: equality, or a regular cell below the singular
cell `1`. -/
theorem iv_le_iff (x y : Fin 3) :
    @LE.le iv.toOneTruss.El _ x y ↔ x = y ∨ (y = 1 ∧ x ≠ 1) := by
  constructor
  · rintro (h | ⟨h1, h2, -⟩)
    · exact Or.inl h
    · have key : ∀ z : Fin 3, iv.toOneTruss.dim z = 0 → z = 1 := by decide
      have hy := key y h2
      refine Or.inr ⟨hy, ?_⟩
      rintro rfl
      exact absurd h1 (by decide)
  · rintro (h | ⟨rfl, hx⟩)
    · exact Or.inl h
    · refine Or.inr ⟨?_, by decide, ?_⟩
      · revert hx; revert x; decide
      · revert hx; revert x; decide

/-! ### (B') An arrow-only label into a gaunt one-object category -/

/-- The two-element idempotent monoid `{1, e}` with `e * e = e`.  As a one-object category
it is gaunt (its only invertible element is `1`) and not thin. -/
inductive Idem : Type
  /-- The unit. -/
  | one
  /-- The non-identity idempotent. -/
  | e
  deriving DecidableEq

/-- Multiplication of `Idem`: `1` is a unit and `e * e = e`. -/
def Idem.mul : Idem → Idem → Idem
  | .one, x => x
  | .e, _ => .e

/-- `Idem` is a monoid. -/
instance : Monoid Idem where
  mul := Idem.mul
  one := .one
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl

/-- The only unit of `Idem` is `1`: the category `SingleObj Idem` is gaunt. -/
theorem Idem.eq_one_of_mul_eq_one {a b : Idem} (h : a * b = 1) : a = 1 := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- (B') Arrow part on `[3]`: identities to `1`, both incoming arrows of the singular cell to
the idempotent `e`. -/
def idemVal (x y : Fin 3) : Idem := if x = y then 1 else .e

/-- `idemVal` is functorial along composable face comparisons of `[3]`. -/
theorem idemVal_comp : ∀ x y z : Fin 3, (x = y ∨ (y = 1 ∧ x ≠ 1)) →
    (y = z ∨ (z = 1 ∧ y ≠ 1)) → idemVal x z = idemVal y z * idemVal x y := by decide

/-- (B') The label `Tot(bunA) ⥤ SingleObj Idem`: every cell goes to the unique object; the
two incoming arrows of the singular cell go to the non-identity idempotent `e`.  All object
labels agree, so the non-triviality is carried by arrows alone. -/
def labB' : bunA.Tot ⥤ SingleObj Idem where
  obj _ := SingleObj.star Idem
  map {p q} _ := idemVal p.2 q.2
  map_id p := by change idemVal p.2 p.2 = 1; exact if_pos rfl
  map_comp {p q r} f g :=
    idemVal_comp p.2 q.2 r.2 ((iv_le_iff _ _).1 (constIv_le (leOfHom f)))
      ((iv_le_iff _ _).1 (constIv_le (leOfHom g)))

/-- (B') The singular cell is non-trivially labelled, although its object label agrees with
those of its neighbours. -/
theorem s0_mem_nonTrivFam_B' : s0 ∈ bunA.nonTrivFam labB' 0 := by
  rw [OpenBundle.mem_nonTrivFam]
  rintro ⟨⟨e, he⟩, -⟩
  have key : ∀ e' : SingleObj.star Idem = SingleObj.star Idem, eqToHom e' = (1 : Idem) :=
    fun _ => rfl
  change (Idem.e : Idem) = eqToHom (e : SingleObj.star Idem = SingleObj.star Idem) at he
  rw [key] at he
  exact absurd he (by decide)

/-- **(B') The arrow-only label makes the bundle normal.** -/
theorem isNormal_B' : IsNormal (⟨towA, labB'⟩ : LabObj 1 (Tower P1 1) (SingleObj Idem)) := by
  refine (isNormal_towerOf_iff P1 bunA labB').2 (funext fun b => Set.ext fun i => ?_)
  refine iff_of_true (Set.mem_univ i) ?_
  obtain rfl : b = 0 := Subsingleton.elim _ _
  obtain rfl : i = s0 := eq_s0 _
  exact bunA.singTransport.le_closure _ 0 s0_mem_nonTrivFam_B'

/-! ### (C) Two fibres: retention forced across the base -/

/-- (C) The constant `[3]`-bundle over the chain `0 < 1`: the bordism over `0 ≤ 1` is the
identity bordism, relating corresponding cells. -/
def bunC : OpenBundle (Fin 2) := constBundle (Fin 2) iv

/-- (C) The height-one tower of `bunC`. -/
def towC : Tower P2 1 := towerOf P2 bunC

/-- A face comparison in `Tot(bunC)`, in coordinates. -/
theorem bunC_le_iff {p q : bunC.Tot} :
    p ≤ q ↔ p.1 ≤ q.1 ∧ (@Eq (Fin 3) p.2 q.2 ∨ (@Eq (Fin 3) q.2 1 ∧ ¬ @Eq (Fin 3) p.2 1)) :=
  ⟨fun ⟨h, hr⟩ => ⟨h, (iv_le_iff _ _).1 hr⟩, fun ⟨h, hr⟩ => ⟨h, (iv_le_iff _ _).2 hr⟩⟩

/-- (C, forced) Label values: over `0` the singular cell is `1` and the regular cells `0`;
over `1` everything is `1`. -/
def valC1 (b : Fin 2) (x : Fin 3) : Fin 2 := if b = 1 then 1 else if x = 1 then 1 else 0

/-- (C, reverse) Label values: over `0` everything is `0`; over `1` the singular cell is `1`
and the regular cells `0`. -/
def valC2 (b : Fin 2) (x : Fin 3) : Fin 2 := if b = 0 then 0 else if x = 1 then 1 else 0

/-- `valC1` is monotone for the displayed order. -/
theorem valC1_mono : ∀ b c : Fin 2, ∀ x y : Fin 3, b ≤ c → (x = y ∨ (y = 1 ∧ x ≠ 1)) →
    valC1 b x ≤ valC1 c y := by decide

/-- `valC2` is monotone for the displayed order. -/
theorem valC2_mono : ∀ b c : Fin 2, ∀ x y : Fin 3, b ≤ c → (x = y ∨ (y = 1 ∧ x ≠ 1)) →
    valC2 b x ≤ valC2 c y := by decide

/-- (C, forced) The label `Tot(bunC) ⥤ Fin 2`: non-trivial on the singular cell over `0`,
trivial (constant) over `1`. -/
def labC1 : bunC.Tot ⥤ Fin 2 :=
  Monotone.functor (f := fun p : bunC.Tot => valC1 p.1 p.2) fun _ _ h =>
    valC1_mono _ _ _ _ (bunC_le_iff.1 h).1 (bunC_le_iff.1 h).2

/-- (C, reverse) The label `Tot(bunC) ⥤ Fin 2`: trivial (constant) over `0`, non-trivial on
the singular cell over `1`. -/
def labC2 : bunC.Tot ⥤ Fin 2 :=
  Monotone.functor (f := fun p : bunC.Tot => valC2 p.1 p.2) fun _ _ h =>
    valC2_mono _ _ _ _ (bunC_le_iff.1 h).1 (bunC_le_iff.1 h).2

/-- In a poset label category an arrow is identity-labelled as soon as its endpoint labels
agree. -/
theorem isIdLabelled_of_obj_eq {T : OpenTruss} (L : Tot T ⥤ Fin 2) {x y : T.toOneTruss.El}
    (h : x ≤ y) (e : L.obj x = L.obj y) : IsIdLabelled L h :=
  ⟨e, Subsingleton.elim _ _⟩

/-- (C, forced) Over `0` the singular cell is non-trivially labelled. -/
theorem s0_mem_nonTrivFam_C1_zero : s0 ∈ bunC.nonTrivFam labC1 0 := by
  rw [OpenBundle.mem_nonTrivFam]
  rintro ⟨⟨e, -⟩, -⟩
  exact absurd e (by decide)

/-- (C, forced) Over `1` the singular cell is trivially labelled: fibrewise, it would be
discarded. -/
theorem s0_not_mem_nonTrivFam_C1_one : s0 ∉ bunC.nonTrivFam labC1 1 := by
  rw [OpenBundle.mem_nonTrivFam]
  exact not_not.2 ⟨isIdLabelled_of_obj_eq _ _ rfl, isIdLabelled_of_obj_eq _ _ rfl⟩

/-- **(C, forced) Cross-fibre forcing.**  The trivially-labelled singular cell over `1` lies
in the forward-stable closure: it is the transport of the non-trivial cell over `0`. -/
theorem s0_mem_nonTrivClosure_C1_one : s0 ∈ bunC.nonTrivClosure labC1 1 :=
  ⟨0, Fin.zero_le _, s0, s0_mem_nonTrivFam_C1_zero, eq_s0 _⟩

/-- **(C, forced) The bundle is normal**, although its fibre over `1` is trivially labelled. -/
theorem isNormal_C1 : IsNormal (⟨towC, labC1⟩ : LabObj 1 (Tower P2 1) (Fin 2)) := by
  refine (isNormal_towerOf_iff P2 bunC labC1).2 (funext fun b => Set.ext fun i => ?_)
  refine iff_of_true (Set.mem_univ i) ?_
  obtain rfl : i = s0 := eq_s0 _
  match b with
  | 0 => exact bunC.singTransport.le_closure _ 0 s0_mem_nonTrivFam_C1_zero
  | 1 => exact s0_mem_nonTrivClosure_C1_one

/-- **(C, forced) The fibrewise answer differs.**  The fibre over `1` with its restricted
label, as a labelled open 1-truss on its own, is *not* normal (§5.3). -/
theorem not_isNormal_C1_fibre_one :
    ¬ IsNormal (⟨bunC.fib 1, bunC.restrictLabel labC1 1⟩ : LabObj 1 OpenTruss (Fin 2)) := by
  intro h
  rw [isNormal_iff_nonTriv_eq_univ] at h
  have hs : s0 ∈ nonTrivOf (⟨bunC.fib 1, bunC.restrictLabel labC1 1⟩ :
      LabObj 1 OpenTruss (Fin 2)) := h ▸ Finset.mem_univ s0
  exact s0_not_mem_nonTrivFam_C1_one (OpenBundle.mem_nonTrivFam.2 (mem_nonTriv.1 hs))

/-- (C, reverse) Over `0` the singular cell is trivially labelled. -/
theorem s0_not_mem_nonTrivFam_C2_zero : s0 ∉ bunC.nonTrivFam labC2 0 := by
  rw [OpenBundle.mem_nonTrivFam]
  exact not_not.2 ⟨isIdLabelled_of_obj_eq _ _ rfl, isIdLabelled_of_obj_eq _ _ rfl⟩

/-- (C, reverse) Over `1` the singular cell is non-trivially labelled. -/
theorem s0_mem_nonTrivFam_C2_one : s0 ∈ bunC.nonTrivFam labC2 1 := by
  rw [OpenBundle.mem_nonTrivFam]
  rintro ⟨⟨e, -⟩, -⟩
  exact absurd e (by decide)

/-- (C, reverse) Nothing forces the cell over `0`: closure only transports forwards. -/
theorem s0_not_mem_nonTrivClosure_C2_zero : s0 ∉ bunC.nonTrivClosure labC2 0 := by
  rintro ⟨a, ha, x, hx, -⟩
  obtain rfl : a = 0 := Fin.le_zero_iff'.1 ha
  obtain rfl : x = s0 := eq_s0 _
  exact s0_not_mem_nonTrivFam_C2_zero hx

/-- **(C, reverse) The bundle is not normal**: the non-trivial cell over `1` does not force
retention over `0`. -/
theorem not_isNormal_C2 : ¬ IsNormal (⟨towC, labC2⟩ : LabObj 1 (Tower P2 1) (Fin 2)) := by
  intro h
  have h' := congrFun ((isNormal_towerOf_iff P2 bunC labC2).1 h) 0
  have hs : s0 ∈ bunC.nonTrivClosure labC2 0 := h' ▸ Set.mem_univ s0
  exact s0_not_mem_nonTrivClosure_C2_zero hs

/-! ### (D) Height two: the lower level is labelled in `LabOneTruss C` -/

/-- (D) The constant `[3]`-bundle over `Tot(bunA)`, the second level of the tower. -/
def bunD : OpenBundle bunA.Tot := constBundle bunA.Tot iv

/-- (D) The height-two tower: `towA` with `bunD` appended. -/
def towD : Tower P1 2 := Tower.succ (n := 1) towA bunD

/-- (D) The parallel-pair label on the top level: every top fibre is non-trivially
labelled, and the label ignores the lower coordinate. -/
def labD : bunD.Tot ⥤ WalkingParallelPair := wppLabel bunA.Tot

/-- (D) The collapse target's second level. -/
def bunDpt : OpenBundle bunPt.Tot := constBundle bunPt.Tot iv

/-- (D) The collapse target: `towPt` with `bunDpt` appended. -/
def towDpt : Tower P1 2 := Tower.succ (n := 1) towPt bunDpt

/-- (D) The label on the collapse target. -/
def labDpt : bunDpt.Tot ⥤ WalkingParallelPair := wppLabel bunPt.Tot

/-- (D) The top component of the collapse: the identity on each top fibre. -/
def collapseDTop : BundleMap bunD (OpenBundle.reindex collapseTower.totHom bunDpt) where
  fibMap _ := TrussMap.id _
  face := fun {_ _} _ {_ _} hr => hr

/-- (D) The collapse of the *lower* level, lifted to height two. -/
def collapseD : towD ⟶ towDpt := TowerMap.succ (P := P1) (n := 1) collapseTower collapseDTop

/-- (D) The collapse as a labelled map. -/
def collapseDLab : (⟨towD, labD⟩ : LabObj 2 (Tower P1 2) WalkingParallelPair) ⟶
    ⟨towDpt, labDpt⟩ := ⟨collapseD, rfl⟩

/-- (D) The collapse is a coarsening of height-two towers. -/
theorem collapseD_isCoarsening : IsCoarsening collapseD :=
  isCoarsening_of_parts collapseD collapseTower_isCoarsening
    (OpenBundle.isCoarsening_of_fibrewise collapseDTop fun _ => IsCoarsening.id _)

/-- The singular top cell over the lower regular cell `x0`. -/
def y0 : (towerTot P1 2 towD).carrier := (⟨x0, OneTruss.ofIdx 1⟩ : bunD.Tot)

/-- The singular top cell over the lower regular cell `x2`. -/
def y2 : (towerTot P1 2 towD).carrier := (⟨x2, OneTruss.ofIdx 1⟩ : bunD.Tot)

/-- The two top cells are distinct. -/
theorem y0_ne_y2 : y0 ≠ y2 := fun h =>
  x0_ne_x2 (congrArg (fun p : (towerTot P1 2 towD).carrier => (p.1 : bunA.Tot)) h)

/-- The collapse identifies them. -/
theorem collapseD_y0_y2 : totMap collapseD y0 = totMap collapseD y2 := rfl

/-- **(D) Not normal.**  The height-two tower is not normal: the lower collapse lifts to a
labelled coarsening that identifies two top cells. -/
theorem not_isNormal_D :
    ¬ IsNormal (⟨towD, labD⟩ : LabObj 2 (Tower P1 2) WalkingParallelPair) := by
  intro h
  obtain ⟨p, -, hqp, -⟩ := h.isIso_of_isCoarsening (q := collapseDLab) collapseD_isCoarsening
  have hid : ∀ x, totMap p.1 (totMap collapseD x) = x := by
    intro x
    have := congrArg (fun k => totMap (k.1 : towD ⟶ towD) x) hqp
    simpa [LabObj.comp_coe, totMap_comp] using this
  exact y0_ne_y2 ((hid y0).symm.trans ((congrArg _ collapseD_y0_y2).trans (hid y2)))

/-- (D) Every top fibre's singular cell is non-trivially labelled. -/
theorem s0_mem_nonTrivFam_D (b : bunA.Tot) : s0 ∈ bunD.nonTrivFam labD b := by
  rw [OpenBundle.mem_nonTrivFam]
  rintro ⟨⟨e, -⟩, -⟩
  exact WalkingParallelPair.noConfusion e

/-- **(D) The top labelled 1-truss bundle is normal** (§5.4). -/
theorem isNormal_D_top :
    IsNormal (⟨bunD, labD⟩ : LabObj 1 (OpenBundle bunA.Tot) WalkingParallelPair) := by
  refine (OpenBundle.isNormal_iff_sing_eq_closure' bunD labD).2
    (funext fun b => Set.ext fun i => ?_)
  refine iff_of_true (Set.mem_univ i) ?_
  obtain rfl : i = s0 := eq_s0 _
  exact bunD.singTransport.le_closure _ b (s0_mem_nonTrivFam_D b)

/-- **(D) The obstruction is in the lower level.**  By `succ_isNormal_iff`, the lower tower
labelled by the classifier `χ(bunD, labD) : Tot(bunA) ⥤ LabOneTruss WalkingParallelPair`
is not normal: the classifier labels both incoming arrows of the lower singular cell by
identities of `LabOneTruss`, because the top bundle is constant across them. -/
theorem not_isNormal_D_lower :
    ¬ IsNormal (⟨towA, OpenBundle.classify bunD labD⟩ :
      LabObj 1 (Tower P1 1) (LabOneTruss WalkingParallelPair)) := fun h =>
  not_isNormal_D ((succ_isNormal_iff towD labD).2 ⟨h, isNormal_D_top⟩)

/-- **(D) The recursion collapses the lower level.**  The total map of the normalising
coarsening returned by `towerNormalise` at height two is not injective. -/
theorem towerNormalise_D_not_injective :
    ¬ Function.Injective (totMap (towerNormalise P1 2 towD labD).2.1) := by
  intro hinj
  obtain ⟨m, -, hm⟩ := (towerNormalise_isNormalising P1 2 towD labD).exists_mediator
    collapseDLab collapseD_isCoarsening
  have hfac : ∀ x, totMap (towerNormalise P1 2 towD labD).2.1 x
      = totMap m.1 (totMap collapseD x) := by
    intro x
    rw [hm, LabObj.comp_coe, totMap_comp]
    rfl
  exact y0_ne_y2 (hinj ((hfac y0).trans ((congrArg _ collapseD_y0_y2).trans (hfac y2).symm)))


/-! ### Axiom audit -/

#print axioms isNormal_towerOf_iff
#print axioms not_isNormal_A_criterion
#print axioms not_isNormal_A
#print axioms towerNormalise_A_not_injective
#print axioms labB_map_low
#print axioms labB_map_high
#print axioms isNormal_B
#print axioms towerNormalise_B_bijective
#print axioms Idem.eq_one_of_mul_eq_one
#print axioms s0_mem_nonTrivFam_B'
#print axioms isNormal_B'
#print axioms not_isNormal_C1_fibre_one
#print axioms s0_not_mem_nonTrivFam_C1_one
#print axioms s0_mem_nonTrivClosure_C1_one
#print axioms isNormal_C1
#print axioms s0_not_mem_nonTrivClosure_C2_zero
#print axioms not_isNormal_C2
#print axioms isNormal_D_top
#print axioms not_isNormal_D
#print axioms not_isNormal_D_lower
#print axioms towerNormalise_D_not_injective

end Truss.Transfer.Audit.ReflectionExamples
