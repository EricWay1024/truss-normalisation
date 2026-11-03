/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.LabBordism
import Truss.Transfer.Normalisation.NoAut

/-!
# The chapter's standing convention, realised

The draft normalisation chapter opens with a `Standing label convention`.  Stripped of its
motivation, it asserts three things about the chosen representatives:

1. every labelled bundle **is** the canonical totalisation of its classifying functor;
2. `π^n_(P,C)(F ∘ f) = f^* π^n_(B,C)(F)` as labelled bundles;
3. if `F = F' ∘ p` then `(A,L) = p^*(A',L')`, where `(A,L) := π_B(F)` and `(A',L') := π_(B')(F')`.

The chapter adds: *"This is a strict choice of representatives, not an additional
mathematical assertion."*  In the functorial presentation used here that is literally true —
all three are **theorems**, and (2) and (3) hold by `rfl`, because `f^*` *is* precomposition.
Nothing is postulated.

The convention's remaining ingredients are a standing hypothesis and a modelling choice, not
assertions: `C` is automorphism-free (`NoAut`, whose consequence for label comparisons is
`labelComparison_unique`), and the chosen models of `B^r(C)` are skeletal.  Here `B^r(C)` is
realised as the `r`-fold iterate of `LabOneTruss`, and no separate skeletality assumption is
needed: `OpenTruss` is already skeletal (`OpenTruss.skeletal`), and bordisms are determined by
their singular functions.

## Main results

* `strictRep_totalise_classify` — clause (1).
* `strictRep_pullback` — clause (2).
* `strictRep_factor` — clause (3).
* `strictRep_classify_totalise` — the other round trip, so the correspondence is a bijection.
-/

universe u v

namespace Truss.Transfer

open CategoryTheory

variable {C : Type v} [Category.{v} C]
variable {P P' : Type v} [PartialOrder P] [PartialOrder P']

/-- **Standing convention, clause (1).**  *"Every labelled bundle is represented by the
canonical totalisation of its classifying functor."*  Here that is an equality, not a choice:
`π ∘ χ = id`. -/
theorem strictRep_totalise_classify (A : OpenBundle P) (L : A.Tot ⥤ C) :
    totalise (OpenBundle.classify A L) = ⟨A, L⟩ := totalise_classify A L

/-- The other round trip, `χ ∘ π = id`, so classification and totalisation are mutually
inverse **on the nose** rather than quasi-inverse. -/
theorem strictRep_classify_totalise (F : P ⥤ LabOneTruss C) :
    OpenBundle.classify (totalise F).1 (totalise F).2 = F := classify_totalise F

/-- **Standing convention, clause (2).**  *"`π_(P,C)(F ∘ f) = f^* π_(B,C)(F)` as labelled
bundles."*  In the functorial presentation `f^*` is precomposition, so this holds by `rfl`. -/
theorem strictRep_pullback (f : P' →o P) (F : P ⥤ LabOneTruss C) :
    totalise (posetFunctor f ⋙ F)
      = ⟨reindexBundle f (totalise F).1,
         posetFunctor (reindexTilde f (totalise F).1) ⋙ (totalise F).2⟩ := rfl

/-- **Standing convention, clause (3).**  *"If `F = F' ∘ p` then `(A,L) = p^*(A',L')`."*
This is clause (2) read along the factorisation, and is again `rfl`. -/
theorem strictRep_factor (p : P' →o P) (F' : P ⥤ LabOneTruss C) {F : P' ⥤ LabOneTruss C}
    (hF : F = posetFunctor p ⋙ F') :
    totalise F
      = ⟨reindexBundle p (totalise F').1,
         posetFunctor (reindexTilde p (totalise F').1) ⋙ (totalise F').2⟩ := by
  subst hF; rfl

/-- The same three clauses, packaged: the chapter's convention is a theorem. -/
theorem standingConvention :
    (∀ (A : OpenBundle P) (L : A.Tot ⥤ C), totalise (OpenBundle.classify A L) = ⟨A, L⟩) ∧
      (∀ F : P ⥤ LabOneTruss C, OpenBundle.classify (totalise F).1 (totalise F).2 = F) ∧
      (∀ (f : P' →o P) (F : P ⥤ LabOneTruss C),
        totalise (posetFunctor f ⋙ F)
          = ⟨reindexBundle f (totalise F).1,
             posetFunctor (reindexTilde f (totalise F).1) ⋙ (totalise F).2⟩) :=
  ⟨strictRep_totalise_classify, strictRep_classify_totalise, strictRep_pullback⟩

/-! ### Iterated label categories

`B^r(C)` is the `r`-fold iterate of the labelled-1-truss construction, and the chapter states
the convention for every `r`.  No separate argument is needed here: every result above is
stated for an **arbitrary** label category `C`, so each applies verbatim with
`LabOneTruss (LabOneTruss (… C …))` in place of `C`.  In particular clause (2) holds at every
level, which is what §5.5's recursion consumes — it recurses "simultaneously for all
automorphism-free label categories", and the results above are simultaneous in exactly that
sense.

The convention's two remaining ingredients are not assertions and are not discharged here:
`C` is automorphism-free (a standing hypothesis; its consequence for label comparisons is
`labelComparison_unique`), and the chosen models are skeletal (a modelling choice, already
true of `OpenTruss` by `OpenTruss.skeletal`).  `prop:noaut-iteration` is proved for this
model in `NoAutIteration.lean` (`noAut_labOneTruss`, `noAut_iterLab`). -/

end Truss.Transfer
