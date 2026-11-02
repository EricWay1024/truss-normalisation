/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.CoCylBij
import Truss.Transfer.Normalisation.OneTruss
import Truss.Transfer.Normalisation.OneTrussNorm
import Truss.Transfer.Normalisation.BundleRetract
import Truss.Transfer.Normalisation.Section54
import Truss.Transfer.Normalisation.Section55
import Truss.Transfer.Normalisation.StrictReps
import Truss.Transfer.Normalisation.RecursiveNorm
import Truss.Transfer.Normalisation.Successor
import Truss.Transfer.Normalisation.Terminality

/-!
# The draft normalisation chapter — public re-export

This is the public entry point for the `Truss.Transfer` formalisation of the author's active
draft normalisation chapter.  It contains no declarations of its own: it is a re-export, as
[`plan/DraftNormalisationVerification.md`](../../plan/DraftNormalisationVerification.md) §7
specifies.

**Current coverage: §5.1, §5.2, §5.3, §5.4 and §5.5 are complete** — every statement of the
draft chapter is proved, with no `sorry` and no chapter-specific axiom.  The chapter's
**standing convention is a theorem** here, not a postulate: see `StrictReps.lean`.  The
fibrewise characterisation that §5.4 and §5.5 are stated against is discharged
unconditionally in `Section54.lean` and `Section55.lean`, so no result below carries it as
a hypothesis.

Existence theorems **are** asserted, and proved: `normaliseMap_isNormalising` for labelled
open 1-trusses (§5.3) and `bundleNormaliseMap_isNormalising'` for labelled fibrewise-open
1-truss bundles over a finite poset (§5.4).  See
[`plan/DraftNormalisationCoverage.md`](../../plan/DraftNormalisationCoverage.md).
-/
