/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Normalisation.CoCylBij
import Truss.Transfer.Normalisation.OneTruss
import Truss.Transfer.Normalisation.OneTrussOrder
import Truss.Transfer.Normalisation.BundleOrder
import Truss.Transfer.Normalisation.Section54
import Truss.Transfer.Normalisation.Section55
import Truss.Transfer.Normalisation.StrictReps
import Truss.Transfer.Normalisation.LayerNormality
import Truss.Transfer.Normalisation.TowerBlocks
import Truss.Transfer.Normalisation.IteratedClassifier
import Truss.Transfer.Normalisation.BlockNormality
import Truss.Transfer.Normalisation.SuccNormalisingDirect
import Truss.Transfer.Normalisation.NoAutIteration
import Truss.Transfer.Normalisation.Successor
import Truss.Transfer.Normalisation.Terminality

/-!
# The draft normalisation chapter — public re-export

This is the public entry point for the `Truss.Transfer` formalisation of the author's active
draft normalisation chapter.  It contains no declarations of its own: it is a re-export, as
[`plan/DraftNormalisationVerification.md`](../../plan/DraftNormalisationVerification.md) §7
specifies.

The retained-set and retained-family order isomorphisms, the reflection, the successor
criteria, arbitrary middle-block normality and recursive correctness are exported here.
Current per-label correspondence is recorded in `plan/CurrentChapterCoverage.md`.
The cross-framework comparison remark and the bridge from coordinate towers to all
intrinsic Chapter 2 objects/maps are not supplied by these modules.

Existence theorems **are** asserted, and proved: `normaliseMap_isNormalising` for labelled
open 1-trusses (§5.3) and `bundleNormaliseMap_isNormalising'` for labelled fibrewise-open
1-truss bundles over a finite poset (§5.4).  See
[`plan/DraftNormalisationCoverage.md`](../../plan/DraftNormalisationCoverage.md).
-/
