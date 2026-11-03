/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Audit.Chapter3
import Truss.Transfer.Audit.NonVacuity
import Truss.Transfer.Audit.OpenTrussProbe
import Truss.Transfer.Audit.Reflection
import Truss.Transfer.Audit.ReflectionBoundary
import Truss.Transfer.Audit.ReflectionExamples

/-!
# Audit modules for the draft normalisation verification — public re-export

Audit modules contain **exact-typed witnesses**, never new assumptions, per
[`plan/DraftNormalisationVerification.md`](../../plan/DraftNormalisationVerification.md) §7.

* `Truss.Transfer.Audit.Chapter3` — **exact-typed witnesses**: each accepted result is
  restated from scratch and then supplied by the proved declaration, so a refactor that
  quietly changes a statement breaks the audit. Rows that are OPEN are listed there and
  deliberately not witnessed.
* `Truss.Transfer.Audit.NonVacuity` — the plan's §9 non-vacuity and diagnostic probes: the
  interface is inhabited, the label categories used are not degenerate, and the
  arrow-fibre-connectivity clause of `IsPosetCoarsening` is shown to be *necessary* for label
  descent.

* `Truss.Transfer.Audit.OpenTrussProbe` — the non-vacuity probe for rows `T01`/`T02`: both
  sides of `isCoarsening_iff_surjective_regular` are shown to be inhabited, and the
  `reg`/`sing`/`reg` cell structure of the three-element open 1-truss is checked cell by cell.

* `Truss.Transfer.Audit.Reflection` — rows `R1`–`R8` of
  [`plan/ReflectionNormalisationVerification.md`](../../plan/ReflectionNormalisationVerification.md):
  exact-typed witnesses for the reflection-based proof, the recursion's construction equation
  with `Λ`, the axiom audit, and a **checked proof-route gate** (`#assert_no_dep`).
* `Truss.Transfer.Audit.ReflectionBoundary` — boundary probes for row `R8`: height zero (the
  identity is the only outgoing map), the empty base (towers exist; everything is normal),
  and height-one agreement with the §5.4 normaliser.
* `Truss.Transfer.Audit.ReflectionExamples` — concrete probes for row `R8`: a removable
  identity, `WalkingParallelPair` and arrow-only (gaunt monoid) labels, two-fibre forward
  retention, and a height-two example exercising `B(C)`-labelled lower towers.

The construction-agreement audits (plan §4) are **OPEN**: no module here witnesses any of
them.
-/
