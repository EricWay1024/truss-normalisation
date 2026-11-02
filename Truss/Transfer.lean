/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Audit
import Truss.Transfer.Chapter2
import Truss.Transfer.Normalisation

/-!
# `Truss.Transfer` — verification of the active draft normalisation chapter

A self-contained chapter-facing namespace verifying the author's draft normalisation chapter
(`dphil-notes-typst/transfer/ch03-normalisation-draft.typ`) and the Chapter 2 constructions
it uses (`transfer/ch02-trusses.typ`), per
[`plan/DraftNormalisationVerification.md`](../plan/DraftNormalisationVerification.md).

It shares **nothing** with `Truss/Normalization/`.  The plan forbids substituting the legacy
`NormData`, `ProcResult`, `TowerNormal`, `PresCatN` or `CollapseMap` interfaces for the
chapter's, and no legacy result is promoted to draft coverage without a proved
construction-agreement bridge.  No such bridge exists yet.

* `Truss.Transfer.Chapter2` — the Chapter 2 support (rows `G01`–`G03`, and the primitive
  part of `G05`).
* `Truss.Transfer.Normalisation` — the chapter itself (rows `P01`–`P05`, `C01`–`C10`).
* `Truss.Transfer.Audit` — the plan's §9 non-vacuity and diagnostic probes.

Everything else is **OPEN**.  The per-row ledger, with source hashes, the reviewed source
correspondence and the axiom evidence, is
[`plan/DraftNormalisationCoverage.md`](../plan/DraftNormalisationCoverage.md); the frontier is
[`plan/DraftNormalisationRunReport.md`](../plan/DraftNormalisationRunReport.md).
-/
