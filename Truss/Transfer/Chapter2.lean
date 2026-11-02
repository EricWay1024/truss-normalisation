/-
Copyright (c) 2026 Yuhang Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Truss.Transfer.Geometry.Bordism
import Truss.Transfer.Geometry.OneTruss

/-!
# Chapter 2 support for the draft normalisation verification — public re-export

This is the public entry point for the `Truss.Transfer` formalisation of the Chapter 2
constructions used by the draft normalisation chapter.  It contains no declarations of its
own: it is a re-export, exactly as
[`plan/DraftNormalisationVerification.md`](../../plan/DraftNormalisationVerification.md) §7
specifies, so that an audit can import the Chapter 2 support and the Chapter 3 normalisation
re-export together.

**Current coverage: rows `G01`–`G03`, plus the primitive interface of row `G05`
(`AdmSing`, `AdmReg`, `Bord1` and the derived `f_R` / `g_R` with their monotonicity).**
The endpoint clauses of admissibility for the derived functions, rows `G04`, `G06`–`G25`, and
every reconstruction/equivalence statement are **OPEN**; importing this module certifies
nothing about them.  See
[`plan/DraftNormalisationCoverage.md`](../../plan/DraftNormalisationCoverage.md).
-/
