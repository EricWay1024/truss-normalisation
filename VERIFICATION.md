# Extraction verification — 2 November 2026

- 43 source files copied byte-for-byte from `Truss.Transfer`; their individual
  SHA-256 values and source revision are in `SOURCE.json`.
- Imports checked to stay within `Truss.Transfer`, Mathlib, Lean and Std.
- `lake build` in a new package directory, with no existing project build output:
  **passed, 1048 jobs**. The installed Mathlib/dependency cache was reused; the
  private library's project objects were not available to this package.
- `lake env lean CheckAxioms.lean`: **passed, 1776 theorems**, including private
  Transfer-module theorems. Union of transitive axiom dependencies:
  `[propext, Quot.sound, Classical.choice]`.
- No proof source was modified for this extraction.

This is build and axiom evidence, not a full current-manuscript correspondence
review, a review of every informal argument, or a C++ construction-agreement test.
The independent CI run is recorded in GitHub Actions; consult its actual result,
not this local-build record, when assessing whether CI passed.
