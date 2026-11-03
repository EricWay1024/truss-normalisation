# Truss normalisation

A Lean 4 formalisation of the normalisation of labelled open truss bundles: Chapter 2 of Yuhang Wei's transfer
report, *Framed combinatorial constructions for embedded PL manifolds*. It is extracted from a private repository;
`SOURCE.json` records the revision and the hash of every file.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
lake env lean CheckAxioms.lean
```

Lean and Mathlib are pinned to v4.28.0. `CheckAxioms.lean` fails if any theorem or definition in `Truss.Transfer`
depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`. CI runs the build and this check on
every push.

## Main results

Start at `Truss/Transfer.lean`. [`COVERAGE.md`](COVERAGE.md) lists the declarations for each result of the chapter;
only Remark 2.49 has none.

| Report | Declarations | Module |
|---|---|---|
| Proposition 2.6, descent of labels | `label_descent`, `label_descent_unique` | `Descent` |
| Propositions 2.31 and 2.35, outgoing coarsenings as stable families | `OpenBundle.retOrderIso`, `OpenBundle.labelledRetOrderIso` | `BundleOrder` |
| Proposition 2.44, top normalisation as a reflection | `reflection`, `lamFullyFaithful` | `TopReflection` |
| Theorem 2.45, the inductive criterion | `succ_isNormalising_iff` | `SuccNormalising` |
| Corollary 2.47, normality of tower layers | `normality_of_tower_layers` | `BlockNormality` |
| Construction 2.48, recursive normalisation | `towerNormalise_isNormalising`, `towerNormalise_universal` | `RecursiveNorm` |

## Conventions

- Trusses are coordinate models: a 1-truss is a length and the dimension of its first element, and a bundle is a
  functor into 1-truss bordisms. A comparison with the abstract definitions of the FCT book is not part of this
  package, and neither is the C++ truss library.
- Maps preserve labels by equality, as in the report's strict convention. The main theorems take any label category
  with objects and morphisms in one universe, and do not assume the report's condition that it has no non-identity
  automorphisms; `NoAut.lean` shows that this condition makes label comparisons unique.
- The constructions are `noncomputable`: they are proved correct, not run.
- Module names such as `Section55` and `Audit/Chapter3.lean`, and some docstrings, keep the numbering of an earlier
  draft. Labels such as `thm:draft-successor-normalising` are those of the report's source.

Released under Apache 2.0; see `LICENSE`.
