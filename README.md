# Truss normalisation

A standalone Lean 4 development of labelled open-truss normalisation, extracted
from Yuhang Wei's transfer-report formalisation. Only `Truss.Transfer` is included;
this repository does not contain the older `Truss.Normalization` library.

## Build and check

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
lake env lean CheckAxioms.lean
```

Lean and Mathlib are pinned to **v4.28.0**. `lake-manifest.json` pins dependency
commits. `SOURCE.json` records the source revision and SHA-256 of every exported
proof file. The original copyright headers and Apache 2.0 licence are preserved.

## Reading guide

Start with [`Truss/Transfer.lean`](Truss/Transfer.lean). The following links point
to statements and proofs, not to an executable normaliser:

| Topic | Source / principal declarations |
|---|---|
| Poset coarsenings and label descent | [Descent](Truss/Transfer/Normalisation/Descent.lean): `label_descent`, `label_descent_unique` |
| Normalisation as terminality | [Terminality](Truss/Transfer/Normalisation/Terminality.lean) |
| Retained singular points | [Retained](Truss/Transfer/Normalisation/Retained.lean): `retOrderIso` |
| Forward-stable families | [StableFamily](Truss/Transfer/Normalisation/StableFamily.lean) |
| Bundle normalisation | [BundleNorm](Truss/Transfer/Normalisation/BundleNorm.lean) |
| Successor criterion | [SuccNormalising](Truss/Transfer/Normalisation/SuccNormalising.lean): `succ_isNormalising_iff` |
| Recursive normalisation and universal property | [RecursiveNorm](Truss/Transfer/Normalisation/RecursiveNorm.lean): `towerNormalise_isNormalising`, `towerNormalise_universal` |
| Exact-typed theorem witnesses | [Chapter audit](Truss/Transfer/Audit/Chapter3.lean) |
| Non-vacuity / diagnostic examples | [NonVacuity](Truss/Transfer/Audit/NonVacuity.lean), [OpenTrussProbe](Truss/Transfer/Audit/OpenTrussProbe.lean) |

## Scope and limitations

A successful build checks the **formal statements in these files**. It does not
certify the C++ implementation, the visualiser, or every sentence of the current
manuscript. Definitions include `noncomputable` constructions; this is not an
executable normalisation package.

The code uses coordinate models of open trusses and equality of label functors.
Read each declaration's hypotheses, including label-category assumptions, rather
than transferring a theorem to a different interface by name alone.

Some preserved module comments and audit row numbers refer to the September 2026
draft. They are historical, not a claim about current chapter numbering or current
coverage. In particular, a full current-manuscript correspondence review and
construction-agreement bridges are **not supplied by this extraction**.

`CheckAxioms.lean` rejects axioms outside `propext`, `Classical.choice`, and
`Quot.sound` for every theorem in the `Truss.Transfer` namespace, including the
chapter witnesses. CI rebuilds the package and runs this check independently.
