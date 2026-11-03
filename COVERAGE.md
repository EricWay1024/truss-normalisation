# Coverage of Chapter 2

The lemmas, propositions, theorems, corollaries, constructions and remarks of Chapter 2 of the transfer report, and
three of its definitions, with their Lean declarations under `Truss.Transfer`. Modules under
`Truss/Transfer/Normalisation/` are in brackets. The other definitions appear only through the declarations that use
them. Numbers are those of the report as of 3 November 2026.

Lean checks the declarations, not that they match the report; the correspondence was checked by reading the
statements. See the conventions in the [README](README.md).

| Report | Lean |
|---|---|
| Definition 2.1 | `IsOpenPosetMap`, `isOpenPosetMap_iff_exists_le` (Poset) |
| Lemma 2.5 | `IsPosetCoarsening.surjective`, `.arr_surjective`; `.pointFibre_nonempty`, `.pointFibre_connected`, `.arrowFibre_nonempty`, `.arrowFibre_connected`; `.exists_monotone_lift`; `.comp`, `.id`; `.pullback_proj` (Poset) |
| Proposition 2.6 | `label_descent`, `label_descent_unique`, `descend`, `descend_spec` (Descent) |
| Definition 2.8 | `IsCoarsening`, `isCoarsening_iff_exists_dimsigNatTrans` (Context) |
| Lemma 2.13 | `descendsAlong_iff`, `LabOutCoarse.full`, `LabOutCoarse.thin` (Context); `LabOutCoarse.forgetObj_injective`, `.nonempty_hom_iff` (OutgoingOrder) |
| Definition 2.14 | `IsNormalising`, `IsNormal`, `LabOutCoarse.isNormalising_iff_nonempty_isTerminal` (Terminality) |
| Proposition 2.15 | `terminal_factors`, `IsNormalising.comp_isCoarsening`, `normalising_precomp` (Terminality) |
| Corollary 2.16 | `IsNormalising.target_isNormal` (Terminality) |
| Proposition 2.17 | `isCoarsening_iff_surjective_regular` (OneTruss) |
| Construction 2.19 | `OpenTruss.qU`, `.qU_isCoarsening`, `.ret_qU` (Retained) |
| Proposition 2.20 | `OpenTruss.retOrderIso` (Retained) |
| Proposition 2.23 | `OpenTruss.labelledRetOrderIso`, `.labelledRetOrderIso_forget` (OneTrussOrder) |
| Corollary 2.24 | `isNormalising_iff_ret_eq_nonTriv`, `isNormal_iff_nonTriv_eq_univ` (OneTrussNorm) |
| Construction 2.25 | `normalise`, `normaliseMap`, `normaliseMap_isNormalising`, `normalise_isNormal` (OneTrussNorm) |
| Proposition 2.26 | `OpenBundle.isCoarsening_iff_fibrewise` (Fibrewise) |
| Lemma 2.29 | `OpenBundle.retFinset_isForwardStableFam` (BundleRetract) |
| Construction 2.30 | `OpenBundle.quotient`, `.quotientMap`, `.ret_quotientMap` (BundleQuotient); `.isCoarsening_quotientMap` (BundleNorm) |
| Proposition 2.31 | `OpenBundle.retOrderIso`, `.retOrderIso_apply`, `.retOrderIso_symm_map` (BundleOrder) |
| Proposition 2.35 | `OpenBundle.labelledRetOrderIso`, `.labelledRetOrderIso_forget` (BundleOrder) |
| Corollary 2.36 | `OpenBundle.isNormalising_iff_retFam_eq_closure'`, `.isNormal_iff_sing_eq_closure'` (Section54) |
| Construction 2.37 | `OpenBundle.closureFinset`, `.bundleNormalise`, `.bundleNormaliseMap` (BundleNorm); `.bundleNormaliseMap_isNormalising'` (Section54) |
| Proposition 2.38 | `OpenBundle.isNormalising_reindex'` (Section54) |
| Theorem 2.39 | `successor_tfae'` (Section55) |
| Remark 2.40 | `isCoarsening_iff_two` (Section55) |
| Construction 2.41 | `succTopTarget`, `succTopMap`, `succTopMap_isNormalising`, `succClassifier`, `topNormObj`, `topNorm`, `topNorm_isCoarsening` (TopReflection) |
| Lemma 2.42 | `topNorm_along_lower`, `succClassifier_along_lower`, `phiHom` (TopReflection) |
| Lemma 2.43 | `lift`, `lift_target_eq`, `classify_liftTarget`, `lift_isCoarsening`, `lift_base_surjective` (TopReflection) |
| Proposition 2.44 | `phi`, `lam`, `lam_comp_phi`, `reflection`, `lamFullyFaithful`, `unitHom`, `lam_phi_map`, `unitTop_appendTop_eq` (TopReflection) |
| Theorem 2.45 | `succ_isNormalising_iff_of_isCoarsening`, `succ_isNormalising_iff` (SuccNormalising) |
| Corollary 2.46 | `succ_isNormal_iff` (RecursiveNorm) |
| Corollary 2.47 | `normality_of_tower_layers`, `isNormal_iff_blocks` (BlockNormality); `Tower.prefix`, `.suffix`, `.suffix_tot`, `.append_prefix_suffix` (TowerBlocks); `towerClassify`, `iterLab_add`, `categoryTransport`, `towerClassify_blocks` (IteratedClassifier) |
| Construction 2.48 | `towerNormalise`, `succStep_eq_lam`, `towerNormalise_isNormalising`, `towerNormalise_universal` (RecursiveNorm) |
| Remark 2.49 | None in this package. |
