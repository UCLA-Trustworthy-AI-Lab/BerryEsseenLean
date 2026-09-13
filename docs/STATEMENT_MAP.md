# Manuscript-to-Lean statement map

This map uses the stable LaTeX labels in the [audited manuscript](../reference/aop-sample.tex). All endpoint names below are in the `BerryEsseen` namespace unless a longer namespace is shown. Links lead to the declaring source file.

There are **31 named statement groups**, including one remark, and **16 registered additional endpoints**. Read a primary endpoint together with all supplemental endpoints listed for its label: a single endpoint does not always return every conjunct in the prose. The separately checked full bounded-extremizer wrapper is described below.

The machine-readable registry is [`notes/manuscript-endpoints.json`](../notes/manuscript-endpoints.json), and the type-checking entry point is [`Checks/ManuscriptCoverage.lean`](../Checks/ManuscriptCoverage.lean). This map records the mathematical correspondence reviewed against the manuscript; the type checks do not automate that comparison.

## Primary endpoints

| Manuscript label | Primary Lean endpoint | Additional parts |
|---|---|---|
| `thm:main` | [`strict_main_theorem`](../BerryEsseen/StrictResults.lean) | 2 below |
| `lem:signed-smoothing` | [`manuscript_signed_smoothing_sup`](../BerryEsseen/ManuscriptSignedSmoothing.lean) | — |
| `lem:jitter` | [`maximal_span_wassersteinThree_jitter_expansion`](../BerryEsseen/GeneralJitterExpansion.lean) | — |
| `rem:jitter-width` | [`raw_wassersteinThree_variable_jitter_expansion_at_raw`](../BerryEsseen/RawJitterWidth.lean) | — |
| `cor:jitter-envelopes` | [`wassersteinThree_jitter_envelopes`](../BerryEsseen/GeneralWassersteinEnvelopes.lean) | 1 below |
| `lem:binomial-estimates` | [`manuscript_binomial_estimates`](../BerryEsseen/ManuscriptBinomialLemma.lean) | — |
| `prop:clusters` | [`manuscript_two_interval_cluster_stability`](../BerryEsseen/ManuscriptClusters.lean) | — |
| `lem:one-sided-loss` | [`manuscript_one_sided_loss`](../BerryEsseen/ManuscriptOneSidedLoss.lean) | — |
| `lem:small-cluster-variance` | [`manuscript_small_cluster_variance_original_parameters`](../BerryEsseen/ManuscriptSmallVarianceOriginalParameters.lean) | — |
| `lem:two-cluster-local-mass` | [`compact_centered_measure_local_mass`](../BerryEsseen/GeneralTwoClusterLocalMass.lean) | — |
| `lem:accumulated-cluster-variance` | [`general_cluster_macroscopic_gap`](../BerryEsseen/GeneralAccumulatedVariance.lean) | 1 below |
| `lem:attainment` | [`manuscript_extremal_attainment_full`](../BerryEsseen/Attainment.lean) | — |
| `lem:selection` | [`manuscript_harmonic_selection`](../BerryEsseen/ManuscriptSelection.lean) | — |
| `lem:influence` | [`contamination_influence`](../BerryEsseen/RawInfluence.lean) | 3 below |
| `lem:gaussian-expansion` | [`gaussianHn_uniform_remainder`](../BerryEsseen/GaussianCancellation.lean) | 2 below |
| `prop:bounded-extremizers` | [`manuscript_bounded_extremizing_sequence`](../BerryEsseen/BoundedExtremizers.lean) | Full-statement wrapper below |
| `lem:limit-extremizer` | [`selected_extremizer_wassersteinThree_subsequence`](../BerryEsseen/GeneralSupportLimits.lean) | — |
| `lem:support-interval` | [`extremizer_support_limit_interval_general`](../BerryEsseen/GeneralSupportLimits.lean) | — |
| `lem:support-separation` | [`extremizer_support_limit_separation_general`](../BerryEsseen/GeneralSupportLimits.lean) | — |
| `lem:effective-selection` | [`effective_selection`](../BerryEsseen/EffectiveSelection.lean) | — |
| `lem:effective-low-frequency` | [`effectiveLowFrequencyIntegral_bound`](../BerryEsseen/EffectiveLowFrequencyIntegral.lean) | 1 below |
| `lem:effective-near-lattice` | [`effective_near_lattice`](../BerryEsseen/EffectiveNearLattice.lean) | — |
| `lem:effective-cluster-jitter` | [`effective_cluster_jitter`](../BerryEsseen/EffectiveClusterJitter.lean) | — |
| `lem:effective-binomial` | [`manuscript_effective_binomial_branches`](../BerryEsseen/ManuscriptBinomialTheorem.lean) | 4 below |
| `lem:effective-small-variance` | [`manuscript_effective_small_variance`](../BerryEsseen/ManuscriptEffectiveSmallVariance.lean) | 1 below |
| `lem:effective-local-mass` | [`manuscript_effective_local_mass`](../BerryEsseen/ManuscriptLocalMass.lean) | — |
| `prop:effective-clusters` | [`manuscript_effective_cluster_stability`](../BerryEsseen/ManuscriptEffectiveClusters.lean) | 1 below |
| `lem:effective-lattice-stability` | [`effective_lattice_stability`](../BerryEsseen/EffectiveLatticeStability.lean) | — |
| `lem:effective-global-jitter` | [`effective_global_jitter`](../BerryEsseen/EffectiveGlobalJitter.lean) | — |
| `lem:effective-identification` | [`effective_identification_with_global_jitter`](../BerryEsseen/EffectiveIdentification.lean) | — |
| `prop:effective-confinement` | [`manuscript_effective_full_support`](../BerryEsseen/ManuscriptConfinement.lean) | — |

## Supplemental endpoints

| Manuscript label | Additional conclusion | Lean endpoint |
|---|---|---|
| `thm:main` | Original explicit sample-size threshold | [`strict_explicit_theorem`](../BerryEsseen/StrictResults.lean) |
| `thm:main` | Sharpness argument following the main theorem | [`strict_sharpness`](../BerryEsseen/StrictResults.lean) |
| `cor:jitter-envelopes` | Original limsup conclusion | [`wassersteinThree_jitter_limsup`](../BerryEsseen/GeneralWassersteinEnvelopes.lean) |
| `lem:accumulated-cluster-variance` | Consequent vanishing of accumulated cluster variance | [`accumulated_cluster_variance_tendsto_zero`](../BerryEsseen/GeneralAccumulatedVarianceCorollary.lean) |
| `lem:influence` | Global nonpositivity | [`influence_nonpos_at_extremizer`](../BerryEsseen/VariationalExtremizer.lean) |
| `lem:influence` | Zero contact on the support | [`influence_contact_at_extremizer`](../BerryEsseen/VariationalExtremizer.lean) |
| `lem:influence` | Original contact equation | [`influence_contact_equation`](../BerryEsseen/VariationalExtremizer.lean) |
| `lem:gaussian-expansion` | Global cubic term and linear remainder bound | [`gaussianHn_global_bound`](../BerryEsseen/GaussianCancellation.lean) |
| `lem:gaussian-expansion` | Uniform convergence on compact sets | [`gaussianHn_uniform_limit`](../BerryEsseen/GaussianCancellation.lean) |
| `lem:effective-low-frequency` | Pointwise error bounds with constants 0.61 and 0.048 | [`effective_charFun_edgeworth_low_frequency`](../BerryEsseen/EffectiveLowFrequency.lean) |
| `lem:effective-binomial` | Mass supremum over arbitrary integers | [`manuscript_effective_binomial_mass_sup`](../BerryEsseen/ManuscriptBinomialTheorem.lean) |
| `lem:effective-binomial` | Central branch for arbitrary integers | [`manuscript_effective_binomial_integer_central`](../BerryEsseen/ManuscriptBinomialTheorem.lean) |
| `lem:effective-binomial` | Wide-interval branch for arbitrary integers | [`manuscript_effective_binomial_integer_wide`](../BerryEsseen/ManuscriptBinomialTheorem.lean) |
| `lem:effective-binomial` | Original lower bound for the constant | [`manuscript_effective_binomial_constant_lower`](../BerryEsseen/ManuscriptBinomialTheorem.lean) |
| `lem:effective-small-variance` | Original explicitly quantified gap | [`manuscript_effective_small_variance_positive`](../BerryEsseen/ManuscriptEffectiveSmallVariance.lean) |
| `prop:effective-clusters` | Two intervals and both parameter conclusions | [`manuscript_effective_interval_stability_support`](../BerryEsseen/ManuscriptExplicitTheorem.lean) |

## Full bounded-extremizer conjunction

For `prop:bounded-extremizers`, additionally check:

```lean
BerryEsseen.CurrentRecheck.bounded_extremizers_full_manuscript_statement
```

This theorem is in [`Checks/BoundedFullStatementAudit.lean`](../Checks/BoundedFullStatementAudit.lean). Under the same H and A inputs and the hypothesis of arbitrarily late violations, it returns a strictly increasing sample-size sequence, the corresponding laws, and evaluation points with all of the following properties:

- Signed attainment and the full Kolmogorov supremum both equal the same extremal constant for the same sample size and law.
- The extremal constant strictly exceeds $c_E$.
- The third absolute moment lies between 1 and the original moment cutoff.
- The support lies in $(-10,10)$.
- The selected scaled drops tend to zero.

The wrapper combines `manuscript_bounded_extremizing_sequence` with the already proved `manuscript_attained_full_ratio`. It adds the formerly implicit full-supremum conjunct without adding an external assumption. Its compilation is included in the verification command.

## Proof-route review

The statement coverage is supplemented by checks of actual proof dependencies for the main and explicit results, and by [`Checks/SupplementalRouteAudit.lean`](../Checks/SupplementalRouteAudit.lean). The designated sharpness endpoint uses `original_manuscript_sharpness`, which specializes the external fixed-law Esseen asymptotic to the constructed Esseen law.

The repository also retains auxiliary results, including an alternative binomial proof of sharpness. Their presence does not change the designated endpoint in this map. See [Verification](VERIFICATION.md) for the distinction between kernel checks, registered route checks, and mathematical review of the prose.
