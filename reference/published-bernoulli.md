# Published Bernoulli bound

Jona Schulz, *The optimal Berry-Esseen constant in the binomial case*, doctoral dissertation, Universität Trier, June 2016.
Primary archived source: https://d-nb.info/1197702695/34 .
Theorem 1, printed page 1, PDF page 11 (zero-based page 10), checked against the source on 2026-09-12.

For 0 < p < 1, q = 1-p, and positive integer n, the supremum over real x of the difference in absolute value between the Bin(n,p) CDF and Φ((x-np)/√(npq)) is strictly less than cE (p²+q²)/√(npq).

`PublishedBernoulliBound.strict_bound` records precisely this strict supremum bound as an explicit premise. `binomialMeasure` is the actual n-fold convolution of the two-atom Bernoulli measure; its finite binomial mass decomposition is proved in `BinomialMeasure.lean`. The pointwise bound, left branch limit, mass bound, and uniform mass estimate for δ ≤ p,q are derived in Lean.

This interface contains no local two-cluster stability assumption and no theorem of the manuscript being formalized.
