# External input: three-Wasserstein convergence topology

Primary source checked and selected for this interface: Cédric Villani,
*Optimal transport, old and new*, author's manuscript dated June 13, 2008,
[author's manuscript PDF](http://elenaher.dinauz.org/B07D.StFlour.pdf).
The uploaded copy is byte-for-byte identical to this URL's PDF (998 pages).
PDF SHA-256: `3ae2db61cbffadfeef0de738742f4f3ce81b21874dacb1ad2991a7000434675d`.

Definition 6.1, printed page 105 (PDF page 111), defines the distance by
probability couplings. Definition 6.4 and its discussion, printed pages
106–107 (PDF pages 112–113), establish finite coupling costs for laws with
finite moments. Definition 6.8(i), printed page 108 (PDF page 114), specifies
weak convergence together with convergence of the moment of order p.
Theorem 6.9 on the same page equates this convergence with convergence in
Wasserstein distance; its complete proof of both directions is on printed
pages 113–115 (PDF pages 119–121). Our specialization is the real line,
its usual distance, p=3, and base point zero. PDF page numbers here count
the first physical page as page 1.

These statements have been directly checked against the Lean interface.
The source adopted here is the specified 2008 author's manuscript, rather
than the 2009 Springer typeset edition. Checking that later edition is not
an outstanding condition of this source audit.

`transportThreeCosts` in `PublishedWassersteinThreeCore.lean` contains cube roots
of integrals of `|x-y|^3` over actual probability measures on ℝ×ℝ with the
two exact pushforward marginal equalities. `wassersteinThree` is their real
infimum. The kernel-checked `cubic_cost_integrable_of_marginals` shows that
restricting the definition to integrable costs excludes no coupling when
the marginal third absolute moments are finite. The product coupling proves
the cost set nonempty; lower boundedness, nonnegativity, and the bound by
each coupling cost are also proved in Lean.

`PublishedWassersteinThreeTopology.tendsto_iff` is an explicit `Prop` premise
for the cited convergence characterization. No instance is asserted.
`standardized_wassersteinThree_tendsto_iff` specializes it to the project's
actual standardized laws. `bounded_weak_wassersteinThree_tendsto` combines
it with the already proved bounded-support third-moment convergence for
every nonnegative support bound A.

The restored proof of Lemma 2.2 uses this classical topology theorem to
pass from weak convergence plus third-moment convergence to W₃ convergence.
Actual near-optimal cubic couplings are then selected from the defined cost
infimum. Their squared error and the independent-difference error are proved
to converge to zero internally. The original independent-difference curvature
argument is not assumed as part of the external topology interface.

The current `strict_main_theorem` explicitly has six classical inputs
H, A, E, B, I, W. A supplies the fixed-law asymptotic used to recover the
manuscript's full extremal-constant limit. Its smoothing input is discharged
internally by the manuscript's sinc⁴ proof. The earlier five-input description
predated that restoration. The explicit numerical theorem keeps its six
classical inputs H, E, B, I, U, K; the fixed-law sharpness argument keeps A.

The mathematical premise and all Lean proofs are unchanged by this source
update. The exact theorem and page numbers above refer to the inspected
June 13, 2008 author's manuscript.
