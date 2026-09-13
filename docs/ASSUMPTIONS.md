# External assumptions

The three designated endpoints in [`StrictResults.lean`](../BerryEsseen/StrictResults.lean) take explicit proposition parameters. Across those endpoints there are **eight external interfaces with ten mathematical fields**. Accepting an interface supplies the corresponding classical result; no Lean proof of that external result is claimed here.

The source audit compared constants, quantifiers, moment conditions, equality cases, and the actual probability and Wasserstein definitions. The source types are given accurately below: **B is a public doctoral dissertation; W and K use the 13 June 2008 author manuscript.** The historical `Published…` names in the Lean API do not mean every input is a journal publication.

## Interfaces and sources

| Input | Lean interface and fields | Mathematical content | Source used in the audit |
|---|---|---|---|
| H | [`ClassicalBerryEsseenBounds`](../BerryEsseen/ClassicalBounds.lean): `structural`, `remainder` | IID structural bounds with coefficients 0.4690 and 0.3031, offset 0.646; remainder coefficient 2.5786 | Shevtsova (2013), printed pp. 124–125; Shevtsova (2012), Corollary 4.18, printed p. 303 |
| A | [`PublishedEsseenFixedLawAsymptotic`](../BerryEsseen/PublishedEsseenFixedLawAsymptotic.lean): `limit` | Esseen's Kolmogorov asymptotic for a **fixed** law and its maximal lattice span | Mattner–Shevtsova, *ALEA* 16 (2019), printed p. 491, (1.5) |
| E | [`PublishedEsseenMoment`](../BerryEsseen/PublishedEsseenMoment.lean): `bound`, `equality` | Esseen's moment inequality and the necessary equality characterization | The same *ALEA* article, printed p. 491, (1.6)–(1.8) |
| B | [`PublishedBernoulliBound`](../BerryEsseen/PublishedBernoulli.lean): `strict_bound` | Strict supremum bound for every nondegenerate binomial law and positive sample size | Jona Schulz, doctoral dissertation (2016), Theorem 1, printed p. 1 / PDF p. 11 |
| I | [`PublishedNonIIDBound`](../BerryEsseen/PublishedNonIID.lean): `bound` | Non-IID Berry–Esseen bound with coefficient 0.5583 and positive total variance | Shevtsova (2013), printed p. 124 |
| U | [`PublishedNonuniformBound`](../BerryEsseen/PublishedNonuniform.lean): `bound` | Nonuniform Berry–Esseen bound with coefficient 17.36 | Shevtsova (2013), printed p. 125 |
| W | [`PublishedWassersteinThreeTopology`](../BerryEsseen/PublishedWassersteinThree.lean): `tendsto_iff` | $W_3$ convergence iff weak convergence and convergence of third absolute moments, on $\mathbb R$ | Villani, 2008 author manuscript, Definition 6.8(i) and Theorem 6.9, printed p. 108 / PDF p. 114 |
| K | [`PublishedWassersteinDuality`](../BerryEsseen/PublishedWasserstein.lean): `eq_dual` | Kantorovich–Rubinstein duality for $W_1$, with finite first moments and all 1-Lipschitz test functions | Villani, same manuscript, Remark 6.5, (6.3), printed p. 107 / PDF p. 113 |

The exact source texts are available from the following primary locations:

- **Shevtsova (2012):** [journal PDF](https://ami.uni-eszterhazy.hu/uploads/papers/finalpdf/AMI_39_from241to307.pdf). The coefficient 2.5786 in Corollary 4.18 applies without an additional upper restriction on the Lyapunov fraction. The manuscript's use of the weaker coefficient 3 is legitimate.
- **Shevtsova (2013):** [journal bibliographic record](https://www.mathnet.ru/eng/ia252) and [full text](https://www.mathnet.ru/php/getFT.phtml?jrnid=ia&option_lang=eng&paperid=252&what=fullt). This is a published two-page results announcement.
- **Mattner and Shevtsova (2019):** [*An optimal Berry–Esseen type theorem for integrals of smooth functions*](https://alea.impa.br/articles/v16/16-19.pdf), *ALEA* 16, 487–530, [DOI](https://doi.org/10.30757/ALEA.v16-19). A and E were checked against these published exact restatements; the audit does not claim to have checked Esseen's original 1956 proof.
- **Schulz (2016):** [*The optimal Berry-Esseen constant in the binomial case*](https://d-nb.info/1197702695/34), doctoral dissertation, Universität Trier. The source states a strict bound on the entire supremum, as required by B.
- **Villani (2008):** [*Optimal Transport, Old and New*, author manuscript dated 13 June 2008](http://elenaher.dinauz.org/B07D.StFlour.pdf). The audit used the supplied copy of this manuscript. W's proof is on printed pp. 113–115 / PDF pp. 119–121. K also appears in Particular Case 5.16, (5.11), printed p. 72 / PDF p. 78. PDF page numbers here are one-based. See the [source identity record](../reference/villani-2008-source.json) and [BibTeX entry](../reference/villani-2008.bib). This repository does not assert that those page numbers refer to the 2009 typeset book.

## Exact dependency boundary

| Endpoint | External parameters |
|---|---|
| `strict_main_theorem` | H, A, E, B, I, W |
| `strict_explicit_theorem` | H, E, B, I, U, K |
| `strict_sharpness` | A |

`PublishedSignedSmoothing` is an intermediate interface whose proof is supplied by [`manuscriptSignedSmoothing`](../BerryEsseen/ManuscriptSmoothingInstance.lean). It is **not** a ninth external input. The manuscript's smoothing, jitter, local-mass, stability, and confinement results are proved in the project.

A is fixed-law convergence, not an assumption of uniform convergence over changing distributions. E's signed equality case identifies the correctly oriented Esseen two-point law; the reflected alternative is derived in Lean. I is applied to actual finite convolutions. Its interface assumes finite fourth moments, which imply the source's finite third moments; it permits individual zero variances and requires only positive total variance. W and K concern actual coupling costs and probability measures, not uninterpreted distance symbols.

## Source-to-interface interpretation

The source audit accepts the usual equivalent reformulation of H, I, and U from strict CDFs to CDFs defined with $\le$, and the normalization of a positive total variance. For the CDF conversion, let thresholds decrease to the target point and use measure continuity and continuity of the Gaussian CDF and error bound; no atomlessness assumption is needed. These source-to-interface reformulations have not been packaged as separate Lean conversion theorems starting from a literal formal transcription of each original publication.

The bundled manuscript is retained byte-for-byte. Two manuscript citations locate Shevtsova (2012), Corollary 4.18, on p. 302; the correct printed page is **303**. This is a citation correction, not a change to the mathematical premise. See [the erratum](../reference/errata-current-recheck.md).
