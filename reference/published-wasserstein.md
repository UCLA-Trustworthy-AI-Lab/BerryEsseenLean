# External input: Kantorovich–Rubinstein duality

The only new external premise is the standard duality equality, restricted
to probability measures on the real line with finite first moments.

Primary source checked and selected for this interface: Cédric Villani,
*Optimal transport, old and new*, author's manuscript dated June 13, 2008,
[author's manuscript PDF](http://elenaher.dinauz.org/B07D.StFlour.pdf).
The uploaded copy is byte-for-byte identical to this URL's PDF (998 pages).
PDF SHA-256: `3ae2db61cbffadfeef0de738742f4f3ce81b21874dacb1ad2991a7000434675d`.

Definition 6.1 and equation (6.2), printed page 105 (PDF page 111), define
the coupling cost. Definition 6.4 and its discussion, printed pages 106–107
(PDF pages 112–113), establish finite coupling costs for laws with finite
moments. Remark 6.5, equation (6.3), printed page 107 (PDF page 113), gives
precisely the supremum over 1-Lipschitz test functions. Particular Case 5.16,
equation (5.11), printed page 72 (PDF page 78), also states the formula.
PDF page numbers here count the first physical page as page 1.

These statements have been directly checked against the Lean interface.
The source adopted here is the specified 2008 author's manuscript, rather
than the 2009 Springer typeset edition. Checking that later edition is not
an outstanding condition of this source audit.

`transportCosts` uses actual probability measures on ℝ×ℝ, both actual
pushforward marginal equalities, and an integrable absolute-distance cost.
`wassersteinOne` is the real infimum of these costs. With finite first
moments, restricting to integrable costs does not alter the infimum.
`PublishedWassersteinDuality.eq_dual` records exactly the signed dual formula.

No instance of the premise is asserted. Triangle inequalities and all
manuscript-specific quantitative estimates are proved separately in Lean.
