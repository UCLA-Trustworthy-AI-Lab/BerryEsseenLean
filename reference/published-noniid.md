# Independent, non-identically distributed Berry–Esseen input

Source: I. G. Shevtsova, “On the absolute constants in the Berry–Esseen
inequality and its structural and nonuniform improvements,” Inform. Primen.
7:1 (2013), 124–125.

Primary bibliographic page: https://www.mathnet.ru/eng/ia252

Primary full text: https://www.mathnet.ru/php/getFT.phtml?jrnid=ia&option_lang=eng&paperid=252&what=fullt

The final displayed general bound on printed page 124 includes
`Delta_n ≤ 0.5583 ell_n`. The preceding definitions concern independent,
centered real summands with finite third absolute moments, with the sum of
variances normalized to one; individual variances need not be positive.

`PublishedNonIIDBound.bound` is an explicit proposition parameter, not a
custom axiom or an assertion that the manuscript's new lemmas hold. It states
this bound for an actual finite convolution of `CenteredFourthLaw` values.
Its finite fourth moment hypotheses imply the published third moment
hypotheses. For positive total variance `V`, applying the published theorem
to all summands divided by `sqrt V` gives the denominator `(sqrt V)^3`.
The paper uses `P(S < x)` in its distribution function. The uniform bound
is identical for `P(S ≤ x)`, by taking thresholds decreasing to `x` and
using continuity of the normal distribution function.

`twoNoiseBlock_normal_bound` proves the application to the actual two
conditional noise blocks. Their third moment budget is at most `ε V` when
every summand has absolute value at most `ε`. Lean derives the weaker
constant `0.56` and the error `0.56 ε / sqrt V`; no local interval mass
conclusion is included in the published premise.
