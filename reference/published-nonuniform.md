# Published iid nonuniform Berry–Esseen input

The primary source used for the current audit is I. G. Shevtsova,
*On the absolute constants in the Berry–Esseen inequality and its structural
and nonuniform improvements*, Informatics and its Applications 7(1) (2013),
124–125: [bibliographic record](https://www.mathnet.ru/eng/ia252) and
[journal full text](https://www.mathnet.ru/php/getFT.phtml?jrnid=ia&option_lang=eng&paperid=252&what=fullt).
The second nonuniform iid bound on printed page **125** gives **17.36**.

For iid mean-zero, variance-one summands, the third-order Lyapunov fraction
is the third absolute moment divided by the square root of the sample size.
The source uses strict CDFs. Letting thresholds decrease to x gives the
right-continuous CDF form, since the Gaussian CDF and the denominator are
continuous. This interface restatement is part of the mathematical source
audit, not a separately formalized conversion from a literal transcription
of the publication.

`PublishedNonuniformBound.bound` records this normalized iid bound as an
explicit proposition parameter, with no asserted instance. It does not
assume any new manuscript lemma. The far-threshold numerical corollaries
are proved in Lean.

The historical Lean file comment also points to Shevtsova's 2020 paper,
*Lower bounds for the constants in non-uniform estimates of the rate of
convergence in the CLT*, Journal of Mathematical Sciences 248, 92–98
([DOI](https://doi.org/10.1007/s10958-020-04858-2)). Table 1 on page 2 of its
[author version](https://arxiv.org/pdf/2001.01123) records the same constant.
The current exact-formula audit uses the directly checked 2013 journal
text, so it does not depend on obtaining the 2020 typeset full text.
