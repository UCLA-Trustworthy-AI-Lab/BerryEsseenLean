# Published Esseen moment bound and equality case

Lutz Mattner and Irina Shevtsova, *An optimal Berry–Esseen type theorem for integrals of smooth functions*, ALEA **16** (2019), 487–530, DOI https://doi.org/10.30757/ALEA.v16-19. Published PDF: https://alea.impa.br/articles/v16/16-19.pdf. Section 1.1, page 491, equations (1.6)–(1.8), attributes the result to Esseen (1956).

For a centered variance-one real probability law with a finite third absolute moment, the signed moment plus three times the maximal lattice span is at most (3 + √10) times the third absolute moment. Span is zero for a nonlattice law. Equality uniquely identifies the positively skewed standardized two-point law with upper-atom probability (4 − √10)/2.

`PublishedEsseenMoment` records the inequality and the necessary equality characterization as explicit premises. `EsseenLaw.lean` constructs that precise measure, verifies its moments and support, and proves the reflection formulas. The absolute-moment inequality and the two equality alternatives are then derived in Lean. The bounded violating-sequence limit identification is a proved consequence, not a published premise.
