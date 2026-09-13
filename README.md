# Berry–Esseen: eventual sharpness in Lean

Lean 4 formalization accompanying [**The Berry–Esseen Bound is Sharp for All Sufficiently Large Sample Sizes**](https://arxiv.org/abs/2609.06358), by **Hengzhi He and Guang Cheng**. The audited manuscript is included as [LaTeX source](reference/aop-sample.tex).

The designated theorem endpoints prove the paper's probability-law statements **conditional on explicitly listed external mathematical results**. The repository includes the proofs, a manuscript-to-Lean statement map, source notes for those inputs, and executable checks of theorem types, axioms, and proof dependencies.

## Main results

Let $P$ be any real probability law with mean zero, variance one, and finite third absolute moment $\beta(P)$. Let $F_{n,P}$ denote the CDF of the standardized sum of $n$ independent copies, and let $\Phi$ be the standard Gaussian CDF. Set

$$
c_E=\frac{3+\sqrt{10}}{6\sqrt{2\pi}}.
$$

The formalized main statement is

$$
\exists N\ge 1\;\forall n\ge N\;\forall P\;\forall x\in\mathbb R,
\qquad |F_{n,P}(x)-\Phi(x)|\le \frac{c_E\beta(P)}{\sqrt n}.
$$

The threshold is uniform in $P$; there is no common upper bound on $\beta(P)$.

| Result | Lean endpoint in [`StrictResults.lean`](BerryEsseen/StrictResults.lean) | External inputs |
|---|---|---|
| Uniform eventual bound | `BerryEsseen.strict_main_theorem` | H, A, E, B, I, W |
| Explicit bound for $n\ge 2\lceil\exp(10^{17})\rceil$ | `BerryEsseen.strict_explicit_theorem` | H, E, B, I, U, K |
| No smaller coefficient works for all sufficiently large sample sizes | `BerryEsseen.strict_sharpness` | A |

The inputs and their source types are documented in [External assumptions](docs/ASSUMPTIONS.md). They include journal articles, a public doctoral dissertation, and Villani's **13 June 2008 author manuscript**. These inputs remain theorem parameters; the repository does not prove those external results from scratch.

## Build and check

Install [Lean through elan](https://github.com/leanprover/elan), Git, and Python 3.10 or later. The release verification and CI use Linux; use WSL for these commands on Windows. Run the following from the repository root:

```sh
lake exe cache get
python3 scripts/verify.py --jobs 3
```

The toolchain is pinned to **Lean 4.28.0**, and mathlib to commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`. The verification command recompiles all 361 project mathematical modules and runs nine gates, including the supplementary full statement of the bounded-extremizer proposition. It writes logs and a machine-readable result to `validation/strict-summary.json`. Reduce `--jobs` if memory is limited.

An ordinary library build is also available:

```sh
lake build
```

`lake build` builds the library; use `scripts/verify.py` for the additional audit gates. See [Verification](docs/VERIFICATION.md) for their scope and interpretation.

## Finding a proof

| Location | Contents |
|---|---|
| [`BerryEsseen/`](BerryEsseen/) | Mathematical definitions and proofs |
| [`BerryEsseen.lean`](BerryEsseen.lean) | Imports every project mathematical module |
| [`Checks/`](Checks/) | Exact-type, axiom, statement-coverage, and proof-route checks |
| [`docs/STATEMENT_MAP.md`](docs/STATEMENT_MAP.md) | All 31 named manuscript statement groups and 16 additional conjunct endpoints |
| [`docs/ASSUMPTIONS.md`](docs/ASSUMPTIONS.md) | Eight external interfaces, ten fields, and precise source locators |
| [`reference/`](reference/) | Audited manuscript and external-source notes |
| [`scripts/`](scripts/) | Reproducible verification utilities |
| [`verification/`](verification/) | Evidence accompanying this release |

## What the verification establishes

Lean checks the formal statements and their proofs. The audit checks that the designated main and explicit proofs use the required manuscript-route nodes, and rejects prohibited substitute dependencies.

The comparison between the original prose, the external sources, and the formal interfaces is a separate mathematical review. That review found no unresolved substantive mismatch in the covered statements and proof routes. It is not a machine proof that natural-language prose is equivalent to Lean. The source boundary and remaining representation choices are stated in [Verification](docs/VERIFICATION.md).

The repository layout takes inspiration from [OpenAI's NavierStokesAndEuler repository](https://github.com/openai/NavierStokesAndEuler). This project has its own Lean audit suite; no independent Comparator certificate is claimed.

The paper's citation is available as [BibTeX](reference/paper.bib).

For Chinese instructions and GitHub upload steps, see [README.zh-CN.md](README.zh-CN.md).
