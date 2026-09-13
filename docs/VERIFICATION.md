# Verification and scope

Run from the repository root after installing the pinned Lean toolchain, Git, and Python 3.10 or later:

```sh
lake exe cache get
python3 scripts/verify.py --jobs 3
```

This command recompiles the project mathematical sources and runs the audit suite. Mathlib and its dependencies are reused from their pinned compiled cache; this is not a fresh reconstruction of every dependency from source. The ordinary `lake build` command builds the library but does not run all audit gates.

## Nine verification gates

| Gate | Purpose |
|---|---|
| Project source compilation | Compile all 361 mathematical modules in dependency order; record source, dependency-closure, and compiled-object hashes |
| Root import | Compile `BerryEsseen.lean` and check that it imports every project mathematical module |
| Project axioms | Inspect the recursive axiom dependencies of project declarations; reject `sorryAx` and unexpected axioms |
| Exact kernel types | Check the designated theorem types, including the original explicit threshold and the order of the main theorem's quantifiers |
| Manuscript statement coverage | Expose the registered 31 primary statement endpoints and 16 additional conjunct endpoints |
| Supplementary original routes | Check additional interfaces and proof dependencies needed by the manuscript routes |
| Main proof dependencies | Inspect the actual main proof expression for the required nodes and prohibited substitutes |
| Explicit proof dependencies | Perform the corresponding inspection for the explicit theorem |
| Full bounded-extremizer statement | Compile the wrapper that returns all original conjuncts for the same sequence of sample sizes, laws, and evaluation points |

The full-statement gate is in [`Checks/BoundedFullStatementAudit.lean`](../Checks/BoundedFullStatementAudit.lean). It derives the full Kolmogorov supremum equality from the production endpoint's signed attainment, using an already proved theorem. It introduces no new external premise.

Results are written under `validation/`. A successful run ends with `all_strict_gates_passed: true` in `validation/strict-summary.json`. Read that result together with its gate exit codes and hashes. A pre-existing successful log is evidence for its recorded source snapshot, not a substitute for checking modified sources.

The optional `--incremental` mode reuses a compiled project module only when its source, dependency closure, and compiled-object hashes match the recorded build. Omit that option for a full recompilation of project sources. `--jobs 1` reduces concurrent compiler processes.

## Interpreting the result

The axiom audit allows Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. A successful axiom check does **not** discharge explicit proposition parameters: the three final results still depend on the [documented external mathematical interfaces](ASSUMPTIONS.md).

The main and explicit dependency checks inspect actual proof expressions, rather than merely searching source text for theorem names. Their required-node lists support review of the selected proof routes. They do not prove that the lists exhaust every possible semantic mismatch with the manuscript.

The [statement map](STATEMENT_MAP.md) covers 31 named manuscript statement groups, including the jitter-width remark, plus 16 registered supplemental endpoints. Several original statements are conjunctions represented by more than one endpoint. Checking only a row's primary endpoint can omit part of the original statement; use the listed supplemental endpoints and the bounded-extremizer wrapper as indicated.

## Mathematical review beyond the kernel

The accompanying review compared the original manuscript with the formal statements, definitions, and key proof chains, and compared the external interfaces with the cited source texts. That review found no unresolved substantive mismatch in the covered statements or original proof routes. This is a mathematical review conclusion, separate from Lean's checking of the formal proof terms.

The representation choices are explicit:

- The main statement uses real probability laws and actual product/map convolutions. It does not add a separate endpoint transporting the result to arbitrary random variables on an arbitrary underlying probability space via `iIndepFun`.
- The universal sample-size threshold precedes the probability law, and no common bound on third moments is imposed.
- H, I, and U use the source-to-interface CDF and variance reformulations described in [External assumptions](ASSUMPTIONS.md); those reformulations are reviewed mathematically rather than supplied as separate formal conversion proofs from the publications.
- Auxiliary alternative proofs remain in the library. The designated strict endpoints and the registered proof-route checks identify the manuscript routes; in particular, `strict_sharpness` uses the original fixed-law Esseen asymptotic argument.

Neither the kernel checks nor the source audit constitute a machine-certified equivalence between natural-language prose and Lean. No independent Comparator run or certificate is included or claimed.

## Audited manuscript identity

The bundled [`reference/aop-sample.tex`](../reference/aop-sample.tex) is the exact source used for the review. Its SHA-256 is:

```text
c7230bf3a2410f1df8be31045370212f8c4a5d208474528fb8ef966d1c418229
```

The manuscript is included for correspondence checking; this package does not supply the complete external journal template needed to typeset it. Its known citation-page correction is recorded separately in [the erratum](../reference/errata-current-recheck.md).
