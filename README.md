# Odd zeta values and powers of pi

Lean 4 formalization of the Lambert-series identities in Marc Chamberland and Patrick Lopatto, [*Formulas for odd zeta values and powers of π*](https://arxiv.org/abs/2406.00567v2). These exact identities express odd zeta values and powers of π through convergent series with explicit rational Bernoulli-number coefficients, of interest in analytic number theory and numerical evaluation of special values.

For S(s,r) = ∑_{k≥1} 1 / (kˢ(exp(πrk) − 1)), [Challenge.lean](Challenge.lean) states and [Solution.lean](Solution.lean) proves:

| Declaration in `Plouffe.Results` | Result |
|---|---|
| `oddPi` | A three-series formula for π^(4m−1), for m≥1. |
| `oddZeta` | A three-series formula for ζ(4m−1), for m≥1. |
| `evenPi` | A three-series formula for π^(4m+1), for m≥1. |
| `evenZeta` | A three-series formula for ζ(4m+1), for m≥1. |
| `piBase` | π = 72 S(1,1) − 96 S(1,2) + 24 S(1,4). |
| `denominatorSigns` | D(m)>0 and E(m)<0 for m≥1, ensuring nonzero denominators. |

The series use positive successor indexing; Bernoulli numbers use B₁=−1/2. Coefficients are rational, with explicit casts into ℝ or ℂ. Zeta statements use Mathlib's complex `riemannZeta` with a real right-hand side cast into ℂ. Challenge contains concrete definitions and six intentional theorem placeholders; Solution has no proof admissions and uses only `propext`, `Quot.sound`, and `Classical.choice`.

The [Plouffe](Plouffe.lean) library also retains the paper's numbered transformations, both quarter-Gamma endpoint evaluations, six numerical corollaries, and the quantitative even-denominator bound. Source provenance, including the local manuscript used for formalization, authorship, AI assistance and review are recorded in [formalization.yaml](formalization.yaml).

## Build and verify

Use the committed toolchain and Lake manifest without running `lake update`:

```sh
lake exe cache get
lake build Plouffe Solution
lake build Challenge
```

The separate Challenge build has the six expected placeholder warnings. On Linux with working bubblewrap namespaces, the toolchain also supports:

```sh
lake comparator --config comparator.json
```

[Ordinary CI](.github/workflows/ci.yml) builds and lints the sources. The [official full Palomar preflight](.github/workflows/palomar.yml) is pinned to an immutable verifier revision. Submission requires a public repository and successful full verification of the exact commit being submitted.

## Reuse and attribution

The proofs use canonical Mathlib APIs and local analytic and algebraic arguments; no external mathematical code was ported. A surveyed [Ramanujan transformation interface](https://github.com/nickgou-nuke/info-geometry-lean/tree/0a888c5bac874a08cfeb804724fb20ebfd7820f6) takes the analytic identity as a hypothesis and is not a dependency here. The survey was not exhaustive; priority and novelty relative to all prior formalizations are unknown.

Project code is copyright 2026 Patrick Lopatto under [Apache-2.0](LICENSE). Mathlib and its pinned dependencies retain their upstream licenses and notices.
