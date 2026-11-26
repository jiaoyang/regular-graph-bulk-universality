# Bulk universality of random regular graphs in Lean

Lean proofs of Theorem 1.1, Theorem 1.2, and Corollary 1.3 in the
[included article](docs/paper/bulk_universality.pdf) by Yukun He, Jiaoyang Huang,
and Xiaoyu Wang. The model is the uniform law on labelled simple fixed-degree
regular graphs, through exactly the sizes `N > d` with `Even (N*d)`.

This repository does not claim every sharper
intermediate estimate in the revised article: see the explicit
[coverage boundary](docs/v2-coverage-status.txt).

## Public results

| Article result | Lean theorem | Source |
| --- | --- | --- |
| Theorem 1.1: bulk point-process convergence | `GeneralizedBulk.Graph.uniform_regular_graph_bulk_universality_along_admissible_sizes` | [AdmissibleSizeLimits.lean](GeneralizedBulk/Graph/AdmissibleSizeLimits.lean) |
| Theorem 1.2, equation (1.2): polynomial mixed fourth-moment bounds | `GeneralizedBulk.Graph.article_polynomial_mixed_fourth` | [ArticleMixedFourth.lean](GeneralizedBulk/Graph/ArticleMixedFourth.lean) |
| Corollary 1.3: fixed-energy Gaussian approximation in W₂ | `GeneralizedBulk.Graph.corollary_1_3_real_along_sizes` | [Corollary13.lean](GeneralizedBulk/Graph/Corollary13.lean) |

The bulk theorem uses the actual microscopic eigenvalue counting measure,
retaining multiplicities and the constant mode, with the article's
`N*pi*rho_d(E)*(lambda-E)` normalization. The target `sineOneLaw` is identified
by the Gaussian-beta ensemble bulk limit at beta one, on locally finite counting
measures with the vague topology. 

The mixed fourth-moment statement is uniform over orthonormal eigenvector
families with one through four channels in a compact bulk set, including repeated
coordinate choices. Its all-size coefficient is chosen before the size, graph,
family, and slots.

Corollary 1.3 takes the full supremum over orthonormal tuples whose eigenvalues
lie in the shrinking window `abs(lambda_a-E) <= delta(N)`, comparing every tuple
with the same independent variance-one Gaussian star product at the fixed
strict-bulk energy `E`. It uses physical Euclidean W₂. The supremum is measurable
and finite, and equals zero for an empty window. Width nonnegativity and
convergence are required only through the admissible sizes; no compact set,
monotonicity, rate, or tuple-existence premise is added.

[ArithmeticAdmissibility.lean](GeneralizedBulk/Graph/ArithmeticAdmissibility.lean)
proves graph existence for every arithmetic admissible size and equality of the
intrinsic and arithmetic size filters. See the
[article comparison](docs/local-law-completeness-audit.txt) for the precise
quantifiers and definitions, and the [Corollary 1.3 proof map](docs/corollary-1-3-v2.txt)
for its implementation.

## Build and verify

Install [elan](https://github.com/leanprover/elan), Python 3, and Git. The checked-in
`lean-toolchain` selects Lean 4.19.0. `lake-manifest.json` pins Mathlib to
`c44e0c8ee63ca166450922a373c7409c5d26b00b` and records all dependency revisions.
From the repository root run:

```sh
lake exe cache get
./scripts/check.sh
```

Keep the checked-in manifest when reproducing this release. The first command
downloads compiled Mathlib dependencies; project source is built by the checker.
On a clean checkout, all project build directories begin empty. Subsequent runs
may reuse Lake's unchanged project artifacts.

The checker:

1. Verifies unchanged vendor source snapshots, scans all active Lean source,
   and checks complete import coverage.
2. Explicitly compiles all five libraries and checks module resolution to prevent
   project declarations being shadowed by dependency caches.
3. Audits all safe project declarations and exact public theorem signatures,
   permitting only `propext`, `Classical.choice`, and `Quot.sound` as axioms.
4. Rechecks every safe project declaration with the Lean kernel at trust level
   zero, starting from `Mathlib` and `Lean.Replay`, and checks that the required
   endpoints have no unsafe or partial logical dependency.

Mathlib is the trusted base and is not itself replayed. Compiler-generated
implementation auxiliaries are reported separately according to `Lean.Replay`.
The current local verification status and scope are recorded in
[verification/summary.txt](verification/summary.txt). GitHub Actions repeats the
full checker and uploads its logs.

## Reused formalizations

The repository contains five Lean libraries: `GeneralizedBulk`, `GaussianWave`,
`BourgadeHuang`, `LocalLaw`, and `SpectralConsequences`.

- The unchanged [local-law source](vendor/regular_graph_local_laws) is vendored
  from [regular-graph-local-laws](https://github.com/jiaoyang/regular-graph-local-laws)
  at `6b21a613b184d04e5c2f940a20c20a6529dc3a49`. Its proved local law, rigidity,
  and eigenvector estimates are used through explicit scaling and graph-law
  bridges. Structural conditioning is removed by proved probability bounds.
- The unchanged [loop-equation library](vendor/loop_equations) supplies
  `BourgadeHuang.RationalBulk.bourgade_huang_theorem_1_5`, applied at beta one
  after proving the loop hierarchy. Its local source snapshot is hash-verified;
  a remote Git commit has not been verified.
- `GaussianWave.BS` supplies the lower-entropy and heat-flow arguments,
  equality classification, gluing, propagation, and random-graph classification.

The exact sources and licenses are documented in [PROVENANCE.txt](PROVENANCE.txt)
and [NOTICE](NOTICE). The [proof architecture](docs/full-closure-blueprint.txt),
[semantic review](docs/final-theorem-reaudit.txt), and
[article identity](docs/article-source.json) are retained with the source.

The Lean source is MIT-licensed. The article PDF retains its authors' copyright
and is excluded from that software license. See [LICENSE](LICENSE) and
[the paper note](docs/paper/README.md). Contribution guidance is in
[CONTRIBUTING.md](CONTRIBUTING.md); citation metadata is in [CITATION.cff](CITATION.cff).
