# Statement and proof coverage

This project covers Bourgade–Huang Theorems **1.5, 1.9, 1.11, and 1.12**, including their proofs, for every `β : ℚ` with `0 < β`. The reference is *Loop Equations Characterize Random Matrix Statistics*, arXiv:2607.07617v2, 9 September 2026.

All module paths below are relative to `BourgadeHuang/`. Declaration names have the prefix `BourgadeHuang.`.

## The four statements

| Theorem | Declaration | Hypotheses and conclusion |
|---|---|---|
| 1.5 | `RationalBulk.bourgade_huang_theorem_1_5` | Finite moments and the exact mixed bulk loop hierarchy identify the pole counting law with `sineBetaLaw β hβ`. |
| 1.9 | `RationalBulk.bourgade_huang_theorem_1_9` | The full moment-weighted approximate bulk hierarchy on events of probability tending to one gives vague convergence in distribution to `sineBetaLaw β hβ`. |
| 1.11 | `RationalEdge.bourgade_huang_theorem_1_11` | Finite moments and the exact mixed edge loop hierarchy identify the pole counting law with `airyBetaLaw β hβ`. |
| 1.12 | `RationalEdge.bourgade_huang_theorem_1_12` | The corresponding event-restricted approximate edge hierarchy gives vague convergence in distribution to `airyBetaLaw β hβ`. |

The input `AnchoredCountingState` consists of a locally finite integer-valued counting measure and its admissible complex Nevanlinna value at `i`. Its constraint permits multiplicities and the nonnegative affine term. The associated Nevanlinna function, derivatives, and atomic-mass recovery are constructed analytically. State measurability is explicit.

The loop hierarchies include arbitrary auxiliary lengths, both halfplanes, and repeated spectral parameters. Coincident divided differences have their analytic values. The bulk loop expression contains `+1`; the edge expression contains `−w`. Moment estimates establish integrability of the loop expressions, so their equations do not rely on the convention for nonintegrable Bochner integrals.

The `_unbundled` endpoints expose every assumption. Natural-order moments at the anchor suffice. The `_paper` endpoints for 1.5, 1.11, and 1.12 use finite positive real-order moments at every off-real parameter; these imply the anchor assumptions. Each `_anchored` endpoint additionally identifies or converges the complete joint state law.

## Approximate hierarchies

For Theorems 1.9 and 1.12, `EventWeightedHierarchy` requires measurable states and good events `A_N`, with `P(A_Nᶜ) → 0`. Moments are required only on `A_N`.

For each compact off-real parameter set and each auxiliary length `n`, a nonnegative sequence `ε_N → 0` bounds the norm of the restricted expected loop expression by

\[
\varepsilon_N\left(1+\int_{A_N}R_N^{\,n+2}\right).
\]

Here `coordinateMaximum` is the actual maximum of the Nevanlinna-function norms at the head and auxiliary parameters. Thus `n+2=p+1` for a hierarchy with `p=n+1` parameters, as in the article. The estimate is uniform over that compact parameter set.

There is no prescribed error rate or moment requirement outside the good events. Tightness, exponential anchor moments, exact limiting equations, and identification of every subsequential limit are conclusions of the proof. Vague convergence in law is stated using bounded continuous test functions on the space of locally finite counting measures with its vague topology.

## Actual Gaussian reference laws

The finite Gaussian β probability measure is built from the normalized Lebesgue density

\[
Z_{M,\beta}^{-1}
\exp\!\left(-\frac{\beta}{4M}\sum_{i=1}^{M}x_i^2\right)
\prod_{i<j}|x_i-x_j|^\beta.
\]

Positivity and finiteness of the partition function, justified integration by parts, and finite loop identities are proved, including the singular regime `0 < β < 1`.

The bulk particles near the origin define `sineBetaLaw` in the article's normalization. The soft-edge particles and centered transform are

\[
y_i=\frac{x_i-2M}{M^{1/3}},\qquad
s_M(w)=\sum_i\frac1{y_i-w}+M^{1/3}.
\]

They define `airyBetaLaw`. Compactness first produces actual Gaussian subsequential limits. Proved hierarchy uniqueness then supplies full-sequence convergence and independence of the chosen reference. The targets are therefore tied to these concrete ensembles, with no assumed reference-law uniqueness.

Relevant endpoints include `RationalBulk.gaussianBeta_full_convergence`, `RationalBulk.gaussianBeta_vague_full_convergence`, `RationalEdge.gaussianBetaEdge_full_convergence`, and `RationalEdge.gaussianBetaEdge_vague_full_convergence`.

## Proof organization

| Component | Principal modules |
|---|---|
| Representation, moments, tightness, and exact limiting hierarchies | Nevanlinna/counting-state modules; `RationalBulk` and `RationalEdge` modules `MomentBounds`, `FactorialMoments`, `Limits`, and event-reduction modules. |
| Bulk analytic uniqueness | Actual charged observables and their CMS equations; `CMS/PhysicalSectorialBasis`; rational coefficient identification, replication, and `RationalBulk/HierarchyUniqueness`. |
| Edge analytic uniqueness | `EdgeCMS/PhysicalGauge`, `PhysicalCoefficients`, `PhysicalNormalForm`, `PhysicalComparisonSystem`, `RadialSystem`, `BoundedRadial`, `RadialTerminal`, and `GenericBoundedUniqueness`. |
| Actual observable bounds and law determination at the edge | `RationalEdge/PhysicalGaugeBounds`, `ChargedSectorialSolution`, `ChargedProportionality`, `LawDetermination`, and `HierarchyUniqueness`. |
| Concrete targets and final assembly | `RationalBulk/GaussianBetaLimit`, `RationalEdge/GaussianEdgeLimit`, and the four theorem modules. |

For exact characterization, ordinary moments and the exact hierarchy imply the exponential anchor integrability needed by intermediate uniqueness results. Applying the moment argument to a constant sequence proves this implication directly.

The edge uniqueness argument uses a different route from the article's full sectorial-basis construction. An explicit nonzero WKB gauge and the actual Airy coordinate map transform the charged expectation to a homogeneous differential system. A concrete nonempty open cone gives positive spectral gaps. Bounds derived from the hierarchy imply bounded normalized observables on dilations of a neighborhood; Cauchy estimates then bound their actual scaled derivatives.

The resulting finite derivative system, backward integral identities, and an explicit large-radius contraction construct a scalar terminal functional. Its kernel has zero analytic germ. Two nonzero normalized expectations are consequently locally proportional. The invertible normalization transfers this relation to the original expectations; analytic continuation to their integration bases fixes the scalar to `1`. Rational replication determines the entire probability law.

This argument uses boundedness on dilation rays. It does not assume convergence to `1` along every such ray, assume a terminal limit, or assume an independent family of edge solutions. Generic lemmas with explicit solution, boundedness, or contraction hypotheses are instantiated by the physical construction before the final endpoints.

## Scope and verification

The coverage is the four positive-rational-β results above and the dependencies needed for their proofs. It is not every auxiliary theorem of the article. In particular, the complete `2^d` edge sectorial basis of Theorem 6.5 is not constructed. Irrational-β uniqueness, quantitative convergence rates, separate identifications with stochastic-process or stochastic-operator definitions, and largest-particle distribution results are outside the stated scope.

Run the commands in [README.md](README.md) to build the root import and audit the source and theorem dependencies. `Audit.lean` checks that theorem proofs use only `propext`, `Classical.choice`, and `Quot.sound`. The source audit checks for placeholders and custom axioms and verifies that retained modules are reachable from the root import. Kernel checking establishes the encoded propositions; this document records how those propositions correspond to the four article statements.
