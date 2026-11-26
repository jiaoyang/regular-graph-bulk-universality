# Characterization of Random Matrix Statistics Using Loop Equations

Lean statements and proofs of Theorems **1.5, 1.9, 1.11, and 1.12** from Paul Bourgade and Jiaoyang Huang, *Loop Equations Characterize Random Matrix Statistics*, arXiv:2607.07617v2, for **every positive rational β**.

| Theorem | Result | Source |
|---|---|---|
| 1.5 | The exact bulk loop hierarchy identifies the Sineβ law. | `BourgadeHuang/RationalBulk/Theorem15.lean` |
| 1.9 | The event-restricted approximate bulk hierarchy implies vague convergence in law to Sineβ. | `BourgadeHuang/RationalBulk/Theorem19.lean` |
| 1.11 | The exact edge loop hierarchy identifies the Airyβ law. | `BourgadeHuang/RationalEdge/Theorem11.lean` |
| 1.12 | The event-restricted approximate edge hierarchy implies vague convergence in law to Airyβ. | `BourgadeHuang/RationalEdge/Theorem12.lean` |

Sineβ and Airyβ are constructed from the actual Gaussian β bulk and soft-edge ensembles. The proofs establish full-sequence convergence and independence of the reference subsequence. The four endpoints derive the needed moment estimates, tightness, limiting equations, and uniqueness internally.

Import the complete formalization with:

```lean
import BourgadeHuang

#check BourgadeHuang.RationalBulk.bourgade_huang_theorem_1_5
#check BourgadeHuang.RationalBulk.bourgade_huang_theorem_1_9
#check BourgadeHuang.RationalEdge.bourgade_huang_theorem_1_11
#check BourgadeHuang.RationalEdge.bourgade_huang_theorem_1_12
```

Each theorem has an `_unbundled` version exposing its assumptions and an `_anchored` version identifying or converging the joint counting-state and anchor law. Theorems 1.5, 1.11, and 1.12 also have `_paper` versions using the article's real-order moment hypotheses.

## Build and audit

The project pins Lean **4.19.0** and mathlib **v4.19.0**. From this directory, with Lean/Lake installed:

```bash
lake exe cache get
lake build
lake env lean Audit.lean
python3 scripts/check_sources.py
```

The Lean audit permits only `propext`, `Classical.choice`, and `Quot.sound`. The source audit checks proof placeholders, custom axioms, and module reachability. These checks complement mathematical review of the definitions and hypotheses.

See [COVERAGE.md](COVERAGE.md) for the proof structure and precise scope. The edge proof uses bounded normalized analytic germs; it does not construct the article's full Theorem 6.5 sectorial basis. Irrational β and other results from the article are outside this project's stated coverage.
