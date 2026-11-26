# Contributing

Use the Lean toolchain and dependency revisions checked into this repository.
Preserve `lake-manifest.json` when reproducing the release; dependency updates
should be explicit, separately reviewed changes.

```sh
lake exe cache get
./scripts/check.sh
```

The full checker compiles every retained library, audits source and exact public
theorem signatures, checks axioms, and replays safe project declarations through
the Lean kernel. Include the command and its outcome when proposing a change.
Generated verification logs are ignored by Git and uploaded by CI.

Keep the mathematical statements faithful to the included article. Changes to
the ensemble, scaling, target law, quantifiers, admissible sizes, or W₂ cost must
be explained and reflected in the exact-signature checks and coverage notes.
Do not introduce admitted proofs, source axioms, `native_decide`, unsafe/partial
logical dependencies, or kernel-check bypasses.

The two vendored libraries are immutable checked snapshots. To update either
dependency, document the new provenance, retain its license, regenerate its
source snapshot deliberately, and rerun the complete checker. Shared-source
reuse is described in [PROVENANCE.txt](PROVENANCE.txt).

Do not commit `.lake`, compiler artifacts, private absolute paths, credentials,
or scratch copies. Retain the article PDF unchanged unless a new comparison
version is intentionally adopted, recorded by content hash, and audited against
the public theorem statements.
