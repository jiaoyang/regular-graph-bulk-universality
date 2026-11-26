# Verification records

`summary.txt` and `release-summary.json` report the completed local release check.
`release-input-hashes.json` identifies the current distribution.
`proof-check-input-hashes.json` preserves the original 25 November proof-run
inventory, and `proof-check-summary.json` preserves its verification results.
The 26 November PDF-only refresh is recorded in `pdf-update-2026-11-26.json`;
no Lean source, configuration, dependency, or checker changed, and the build
and kernel replay were not rerun for that document update.

The mathematical libraries were built with initially empty project build directories; only pinned Mathlib and
support-package artifacts were shared. The `release-build-start.json` receipt
records that initial state.

`mathematical-source-preservation.json` records the byte comparison with the
pre-cleanup mathematical libraries. `dependency-source-status.json` records the
checked dependency revisions and clean tracked source state.

Run `../scripts/check.sh` from this directory, or `./scripts/check.sh` from the
repository root, to regenerate all compile, endpoint, axiom, and kernel logs.
Generated `.log` files are ignored by Git and are included in the release ZIP;
GitHub Actions also uploads them as verification artifacts. The tracked local
receipts describe their recorded run and are not a claim that GitHub CI has
already run.

The project kernel replay starts from Mathlib and Lean.Replay. Mathlib is not
itself replayed. The allowed logical foundations are propext, Classical.choice,
and Quot.sound. Sharper intermediate article estimates outside the principal
three conclusions remain listed in `../docs/v2-coverage-status.txt`.
