# Vendored proof libraries

Build and verify these libraries through the repository-root `scripts/check.sh`.
It explicitly builds `BourgadeHuang`, `LocalLaw`, and `SpectralConsequences`
alongside the bulk and Gaussian-wave libraries, verifies the source snapshots,
and includes their safe declarations in the full kernel replay.

`loop_equations/` retains all 402 mathematical Lean sources of the checked local
loop-characterization snapshot. Its upstream README describes the standalone
project; standalone audit scripts are not bundled in this source snapshot.
The root checker supplies the integrated audits. Its hash inventory is
`SOURCE_SNAPSHOT.json`.

`regular_graph_local_laws/` retains the upstream snapshot at revision
6b21a613b184d04e5c2f940a20c20a6529dc3a49, including its source/configuration
and license hashes in its own `SOURCE_SNAPSHOT.json`.

Both upstream licenses remain in place. See the root `NOTICE` and
`PROVENANCE.txt` for attribution and exact mathematical scope.
