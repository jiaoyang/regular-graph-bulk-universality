#!/usr/bin/env python3
"""Freeze a source release, then summarize its completed build/kernel audit.

Run ``python3 scripts/check_release.py --freeze`` before ``scripts/check.sh``.
After recording its actual exit code in verification/release-run-exit.json,
run this script with ``--finish``. The helper checks receipts and source hashes;
Lean's checkers, rather than this Python script, check the mathematical proofs.
All paths in generated receipts are relative to the repository root.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import re


TOOLCHAIN = "leanprover/lean4:v4.19.0"
MATHLIB_REV = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
EXCLUDED = {".lake", ".git", "__pycache__", ".DS_Store"}
VENDORS = ("vendor/loop_equations", "vendor/regular_graph_local_laws")
ENDPOINTS = {
    "thm:main": "GeneralizedBulk.Graph.uniform_regular_graph_bulk_universality_along_admissible_sizes",
    "thm:fourth": "GeneralizedBulk.Graph.article_polynomial_mixed_fourth",
    "cor:gaussian": "GeneralizedBulk.Graph.corollary_1_3_real_along_sizes",
}


def fail(message):
    raise SystemExit(message)


def load_json(path):
    try:
        return json.loads(path.read_text())
    except (OSError, ValueError) as exc:
        fail(f"Invalid or missing {path.name}: {exc}")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def relative_path(value):
    path = Path(value)
    if path.is_absolute() or ".." in path.parts:
        fail(f"Release metadata contains a nonportable path: {value}")
    return path


def inventory(root):
    hashes = {}
    for path in sorted(root.rglob("*")):
        relative = path.relative_to(root)
        if relative.parts[0] == "verification" or EXCLUDED.intersection(relative.parts):
            continue
        if path.is_symlink():
            fail(f"Distributable source is a symlink: {relative}")
        if path.is_file():
            if path.suffix in {".olean", ".ilean", ".o", ".a", ".so", ".dylib", ".pyc"}:
                fail(f"Build artifact outside an excluded cache: {relative}")
            hashes[relative.as_posix()] = digest(path)
    return hashes


def check_metadata(root):
    for base in ("", *VENDORS):
        directory = root / base
        if (directory / "lean-toolchain").read_text().strip() != TOOLCHAIN:
            fail(f"Unexpected Lean toolchain in {base or 'root'}")
        if not (directory / "LICENSE").is_file():
            fail(f"Missing source license in {base or 'root'}")
    manifests = {}
    for base in ("", *VENDORS):
        manifest = load_json(root / base / "lake-manifest.json")
        packages = {p["name"]: p for p in manifest["packages"]}
        if packages.get("mathlib", {}).get("rev") != MATHLIB_REV:
            fail(f"Unexpected Mathlib revision in {base or 'root'} manifest")
        for package in packages.values():
            if package["type"] == "path":
                relative_path(package["dir"])
            elif package["type"] == "git":
                if not re.fullmatch(r"[0-9a-f]{40}", package.get("rev", "")):
                    fail(f"Unpinned Git dependency: {package['name']}")
            else:
                fail(f"Unsupported dependency type: {package['name']}")
        manifests[base] = packages
    root_packages = manifests[""]
    expected_paths = {"bourgade_huang": VENDORS[0], "regular_graph_local_laws": VENDORS[1]}
    for name, directory in expected_paths.items():
        package = root_packages.get(name, {})
        if package.get("type") != "path" or package.get("dir") != directory:
            fail(f"Missing relative vendored dependency: {name}")
    for base in VENDORS:
        for name, package in manifests[base].items():
            if package["type"] == "git" and root_packages.get(name, {}).get("rev") != package["rev"]:
                fail(f"Dependency revision differs between root and {base}: {name}")
    config = (root / "lakefile.toml").read_text()
    if not re.search(r'rev\s*=\s*"' + MATHLIB_REV + r'"', config):
        fail("Root lakefile.toml does not explicitly pin the expected Mathlib commit")
    article = load_json(root / "docs/article-source.json")
    pdf = article.get("pdf", {})
    pdf_path = relative_path(pdf.get("path", ""))
    if not pdf_path.parts or pdf_path.suffix != ".pdf":
        fail("Article metadata must identify the bundled PDF")
    actual_pdf = root / pdf_path
    if not actual_pdf.is_file() or digest(actual_pdf) != pdf.get("sha256"):
        fail("Bundled PDF does not match docs/article-source.json")
    if not actual_pdf.read_bytes().startswith(b"%PDF-") or pdf.get("pages", 0) <= 0:
        fail("Bundled article does not have valid PDF metadata")
    if article.get("principal_labels") != ENDPOINTS:
        fail("Article endpoint map is not the checked three-endpoint map")
    return article


def log_text(root, name, marker):
    path = root / "verification" / name
    if not path.is_file():
        fail(f"Missing verification log: {name}")
    text = re.sub(r"\x1b\[[0-9;]*m", "", path.read_text())
    if marker not in text:
        fail(f"Required completion marker absent from {name}: {marker}")
    return text


def match_numbers(pattern, text, name):
    match = re.search(pattern, text)
    if match is None:
        fail(f"Cannot read verification counts from {name}")
    return tuple(int(value) for value in match.groups())


def finish(root, article):
    verification = root / "verification"
    exit_receipt = load_json(verification / "release-run-exit.json")
    if type(exit_receipt.get("exit_code")) is not int or exit_receipt["exit_code"] != 0:
        fail("Canonical release check did not finish with exit code zero")
    start = load_json(verification / "release-build-start.json")
    if start.get("project_build_directories_empty") is not True:
        fail("Missing confirmation that project build directories started empty")
    if start.get("mathlib_revision") != MATHLIB_REV:
        fail("Build-start receipt identifies a different Mathlib revision")
    if start.get("project_artifacts_reused") is not False:
        fail("Build-start receipt does not exclude reuse of old project artifacts")
    expected_build_dirs = {".lake/build", *(base + "/.lake/build" for base in VENDORS)}
    build_dirs = start.get("project_build_directories", [])
    if {item.get("path") for item in build_dirs} != expected_build_dirs:
        fail("Build-start receipt omits a project-library build directory")
    if any(item.get("exists") is not False or item.get("olean_count") != 0 for item in build_dirs):
        fail("A project build directory was not absent before the fresh build")
    fresh_build = log_text(root, "fresh-source-build.log", "Build completed successfully.")
    frozen = load_json(verification / "release-input-hashes.json")
    current = inventory(root)
    if current != frozen.get("files"):
        old = frozen.get("files", {})
        changes = sorted(name for name in set(old) | set(current) if old.get(name) != current.get(name))
        fail("Release files changed after --freeze: " + ", ".join(changes[:20]))
    source = log_text(root, "source-audit.log", "Import coverage passed:")
    source_files, source_theorems = match_numbers(
        r"Source audit passed for (\d+) Lean files: (\d+) theorem/lemma", source, "source-audit.log")
    modules, = match_numbers(r"Import coverage passed: all (\d+) local library modules", source, "source-audit.log")
    if "Loop-characterization snapshot verified:" not in source or "GitHub local-law snapshot verified:" not in source:
        fail("Source audit did not verify both upstream snapshots")
    build = log_text(root, "build.log", "Build completed successfully.")
    totals = [int(value) for value in re.findall(r"\[\d+/(\d+)\]", fresh_build + "\n" + build)]
    if not totals:
        fail("Build log does not report a target count")
    log_text(root, "default-targets-check.log", "Build completed successfully.")
    log_text(root, "module-resolution-audit.log", f"all {modules} project modules resolve to their own checked build directories")
    axioms = log_text(root, "merged-axiom-audit.log", "Allowed foundations: propext, Classical.choice, Quot.sound.")
    safe, axiom_modules = match_numbers(
        r"Merged axiom audit passed for all (\d+) safe constants from (\d+) local modules", axioms, "merged-axiom-audit.log")
    if axiom_modules != modules:
        fail("Axiom/source module counts disagree")
    for name in ENDPOINTS.values():
        if f"Complete article endpoint has no BS/HY hypothesis: {name}" not in axioms:
            fail(f"Missing axiom/signature guard for {name}")
    for name in ("bulk-endpoint-audit.log", "gaussian-wave-audit.log", "local-law-integration-audit.log"):
        log_text(root, name, "depends on axioms:")
    article_audit = log_text(root, "article-endpoint-audit.log", "depends on axioms:")
    if article_audit.count("depends on axioms:") < len(ENDPOINTS):
        fail("Article endpoint audit does not report axioms for all three endpoints")
    for name in ENDPOINTS.values():
        if name not in article_audit or f"'{name}' depends on axioms:" not in article_audit:
            fail(f"Article endpoint audit is missing its checked type or axiom report: {name}")
    deep = log_text(root, "deep-audit.log", "PASSED: exact literal uniform-graph, arithmetic admissibility,")
    deep_safe, origin_changes = match_numbers(
        r"PASSED: (\d+) safe local declarations have identical types, bodies and universes under reversed root-import order; (\d+) shared declaration origin changes", deep, "deep-audit.log")
    kernel = log_text(root, "merged-kernel-replay.log", f"PASSED: all {safe} safe declarations from all five merged libraries replayed at trust level zero")
    kernel_modules, kernel_safe, auxiliaries, closure = match_numbers(
        r"Merged replay: (\d+) modules; (\d+) safe declarations; (\d+) generated implementation auxiliaries skipped\. Complete endpoint closure: (\d+) safe constants", kernel, "merged-kernel-replay.log")
    if (deep_safe, kernel_safe, kernel_modules) != (safe, safe, modules):
        fail("Axiom, deep-audit, and kernel-replay counts disagree")
    summary = {
        "status": "PASS", "date_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "toolchain": TOOLCHAIN, "mathlib_revision": MATHLIB_REV,
        "fresh_project_source_build": True, "dependency_artifacts_reused": start.get("dependency_artifacts_reused", True),
        "fresh_build_log": "verification/fresh-source-build.log", "project_artifacts_reused": False,
        "mathlib_replayed": False, "allowed_foundations": ["propext", "Classical.choice", "Quot.sound"],
        "source_release_files": len(current), "scanned_lean_files": source_files,
        "textual_theorem_lemma_declarations": source_theorems, "library_modules": modules,
        "build_targets": max(totals), "safe_declarations_audited_and_replayed": safe,
        "generated_implementation_auxiliaries_skipped": auxiliaries,
        "safe_logical_endpoint_closure": closure, "identical_equation_lemma_origin_changes": origin_changes,
        "article_pdf": article["pdf"], "principal_endpoints": ENDPOINTS,
        "source_inventory": "verification/release-input-hashes.json",
        "canonical_command": "./scripts/check.sh", "canonical_exit_code": 0,
        "scope": "Principal Theorem 1.1, Theorem 1.2, and Corollary 1.3; sharper intermediate estimates remain governed by docs/v2-coverage-status.txt.",
    }
    (verification / "release-summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    text = f"""BULK UNIVERSALITY SOURCE RELEASE — PASS

Theorem 1.1: {ENDPOINTS['thm:main']}
Theorem 1.2: {ENDPOINTS['thm:fourth']}
Corollary 1.3: {ENDPOINTS['cor:gaussian']}

Fresh project-source build: {max(totals)} targets; {modules} library modules.
Project build directories began empty. Pinned Mathlib/support artifacts were reused.
Source scan: {source_files} Lean files; {source_theorems} textual theorem/lemma declarations.
Both unchanged upstream source snapshots and module-provider paths checked.
Exact endpoint signatures and literal model/metric definitions checked.
All {safe} safe project declarations passed axiom audit and trust-level-zero kernel replay.
Only propext, Classical.choice, and Quot.sound occur transitively.
Endpoint logical closure: {closure} safe constants, with no unsafe/partial dependency.
Generated implementation auxiliaries separately skipped: {auxiliaries}.
Reversed imports preserve all safe types/bodies/universes; {origin_changes} identical
generated equation lemmas change only their origin attribution.
Replay base: Mathlib + Lean.Replay; Mathlib itself was not replayed.

Toolchain: {TOOLCHAIN}; Mathlib: {MATHLIB_REV}.
Bundled article: {article['pdf']['path']}
PDF SHA256: {article['pdf']['sha256']}
Frozen source/doc/config/PDF files rehashed unchanged: {len(current)}.
Canonical command: ./scripts/check.sh; final exit code: 0.
Machine-readable receipt: verification/release-summary.json.

Scope: the three principal conclusions. Sharper intermediate article estimates
are documented separately in docs/v2-coverage-status.txt.
"""
    (verification / "summary.txt").write_text(text)
    print(json.dumps(summary, indent=2, sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--freeze", action="store_true")
    action.add_argument("--finish", action="store_true")
    args = parser.parse_args()
    root = args.root.resolve()
    article = check_metadata(root)
    if args.freeze:
        verification = root / "verification"
        verification.mkdir(exist_ok=True)
        files = inventory(root)
        receipt = {"schema_version": 1, "toolchain": TOOLCHAIN, "mathlib_revision": MATHLIB_REV, "files": files}
        (verification / "release-input-hashes.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
        print(f"Frozen {len(files)} source/doc/config/PDF files; article hash and pinned manifests verified.")
    else:
        finish(root, article)


if __name__ == "__main__":
    main()
