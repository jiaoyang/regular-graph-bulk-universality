#!/usr/bin/env python3
"""Audit the merged libraries and both complete vendored dependencies.

This scans source text after removing nested comments and strings. All retained
library modules must also be reachable from their checked root imports.
The Lean audit separately checks actual theorem dependency axioms.
"""
from pathlib import Path
import re
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]


def code_only(source):
    """Strip nested Lean block comments, line comments, and string literals."""
    out = []
    i, depth, string = 0, 0, False
    while i < len(source):
        pair = source[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                if source[i] == "\n":
                    out.append("\n")
                i += 1
        elif string:
            if source[i] == "\\":
                i += 2
            elif source[i] == '"':
                string = False
                i += 1
                out.append(" ")
            else:
                i += 1
        elif pair == "/-":
            depth = 1
            i += 2
            out.append(" ")
        elif pair == "--":
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        elif source[i] == '"':
            string = True
            i += 1
        else:
            out.append(source[i])
            i += 1
    if depth or string:
        raise ValueError("Unterminated comment or string")
    return "".join(out)


def main():
    loop = ROOT / "vendor" / "loop_equations"
    loop_snapshot = json.loads((ROOT / "vendor" / "SOURCE_SNAPSHOT.json").read_text())
    for relative, expected in loop_snapshot["files"].items():
        path = loop / relative
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise SystemExit(f"Vendored loop-characterization snapshot mismatch: {relative}")
    print(f"Loop-characterization snapshot verified: {len(loop_snapshot['files'])} unchanged sources.")
    dependency = ROOT / "vendor" / "regular_graph_local_laws"
    snapshot = json.loads((dependency / "SOURCE_SNAPSHOT.json").read_text())
    for relative, expected in snapshot["unchanged_upstream_files"].items():
        path = dependency / relative
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise SystemExit(f"Vendored local-law snapshot mismatch: {relative}")
    print(f"GitHub local-law snapshot verified: {snapshot['revision']}; "
          f"{len(snapshot['unchanged_upstream_files'])} unchanged upstream files.")
    libraries = {
        "GeneralizedBulk": ROOT,
        "GaussianWave": ROOT,
        "BourgadeHuang": ROOT / "vendor" / "loop_equations",
        "LocalLaw": ROOT / "vendor" / "regular_graph_local_laws",
        "SpectralConsequences": ROOT / "vendor" / "regular_graph_local_laws",
    }
    modules = {}
    for name, base in libraries.items():
        root_file = base / f"{name}.lean"
        if root_file.exists():
            modules[name] = root_file
        for path in (base / name).rglob("*.lean"):
            suffix = ".".join(path.relative_to(base / name).with_suffix("").parts)
            modules[f"{name}.{suffix}"] = path
    audit_files = [ROOT / "Audit.lean", *sorted((ROOT / "scripts").glob("*.lean"))]
    paths = sorted(set(modules.values()) | set(audit_files))
    count = 0
    cleaned = {}
    for path in paths:
        code = code_only(path.read_text())
        cleaned[path] = code
        forbidden = re.search(r"\b(sorry|admit|axiom|native_decide|unsafe|partial|sorryAx)\b", code)
        if forbidden:
            raise SystemExit(f"Forbidden proof construct {forbidden.group()!r} in {path.relative_to(ROOT)}")
        if "skipKernelTC" in code:
            raise SystemExit(f"Kernel-check bypass in {path.relative_to(ROOT)}")
        count += len(re.findall(r"\b(?:theorem|lemma)\s+", code))
    reachable = set()
    todo = ["GeneralizedBulk", "GaussianWave", "BourgadeHuang",
            "LocalLaw.Audit", "SpectralConsequences.Audit"]
    while todo:
        name = todo.pop()
        if name in reachable or name not in modules:
            continue
        reachable.add(name)
        for line in cleaned[modules[name]].splitlines():
            if line.strip().startswith("import "):
                for imported in line.strip()[7:].split():
                    if imported.split(".")[0] in libraries and imported not in modules:
                        raise SystemExit(f"Missing local import {imported} in {modules[name].relative_to(ROOT)}")
                    todo.append(imported)
    missing = sorted(set(modules) - reachable)
    if missing:
        raise SystemExit("Library modules outside checked root imports: " + ", ".join(missing))
    print(f"Source audit passed for {len(paths)} Lean files: {count} theorem/lemma declarations;")
    print("no admitted proofs, source axioms, unsafe/partial declarations or kernel-check bypasses.")
    print(f"Import coverage passed: all {len(modules)} local library modules are reachable.")
    for name, base in libraries.items():
        total = sum(1 for module in modules if module == name or module.startswith(name + "."))
        print(f"  {name}: {total} modules")


if __name__ == "__main__":
    main()
