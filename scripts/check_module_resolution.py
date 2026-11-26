#!/usr/bin/env python3
"""Reject dependency-cache shadowing of any project module after the build."""
from pathlib import Path
import os

ROOT = Path(__file__).resolve().parents[1]
LIBRARIES = {
    "GeneralizedBulk": ROOT,
    "GaussianWave": ROOT,
    "BourgadeHuang": ROOT / "vendor/loop_equations",
    "LocalLaw": ROOT / "vendor/regular_graph_local_laws",
    "SpectralConsequences": ROOT / "vendor/regular_graph_local_laws",
}


def main():
    search = os.environ.get("LEAN_PATH")
    if not search:
        raise SystemExit("Run this check with lake env python3.")
    directories = [Path(p).resolve() for p in search.split(os.pathsep)]
    count = 0
    for name, base in LIBRARIES.items():
        root_file = base / f"{name}.lean"
        sources = ([root_file] if root_file.is_file() else []) + sorted((base / name).rglob("*.lean"))
        # Lean selects the first provider of the root prefix, even when an
        # individual descendant .olean is missing from that provider.
        package_provider = next((p for p in directories if
            (p / name).is_dir() or (p / f"{name}.olean").exists()), None)
        if package_provider is None:
            raise SystemExit(f"No module provider for root prefix {name}")
        for source in sources:
            relative = source.relative_to(base).with_suffix(".olean")
            expected = (base / ".lake/build/lib/lean" / relative).resolve()
            provider = package_provider / relative
            if not provider.is_file() or provider.resolve() != expected:
                raise SystemExit(f"Unexpected module provider for {relative}: {provider}; expected {expected}")
            count += 1
    print(f"Module-resolution audit passed: all {count} project modules resolve to their own checked build directories; no dependency-cache shadowing.")


if __name__ == "__main__":
    main()
