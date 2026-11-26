#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p verification
python3 scripts/check_sources.py | tee verification/source-audit.log
lake build GeneralizedBulk GaussianWave BourgadeHuang LocalLaw SpectralConsequences 2>&1 | tee verification/build.log
lake --no-build build 2>&1 | tee verification/default-targets-check.log
lake env python3 scripts/check_module_resolution.py 2>&1 | tee verification/module-resolution-audit.log
lake env lean scripts/AuditAll.lean 2>&1 | tee verification/merged-axiom-audit.log
lake env lean Audit.lean 2>&1 | tee verification/bulk-endpoint-audit.log
lake env lean scripts/GaussianWaveAudit.lean 2>&1 | tee verification/gaussian-wave-audit.log
lake env lean scripts/LocalLawIntegrationAudit.lean 2>&1 | tee verification/local-law-integration-audit.log
lake env lean scripts/ArticleAudit.lean 2>&1 | tee verification/article-endpoint-audit.log
lake env lean scripts/DeepAudit.lean 2>&1 | tee verification/deep-audit.log
lake env lean scripts/KernelReplayAll.lean 2>&1 | tee verification/merged-kernel-replay.log
