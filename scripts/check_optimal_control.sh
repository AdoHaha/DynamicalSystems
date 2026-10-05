#!/usr/bin/env bash
# Build the actual library, regression modules, and exhaustive K3/K4 audits.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.."

lake build DynamicalSystems

kirk_check_options=(
  -DautoImplicit=false
  -DrelaxedAutoImplicit=false
  -DmaxSynthPendingDepth=3
  -Dlinter.flexible=true
  -Dlinter.mathlibStandardSet=true
  -Dwarn.sorry=true
)

mkdir -p .lake/build/lib/lean/DynamicalSystemsTest/KirkMedhin
for kirk_test in \
  K3IsoperimetricExample \
  WeakEulerLagrangeEndpoint \
  WeakDuBoisReymond \
  NonautonomousDuBoisReymond
do
  lake env lean "${kirk_check_options[@]}" --root=. \
    -o ".lake/build/lib/lean/DynamicalSystemsTest/KirkMedhin/${kirk_test}.olean" \
    "DynamicalSystemsTest/KirkMedhin/${kirk_test}.lean"
done

lake env lean "${kirk_check_options[@]}" --root=. docs/kirk_medhin/K3K4Audit.lean
lake env lean "${kirk_check_options[@]}" --root=. docs/kirk_medhin/K3K4ProofPaths.lean
lake env lean "${kirk_check_options[@]}" --root=. docs/kirk_medhin/CampaignTargets.lean
