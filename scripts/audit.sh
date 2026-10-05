#!/usr/bin/env bash
# Certification audit: clean rebuild of both libraries, diagnostic count, proof-escape search,
# axiom audits and declaration count.
# Usage (project root; Git Bash, Linux or macOS):  bash scripts/audit.sh
# Exit status 0 and "AUDIT PASSED" mean every check passed; any failure prints FAIL and exits 1.
set -u
cd "$(dirname "$0")/.."
fail=0

echo "== 1. Clean rebuild of project modules (dependency builds are kept)"
rm -rf .lake/build
lake build > audit_build.log 2>&1
build_status=$?
grep -E "Built (ELVAE|Official|PostHoc)|warning|error" audit_build.log || true
if [ $build_status -ne 0 ]; then echo "FAIL: lake build exited with $build_status"; fail=1; fi

echo
echo "== 2. Diagnostics"
n=$(grep -cE "^(warning|error)" audit_build.log || true)
echo "warnings+errors: ${n}"
if [ "$n" != "0" ]; then echo "FAIL: build produced diagnostics"; fail=1; fi

echo
echo "== 3. Proof-escape search (should find nothing)"
if grep -nE "\bsorry\b|\badmit\b|^\s*(private\s+)?axiom\b|\bunsafe\b|native_decide|implemented_by" \
    ELVAELeanVerification/*.lean Official/*.lean PostHoc/*/*.lean; then
  echo "FAIL: proof escape found"; fail=1
else
  echo "none found"
fi

echo
echo "== 3b. Relation audits (#relation_audit in PostHoc.Relations / PostHoc.LeanL2)"
pass=$(grep -c "RELATION_AUDIT .* PASS" audit_build.log || true)
rfail=$(grep -c "RELATION_AUDIT .* FAIL" audit_build.log || true)
echo "relation audits passed: ${pass}; failed: ${rfail}"
if [ "$rfail" != "0" ] || [ "$pass" -lt 46 ]; then echo "FAIL: relation audits"; fail=1; fi

echo
echo "== 4. Axiom audit of main results (ELVAE library)"
lake env lean AxiomAudit.lean > audit_axioms.log 2>&1
ax_status=$?
checked=$(grep -c "depends on axioms" audit_axioms.log || true)
bad=$(grep "depends on" audit_axioms.log | grep -vc "\[propext, Classical.choice, Quot.sound\]" || true)
errs=$(grep -c "error" audit_axioms.log || true)
echo "results checked: ${checked}; with non-standard axioms: ${bad}; Lean errors: ${errs}"
if [ $ax_status -ne 0 ] || [ "$errs" != "0" ] || [ "$bad" != "0" ] || [ "$checked" = "0" ]; then
  echo "FAIL: axiom audit"; fail=1
fi

echo
echo "== 5. Axiom report over every constant of all libraries"
if lake env lean scripts/AxiomReport.lean > audit_axiom_report.log 2>&1 \
    && grep -q "AXIOM_REPORT PASS" audit_axiom_report.log; then
  grep "AXIOM_REPORT" audit_axiom_report.log
else
  cat audit_axiom_report.log; echo "FAIL: axiom report"; fail=1
fi

echo
echo "== 6. Declaration count (ELVAE library)"
lake env lean scripts/CountDeclarations.lean || { echo "FAIL: declaration count"; fail=1; }

echo
if [ $fail -eq 0 ]; then echo "AUDIT PASSED"; else echo "AUDIT FAILED"; fi
exit $fail
