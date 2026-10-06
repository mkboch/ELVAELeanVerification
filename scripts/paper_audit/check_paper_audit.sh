#!/usr/bin/env bash
# Post-arXiv paper-wide verification checks (code-level; run from the repository root after `lake build`).
#   1. proof-escape scan of PostHoc/PaperAudit (no sorry/admit/axiom/unsafe/native_decide/implemented_by);
#   2. #print axioms for every paper-audit theorem: only propext, Classical.choice, Quot.sound allowed;
#   3. the number of audited theorems equals the number of theorems declared in PostHoc/PaperAudit;
#   4. recomputation of the explicit arithmetic stated in the paper.
# Exit status 0 and "PAPER AUDIT PASSED" mean every check passed.
set -u
cd "$(dirname "$0")/../.."
fail=0

echo "== 1. Proof-escape scan (PostHoc/PaperAudit)"
if grep -nE "\bsorry\b|\badmit\b|^\s*(private\s+)?axiom\b|\bunsafe\b|native_decide|implemented_by" \
    PostHoc/PaperAudit/*.lean PostHoc/PaperAudit.lean; then
  echo "FAIL: proof escape found"; fail=1
else
  echo "none found"
fi

echo
echo "== 2. Axioms of the paper-audit theorems"
lake env lean scripts/paper_audit/PaperAuditAxioms.lean > paper_audit_axioms.log 2>&1
st=$?
total=$(grep -cE "depends on axioms|does not depend on any axioms" paper_audit_axioms.log || true)
bad=$(grep "depends on axioms" paper_audit_axioms.log \
  | grep -vE "depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]" \
  | wc -l)
errs=$(grep -c "error" paper_audit_axioms.log || true)
echo "theorems checked: ${total}; with non-standard axioms: ${bad}; Lean errors: ${errs}"
if [ $st -ne 0 ] || [ "$errs" != "0" ] || [ "$bad" != "0" ] || [ "$total" = "0" ]; then
  cat paper_audit_axioms.log; echo "FAIL: paper-audit axioms"; fail=1
fi

echo
echo "== 3. Coverage of the axiom list"
declared=$(cat PostHoc/PaperAudit/*.lean | grep -cE "^theorem ")
listed=$(grep -c "^#print axioms" scripts/paper_audit/PaperAuditAxioms.lean)
echo "theorems declared in PostHoc/PaperAudit: ${declared}; listed in PaperAuditAxioms.lean: ${listed}"
if [ "$declared" != "$listed" ] || [ "$total" != "$listed" ]; then echo "FAIL: axiom list incomplete"; fail=1; fi

echo
echo "== 4. Arithmetic stated in the paper"
python scripts/paper_audit/paper_arithmetic.py | tail -1 || fail=1
python scripts/paper_audit/paper_arithmetic.py > /dev/null || { echo "FAIL: arithmetic"; fail=1; }

echo
if [ $fail -eq 0 ]; then echo "PAPER AUDIT PASSED"; else echo "PAPER AUDIT FAILED"; fi
exit $fail
