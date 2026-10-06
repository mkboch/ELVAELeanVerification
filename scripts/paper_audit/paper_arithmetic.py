"""Post-arXiv paper-wide verification: recompute the explicit arithmetic stated in arXiv v1.

Every total, fraction and percentage below is recomputed from its stated components with exact decimal
arithmetic. The components are the values printed in the paper; checking them against the underlying
study records requires the non-public research archive and is not done here.

Run: python scripts/paper_audit/paper_arithmetic.py      (exit status 0 iff all checks pass)
"""
from decimal import Decimal as D
from fractions import Fraction as F

CHECKS = []


def check(where, description, stated, recomputed):
    CHECKS.append((where, description, stated, recomputed, stated == recomputed))


# B1 / B2 outcome (Abstract, Sections 5.1-5.2, Table 3)
check("Sec 5.1", "3/25 as a percentage", "12%", f"{F(3, 25) * 100}%")
check("Sec 5.1", "accepted + repair-exhausted + blocked = 25", 25, 3 + 1 + 21)
check("Table 3", "B1 requests: 1 plan + 1 (M01) + 6 (M02) + 7 (M03)", 15, 1 + 1 + 6 + 7)
check("Sec 4.3", "module requests 1 + 6 + 7", 14, 1 + 6 + 7)
check("Sec 5.1", "blocked modules = 23 - 3 attempted (M01, M02, M03)", 20, 23 - 3)
check("Sec 5.2", "B2 fidelity labels 15 + 8 + 2", 25, 15 + 8 + 2)
check("Sec 3.4", "item types 3 + 1 + 6 + 13 + 2", 25, 3 + 1 + 6 + 13 + 2)

# Semantic record and relation audits (Abstract, Sections 5.3-5.4, Tables 4 and 8)
check("Sec 5.3", "Stage D labels 21 + 2 + 2", 25, 21 + 2 + 2)
check("Sec 4.7", "Grok item labels 24 + 1", 25, 24 + 1)
check("Sec 4.7", "Gemini item labels 22 + 3", 25, 22 + 3)
check("Sec 5.4", "relation entries 5 + 1 + 18", 24, 5 + 1 + 18)
check("Sec 5.4", "full + partial certificates 23 + 1", 24, 23 + 1)
check("Sec 5.4", "certificate entries + proposition-2 = 25", 25, 24 + 1)
check("Sec 5.4", "Lean-L2 items: 3 definition + 22 statement", 25, 3 + 22)
check("Sec 5.4", "statement schemas 11 literal + 11 adopted", 22, 11 + 11)
check("Sec 5.4", "statement items 17 audited + 5 identity", 22, 17 + 5)
check("Sec 5.7", "B2 reuse classes 2 + 2 + 1 + 4 + 14", 23, 2 + 2 + 1 + 4 + 14)
check("Sec 4.4", "reference files 12 + 24 + Basic.lean", 37, 12 + 24 + 1)
check("Sec 4.6", "Stage C declarations = 621 - 1 instance", 620, 621 - 1)
check("Sec 5.3", "Stage C corpus theorems 300 public + 25 private", 325, 300 + 25)

# E3 (Sections 4.9, 5.6, Table 5)
check("Sec 4.9", "no-change controls 6 + 4 + 5", 15, 6 + 4 + 5)
check("Sec 4.9", "semantic-change controls 10 + 14 + 8", 32, 10 + 14 + 8)
check("Sec 4.9", "controls 15 + 32", 47, 15 + 32)

# Costs (Abstract, Sections 5.7 and 6.6, Table 6, Appendix C)
historical = D("1.355855") + D("13.271525") + D("4.137840")
check("Table 6", "Stage A + B1 + Stage C (USD)", D("18.765220"), historical)
check("Abstract", "historical total as printed in the abstract", D("18.76522"), historical)
check("Table 6", "requests 1 + 15 + 2", 18, 1 + 15 + 2)
check("App C", "E1 + E2 (USD)", D("5.477745"), D("2.042540") + D("3.435205"))
check("Sec 4.2", "Stage A cost = settled 1.34958 + correction 0.006275", D("1.355855"), D("1.34958") + D("0.006275"))


def main():
    width = max(len(c[1]) for c in CHECKS)
    for where, description, stated, recomputed, ok in CHECKS:
        print(f"{'PASS' if ok else 'FAIL'}  {where:8}  {description:{width}}  stated={stated}  recomputed={recomputed}")
    failed = [c for c in CHECKS if not c[4]]
    print(f"{len(CHECKS)} arithmetic checks, {len(CHECKS) - len(failed)} pass, {len(failed)} fail")
    raise SystemExit(1 if failed else 0)


if __name__ == "__main__":
    main()
