import PostHoc.PaperAudit

/-!
# Axioms of the post-arXiv paper-audit theorems

Prints `#print axioms` for every paper-audit theorem. Run: `lake env lean scripts/paper_audit/PaperAuditAxioms.lean`.
`scripts/paper_audit/check_paper_audit.sh` fails unless every line lists only
`propext`, `Classical.choice` and `Quot.sound` (or no axioms).
-/

open PaperAudit

#print axioms paper_eq1_eq3_hierarchy
#print axioms paper_eq2_ig_density
#print axioms paper_eq4_objective
#print axioms paper_eq5_kl_closed_form
#print axioms digamma_eq_realDigamma
#print axioms paper_eq5_closed_forms_agree
#print axioms paper_eq6_predictive_student
#print axioms paper_eq6_student_convention
#print axioms paper_eq7_eq8_quotient
#print axioms paperFiberParams_eq
#print axioms paper_eq9_fiber
#print axioms paper_fiber_predictive_invariance
#print axioms paper_eq11_B_pos
#print axioms selD_eq_two_paperB
#print axioms paper_eq12_nuCan
#print axioms paper_eq12_pos
#print axioms paper_eq13_betaCan
#print axioms paper_selected_point
#print axioms paper_eq10_unique_argmin
#print axioms paper_R_is_fiber_minimum
#print axioms paper_reduction_same_infimum
#print axioms paper_eq14_16_allocation
#print axioms paperRho0_pos
#print axioms paperT_pos
#print axioms paperT_inv_eq_score
#print axioms paper_transfer_identity
#print axioms paper_transfer_strictMono
#print axioms paper_inverse_allocation_order
#print axioms paper_prop2_formula_correspondence
#print axioms paper_prop2_found_entails_finiteness
#print axioms paper_prop10_B2_implies_L1
#print axioms paper_prop10_quantifier_gap
#print axioms paper_prop11_B2_bound
#print axioms paper_prop11_added_case
#print axioms paper_prop11_R_nonneg
#print axioms paper_prop11_reverse
#print axioms paper_prop11_B2_implies_L1
#print axioms paper_thm6_A_pos
#print axioms paper_thm6_A_zero_not_admissible
#print axioms paper_thm6_formula_boundary
#print axioms paper_thm6_admissible_monotone
