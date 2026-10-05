import ELVAELeanVerification.VerifiedCore

/-!
Axiom audit for the key results. Run with

  lake env lean AxiomAudit.lean

Every line must report only `[propext, Classical.choice, Quot.sound]`
(the standard axioms of Lean 4 + mathlib). Any project-specific axiom or
`sorryAx` would indicate a gap.
-/

open ELVAE

-- Canonical selector and global minimum
#print axioms verified_canonical_selector_core
#print axioms nuCan_unique_global_minimizer
#print axioms stationaryDerivative_zero_iff_nuCan
#print axioms fiberObjective_deriv_eq_zero_iff_nuCan
-- Parameter bridge, variance allocation, sensitivity
#print axioms betaCanFromParams_lt_c
#print axioms canonical_variance_allocation_ratio
#print axioms nuCan_deriv_B_bounds
#print axioms nuCan_strictMonoOn_B
-- Ordinal geometry / geometric transfer
#print axioms canonicalTransfer_order_iff
#print axioms actual_inverse_allocation_order_iff_T
#print axioms actual_invNuCan_eq_closedForm
-- The prior ceiling M₀
#print axioms M0_eq_closedForm
#print axioms actual_inverse_allocation_bounds
#print axioms canonical_variance_ratio_lt_M0
#print axioms M0_strictMono_alpha0
#print axioms M0_tendsto_alpha0_zero
#print axioms M0_asymptotic_isBigO
#print axioms M0_remainder_first_order
-- Boundary behaviour of the fiber objective
#print axioms fiberObjective_tendsto_atTop_nhdsGT_zero
#print axioms fiberObjective_tendsto_atTop_atTop
#print axioms restrictedNIGKL_boundary
-- Prior self-consistency and gauge limits
#print axioms nuCanFromParams_at_prior
#print axioms betaCanFromParams_at_prior
#print axioms Rcan_at_prior
#print axioms rho0_fixed_marginal_tendsto_atTop
#print axioms rho0_fixed_marginal_tendsto_nhdsGT_zero
-- Real analyticity of the canonical section
#print axioms canonicalSection_analyticOnNhd
-- Exact partial minimization
#print axioms partial_minimization_sInf_eq
#print axioms partial_minimization_minimizer_iff
#print axioms theorem2_nigKL_sInf_eq
#print axioms theorem2_nigKL_strict_penalty
#print axioms verified_theorem2_certificate
-- Level-A KL reduction
#print axioms nigKL_on_fiber
-- Student-t marginal law of the latent variable
#print axioms nigZMarginal_eq_studentT
#print axioms nigZMarginal_fiber_invariant
#print axioms nigMuMarginal_eq_studentT
#print axioms isProbabilityMeasure_studentTMeasure
-- Envelope and covariance
#print axioms fiberObjectiveMin_hasDerivAt
#print axioms TFromParams_scale_translate
#print axioms betaCanFromParams_scale_translate
-- Uncertainty decomposition from the NIG law
#print axioms integral_invGammaMeasure
#print axioms integral_sq_sub_nigMuMarginal
#print axioms integral_sq_sub_nigZMarginal
#print axioms nig_uncertainty_decomposition_on_fiber
-- Level B: NIG KL from the measures
#print axioms integral_log_mul_gammaPDFReal
#print axioms klDiv_withDensity_ofReal
#print axioms klDiv_nigMeasure
#print axioms toReal_klDiv_nigMeasure
#print axioms nigKLClosedForm_nonneg
#print axioms nigMeasure_map_fst
#print axioms nigMeasure_map_snd
-- Partial minimization / selector / boundary behaviour for the measure-theoretic KL
#print axioms klDiv_nig_fiber_eq
#print axioms klDiv_nig_fiber_strict_min
#print axioms klDiv_nig_fiber_boundary
#print axioms theorem2_klDiv_sInf_eq
#print axioms theorem2_klDiv_strict_penalty
#print axioms theorem2_klDiv_minimizer_iff
#print axioms verified_theorem2_klDiv_certificate
#print axioms klDiv_nigMeasureMuSigma
-- Further results
#print axioms variance_nigZMarginal
#print axioms variance_nigMuMarginal
#print axioms nig_variance_decomposition_on_fiber
#print axioms TFromParams_eq_variance_form
#print axioms nigZMarginal_eq_collapsed
#print axioms gaussian_collapse
#print axioms functional_fiber_invariant
#print axioms fiber_bijection
#print axioms corollary1_ratio_fraction
#print axioms corollary2_same_ordering
#print axioms corollary2_values_can_differ
#print axioms cross_dimension_rank_reversal
#print axioms TOfRho_tendsto_zero
#print axioms rho_mul_TOfRho_tendsto_atTop
#print axioms small_rho_endpoint_variance_form
#print axioms nuCan_tendsto_atTop_c
#print axioms invNuCan_tendsto_M0_c
#print axioms TFromParams_limits_c
#print axioms M0_isGLB_alpha0
#print axioms fiber_argmin_weight_invariant
#print axioms Rcan_pos_of_gamma_ne
#print axioms outer_optimum_depends_on_weight
#print axioms envelope_identity_klDiv
#print axioms invGammaMeasure_eq_withDensity
#print axioms invGammaMeasure_map_const_mul
#print axioms remark2_marginal_does_not_determine_section
#print axioms fixed_marginal_ordering_can_change
#print axioms remark5_state_rescaling_changes_T
-- Closed-form formulas in expanded form
#print axioms manuscriptNIGKL_eq_closedForm
#print axioms klDiv_eq_manuscriptNIGKL
#print axioms Rcan_eq_manuscript_closed_form
#print axioms integral_log_invGammaMeasure
#print axioms integral_inv_invGammaMeasure
#print axioms offSection_diagnostics
#print axioms M0_tendsto_atTop_alpha0
#print axioms conditional_kl_vanishes
#print axioms joint_kl_eq_manuscriptNIGKL
#print axioms nonlinear_aggregation_can_reverse_ranks
#print axioms klDiv_gaussianReal
#print axioms klDiv_gammaMeasure
#print axioms klDiv_invGammaMeasure
#print axioms integral_klDiv_gaussian_invGamma
#print axioms klDiv_chain_rule_split
#print axioms ordering_across_outer_optima_can_change
