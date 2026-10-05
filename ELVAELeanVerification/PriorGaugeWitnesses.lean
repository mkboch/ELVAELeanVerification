import Mathlib
import ELVAELeanVerification.OrdinalPrior
import ELVAELeanVerification.PriorSelfConsistency

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# The residual prior gauge: explicit witnesses

Three "can differ / can change" statements concern the residual
prior gauge. Each is a statement that some invariance **fails**, so each is
formalized by an explicit witness.

* `remark2_marginal_does_not_determine_section`: fixing only the prior
  marginal law `(γ₀, α₀, c₀)` does not determine the section. Two priors on the
  same marginal law but with different `ν₀` select different `ν_can`.
* `fixed_marginal_ordering_can_change`:
  moving the prior along its fixed-marginal fiber changes `ρ₀` and can reverse the
  ordering of two quotient states by `1/ν_can`.
* `remark5_state_rescaling_changes_T`: rescaling the quotient state
  while holding the prior fixed changes `T`, in contrast to the consistent
  rescaling of `TFromParams_scale_translate`.
-/

namespace ELVAE

/-- The prior on the fixed marginal fiber: `β₀ = c₀ν₀/(1+ν₀)` has `c₀ = β₀(1 + 1/ν₀)`. -/
lemma priorC0_priorBetaOnFiber {c0 nu0 : ℝ} (hnu0 : 0 < nu0) :
    priorC0 nu0 (priorBetaOnFiber c0 nu0) = c0 := by
  unfold priorC0 priorBetaOnFiber
  exact fiber_parameterization c0 nu0 hnu0

/--
For any prior marginal law `(γ₀, α₀, c₀)` with `α₀, c₀ > 0` and any two
fiber positions `ν₀₁ ≠ ν₀₂`, the two complete priors select different canonical
allocations at the quotient state `(γ₀, α₀, c₀)` (namely `ν₀₁` and `ν₀₂`).
-/
theorem remark2_marginal_does_not_determine_section (gamma0 alpha0 c0 nu01 nu02 : ℝ)
    (halpha0 : 0 < alpha0) (hc0 : 0 < c0) (hnu01 : 0 < nu01) (hnu02 : 0 < nu02)
    (hne : nu01 ≠ nu02) :
    nuCanFromParams gamma0 alpha0 c0 gamma0 nu01 alpha0 (priorBetaOnFiber c0 nu01)
      ≠ nuCanFromParams gamma0 alpha0 c0 gamma0 nu02 alpha0 (priorBetaOnFiber c0 nu02) := by
  have hb1 : 0 < priorBetaOnFiber c0 nu01 := beta_positive c0 nu01 hc0 hnu01
  have hb2 : 0 < priorBetaOnFiber c0 nu02 := beta_positive c0 nu02 hc0 hnu02
  have h1 := nuCanFromParams_at_prior gamma0 nu01 alpha0 _ hnu01 halpha0 hb1
  have h2 := nuCanFromParams_at_prior gamma0 nu02 alpha0 _ hnu02 halpha0 hb2
  rw [priorC0_priorBetaOnFiber hnu01] at h1
  rw [priorC0_priorBetaOnFiber hnu02] at h2
  rw [h1, h2]
  exact hne

/--
**Fixed-marginal ordering can change.** With the prior marginal law
`(γ₀, α₀, c₀) = (0, 1, 1)` held fixed, the fiber positions `ν₀ = 3` (`ρ₀ = 1/2`) and
`ν₀ = 1/3` (`ρ₀ = 3/2`) order the quotient states `θ₁ = (0, 1, 1)` and
`θ₂ = (1, 1, 2)` oppositely by inverse canonical allocation.
-/
theorem fixed_marginal_ordering_can_change :
    let P1beta := priorBetaOnFiber 1 3
    let P2beta := priorBetaOnFiber 1 (1 / 3)
    rho0FromPrior 3 P1beta = 1 / 2 ∧ rho0FromPrior (1 / 3) P2beta = 3 / 2
      ∧ invNuCan 1 (BFromParams 1 1 2 0 3 P1beta) < invNuCan 1 (BFromParams 0 1 1 0 3 P1beta)
      ∧ invNuCan 1 (BFromParams 0 1 1 0 (1 / 3) P2beta)
          < invNuCan 1 (BFromParams 1 1 2 0 (1 / 3) P2beta) := by
  intro P1beta P2beta
  have hP1 : P1beta = 3 / 4 := by simp only [P1beta, priorBetaOnFiber]; norm_num
  have hP2 : P2beta = 1 / 4 := by simp only [P2beta, priorBetaOnFiber]; norm_num
  refine ⟨by rw [hP1]; unfold rho0FromPrior; norm_num,
    by rw [hP2]; unfold rho0FromPrior; norm_num, ?_, ?_⟩
  · rw [actual_inverse_allocation_order_iff_T _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [hP1]; norm_num), hP1]
    unfold TFromParams rho0FromPrior
    norm_num
  · rw [actual_inverse_allocation_order_iff_T _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [hP2]; norm_num), hP2]
    unfold TFromParams rho0FromPrior
    norm_num

/--
Rescaling the quotient state (`γ ↦ κγ`, `c ↦ κ²c`) while holding the prior
fixed changes `T` in general: with `κ = 2`, `θ = (0, 1, 1)` and the prior
`(γ₀, ν₀, β₀) = (0, 2, 1)`, `T` changes from `1` to `4`.
-/
theorem remark5_state_rescaling_changes_T :
    TFromParams 0 1 1 0 2 1 = 1 ∧ TFromParams (2 * 0) 1 (2 ^ 2 * 1) 0 2 1 = 4 := by
  unfold TFromParams rho0FromPrior
  norm_num

end ELVAE
