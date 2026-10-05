import Mathlib
import ELVAELeanVerification.M0Dependence
import ELVAELeanVerification.RestrictedKLDivergence

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Prior self-consistency and prior-gauge limits

**Self-consistency at the prior base point.** Let the quotient state coincide
with the prior's own marginal coordinates,

  γ = γ₀,  α = α₀,  c = c₀ := β₀ (1 + 1/ν₀).

Then
* `B = ν₀/2 + α₀ ν₀/(1 + ν₀)`;
* the canonical selector recovers the prior exactly: `ν_can = ν₀` and
  `β_can = β₀`;
* the geometric score is `T₀ = (1 + ν₀)/(2 α₀)`;
* the closed-form KL vanishes there, so `R_can(θ₀) = 0`;
* the inverse allocation at the base point, `1/ν₀`, lies strictly below
  the ceiling `M₀` (for `α₀ > 0`).

**Prior-gauge limits.** On a fixed prior marginal (`ρ₀ = 2 c₀/(1 + ν₀)`):

  ν₀ → ∞  ⟹ ρ₀ → 0,     ν₀ → 0⁺ ⟹ ρ₀ → 2 c₀,

and the upper endpoint `2 c₀` is never attained for `ν₀ > 0`.
-/

namespace ELVAE

open Filter Topology

/-- Prior marginal coordinate `c₀ = β₀ (1 + 1/ν₀)`. -/
noncomputable def priorC0 (nu0 beta0 : ℝ) : ℝ :=
  beta0 * (1 + 1 / nu0)

theorem priorC0_positive (nu0 beta0 : ℝ) (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0) :
    0 < priorC0 nu0 beta0 := by
  unfold priorC0
  positivity

/-- `B` at the prior base point. -/
theorem BFromParams_at_prior
    (gamma0 nu0 alpha0 beta0 : ℝ) (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0) :
    BFromParams gamma0 alpha0 (priorC0 nu0 beta0) gamma0 nu0 beta0
      = nu0 / 2 + alpha0 * nu0 / (1 + nu0) := by
  have h1 : 1 + nu0 ≠ 0 := by linarith
  unfold BFromParams priorC0
  field_simp
  ring

/--
**Self-consistency.** The canonical selector of the prior's own quotient class
is the prior precision: `ν_can(γ₀, α₀, c₀) = ν₀`.
-/
theorem nuCanFromParams_at_prior
    (gamma0 nu0 alpha0 beta0 : ℝ)
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0) :
    nuCanFromParams gamma0 alpha0 (priorC0 nu0 beta0) gamma0 nu0 alpha0 beta0 = nu0 := by
  have hB : 0 < BFromParams gamma0 alpha0 (priorC0 nu0 beta0) gamma0 nu0 beta0 :=
    BFromParams_positive _ _ _ _ _ _ halpha0 (priorC0_positive nu0 beta0 hnu0 hbeta0)
      hnu0 hbeta0
  unfold nuCanFromParams
  symm
  apply stationary_quadratic_unique_positive alpha0 _ nu0 hB hnu0
  rw [BFromParams_at_prior gamma0 nu0 alpha0 beta0 hnu0 hbeta0]
  have h1 : 1 + nu0 ≠ 0 := by linarith
  field_simp
  ring

/-- **Self-consistency.** The canonical `β` recovers the prior: `β_can = β₀`. -/
theorem betaCanFromParams_at_prior
    (gamma0 nu0 alpha0 beta0 : ℝ)
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0) :
    betaCanFromParams gamma0 alpha0 (priorC0 nu0 beta0) gamma0 nu0 alpha0 beta0 = beta0 := by
  unfold betaCanFromParams
  rw [nuCanFromParams_at_prior gamma0 nu0 alpha0 beta0 hnu0 halpha0 hbeta0]
  have h1 : 1 + nu0 ≠ 0 := by linarith
  unfold priorC0
  field_simp
  ring

/-- The geometric score at the base point: `T₀ = (1 + ν₀)/(2 α₀)`. -/
theorem TFromParams_at_prior
    (gamma0 nu0 alpha0 beta0 : ℝ)
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0) :
    TFromParams gamma0 alpha0 (priorC0 nu0 beta0) gamma0 nu0 beta0
      = (1 + nu0) / (2 * alpha0) := by
  unfold TFromParams rho0FromPrior priorC0
  field_simp
  ring

/-- The closed-form NIG KL of the prior against itself is zero. -/
theorem nigKLClosedForm_self
    (gamma0 nu0 alpha0 beta0 : ℝ) (hnu0 : 0 < nu0) :
    nigKLClosedForm gamma0 nu0 alpha0 beta0 gamma0 nu0 alpha0 beta0 = 0 := by
  unfold nigKLClosedForm
  rw [div_self hnu0.ne', Real.log_one]
  ring

/-- The prior's quotient state. -/
noncomputable def priorQuotient (gamma0 nu0 alpha0 beta0 : ℝ) : QuotientState :=
  ⟨gamma0, alpha0, priorC0 nu0 beta0⟩

/--
At the base point the canonical regularizer vanishes:
`R_can(θ₀) = KL(p₀ ‖ p₀) = 0`.
-/
theorem Rcan_at_prior
    (gamma0 nu0 alpha0 beta0 : ℝ)
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0) :
    restrictedNIGKL gamma0 nu0 alpha0 beta0 (priorQuotient gamma0 nu0 alpha0 beta0)
      ((priorQuotient gamma0 nu0 alpha0 beta0).nuCan gamma0 nu0 alpha0 beta0) = 0 := by
  have hnu := nuCanFromParams_at_prior gamma0 nu0 alpha0 beta0 hnu0 halpha0 hbeta0
  have hbeta := betaCanFromParams_at_prior gamma0 nu0 alpha0 beta0 hnu0 halpha0 hbeta0
  unfold restrictedNIGKL
  simp only [QuotientState.nuCan, priorQuotient]
  unfold betaCanFromParams at hbeta
  rw [hbeta, hnu]
  exact nigKLClosedForm_self gamma0 nu0 alpha0 beta0 hnu0

/-- `M₀(ν₀, 0) = 1/ν₀`. -/
theorem M0_at_alpha0_zero (nu0 : ℝ) (hnu0 : 0 < nu0) :
    M0 nu0 0 = 1 / nu0 := by
  rw [M0_eq_closedForm nu0 0 hnu0, M0ClosedForm_at_zero nu0 hnu0]

/--
At the base point the inverse allocation is `1/ν₀`, which lies strictly
below the ceiling `M₀` whenever `α₀ > 0`, consistently with the ceiling bound.
-/
theorem prior_inverse_allocation_lt_M0
    (gamma0 nu0 alpha0 beta0 : ℝ)
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0) :
    1 / nuCanFromParams gamma0 alpha0 (priorC0 nu0 beta0) gamma0 nu0 alpha0 beta0
        = 1 / nu0
      ∧ 1 / nu0 < M0 nu0 alpha0 := by
  refine ⟨by rw [nuCanFromParams_at_prior gamma0 nu0 alpha0 beta0 hnu0 halpha0 hbeta0], ?_⟩
  rw [← M0_at_alpha0_zero nu0 hnu0]
  exact M0_strictMono_alpha0 nu0 hnu0 halpha0

/-! ## Prior-gauge limits -/

/-- `ρ₀ = 2c₀/(1+ν₀) → 0` as `ν₀ → ∞`. -/
theorem rho0_fixed_marginal_tendsto_atTop (c0 : ℝ) :
    Tendsto (fun nu0 : ℝ => rho0OnFixedMarginal c0 nu0) atTop (𝓝 0) := by
  have h : Tendsto (fun nu0 : ℝ => 2 * c0 / (1 + nu0)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _ tendsto_id)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with nu0 hnu0
  exact (rho0_fixed_marginal_identity c0 nu0 hnu0).symm

/-- `ρ₀ = 2c₀/(1+ν₀) → 2c₀` as `ν₀ → 0⁺`. -/
theorem rho0_fixed_marginal_tendsto_nhdsGT_zero (c0 : ℝ) :
    Tendsto (fun nu0 : ℝ => rho0OnFixedMarginal c0 nu0) (𝓝[>] 0) (𝓝 (2 * c0)) := by
  have hc : ContinuousAt (fun nu0 : ℝ => 2 * c0 / (1 + nu0)) 0 :=
    continuousAt_const.div (continuousAt_const.add continuousAt_id) (by norm_num)
  have h : Tendsto (fun nu0 : ℝ => 2 * c0 / (1 + nu0)) (𝓝[>] 0) (𝓝 (2 * c0)) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with nu0 hnu0
  exact (rho0_fixed_marginal_identity c0 nu0 hnu0).symm

/-- The endpoint `2c₀` is never attained for `ν₀ > 0` (and `c₀ > 0`). -/
theorem rho0_fixed_marginal_ne_upper
    (c0 nu0 : ℝ) (hc0 : 0 < c0) (hnu0 : 0 < nu0) :
    rho0OnFixedMarginal c0 nu0 ≠ 2 * c0 :=
  (rho0_fixed_marginal_bounds c0 nu0 hc0 hnu0).2.ne

end ELVAE
