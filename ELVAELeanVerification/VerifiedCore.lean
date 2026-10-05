import ELVAELeanVerification.CanonicalReduction
import ELVAELeanVerification.CanonicalSelector
import ELVAELeanVerification.StationarityReduction
import ELVAELeanVerification.ObjectiveDerivative
import ELVAELeanVerification.GlobalMinimum
import ELVAELeanVerification.ParameterBridge
import ELVAELeanVerification.VarianceAllocation
import ELVAELeanVerification.SelectorSensitivity
import ELVAELeanVerification.OrdinalGeometry
import ELVAELeanVerification.GeometricTransfer
import ELVAELeanVerification.PriorGaugeCeiling
import ELVAELeanVerification.ExactPartialMinimization
import ELVAELeanVerification.RestrictedKLDivergence
import ELVAELeanVerification.M0Dependence
import ELVAELeanVerification.BoundaryLimits
import ELVAELeanVerification.PriorSelfConsistency
import ELVAELeanVerification.Analyticity
import ELVAELeanVerification.NIGStudentTMarginal
import ELVAELeanVerification.EnvelopeAndInvariance
import ELVAELeanVerification.UncertaintyMoments
import ELVAELeanVerification.GammaMoments
import ELVAELeanVerification.KLDensity
import ELVAELeanVerification.NIGKLDivergence
import ELVAELeanVerification.NIGConsistency
import ELVAELeanVerification.KLTheorem2
import ELVAELeanVerification.LatentVariance
import ELVAELeanVerification.OrdinalPrior
import ELVAELeanVerification.WeightInvariance
import ELVAELeanVerification.EnvelopeFull
import ELVAELeanVerification.InvGammaDensity
import ELVAELeanVerification.PriorGaugeWitnesses
import ELVAELeanVerification.ManuscriptForms
import ELVAELeanVerification.ManuscriptRemaining
import ELVAELeanVerification.ChainRuleSplit
import ELVAELeanVerification.OrderingWitness

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# ELVAE Verified Core

Machine-checked core of the prior-relative canonical NIG reduction.

Current verified components:

* fiber parameterization
* positivity of beta
* closed-form canonical selector
* positivity of the canonical selector
* stationary quadratic identity
* uniqueness of the positive stationary root
* derivative-to-quadratic reduction
* formal differentiation of the restricted objective
* derivative sign before and after the canonical selector
* strict global minimality
* uniqueness of the global minimizer
* parameter bridge, variance allocation, selector sensitivity
* ordinal geometry and geometric transfer
* prior gauge and the `M₀` ceiling, including
  monotonicity in `α₀`, the `α₀ → 0⁺` limit and the large-`α₀` asymptotic
* boundary divergence of the fiber objective
* prior self-consistency and prior-gauge limits
* real analyticity of the canonical section
* exact partial minimization, abstractly and for the
  closed-form NIG KL expression (Level A; see `RestrictedKLDivergence`)
* the marginal law of the latent `z` in the NIG hierarchy
  is Student-t with `2α` degrees of freedom, location `γ`, squared
  scale `c/α`, and is constant on fibers
  (identity of probability measures; see `NIGStudentTMarginal`)
* envelope identity `dR̃_can/dB = 1/ν_can` and scale/translation covariance
* uncertainty decomposition derived from the NIG law:
  `E[σ²] = u_var`, `E[(μ−γ)²] = u_epi`, `E[(z−γ)²] = c/(α−1)`
* Level B: the closed-form NIG KL equals mathlib's `klDiv` between the NIG
  laws (`klDiv_nigMeasure`), and it is nonnegative
* exact partial minimization, the unique fiber minimum and boundary behaviour for the
  measure-theoretic KL (`KLTheorem2`)
* further results: latent variance and the variance form of `T`, the
  collapsed hierarchy, ordinal dependence on the prior with witnesses, conditional
  weight invariance (with a witness that the outer optimum depends on `λ`),
  radius-floor limits, the `c`-regimes, and the envelope identity for the
  measure-theoretic KL
-/

namespace ELVAE

/--
Master certificate for the currently verified canonical-selector result.

For B > 0:

1. `nuCan` is positive;
2. it is the unique global minimizer of the restricted objective
   over the positive real domain.
-/
theorem verified_canonical_selector_core
    (alpha0 B : ℝ)
    (hB : 0 < B) :
    0 < nuCan alpha0 B
    ∧
    (∀ x : ℝ,
      0 < x →
      fiberObjective alpha0 B (nuCan alpha0 B)
        ≤
      fiberObjective alpha0 B x)
    ∧
    (∀ x : ℝ,
      0 < x →
      fiberObjective alpha0 B x
          =
        fiberObjective alpha0 B (nuCan alpha0 B) →
      x = nuCan alpha0 B) := by
  constructor
  · exact nuCan_positive alpha0 B hB
  · exact nuCan_unique_global_minimizer alpha0 B hB

/--
Master certificate for exact partial minimization with the closed-form NIG KL expression.

For a valid prior (`ν₀, β₀ > 0`), any reconstruction term `L`, and `λ > 0`:

1. the four-coordinate infimum over natural NIG coordinates
   `(γ, ν > 0, α > 0, β > 0)` equals the three-coordinate infimum over
   quotient states `(γ, α > 0, c > 0)`;
2. every non-canonical fiber representative of an admissible quotient state
   has strictly larger objective than the canonical one.
-/
theorem verified_theorem2_certificate
    (gamma0 nu0 alpha0 beta0 lam : ℝ) (L : QuotientState → ℝ)
    (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0) (hlam : 0 < lam) :
    sInf (nigJ4Values gamma0 nu0 alpha0 beta0 lam L)
        = sInf (J3Values admissibleQuotients L
            (restrictedNIGKL gamma0 nu0 alpha0 beta0)
            (QuotientState.nuCan gamma0 nu0 alpha0 beta0) lam)
    ∧
    (∀ θ ∈ admissibleQuotients, ∀ nu : ℝ, 0 < nu →
      nu ≠ θ.nuCan gamma0 nu0 alpha0 beta0 →
      partialJ3 L (restrictedNIGKL gamma0 nu0 alpha0 beta0)
          (QuotientState.nuCan gamma0 nu0 alpha0 beta0) lam θ
        < partialJ4 L (restrictedNIGKL gamma0 nu0 alpha0 beta0) lam θ nu) :=
  ⟨theorem2_nigKL_sInf_eq gamma0 nu0 alpha0 beta0 lam L hnu0 hbeta0 hlam.le,
    fun _ hθ _ hnu hne =>
      theorem2_nigKL_strict_penalty gamma0 nu0 alpha0 beta0 lam L hnu0 hbeta0 hlam
        hθ hnu hne⟩

/--
Master certificate for exact partial minimization with the measure-theoretic KL divergence.

For a valid NIG prior (`ν₀, α₀, β₀ > 0`), any reconstruction term `L`, and `λ > 0`:

1. `KL(NIG(γ,ν,α,β) ‖ NIG₀)` (mathlib's `klDiv`) equals the closed-form expression;
2. the four-coordinate infimum over natural NIG coordinates equals the
   three-coordinate infimum over quotient states;
3. every non-canonical fiber representative has strictly larger objective.
-/
theorem verified_theorem2_klDiv_certificate
    (gamma0 nu0 alpha0 beta0 lam : ℝ) (L : QuotientState → ℝ)
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0) (hlam : 0 < lam) :
    (∀ gamma nu alpha beta : ℝ, 0 < nu → 0 < alpha → 0 < beta →
      InformationTheory.klDiv (nigMeasure gamma nu alpha beta)
          (nigMeasure gamma0 nu0 alpha0 beta0)
        = ENNReal.ofReal (nigKLClosedForm gamma nu alpha beta gamma0 nu0 alpha0 beta0))
    ∧
    sInf (klJ4Values gamma0 nu0 alpha0 beta0 lam L)
        = sInf (J3Values admissibleQuotients L (fiberKL gamma0 nu0 alpha0 beta0)
            (QuotientState.nuCan gamma0 nu0 alpha0 beta0) lam)
    ∧
    (∀ θ ∈ admissibleQuotients, ∀ nu : ℝ, 0 < nu →
      nu ≠ θ.nuCan gamma0 nu0 alpha0 beta0 →
      partialJ3 L (fiberKL gamma0 nu0 alpha0 beta0)
          (QuotientState.nuCan gamma0 nu0 alpha0 beta0) lam θ
        < partialJ4 L (fiberKL gamma0 nu0 alpha0 beta0) lam θ nu) :=
  ⟨fun _ _ _ _ hnu halpha hbeta => klDiv_nigMeasure hnu halpha hbeta hnu0 halpha0 hbeta0,
    theorem2_klDiv_sInf_eq hnu0 halpha0 hbeta0 hlam.le L,
    fun _ hθ _ hnu hne => theorem2_klDiv_strict_penalty hnu0 halpha0 hbeta0 hlam L hθ hnu hne⟩

end ELVAE