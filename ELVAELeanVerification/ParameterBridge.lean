import Mathlib
import ELVAELeanVerification.GlobalMinimum
import ELVAELeanVerification.CanonicalReduction

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Parameter bridge for the prior-relative canonical selector

The earlier modules proved the selector theorem assuming `B > 0`.

This module connects that abstract scalar to the actual parameters
of the NIG quotient state and complete hierarchical prior:

  B =
    ν₀ / 2
    + (α / c) *
      (β₀ + (ν₀ / 2) * (γ - γ₀)^2).

For admissible positive parameters, this proves

  B > ν₀ / 2 > 0,

and then instantiates the previously verified selector and fiber
results at the actual NIG parameters.
-/

namespace ELVAE

noncomputable def BFromParams
    (gamma alpha c gamma0 nu0 beta0 : ℝ) : ℝ :=
  nu0 / 2
    + (alpha / c) *
      (beta0 + (nu0 / 2) * (gamma - gamma0) ^ 2)

/--
The parameter-defined `B` strictly exceeds `ν₀ / 2`.
-/
theorem BFromParams_gt_half_nu0
    (gamma alpha c gamma0 nu0 beta0 : ℝ)
    (halpha : 0 < alpha)
    (hc : 0 < c)
    (hnu0 : 0 < nu0)
    (hbeta0 : 0 < beta0) :
    nu0 / 2
      <
    BFromParams gamma alpha c gamma0 nu0 beta0 := by
  have hscale :
      0 < alpha / c := by
    exact div_pos halpha hc
  have hinside :
      0 <
        beta0 +
          (nu0 / 2) * (gamma - gamma0) ^ 2 := by
    have hsquare :
        0 ≤ (gamma - gamma0) ^ 2 := sq_nonneg _
    have hhalf :
        0 < nu0 / 2 := by
      linarith
    have hnonneg :
        0 ≤
          (nu0 / 2) * (gamma - gamma0) ^ 2 :=
      mul_nonneg hhalf.le hsquare
    nlinarith
  unfold BFromParams
  have hproduct :
      0 <
        (alpha / c) *
          (beta0 +
            (nu0 / 2) * (gamma - gamma0) ^ 2) :=
    mul_pos hscale hinside
  linarith

/--
Hence the parameter-defined `B` is strictly positive.
-/
theorem BFromParams_positive
    (gamma alpha c gamma0 nu0 beta0 : ℝ)
    (halpha : 0 < alpha)
    (hc : 0 < c)
    (hnu0 : 0 < nu0)
    (hbeta0 : 0 < beta0) :
    0 <
      BFromParams gamma alpha c gamma0 nu0 beta0 := by
  have hhalf :
      0 < nu0 / 2 := by
    linarith
  have hgt :=
    BFromParams_gt_half_nu0
      gamma alpha c gamma0 nu0 beta0
      halpha hc hnu0 hbeta0
  linarith

noncomputable def nuCanFromParams
    (gamma alpha c gamma0 nu0 alpha0 beta0 : ℝ) : ℝ :=
  nuCan alpha0
    (BFromParams gamma alpha c gamma0 nu0 beta0)

noncomputable def betaCanFromParams
    (gamma alpha c gamma0 nu0 alpha0 beta0 : ℝ) : ℝ :=
  c *
      nuCanFromParams
        gamma alpha c gamma0 nu0 alpha0 beta0
    /
      (1 +
        nuCanFromParams
          gamma alpha c gamma0 nu0 alpha0 beta0)

/--
The canonical allocation obtained from the actual NIG parameters
is strictly positive.
-/
theorem nuCanFromParams_positive
    (gamma alpha c gamma0 nu0 alpha0 beta0 : ℝ)
    (halpha : 0 < alpha)
    (hc : 0 < c)
    (hnu0 : 0 < nu0)
    (hbeta0 : 0 < beta0) :
    0 <
      nuCanFromParams
        gamma alpha c gamma0 nu0 alpha0 beta0 := by
  unfold nuCanFromParams
  apply nuCan_positive
  exact
    BFromParams_positive
      gamma alpha c gamma0 nu0 beta0
      halpha hc hnu0 hbeta0

/--
The corresponding canonical `β` is strictly positive.
-/
theorem betaCanFromParams_positive
    (gamma alpha c gamma0 nu0 alpha0 beta0 : ℝ)
    (halpha : 0 < alpha)
    (hc : 0 < c)
    (hnu0 : 0 < nu0)
    (hbeta0 : 0 < beta0) :
    0 <
      betaCanFromParams
        gamma alpha c gamma0 nu0 alpha0 beta0 := by
  have hnu :
      0 <
        nuCanFromParams
          gamma alpha c gamma0 nu0 alpha0 beta0 :=
    nuCanFromParams_positive
      gamma alpha c gamma0 nu0 alpha0 beta0
      halpha hc hnu0 hbeta0
  unfold betaCanFromParams
  positivity

/--
The canonical pair lies exactly on the required fiber:

  c = β_can (1 + 1 / ν_can).
-/
theorem betaCanFromParams_fiber
    (gamma alpha c gamma0 nu0 alpha0 beta0 : ℝ)
    (halpha : 0 < alpha)
    (hc : 0 < c)
    (hnu0 : 0 < nu0)
    (hbeta0 : 0 < beta0) :
    betaCanFromParams
        gamma alpha c gamma0 nu0 alpha0 beta0
      *
        (1 +
          1 /
            nuCanFromParams
              gamma alpha c gamma0 nu0 alpha0 beta0)
      =
    c := by
  have hnu :
      0 <
        nuCanFromParams
          gamma alpha c gamma0 nu0 alpha0 beta0 :=
    nuCanFromParams_positive
      gamma alpha c gamma0 nu0 alpha0 beta0
      halpha hc hnu0 hbeta0
  simpa [betaCanFromParams] using
    fiber_parameterization
      c
      (nuCanFromParams
        gamma alpha c gamma0 nu0 alpha0 beta0)
      hnu

/--
The canonical β also lies strictly inside its equivalent fiber
interval `(0,c)`.
-/
theorem betaCanFromParams_lt_c
    (gamma alpha c gamma0 nu0 alpha0 beta0 : ℝ)
    (halpha : 0 < alpha)
    (hc : 0 < c)
    (hnu0 : 0 < nu0)
    (hbeta0 : 0 < beta0) :
    betaCanFromParams
        gamma alpha c gamma0 nu0 alpha0 beta0
      < c := by
  have hnu :
      0 <
        nuCanFromParams
          gamma alpha c gamma0 nu0 alpha0 beta0 :=
    nuCanFromParams_positive
      gamma alpha c gamma0 nu0 alpha0 beta0
      halpha hc hnu0 hbeta0
  have hden :
      0 <
        1 +
          nuCanFromParams
            gamma alpha c gamma0 nu0 alpha0 beta0 := by
    linarith
  unfold betaCanFromParams
  rw [div_lt_iff₀ hden]
  nlinarith

end ELVAE