import Mathlib
import ELVAELeanVerification.GeometricTransfer
import ELVAELeanVerification.VarianceAllocation

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Residual prior gauge and the M0 ceiling

This module verifies the fixed-marginal prior-fiber identity

  β₀ = c₀ ν₀ / (1 + ν₀)

and therefore

  ρ₀ = 2 c₀ / (1 + ν₀),

with

  0 < ρ₀ < 2 c₀.

It also defines the prior-only amplitude ceiling

  M₀ = 1 / ν_can(ν₀/2),

proves its explicit closed form, and verifies

  0 < 1 / ν_can < M₀

for every admissible quotient state.

These are the central algebraic facts about the prior gauge and the
ceiling `M₀`.
-/

namespace ELVAE

noncomputable def priorBetaOnFiber
    (c0 nu0 : ℝ) : ℝ :=
  c0 * nu0 / (1 + nu0)

noncomputable def rho0OnFixedMarginal
    (c0 nu0 : ℝ) : ℝ :=
  rho0FromPrior
    nu0
    (priorBetaOnFiber c0 nu0)

/--
Along a fixed prior marginal law,

  ρ₀ = 2 c₀ / (1 + ν₀).
-/
theorem rho0_fixed_marginal_identity
    (c0 nu0 : ℝ)
    (hnu0 : 0 < nu0) :
    rho0OnFixedMarginal c0 nu0
      =
    2 * c0 / (1 + nu0) := by

  have hnu00 :
      nu0 ≠ 0 :=
    ne_of_gt hnu0

  have hden :
      1 + nu0 ≠ 0 := by
    linarith

  unfold rho0OnFixedMarginal
  unfold rho0FromPrior
  unfold priorBetaOnFiber

  field_simp [hnu00, hden]

/--
The residual gauge explored by a fixed prior marginal law
lies strictly inside `(0, 2 c₀)`.
-/
theorem rho0_fixed_marginal_bounds
    (c0 nu0 : ℝ)
    (hc0 : 0 < c0)
    (hnu0 : 0 < nu0) :
    0 < rho0OnFixedMarginal c0 nu0
      ∧
    rho0OnFixedMarginal c0 nu0 < 2 * c0 := by

  have hid :=
    rho0_fixed_marginal_identity
      c0 nu0 hnu0

  have hden :
      0 < 1 + nu0 := by
    linarith

  constructor

  · rw [hid]
    positivity

  · rw [hid]

    apply
      (div_lt_iff₀ hden).2

    have hprod :
        0 < 2 * c0 * nu0 := by
      positivity

    nlinarith

/--
Prior-only ceiling defined intrinsically as the inverse
canonical allocation at the limiting value `B = ν₀/2`.
-/
noncomputable def M0
    (nu0 alpha0 : ℝ) : ℝ :=
  invNuCan alpha0 (nu0 / 2)

/--
Closed form of the ceiling.
-/
noncomputable def M0ClosedForm
    (nu0 alpha0 : ℝ) : ℝ :=
  (
    Real.sqrt
      ((nu0 - 2 * alpha0 - 1) ^ 2 + 4 * nu0)
      -
    (nu0 - 2 * alpha0 - 1)
  )
  /
  (2 * nu0)

/--
The intrinsic ceiling definition equals its
explicit closed-form expression.
-/
theorem M0_eq_closedForm
    (nu0 alpha0 : ℝ)
    (hnu0 : 0 < nu0) :
    M0 nu0 alpha0
      =
    M0ClosedForm nu0 alpha0 := by

  have hhalf :
      0 < nu0 / 2 := by
    linarith

  let Ds : ℝ :=
    selectorDiscriminant
      alpha0
      (nu0 / 2)

  let Db : ℝ :=
    (nu0 - 2 * alpha0 - 1) ^ 2
      + 4 * nu0

  have hDs :
      0 ≤ Ds := by
    dsimp [Ds]

    exact
      (selectorDiscriminant_positive
        alpha0
        (nu0 / 2)
        hhalf).le

  have hDb :
      0 ≤ Db := by
    dsimp [Db]
    positivity

  have hscale :
      Db = 4 * Ds := by

    dsimp [Db, Ds]

    unfold selectorDiscriminant

    ring

  have hsSmall :
      (Real.sqrt Ds) ^ 2 = Ds :=
    Real.sq_sqrt hDs

  have hsBig :
      (Real.sqrt Db) ^ 2 = Db :=
    Real.sq_sqrt hDb

  have hsSmallNonneg :
      0 ≤ Real.sqrt Ds :=
    Real.sqrt_nonneg Ds

  have hsBigNonneg :
      0 ≤ Real.sqrt Db :=
    Real.sqrt_nonneg Db

  have hsqrtScale :
      Real.sqrt Db
        =
      2 * Real.sqrt Ds := by

    nlinarith [
      hsSmall,
      hsBig,
      hscale,
      hsSmallNonneg,
      hsBigNonneg
    ]

  have hsqrtScale' :
      Real.sqrt
          ((nu0 - 2 * alpha0 - 1) ^ 2
            + 4 * nu0)
        =
      2 *
        Real.sqrt
          (selectorDiscriminant
            alpha0
            (nu0 / 2)) := by

    simpa [Db, Ds] using hsqrtScale

  have hlinear :
      nu0 - 2 * alpha0 - 1
        =
      2 *
        (nu0 / 2
          - alpha0
          - (1 / 2 : ℝ)) := by
    ring

  have hden :
      2 * (nu0 / 2) = nu0 := by
    ring

  have hnu00 :
      nu0 ≠ 0 :=
    ne_of_gt hnu0

  unfold M0

  rw [
    invNuCan_rationalized
      alpha0
      (nu0 / 2)
      hhalf
  ]

  unfold M0ClosedForm

  rw [
    hsqrtScale',
    hlinear,
    hden
  ]

  field_simp [hnu00]
/--
The ceiling itself is strictly positive.
-/
theorem M0_positive
    (nu0 alpha0 : ℝ)
    (hnu0 : 0 < nu0) :
    0 < M0 nu0 alpha0 := by

  have hhalf :
      0 < nu0 / 2 := by
    linarith

  have hnu :
      0 <
        nuCan
          alpha0
          (nu0 / 2) :=
    nuCan_positive
      alpha0
      (nu0 / 2)
      hhalf

  unfold M0 invNuCan

  exact one_div_pos.mpr hnu

/--
For every admissible quotient state,

  1 / ν_can < M₀.

This is the strict upper bound by the ceiling.
-/
theorem actual_inverse_allocation_lt_M0
    (gamma alpha c gamma0 nu0 alpha0 beta0 : ℝ)
    (halpha : 0 < alpha)
    (hc : 0 < c)
    (hnu0 : 0 < nu0)
    (halpha0 : 0 < alpha0)
    (hbeta0 : 0 < beta0) :
    invNuCan
        alpha0
        (BFromParams
          gamma alpha c gamma0 nu0 beta0)
      <
    M0 nu0 alpha0 := by

  have hhalf :
      0 < nu0 / 2 := by
    linarith

  have hB :
      0 <
        BFromParams
          gamma alpha c gamma0 nu0 beta0 :=
    BFromParams_positive
      gamma alpha c gamma0 nu0 beta0
      halpha hc hnu0 hbeta0

  have hBgt :
      nu0 / 2
        <
      BFromParams
        gamma alpha c gamma0 nu0 beta0 :=
    BFromParams_gt_half_nu0
      gamma alpha c gamma0 nu0 beta0
      halpha hc hnu0 hbeta0

  have hdec :=
    invNuCan_strict_decreasing
      alpha0
      (nu0 / 2)
      (BFromParams
        gamma alpha c gamma0 nu0 beta0)
      halpha0
      hhalf
      hB
      hBgt

  simpa [M0] using hdec

/--
Full ceiling inequality at the actual NIG parameters:

  0 < 1 / ν_can < M₀.
-/
theorem actual_inverse_allocation_bounds
    (gamma alpha c gamma0 nu0 alpha0 beta0 : ℝ)
    (halpha : 0 < alpha)
    (hc : 0 < c)
    (hnu0 : 0 < nu0)
    (halpha0 : 0 < alpha0)
    (hbeta0 : 0 < beta0) :
    0 <
      invNuCan
        alpha0
        (BFromParams
          gamma alpha c gamma0 nu0 beta0)
    ∧
      invNuCan
        alpha0
        (BFromParams
          gamma alpha c gamma0 nu0 beta0)
      <
      M0 nu0 alpha0 := by

  have hB :
      0 <
        BFromParams
          gamma alpha c gamma0 nu0 beta0 :=
    BFromParams_positive
      gamma alpha c gamma0 nu0 beta0
      halpha hc hnu0 hbeta0

  have hnu :
      0 <
        nuCan
          alpha0
          (BFromParams
            gamma alpha c gamma0 nu0 beta0) :=
    nuCan_positive
      alpha0
      (BFromParams
        gamma alpha c gamma0 nu0 beta0)
      hB

  constructor

  · unfold invNuCan
    exact one_div_pos.mpr hnu

  · exact
      actual_inverse_allocation_lt_M0
        gamma alpha c gamma0
        nu0 alpha0 beta0
        halpha hc hnu0 halpha0 hbeta0

/--
When `α > 1`, the canonical uncertainty ratio inherits the
same prior-determined ceiling.
-/
theorem canonical_variance_ratio_lt_M0
    (gamma alpha c gamma0 nu0 alpha0 beta0 : ℝ)
    (halpha : 1 < alpha)
    (hc : 0 < c)
    (hnu0 : 0 < nu0)
    (halpha0 : 0 < alpha0)
    (hbeta0 : 0 < beta0) :
    uEpi
        c
        alpha
        (nuCanFromParams
          gamma alpha c gamma0 nu0 alpha0 beta0)
      /
      uVar
        c
        alpha
        (nuCanFromParams
          gamma alpha c gamma0 nu0 alpha0 beta0)
      <
    M0 nu0 alpha0 := by

  have halphaPos :
      0 < alpha := by
    linarith

  have hratio :=
    canonical_variance_allocation_ratio
      gamma alpha c gamma0
      nu0 alpha0 beta0
      halpha hc hnu0 hbeta0

  have hbound :=
    actual_inverse_allocation_lt_M0
      gamma alpha c gamma0
      nu0 alpha0 beta0
      halphaPos hc hnu0 halpha0 hbeta0

  rw [hratio]

  simpa [
    invNuCan,
    nuCanFromParams
  ] using hbound

end ELVAE