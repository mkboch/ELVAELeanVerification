import Mathlib
import ELVAELeanVerification.OrdinalGeometry
import ELVAELeanVerification.ParameterBridge

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Geometric transfer function

This module connects the ordinal geometry to the actual quotient and prior
parameters.

Define

  ρ₀ = 2 β₀ / ν₀

and

  T =
    c /
      (α * ((γ - γ₀)^2 + ρ₀)).

The module verifies:

1. `ρ₀ > 0`;
2. `T > 0`;
3. the parameter-defined scalar `B` satisfies exactly

       B = ν₀/2 * (1 + 1/T);

4. the reciprocal canonical selector admits the rationalized form

       1/ν_can
       =
       [sqrt((B-a)^2 + 2B) - (B-a)] / (2B),

   where `a = α₀ + 1/2`;

5. therefore the explicit geometric transfer formula is exactly
   inverse canonical allocation.

These are the algebraic identities underlying the geometric transfer formula.
-/

namespace ELVAE

noncomputable def rho0FromPrior
    (nu0 beta0 : ℝ) : ℝ :=
  2 * beta0 / nu0

noncomputable def TFromParams
    (gamma alpha c gamma0 nu0 beta0 : ℝ) : ℝ :=
  c /
    (alpha *
      ((gamma - gamma0) ^ 2 +
        rho0FromPrior nu0 beta0))

noncomputable def canonicalTransferClosedForm
    (nu0 alpha0 T : ℝ) : ℝ :=
  (
    Real.sqrt
      (selectorDiscriminant
        alpha0
        (BOfT nu0 T))
      -
    (BOfT nu0 T - alpha0 - (1 / 2 : ℝ))
  )
  /
  (2 * BOfT nu0 T)

/--
The prior radius floor is strictly positive for a valid prior.
-/
theorem rho0FromPrior_positive
    (nu0 beta0 : ℝ)
    (hnu0 : 0 < nu0)
    (hbeta0 : 0 < beta0) :
    0 < rho0FromPrior nu0 beta0 := by
  unfold rho0FromPrior
  positivity

/--
The geometric score `T` is strictly positive on the admissible
quotient/prior domain.
-/
theorem TFromParams_positive
    (gamma alpha c gamma0 nu0 beta0 : ℝ)
    (halpha : 0 < alpha)
    (hc : 0 < c)
    (hnu0 : 0 < nu0)
    (hbeta0 : 0 < beta0) :
    0 <
      TFromParams
        gamma alpha c gamma0 nu0 beta0 := by

  have hrho :
      0 < rho0FromPrior nu0 beta0 :=
    rho0FromPrior_positive
      nu0 beta0 hnu0 hbeta0

  have hsum :
      0 <
        (gamma - gamma0) ^ 2 +
          rho0FromPrior nu0 beta0 := by
    nlinarith [sq_nonneg (gamma - gamma0)]

  have hden :
      0 <
        alpha *
          ((gamma - gamma0) ^ 2 +
            rho0FromPrior nu0 beta0) :=
    mul_pos halpha hsum

  unfold TFromParams

  exact div_pos hc hden

/--
Equivalent prior parameterization:

  β₀ = ρ₀ ν₀ / 2.
-/
theorem beta0_from_rho0
    (nu0 beta0 : ℝ)
    (hnu0 : 0 < nu0) :
    beta0 =
      rho0FromPrior nu0 beta0 * nu0 / 2 := by

  have hnu00 :
      nu0 ≠ 0 :=
    ne_of_gt hnu0

  unfold rho0FromPrior

  field_simp [hnu00]

/--
Exact bridge from the scalar `B(γ,α,c)` to the
geometric coordinate `T`:

  B = ν₀/2 * (1 + 1/T).
-/
theorem BFromParams_eq_BOfT
    (gamma alpha c gamma0 nu0 beta0 : ℝ)
    (halpha : 0 < alpha)
    (hc : 0 < c)
    (hnu0 : 0 < nu0)
    (hbeta0 : 0 < beta0) :
    BFromParams
        gamma alpha c gamma0 nu0 beta0
      =
    BOfT
      nu0
      (TFromParams
        gamma alpha c gamma0 nu0 beta0) := by

  have hrho :
      0 < rho0FromPrior nu0 beta0 :=
    rho0FromPrior_positive
      nu0 beta0 hnu0 hbeta0

  have hsum :
      0 <
        (gamma - gamma0) ^ 2 +
          rho0FromPrior nu0 beta0 := by
    nlinarith [sq_nonneg (gamma - gamma0)]

  have hden :
      0 <
        alpha *
          ((gamma - gamma0) ^ 2 +
            rho0FromPrior nu0 beta0) :=
    mul_pos halpha hsum

  have hc0 :
      c ≠ 0 :=
    ne_of_gt hc

  have halpha0 :
      alpha ≠ 0 :=
    ne_of_gt halpha

  have hnu00 :
      nu0 ≠ 0 :=
    ne_of_gt hnu0

  have hsum0 :
      (gamma - gamma0) ^ 2 +
          rho0FromPrior nu0 beta0
        ≠ 0 :=
    ne_of_gt hsum

  have hden0 :
      alpha *
          ((gamma - gamma0) ^ 2 +
            rho0FromPrior nu0 beta0)
        ≠ 0 :=
    ne_of_gt hden

  unfold BFromParams
  unfold BOfT
  unfold TFromParams
  unfold rho0FromPrior

  field_simp [
    hc0,
    halpha0,
    hnu00,
    hsum0,
    hden0
  ]

  ring

/--
Rationalization identity for the reciprocal canonical selector.
-/
theorem invNuCan_rationalized
    (alpha0 B : ℝ)
    (hB : 0 < B) :
    invNuCan alpha0 B
      =
    (
      Real.sqrt
        (selectorDiscriminant alpha0 B)
        -
      (B - alpha0 - (1 / 2 : ℝ))
    )
    /
    (2 * B) := by

  let d : ℝ :=
    B - alpha0 - (1 / 2 : ℝ)

  let D : ℝ :=
    d ^ 2 + 2 * B

  let s : ℝ :=
    Real.sqrt D

  have hD :
      0 ≤ D := by
    dsimp [D]
    positivity

  have hsquare :
      s ^ 2 = D := by
    dsimp [s]
    exact Real.sq_sqrt hD

  have hprod :
      (d + s) * (s - d) = 2 * B := by
    dsimp [D] at hsquare
    nlinarith [hsquare]

  have hnuEq :
      nuCan alpha0 B = d + s := by
    simp [nuCan, d, s, D]

  have hnuPos :
      0 < d + s := by
    rw [← hnuEq]
    exact nuCan_positive alpha0 B hB

  have hnu0 :
      d + s ≠ 0 :=
    ne_of_gt hnuPos

  have hB0 :
      B ≠ 0 :=
    ne_of_gt hB

  have h2B0 :
      2 * B ≠ 0 := by
    nlinarith

  have hrational :
      1 / (d + s)
        =
      (s - d) / (2 * B) := by
    field_simp [hnu0, h2B0]
    nlinarith [hprod]

  unfold invNuCan

  rw [hnuEq]

  simpa [
    d,
    D,
    s,
    selectorDiscriminant
  ] using hrational
/--
The explicit rationalized transfer formula
is exactly the inverse canonical allocation.
-/
theorem canonicalTransfer_eq_closedForm
    (nu0 alpha0 T : ℝ)
    (hnu0 : 0 < nu0)
    (hT : 0 < T) :
    canonicalTransfer nu0 alpha0 T
      =
    canonicalTransferClosedForm
      nu0 alpha0 T := by

  have hB :
      0 < BOfT nu0 T :=
    BOfT_positive
      nu0 T hnu0 hT

  unfold canonicalTransfer

  exact
    invNuCan_rationalized
      alpha0
      (BOfT nu0 T)
      hB

/--
The actual parameter-defined inverse allocation is exactly the
geometric transfer evaluated at the quotient score `T`.
-/
theorem actual_invNuCan_eq_transfer
    (gamma alpha c gamma0 nu0 alpha0 beta0 : ℝ)
    (halpha : 0 < alpha)
    (hc : 0 < c)
    (hnu0 : 0 < nu0)
    (hbeta0 : 0 < beta0) :
    invNuCan
        alpha0
        (BFromParams
          gamma alpha c gamma0 nu0 beta0)
      =
    canonicalTransfer
      nu0
      alpha0
      (TFromParams
        gamma alpha c gamma0 nu0 beta0) := by

  have hbridge :=
    BFromParams_eq_BOfT
      gamma alpha c gamma0 nu0 beta0
      halpha hc hnu0 hbeta0

  unfold canonicalTransfer

  rw [← hbridge]

/--
The actual parameter-defined inverse allocation also equals the
explicit closed-form transfer formula.
-/
theorem actual_invNuCan_eq_closedForm
    (gamma alpha c gamma0 nu0 alpha0 beta0 : ℝ)
    (halpha : 0 < alpha)
    (hc : 0 < c)
    (hnu0 : 0 < nu0)
    (hbeta0 : 0 < beta0) :
    invNuCan
        alpha0
        (BFromParams
          gamma alpha c gamma0 nu0 beta0)
      =
    canonicalTransferClosedForm
      nu0
      alpha0
      (TFromParams
        gamma alpha c gamma0 nu0 beta0) := by

  have hT :
      0 <
        TFromParams
          gamma alpha c gamma0 nu0 beta0 :=
    TFromParams_positive
      gamma alpha c gamma0 nu0 beta0
      halpha hc hnu0 hbeta0

  calc
    invNuCan
        alpha0
        (BFromParams
          gamma alpha c gamma0 nu0 beta0)
        =
      canonicalTransfer
        nu0
        alpha0
        (TFromParams
          gamma alpha c gamma0 nu0 beta0) :=
      actual_invNuCan_eq_transfer
        gamma alpha c gamma0 nu0 alpha0 beta0
        halpha hc hnu0 hbeta0

    _ =
      canonicalTransferClosedForm
        nu0
        alpha0
        (TFromParams
          gamma alpha c gamma0 nu0 beta0) :=
      canonicalTransfer_eq_closedForm
        nu0
        alpha0
        (TFromParams
          gamma alpha c gamma0 nu0 beta0)
        hnu0
        hT

/--
For two admissible quotient states under the same complete prior,
ordering by the geometric score `T` is exactly equivalent to
ordering by inverse canonical allocation.
-/
theorem actual_inverse_allocation_order_iff_T
    (gamma1 alpha1 c1 gamma2 alpha2 c2
      gamma0 nu0 alpha0 beta0 : ℝ)
    (halpha01 : 0 < alpha1)
    (hc1 : 0 < c1)
    (halpha02 : 0 < alpha2)
    (hc2 : 0 < c2)
    (hnu0 : 0 < nu0)
    (halpha0 : 0 < alpha0)
    (hbeta0 : 0 < beta0) :
    invNuCan
        alpha0
        (BFromParams
          gamma1 alpha1 c1 gamma0 nu0 beta0)
      <
    invNuCan
        alpha0
        (BFromParams
          gamma2 alpha2 c2 gamma0 nu0 beta0)
      ↔
    TFromParams
        gamma1 alpha1 c1 gamma0 nu0 beta0
      <
    TFromParams
        gamma2 alpha2 c2 gamma0 nu0 beta0 := by

  have hT1 :
      0 <
        TFromParams
          gamma1 alpha1 c1 gamma0 nu0 beta0 :=
    TFromParams_positive
      gamma1 alpha1 c1 gamma0 nu0 beta0
      halpha01 hc1 hnu0 hbeta0

  have hT2 :
      0 <
        TFromParams
          gamma2 alpha2 c2 gamma0 nu0 beta0 :=
    TFromParams_positive
      gamma2 alpha2 c2 gamma0 nu0 beta0
      halpha02 hc2 hnu0 hbeta0

  rw [
    actual_invNuCan_eq_transfer
      gamma1 alpha1 c1 gamma0 nu0 alpha0 beta0
      halpha01 hc1 hnu0 hbeta0,

    actual_invNuCan_eq_transfer
      gamma2 alpha2 c2 gamma0 nu0 alpha0 beta0
      halpha02 hc2 hnu0 hbeta0
  ]

  exact
    canonicalTransfer_order_iff
      nu0
      alpha0
      (TFromParams
        gamma1 alpha1 c1 gamma0 nu0 beta0)
      (TFromParams
        gamma2 alpha2 c2 gamma0 nu0 beta0)
      hnu0
      halpha0
      hT1
      hT2

end ELVAE