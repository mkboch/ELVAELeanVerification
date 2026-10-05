import Mathlib
import ELVAELeanVerification.ParameterBridge

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Variance budget and internal canonical allocation

For `α > 1`, this module verifies the algebraic identities

  u_var =
    c / (α - 1) * ν / (1 + ν),

  u_epi =
    c / (α - 1) * 1 / (1 + ν),

and proves

  u_var + u_epi = c / (α - 1),

  u_epi / u_var = 1 / ν.

The final theorem instantiates these identities at the
prior-relative canonical selector.
-/

namespace ELVAE

noncomputable def uVar
    (c alpha nu : ℝ) : ℝ :=
  (c / (alpha - 1)) *
    (nu / (1 + nu))

noncomputable def uEpi
    (c alpha nu : ℝ) : ℝ :=
  (c / (alpha - 1)) *
    (1 / (1 + nu))

/--
The total variance budget is independent of the fiber allocation.
-/
theorem variance_budget
    (c alpha nu : ℝ)
    (halpha : 1 < alpha)
    (hnu : 0 < nu) :
    uVar c alpha nu + uEpi c alpha nu
      =
    c / (alpha - 1) := by
  have ha :
      alpha - 1 ≠ 0 := by
    linarith
  have hn :
      1 + nu ≠ 0 := by
    linarith
  unfold uVar uEpi
  field_simp [ha, hn]
  <;> ring

/--
The epistemic-to-conditional allocation ratio is exactly `1 / ν`.
-/
theorem variance_allocation_ratio
    (c alpha nu : ℝ)
    (hc : 0 < c)
    (halpha : 1 < alpha)
    (hnu : 0 < nu) :
    uEpi c alpha nu / uVar c alpha nu
      =
    1 / nu := by
  have hc0 :
      c ≠ 0 := ne_of_gt hc
  have ha :
      alpha - 1 ≠ 0 := by
    linarith
  have hnu0 :
      nu ≠ 0 := ne_of_gt hnu
  have hn :
      1 + nu ≠ 0 := by
    linarith
  unfold uVar uEpi
  field_simp [hc0, ha, hnu0, hn]

/--
At the prior-relative canonical representative, the total
variance is fixed by the quotient coordinate.
-/
theorem canonical_variance_budget
    (gamma alpha c gamma0 nu0 alpha0 beta0 : ℝ)
    (halpha : 1 < alpha)
    (hc : 0 < c)
    (hnu0 : 0 < nu0)
    (hbeta0 : 0 < beta0) :
    uVar
        c
        alpha
        (nuCanFromParams
          gamma alpha c gamma0 nu0 alpha0 beta0)
      +
      uEpi
        c
        alpha
        (nuCanFromParams
          gamma alpha c gamma0 nu0 alpha0 beta0)
      =
    c / (alpha - 1) := by
  have halpha0 :
      0 < alpha := by
    linarith
  have hnu :
      0 <
        nuCanFromParams
          gamma alpha c gamma0 nu0 alpha0 beta0 :=
    nuCanFromParams_positive
      gamma alpha c gamma0 nu0 alpha0 beta0
      halpha0 hc hnu0 hbeta0
  exact
    variance_budget
      c alpha
      (nuCanFromParams
        gamma alpha c gamma0 nu0 alpha0 beta0)
      halpha hnu

/--
At the canonical representative,

  u_epi / u_var = 1 / ν_can.
-/
theorem canonical_variance_allocation_ratio
    (gamma alpha c gamma0 nu0 alpha0 beta0 : ℝ)
    (halpha : 1 < alpha)
    (hc : 0 < c)
    (hnu0 : 0 < nu0)
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
      =
    1 /
      nuCanFromParams
        gamma alpha c gamma0 nu0 alpha0 beta0 := by
  have halpha0 :
      0 < alpha := by
    linarith
  have hnu :
      0 <
        nuCanFromParams
          gamma alpha c gamma0 nu0 alpha0 beta0 :=
    nuCanFromParams_positive
      gamma alpha c gamma0 nu0 alpha0 beta0
      halpha0 hc hnu0 hbeta0
  exact
    variance_allocation_ratio
      c alpha
      (nuCanFromParams
        gamma alpha c gamma0 nu0 alpha0 beta0)
      hc halpha hnu

end ELVAE