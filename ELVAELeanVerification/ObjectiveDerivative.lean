import Mathlib
import ELVAELeanVerification.StationarityReduction

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# ELVAE restricted objective derivative

This module formally differentiates the ν-dependent part of the
fiber-restricted KL objective

  R(ν) =
    (α₀ + 1/2) log ν
    - α₀ log(1 + ν)
    + B / ν

up to an additive constant independent of ν.

It verifies the stationary derivative formula.
-/

namespace ELVAE

noncomputable def fiberObjective
    (alpha0 B nu : ℝ) : ℝ :=
  (alpha0 + (1 / 2 : ℝ)) * Real.log nu
    - alpha0 * Real.log (1 + nu)
    + B / nu

/--
For ν > 0, the derivative of the restricted objective is exactly
the stationary derivative expression.
-/
theorem fiberObjective_hasDerivAt
    (alpha0 B nu : ℝ)
    (hnu : 0 < nu) :
    HasDerivAt
      (fun x : ℝ => fiberObjective alpha0 B x)
      (stationaryDerivative alpha0 B nu)
      nu := by

  have hnu0 : nu ≠ 0 := ne_of_gt hnu

  have h1nu0 : 1 + nu ≠ 0 := by
    linarith

  have hlogNu :
      HasDerivAt
        (fun x : ℝ => Real.log x)
        (1 / nu)
        nu := by
    simpa [one_div] using Real.hasDerivAt_log hnu0

  have hinner :
      HasDerivAt
        (fun x : ℝ => 1 + x)
        1
        nu := by
    simpa using (hasDerivAt_id nu).const_add (1 : ℝ)

  have hlogOneNu :
      HasDerivAt
        (fun x : ℝ => Real.log (1 + x))
        (1 / (1 + nu))
        nu := by
    simpa using hinner.log h1nu0

  have hinv :
      HasDerivAt
        (fun x : ℝ => x⁻¹)
        (-(nu ^ 2)⁻¹)
        nu :=
    hasDerivAt_inv hnu0

  have hBdiv :
      HasDerivAt
        (fun x : ℝ => B / x)
        (-B / nu ^ 2)
        nu := by
    simpa [div_eq_mul_inv] using hinv.const_mul B

  have hfirst :=
    hlogNu.const_mul (alpha0 + (1 / 2 : ℝ))

  have hsecond :=
    hlogOneNu.const_mul alpha0

  have htotal :=
    (hfirst.sub hsecond).add hBdiv

  convert htotal using 1
  · funext x
    simp [fiberObjective, div_eq_mul_inv]
  · simp [stationaryDerivative, div_eq_mul_inv]
    ring

/--
The ordinary derivative function therefore evaluates to the
stationary derivative expression on the admissible domain ν > 0.
-/
theorem fiberObjective_deriv
    (alpha0 B nu : ℝ)
    (hnu : 0 < nu) :
    deriv
        (fun x : ℝ => fiberObjective alpha0 B x)
        nu
      =
        stationaryDerivative alpha0 B nu := by
  exact (fiberObjective_hasDerivAt alpha0 B nu hnu).deriv

/--
Combining formal differentiation with the previously verified
stationarity reduction:

for B > 0 and ν > 0, the derivative of the actual restricted
objective vanishes if and only if ν is the canonical selector.
-/
theorem fiberObjective_deriv_eq_zero_iff_nuCan
    (alpha0 B nu : ℝ)
    (hB : 0 < B)
    (hnu : 0 < nu) :
    deriv
        (fun x : ℝ => fiberObjective alpha0 B x)
        nu = 0
      ↔
        nu = nuCan alpha0 B := by

  rw [fiberObjective_deriv alpha0 B nu hnu]

  exact
    stationaryDerivative_zero_iff_nuCan
      alpha0 B nu hB hnu

end ELVAE
