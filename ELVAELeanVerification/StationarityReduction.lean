import Mathlib
import ELVAELeanVerification.CanonicalSelector

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

namespace ELVAE

/-
The stationary derivative, represented algebraically.

This is the derivative expression after restricting the NIG KL
divergence to a fiber.
-/
noncomputable def stationaryDerivative
    (alpha0 B nu : ℝ) : ℝ :=
  (alpha0 + (1 / 2 : ℝ)) / nu
    - alpha0 / (1 + nu)
    - B / nu ^ 2


/-
The stationarity condition as a quadratic in `ν`.
-/
def stationaryQuadratic
    (alpha0 B nu : ℝ) : ℝ :=
  nu ^ 2
    + (2 * alpha0 + 1 - 2 * B) * nu
    - 2 * B


/-
For positive ν, multiplying the derivative expression by

  2 ν² (1 + ν)

produces exactly the stationary quadratic.
-/
theorem derivative_multiplier_identity
    (alpha0 B nu : ℝ)
    (hnu : 0 < nu) :
    2 * nu ^ 2 * (1 + nu)
        * stationaryDerivative alpha0 B nu
      =
        stationaryQuadratic alpha0 B nu := by

  have hnu0 : nu ≠ 0 := ne_of_gt hnu

  have h1nu0 : 1 + nu ≠ 0 := by
    linarith

  unfold stationaryDerivative stationaryQuadratic

  field_simp [hnu0, h1nu0]
  <;> ring


/-
The multiplying factor is strictly positive on the admissible domain.
-/
theorem derivative_multiplier_positive
    (nu : ℝ)
    (hnu : 0 < nu) :
    0 < 2 * nu ^ 2 * (1 + nu) := by
  positivity


/-
Therefore, on ν > 0,

  R'(ν) = 0

is equivalent to

  ν² + (2α₀ + 1 - 2B)ν - 2B = 0.
-/
theorem stationaryDerivative_eq_zero_iff_quadratic
    (alpha0 B nu : ℝ)
    (hnu : 0 < nu) :
    stationaryDerivative alpha0 B nu = 0
      ↔ stationaryQuadratic alpha0 B nu = 0 := by

  have hid :=
    derivative_multiplier_identity alpha0 B nu hnu

  have hpos :=
    derivative_multiplier_positive nu hnu

  have hfactor :
      2 * nu ^ 2 * (1 + nu) ≠ 0 :=
    ne_of_gt hpos

  constructor

  · intro hderiv

    calc
      stationaryQuadratic alpha0 B nu
          =
          2 * nu ^ 2 * (1 + nu)
            * stationaryDerivative alpha0 B nu := by
              symm
              exact hid
      _ = 0 := by
            rw [hderiv]
            ring

  · intro hquad

    have hmul :
        2 * nu ^ 2 * (1 + nu)
            * stationaryDerivative alpha0 B nu = 0 := by
      rw [hid, hquad]

    rcases mul_eq_zero.mp hmul with hf | hd

    · exact False.elim (hfactor hf)

    · exact hd


/-
Combining the stationarity reduction with the already verified
canonical-selector theorem:

for B > 0 and ν > 0,

  stationaryDerivative = 0

if and only if

  ν = ν_can.
-/
theorem stationaryDerivative_zero_iff_nuCan
    (alpha0 B nu : ℝ)
    (hB : 0 < B)
    (hnu : 0 < nu) :
    stationaryDerivative alpha0 B nu = 0
      ↔ nu = nuCan alpha0 B := by

  constructor

  · intro hderiv

    have hquad :
        stationaryQuadratic alpha0 B nu = 0 :=
      (stationaryDerivative_eq_zero_iff_quadratic
        alpha0 B nu hnu).mp hderiv

    unfold stationaryQuadratic at hquad

    exact
      stationary_quadratic_unique_positive
        alpha0 B nu hB hnu hquad

  · intro hnuCan

    subst nu

    have hcanpos :
        0 < nuCan alpha0 B :=
      nuCan_positive alpha0 B hB

    have hquad :
        stationaryQuadratic
          alpha0 B (nuCan alpha0 B) = 0 := by

      unfold stationaryQuadratic

      exact
        nuCan_satisfies_stationary_quadratic
          alpha0 B hB

    exact
      (stationaryDerivative_eq_zero_iff_quadratic
        alpha0 B (nuCan alpha0 B) hcanpos).mpr hquad

end ELVAE
