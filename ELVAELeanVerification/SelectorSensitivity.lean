import Mathlib
import ELVAELeanVerification.ParameterBridge

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Sensitivity of the canonical selector

This module verifies the derivative formula

  dν_can/dB =
    1 +
    (B - α₀ - 1/2 + 1) /
      sqrt((B - α₀ - 1/2)^2 + 2B)

and proves, for `α₀ > 0` and `B > 0`,

  0 < dν_can/dB < 2.

It then derives strict monotonicity of the canonical selector
as a function of `B` on the positive real axis.
-/

namespace ELVAE

noncomputable def selectorDiscriminant
    (alpha0 B : ℝ) : ℝ :=
  (B - alpha0 - (1 / 2 : ℝ)) ^ 2 + 2 * B

noncomputable def selectorDerivative
    (alpha0 B : ℝ) : ℝ :=
  1 +
    (B - alpha0 - (1 / 2 : ℝ) + 1) /
      Real.sqrt (selectorDiscriminant alpha0 B)

/--
The selector discriminant is strictly positive whenever `B > 0`.
-/
theorem selectorDiscriminant_positive
    (alpha0 B : ℝ)
    (hB : 0 < B) :
    0 < selectorDiscriminant alpha0 B := by
  unfold selectorDiscriminant
  nlinarith [sq_nonneg (B - alpha0 - (1 / 2 : ℝ))]

/--
Formal differentiation of the closed-form canonical selector
with respect to `B`.
-/
theorem nuCan_hasDerivAt_B
    (alpha0 B : ℝ)
    (hB : 0 < B) :
    HasDerivAt
      (fun x : ℝ => nuCan alpha0 x)
      (selectorDerivative alpha0 B)
      B := by

  have hbase :
      HasDerivAt
        (fun x : ℝ =>
          x - alpha0 - (1 / 2 : ℝ))
        1
        B := by
    simpa using
      ((hasDerivAt_id B).sub_const alpha0).sub_const
        (1 / 2 : ℝ)

  have hsq :
      HasDerivAt
        (fun x : ℝ =>
          (x - alpha0 - (1 / 2 : ℝ)) ^ 2)
        (2 * (B - alpha0 - (1 / 2 : ℝ)))
        B := by
    convert hbase.pow 2 using 1 <;> norm_num

  have hlin :
      HasDerivAt
        (fun x : ℝ => 2 * x)
        2
        B := by
    simpa using
      (hasDerivAt_id B).const_mul (2 : ℝ)

  have hdisc :
      HasDerivAt
        (fun x : ℝ =>
          selectorDiscriminant alpha0 x)
        (2 * (B - alpha0 - (1 / 2 : ℝ)) + 2)
        B := by
    have hsum := hsq.add hlin
    convert hsum using 1
    · funext x
      simp [selectorDiscriminant]

  have hdiscPos :
      0 < selectorDiscriminant alpha0 B :=
    selectorDiscriminant_positive alpha0 B hB

  have hsqrt :
      HasDerivAt
        (fun x : ℝ =>
          Real.sqrt
            (selectorDiscriminant alpha0 x))
        ((2 * (B - alpha0 - (1 / 2 : ℝ)) + 2) /
          (2 *
            Real.sqrt
              (selectorDiscriminant alpha0 B)))
        B :=
    hdisc.sqrt (ne_of_gt hdiscPos)

  have htotal :=
    hbase.add hsqrt

  have hsqrtPos :
      0 <
        Real.sqrt
          (selectorDiscriminant alpha0 B) := by
    exact Real.sqrt_pos.2 hdiscPos

  convert htotal using 1
  · funext x
    simp [nuCan, selectorDiscriminant]
  · unfold selectorDerivative
    field_simp [ne_of_gt hsqrtPos]

/--
The derivative function is exactly the closed-form expression.
-/
theorem nuCan_deriv_B
    (alpha0 B : ℝ)
    (hB : 0 < B) :
    deriv
        (fun x : ℝ => nuCan alpha0 x)
        B
      =
    selectorDerivative alpha0 B := by
  exact
    (nuCan_hasDerivAt_B alpha0 B hB).deriv

/--
The algebraic gap used in the derivative bound:

  D(B) - (B - α₀ - 1/2 + 1)^2 = 2 α₀.
-/
theorem selector_discriminant_gap
    (alpha0 B : ℝ) :
    selectorDiscriminant alpha0 B
      -
      (B - alpha0 - (1 / 2 : ℝ) + 1) ^ 2
      =
    2 * alpha0 := by
  unfold selectorDiscriminant
  ring

/--
For a valid prior tail parameter and positive B,

  0 < dν_can/dB < 2.
-/
theorem selectorDerivative_bounds
    (alpha0 B : ℝ)
    (halpha0 : 0 < alpha0)
    (hB : 0 < B) :
    0 < selectorDerivative alpha0 B
      ∧
    selectorDerivative alpha0 B < 2 := by

  let x :
      ℝ :=
    B - alpha0 - (1 / 2 : ℝ) + 1

  let D :
      ℝ :=
    selectorDiscriminant alpha0 B

  have hDpos :
      0 < D := by
    dsimp [D]
    exact
      selectorDiscriminant_positive
        alpha0 B hB

  have hgap :
      x ^ 2 < D := by
    have hid :=
      selector_discriminant_gap alpha0 B
    dsimp [x, D]
    nlinarith

  have hsqrtGap :
      Real.sqrt (x ^ 2) <
        Real.sqrt D := by
    exact
      Real.sqrt_lt_sqrt
        (sq_nonneg x)
        hgap

  have habs :
      |x| < Real.sqrt D := by
    simpa only [Real.sqrt_sq_eq_abs]
      using hsqrtGap

  have hsqrtPos :
      0 < Real.sqrt D :=
    Real.sqrt_pos.2 hDpos

  have habsParts :
      -Real.sqrt D < x
        ∧
      x < Real.sqrt D := by
    exact abs_lt.mp habs

  have hlower :
      -1 < x / Real.sqrt D := by
    apply
      (lt_div_iff₀ hsqrtPos).2
    nlinarith [habsParts.1]

  have hupper :
      x / Real.sqrt D < 1 := by
    apply
      (div_lt_iff₀ hsqrtPos).2
    nlinarith [habsParts.2]

  dsimp [x, D] at hlower hupper
  unfold selectorDerivative

  constructor <;> nlinarith

/--
Therefore the ordinary derivative of `ν_can(B)` lies strictly
between zero and two.
-/
theorem nuCan_deriv_B_bounds
    (alpha0 B : ℝ)
    (halpha0 : 0 < alpha0)
    (hB : 0 < B) :
    0 <
      deriv
        (fun x : ℝ => nuCan alpha0 x)
        B
    ∧
      deriv
        (fun x : ℝ => nuCan alpha0 x)
        B
      < 2 := by

  rw [nuCan_deriv_B alpha0 B hB]

  exact
    selectorDerivative_bounds
      alpha0 B halpha0 hB

/--
The selector is strictly increasing in `B` throughout `B > 0`.
-/
theorem nuCan_strictMonoOn_B
    (alpha0 : ℝ)
    (halpha0 : 0 < alpha0) :
    StrictMonoOn
      (fun B : ℝ => nuCan alpha0 B)
      (Set.Ioi 0) := by

  refine
    strictMonoOn_of_deriv_pos
      (convex_Ioi (0 : ℝ))
      ?_
      ?_

  · intro B hB

    have hBpos :
        0 < B := by
      simpa using hB

    exact
      (nuCan_hasDerivAt_B
        alpha0 B hBpos).continuousAt.continuousWithinAt

  · intro B hB

    have hBpos :
        0 < B := by
      simpa using hB

    exact
      (nuCan_deriv_B_bounds
        alpha0 B halpha0 hBpos).1

end ELVAE