import Mathlib

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

namespace ELVAE

/-
Canonical selector from the prior-relative NIG reduction.

Define

  ν_can =
    B - α₀ - 1/2
    + sqrt((B - α₀ - 1/2)^2 + 2B).

This file verifies the algebraic core of the stationary-point claim.
-/

noncomputable def nuCan (alpha0 B : ℝ) : ℝ :=
  B - alpha0 - (1 / 2 : ℝ) +
    Real.sqrt ((B - alpha0 - (1 / 2 : ℝ)) ^ 2 + 2 * B)


/-
For B > 0, the canonical root is strictly positive.
-/

theorem nuCan_positive
    (alpha0 B : ℝ)
    (hB : 0 < B) :
    0 < nuCan alpha0 B := by

  let d : ℝ := B - alpha0 - (1 / 2 : ℝ)
  let D : ℝ := d ^ 2 + 2 * B

  have hD : 0 ≤ D := by
    dsimp [D]
    positivity

  have hsquare :
      (Real.sqrt D) ^ 2 = D :=
    Real.sq_sqrt hD

  have hsqrt :
      0 ≤ Real.sqrt D :=
    Real.sqrt_nonneg D

  have hpositive :
      0 < d + Real.sqrt D := by
    nlinarith

  simpa [nuCan, d, D] using hpositive


/-
The closed-form canonical selector satisfies the stationary quadratic

  ν² + (2α₀ + 1 - 2B)ν - 2B = 0.
-/

theorem nuCan_satisfies_stationary_quadratic
    (alpha0 B : ℝ)
    (hB : 0 < B) :
    (nuCan alpha0 B) ^ 2
      + (2 * alpha0 + 1 - 2 * B) * nuCan alpha0 B
      - 2 * B = 0 := by

  have hD :
      0 ≤
        (B - alpha0 - (1 / 2 : ℝ)) ^ 2 + 2 * B := by
    positivity

  have hsquare :
      (Real.sqrt
        ((B - alpha0 - (1 / 2 : ℝ)) ^ 2 + 2 * B)) ^ 2
        =
        (B - alpha0 - (1 / 2 : ℝ)) ^ 2 + 2 * B :=
    Real.sq_sqrt hD

  unfold nuCan
  nlinarith


/-
Any strictly positive solution of the stationary quadratic must equal
the canonical root.

Therefore the stationary quadratic has at most one positive solution.
Combined with the previous two theorems, ν_can is exactly its unique
positive solution.
-/

theorem stationary_quadratic_unique_positive
    (alpha0 B nu : ℝ)
    (hB : 0 < B)
    (hnu : 0 < nu)
    (hstationary :
      nu ^ 2
        + (2 * alpha0 + 1 - 2 * B) * nu
        - 2 * B = 0) :
    nu = nuCan alpha0 B := by

  let d : ℝ := B - alpha0 - (1 / 2 : ℝ)
  let D : ℝ := d ^ 2 + 2 * B

  have hD : 0 ≤ D := by
    dsimp [D]
    positivity

  have hsqrt_sq :
      (Real.sqrt D) ^ 2 = D :=
    Real.sq_sqrt hD

  have hsqrt_nonneg :
      0 ≤ Real.sqrt D :=
    Real.sqrt_nonneg D

  have hstationary' :
      nu ^ 2 - 2 * d * nu - 2 * B = 0 := by
    dsimp [d]
    nlinarith [hstationary]

  have hproduct :
      nu * (nu - 2 * d) = 2 * B := by
    nlinarith [hstationary']

  have hmul_positive :
      0 < nu * (nu - 2 * d) := by
    rw [hproduct]
    nlinarith

  have hsecond :
      0 < nu - 2 * d := by
    rcases (mul_pos_iff.mp hmul_positive) with h | h
    · exact h.2
    · linarith [hnu, h.1]

  have hleft_positive :
      0 < nu - d := by
    nlinarith [hnu, hsecond]

  have hleft_square :
      (nu - d) ^ 2 = D := by
    dsimp [D]
    nlinarith [hstationary']

  have hroot :
      nu - d = Real.sqrt D := by
    nlinarith [
      hleft_square,
      hsqrt_sq,
      hsqrt_nonneg,
      hleft_positive
    ]

  unfold nuCan
  dsimp [d, D] at hroot ⊢
  nlinarith [hroot]


/-
Explicit uniqueness statement:
two positive stationary solutions must be equal.
-/

theorem stationary_quadratic_positive_solution_unique
    (alpha0 B nu1 nu2 : ℝ)
    (hB : 0 < B)
    (hnu1 : 0 < nu1)
    (hnu2 : 0 < nu2)
    (h1 :
      nu1 ^ 2
        + (2 * alpha0 + 1 - 2 * B) * nu1
        - 2 * B = 0)
    (h2 :
      nu2 ^ 2
        + (2 * alpha0 + 1 - 2 * B) * nu2
        - 2 * B = 0) :
    nu1 = nu2 := by

  have hcan1 :
      nu1 = nuCan alpha0 B :=
    stationary_quadratic_unique_positive
      alpha0 B nu1 hB hnu1 h1

  have hcan2 :
      nu2 = nuCan alpha0 B :=
    stationary_quadratic_unique_positive
      alpha0 B nu2 hB hnu2 h2

  rw [hcan1, hcan2]

end ELVAE
