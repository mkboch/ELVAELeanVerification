import Mathlib
import ELVAELeanVerification.SelectorSensitivity

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Ordinal geometry of the canonical selector

This module verifies the monotonicity structure of the ordinal
geometry of the canonical selector.

For positive `T`, define

  B(T) = ν₀ / 2 * (1 + 1 / T).

The previously verified selector satisfies

  B₁ < B₂  ->  ν_can(B₁) < ν_can(B₂).

This module proves:

1. `T -> B(T)` is strictly decreasing;
2. `B -> 1 / ν_can(B)` is strictly decreasing;
3. therefore
   `T -> 1 / ν_can(B(T))`
   is strictly increasing.

Thus inverse canonical allocation has exactly the same
coordinatewise ordering as the geometric score `T` whenever
the same prior calibration applies.
-/

namespace ELVAE

noncomputable def BOfT
    (nu0 T : ℝ) : ℝ :=
  (nu0 / 2) * (1 + 1 / T)

noncomputable def invNuCan
    (alpha0 B : ℝ) : ℝ :=
  1 / nuCan alpha0 B

noncomputable def canonicalTransfer
    (nu0 alpha0 T : ℝ) : ℝ :=
  invNuCan alpha0 (BOfT nu0 T)

/--
For positive prior precision and positive geometric score,
`B(T)` lies strictly above `ν₀ / 2`.
-/
theorem BOfT_gt_half_nu0
    (nu0 T : ℝ)
    (hnu0 : 0 < nu0)
    (hT : 0 < T) :
    nu0 / 2 < BOfT nu0 T := by
  have hhalf :
      0 < nu0 / 2 := by
    linarith
  have hinv :
      0 < 1 / T := by
    exact one_div_pos.mpr hT
  have hprod :
      0 < (nu0 / 2) * (1 / T) :=
    mul_pos hhalf hinv
  unfold BOfT
  nlinarith

/--
Consequently `B(T)` is positive.
-/
theorem BOfT_positive
    (nu0 T : ℝ)
    (hnu0 : 0 < nu0)
    (hT : 0 < T) :
    0 < BOfT nu0 T := by
  have hhalf :
      0 < nu0 / 2 := by
    linarith
  have hgt :=
    BOfT_gt_half_nu0
      nu0 T hnu0 hT
  linarith

/--
The geometric transfer is strictly decreasing in `T`.
-/
theorem BOfT_strict_decreasing
    (nu0 T1 T2 : ℝ)
    (hnu0 : 0 < nu0)
    (hT1 : 0 < T1)
    (hT12 : T1 < T2) :
    BOfT nu0 T2 < BOfT nu0 T1 := by

  have hT2 :
      0 < T2 := by
    linarith

  have hinv :
      1 / T2 < 1 / T1 := by
    apply
      (div_lt_div_iff₀ hT2 hT1).2
    nlinarith

  have hhalf :
      0 < nu0 / 2 := by
    linarith

  have hdiff :
      0 <
        (nu0 / 2) *
          ((1 / T1) - (1 / T2)) := by
    exact
      mul_pos
        hhalf
        (sub_pos.mpr hinv)

  unfold BOfT
  nlinarith

/--
The canonical selector is strictly increasing in `B`,
restated pointwise for later composition.
-/
theorem nuCan_lt_of_B_lt
    (alpha0 B1 B2 : ℝ)
    (halpha0 : 0 < alpha0)
    (hB1 : 0 < B1)
    (hB2 : 0 < B2)
    (hB12 : B1 < B2) :
    nuCan alpha0 B1
      <
    nuCan alpha0 B2 := by

  exact
    nuCan_strictMonoOn_B
      alpha0 halpha0
      hB1 hB2 hB12

/--
Since `ν_can > 0`, reciprocal canonical allocation is strictly
decreasing as a function of `B`.
-/
theorem invNuCan_strict_decreasing
    (alpha0 B1 B2 : ℝ)
    (halpha0 : 0 < alpha0)
    (hB1 : 0 < B1)
    (hB2 : 0 < B2)
    (hB12 : B1 < B2) :
    invNuCan alpha0 B2
      <
    invNuCan alpha0 B1 := by

  have hnu1 :
      0 < nuCan alpha0 B1 :=
    nuCan_positive alpha0 B1 hB1

  have hnu2 :
      0 < nuCan alpha0 B2 :=
    nuCan_positive alpha0 B2 hB2

  have hnult :
      nuCan alpha0 B1
        <
      nuCan alpha0 B2 :=
    nuCan_lt_of_B_lt
      alpha0 B1 B2
      halpha0 hB1 hB2 hB12

  unfold invNuCan

  apply
    (div_lt_div_iff₀ hnu2 hnu1).2

  nlinarith

/--
The canonical transfer is strictly positive.
-/
theorem canonicalTransfer_positive
    (nu0 alpha0 T : ℝ)
    (hnu0 : 0 < nu0)
    (hT : 0 < T) :
    0 < canonicalTransfer nu0 alpha0 T := by

  have hB :
      0 < BOfT nu0 T :=
    BOfT_positive
      nu0 T hnu0 hT

  have hnu :
      0 <
        nuCan
          alpha0
          (BOfT nu0 T) :=
    nuCan_positive
      alpha0
      (BOfT nu0 T)
      hB

  unfold canonicalTransfer invNuCan

  exact one_div_pos.mpr hnu

/--
Main ordinal result.

For fixed positive prior parameters, increasing `T`
strictly increases inverse canonical allocation.
-/
theorem canonicalTransfer_strict_increasing
    (nu0 alpha0 T1 T2 : ℝ)
    (hnu0 : 0 < nu0)
    (halpha0 : 0 < alpha0)
    (hT1 : 0 < T1)
    (hT12 : T1 < T2) :
    canonicalTransfer nu0 alpha0 T1
      <
    canonicalTransfer nu0 alpha0 T2 := by

  have hT2 :
      0 < T2 := by
    linarith

  have hB1 :
      0 < BOfT nu0 T1 :=
    BOfT_positive
      nu0 T1 hnu0 hT1

  have hB2 :
      0 < BOfT nu0 T2 :=
    BOfT_positive
      nu0 T2 hnu0 hT2

  have hBdec :
      BOfT nu0 T2
        <
      BOfT nu0 T1 :=
    BOfT_strict_decreasing
      nu0 T1 T2
      hnu0 hT1 hT12

  have hinv :
      invNuCan
          alpha0
          (BOfT nu0 T1)
        <
      invNuCan
          alpha0
          (BOfT nu0 T2) := by

    exact
      invNuCan_strict_decreasing
        alpha0
        (BOfT nu0 T2)
        (BOfT nu0 T1)
        halpha0
        hB2
        hB1
        hBdec

  simpa [canonicalTransfer] using hinv

/--
Set-theoretic form of the ordinal geometry:
the transfer is strictly monotone on `(0,∞)`.
-/
theorem canonicalTransfer_strictMonoOn
    (nu0 alpha0 : ℝ)
    (hnu0 : 0 < nu0)
    (halpha0 : 0 < alpha0) :
    StrictMonoOn
      (canonicalTransfer nu0 alpha0)
      (Set.Ioi 0) := by

  intro T1 hT1 T2 hT2 hlt

  exact
    canonicalTransfer_strict_increasing
      nu0 alpha0 T1 T2
      hnu0
      halpha0
      hT1
      hlt

/--
Exact ordinal equivalence for two positive geometric scores.

`T1 < T2` if and only if inverse canonical allocation at
`T1` is smaller than inverse canonical allocation at `T2`.
-/
theorem canonicalTransfer_order_iff
    (nu0 alpha0 T1 T2 : ℝ)
    (hnu0 : 0 < nu0)
    (halpha0 : 0 < alpha0)
    (hT1 : 0 < T1)
    (hT2 : 0 < T2) :
    canonicalTransfer nu0 alpha0 T1
        <
      canonicalTransfer nu0 alpha0 T2
      ↔
    T1 < T2 := by

  constructor

  · intro htransfer

    by_contra hnot

    have hle :
        T2 ≤ T1 :=
      le_of_not_gt hnot

    rcases lt_or_eq_of_le hle with hlt | heq

    · have hreverse :
          canonicalTransfer nu0 alpha0 T2
            <
          canonicalTransfer nu0 alpha0 T1 :=
        canonicalTransfer_strict_increasing
          nu0 alpha0 T2 T1
          hnu0
          halpha0
          hT2
          hlt

      linarith

    · subst T2
      linarith

  · intro hlt

    exact
      canonicalTransfer_strict_increasing
        nu0 alpha0 T1 T2
        hnu0
        halpha0
        hT1
        hlt

end ELVAE