import Mathlib
import ELVAELeanVerification.PriorGaugeCeiling

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Dependence of the prior ceiling `M₀` on `α₀`

For fixed `ν₀ > 0`, with `M₀(α₀) = 1 / ν_can(α₀, ν₀/2)`, this module proves:

1. `α₀ ↦ M₀` is strictly increasing (on all of `ℝ`, hence on `α₀ > 0`);
2. `M₀ → 1/ν₀` as `α₀ → 0⁺` (and `M₀(0) = 1/ν₀` exactly);
3. the exact remainder identity, valid for every real `α₀`,

     M₀ = (2α₀ + 1)/ν₀ − 1 + 2 / (√(m² + 4ν₀) + m),   m = 2α₀ + 1 − ν₀;

4. the explicit bound `0 < M₀ − [(2α₀+1)/ν₀ − 1] < 1/m` whenever `m > 0`;
5. the large-`α₀` asymptotic as a genuine Big-O statement:

     M₀ − [(2α₀+1)/ν₀ − 1] = O(α₀⁻¹)   as α₀ → ∞;

6. the sharper first-order statement `α₀ · (M₀ − [(2α₀+1)/ν₀ − 1]) → 1/2`.
-/

namespace ELVAE

open Filter Topology

/--
For fixed `B > 0`, the canonical selector is strictly decreasing in `α₀`
(on all of `ℝ`).
-/
theorem nuCan_strictAnti_alpha0
    (B : ℝ) (hB : 0 < B) :
    StrictAnti (fun a : ℝ => nuCan a B) := by
  intro a1 a2 h12
  have hnu1 : 0 < nuCan a1 B := nuCan_positive a1 B hB
  set d1 : ℝ := B - a1 - (1 / 2 : ℝ) with hd1
  set s1 : ℝ := Real.sqrt (d1 ^ 2 + 2 * B) with hs1
  have hs1sq : s1 ^ 2 = d1 ^ 2 + 2 * B := Real.sq_sqrt (by positivity)
  have hnu1' : nuCan a1 B = d1 + s1 := rfl
  have hdelta : 0 < a2 - a1 := sub_pos.mpr h12
  have hpos : 0 < s1 + (a2 - a1) := by
    have : 0 ≤ s1 := Real.sqrt_nonneg _
    linarith
  have hlt :
      Real.sqrt ((B - a2 - (1 / 2 : ℝ)) ^ 2 + 2 * B) < s1 + (a2 - a1) := by
    rw [Real.sqrt_lt' hpos]
    have hprod : 0 < (a2 - a1) * (d1 + s1) := mul_pos hdelta (hnu1' ▸ hnu1)
    nlinarith [hs1sq, hprod]
  change B - a2 - (1 / 2 : ℝ) + Real.sqrt ((B - a2 - (1 / 2 : ℝ)) ^ 2 + 2 * B)
      < nuCan a1 B
  rw [hnu1']
  linarith

/--
**Monotonicity.** For fixed `ν₀ > 0`, `α₀ ↦ M₀(ν₀, α₀)` is
strictly increasing. (Positivity of `α₀` is not needed.)
-/
theorem M0_strictMono_alpha0
    (nu0 : ℝ) (hnu0 : 0 < nu0) :
    StrictMono (fun a : ℝ => M0 nu0 a) := by
  intro a1 a2 h12
  have hhalf : 0 < nu0 / 2 := by linarith
  have hnu1 : 0 < nuCan a1 (nu0 / 2) := nuCan_positive _ _ hhalf
  have hnu2 : 0 < nuCan a2 (nu0 / 2) := nuCan_positive _ _ hhalf
  have hlt := nuCan_strictAnti_alpha0 (nu0 / 2) hhalf h12
  simp only [M0, invNuCan]
  exact one_div_lt_one_div_of_lt hnu2 hlt

/-- Restricted form on the domain `α₀ > 0`. -/
theorem M0_strictMonoOn_alpha0
    (nu0 : ℝ) (hnu0 : 0 < nu0) :
    StrictMonoOn (fun a : ℝ => M0 nu0 a) (Set.Ioi 0) :=
  (M0_strictMono_alpha0 nu0 hnu0).strictMonoOn _

/-- The closed form is continuous in `α₀`. -/
theorem M0ClosedForm_continuous_alpha0 (nu0 : ℝ) :
    Continuous (fun a : ℝ => M0ClosedForm nu0 a) := by
  unfold M0ClosedForm
  fun_prop

/-- At `α₀ = 0` the ceiling is exactly `1/ν₀`. -/
theorem M0ClosedForm_at_zero
    (nu0 : ℝ) (hnu0 : 0 < nu0) :
    M0ClosedForm nu0 0 = 1 / nu0 := by
  have hsq : (nu0 - 2 * 0 - 1) ^ 2 + 4 * nu0 = (nu0 + 1) ^ 2 := by ring
  unfold M0ClosedForm
  rw [hsq, Real.sqrt_sq (by linarith)]
  field_simp
  ring

/--
**Small-`α₀` limit.**

  lim_{α₀ → 0⁺} M₀(ν₀, α₀) = 1/ν₀.
-/
theorem M0_tendsto_alpha0_zero
    (nu0 : ℝ) (hnu0 : 0 < nu0) :
    Tendsto (fun a : ℝ => M0 nu0 a) (𝓝[>] 0) (𝓝 (1 / nu0)) := by
  have hfun : (fun a : ℝ => M0 nu0 a) = fun a => M0ClosedForm nu0 a := by
    funext a
    exact M0_eq_closedForm nu0 a hnu0
  rw [hfun, ← M0ClosedForm_at_zero nu0 hnu0]
  exact ((M0ClosedForm_continuous_alpha0 nu0).tendsto 0).mono_left nhdsWithin_le_nhds

/-- Leading large-`α₀` term `(2α₀ + 1)/ν₀ − 1`. -/
noncomputable def M0Leading (nu0 alpha0 : ℝ) : ℝ :=
  (2 * alpha0 + 1) / nu0 - 1

/-- Shifted variable `m = 2α₀ + 1 − ν₀`. -/
def M0Shift (nu0 alpha0 : ℝ) : ℝ :=
  2 * alpha0 + 1 - nu0

/-- Exact remainder `2 / (√(m² + 4ν₀) + m)`. -/
noncomputable def M0Remainder (nu0 alpha0 : ℝ) : ℝ :=
  2 / (Real.sqrt (M0Shift nu0 alpha0 ^ 2 + 4 * nu0) + M0Shift nu0 alpha0)

theorem M0Remainder_den_pos
    (nu0 alpha0 : ℝ) (hnu0 : 0 < nu0) :
    0 < Real.sqrt (M0Shift nu0 alpha0 ^ 2 + 4 * nu0) + M0Shift nu0 alpha0 := by
  set m := M0Shift nu0 alpha0
  have hlt : |m| < Real.sqrt (m ^ 2 + 4 * nu0) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg m) (by linarith)
  have := neg_abs_le m
  linarith

/--
**Exact remainder identity**, valid for every real `α₀` (with `ν₀ > 0`):

  M₀ = (2α₀+1)/ν₀ − 1 + 2/(√(m² + 4ν₀) + m).
-/
theorem M0_eq_leading_add_remainder
    (nu0 alpha0 : ℝ) (hnu0 : 0 < nu0) :
    M0 nu0 alpha0 = M0Leading nu0 alpha0 + M0Remainder nu0 alpha0 := by
  have hden := M0Remainder_den_pos nu0 alpha0 hnu0
  rw [M0_eq_closedForm nu0 alpha0 hnu0]
  unfold M0ClosedForm M0Leading M0Remainder
  set m := M0Shift nu0 alpha0 with hm
  have hS : (nu0 - 2 * alpha0 - 1) ^ 2 + 4 * nu0 = m ^ 2 + 4 * nu0 := by
    rw [hm, M0Shift]; ring
  rw [hS]
  set S := Real.sqrt (m ^ 2 + 4 * nu0) with hSdef
  have hSsq : S ^ 2 = m ^ 2 + 4 * nu0 := Real.sq_sqrt (by positivity)
  have hlin : nu0 - 2 * alpha0 - 1 = -m := by rw [hm, M0Shift]; ring
  have h2am : 2 * alpha0 + 1 = m + nu0 := by rw [hm, M0Shift]; ring
  have hnu0' : nu0 ≠ 0 := hnu0.ne'
  have hden' : S + m ≠ 0 := hden.ne'
  rw [hlin, h2am]
  field_simp
  nlinarith [hSsq]

/-- The remainder is strictly positive for every real `α₀`. -/
theorem M0Remainder_pos
    (nu0 alpha0 : ℝ) (hnu0 : 0 < nu0) :
    0 < M0Remainder nu0 alpha0 :=
  div_pos two_pos (M0Remainder_den_pos nu0 alpha0 hnu0)

/-- When `m = 2α₀ + 1 − ν₀ > 0`, the remainder is strictly below `1/m`. -/
theorem M0Remainder_lt_inv_shift
    (nu0 alpha0 : ℝ) (hnu0 : 0 < nu0) (hm : 0 < M0Shift nu0 alpha0) :
    M0Remainder nu0 alpha0 < 1 / M0Shift nu0 alpha0 := by
  set m := M0Shift nu0 alpha0
  have hgt : m < Real.sqrt (m ^ 2 + 4 * nu0) := by
    rw [Real.lt_sqrt hm.le]
    linarith
  unfold M0Remainder
  rw [div_lt_div_iff₀ (by linarith) hm]
  linarith

/--
Explicit two-sided bound: for `2α₀ + 1 > ν₀`,

  0 < M₀ − [(2α₀+1)/ν₀ − 1] < 1/(2α₀ + 1 − ν₀).
-/
theorem M0_sub_leading_bounds
    (nu0 alpha0 : ℝ) (hnu0 : 0 < nu0) (hm : 0 < M0Shift nu0 alpha0) :
    0 < M0 nu0 alpha0 - M0Leading nu0 alpha0
      ∧ M0 nu0 alpha0 - M0Leading nu0 alpha0 < 1 / M0Shift nu0 alpha0 := by
  rw [M0_eq_leading_add_remainder nu0 alpha0 hnu0, add_sub_cancel_left]
  exact ⟨M0Remainder_pos nu0 alpha0 hnu0, M0Remainder_lt_inv_shift nu0 alpha0 hnu0 hm⟩

/--
**Large-`α₀` asymptotic.**

  M₀ = (2α₀+1)/ν₀ − 1 + O(α₀⁻¹)   as α₀ → ∞.

Concretely, `|M₀ − [(2α₀+1)/ν₀ − 1]| ≤ |α₀⁻¹|` for all `α₀ ≥ max ν₀ 1`.
-/
theorem M0_asymptotic_isBigO
    (nu0 : ℝ) (hnu0 : 0 < nu0) :
    (fun a : ℝ => M0 nu0 a - M0Leading nu0 a) =O[atTop] (fun a : ℝ => a⁻¹) := by
  refine Asymptotics.IsBigO.of_bound' ?_
  filter_upwards [eventually_ge_atTop (max nu0 1)] with a ha
  have ha1 : 1 ≤ a := le_trans (le_max_right _ _) ha
  have hanu : nu0 ≤ a := le_trans (le_max_left _ _) ha
  have hapos : 0 < a := by linarith
  have hm : 0 < M0Shift nu0 a := by unfold M0Shift; linarith
  have hma : a ≤ M0Shift nu0 a := by unfold M0Shift; linarith
  obtain ⟨hlo, hhi⟩ := M0_sub_leading_bounds nu0 a hnu0 hm
  rw [Real.norm_of_nonneg hlo.le, Real.norm_of_nonneg (inv_nonneg.mpr hapos.le)]
  calc M0 nu0 a - M0Leading nu0 a ≤ 1 / M0Shift nu0 a := hhi.le
    _ ≤ 1 / a := one_div_le_one_div_of_le hapos hma
    _ = a⁻¹ := one_div a

/--
Sharper first-order form: `α₀ · (M₀ − [(2α₀+1)/ν₀ − 1]) → 1/2` as `α₀ → ∞`,
so the `O(α₀⁻¹)` term is exactly `1/(2α₀) + o(α₀⁻¹)`.
-/
theorem M0_remainder_first_order
    (nu0 : ℝ) (hnu0 : 0 < nu0) :
    Tendsto (fun a : ℝ => a * (M0 nu0 a - M0Leading nu0 a)) atTop (𝓝 (1 / 2)) := by
  -- a · R(a) = 2 / (√(m²+4ν₀)/a + m/a), with √(m²+4ν₀)/a → 2 and m/a → 2.
  have hm_div : Tendsto (fun a : ℝ => M0Shift nu0 a / a) atTop (𝓝 2) := by
    have h : ∀ᶠ a : ℝ in atTop, M0Shift nu0 a / a = 2 + (1 - nu0) * a⁻¹ := by
      filter_upwards [eventually_gt_atTop 0] with a ha
      unfold M0Shift
      field_simp
      ring
    rw [tendsto_congr' h]
    have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (1 - nu0)
    simpa using this.const_add 2
  have hsqrt_div :
      Tendsto (fun a : ℝ => Real.sqrt (M0Shift nu0 a ^ 2 + 4 * nu0) / a) atTop (𝓝 2) := by
    have h : ∀ᶠ a : ℝ in atTop,
        Real.sqrt (M0Shift nu0 a ^ 2 + 4 * nu0) / a
          = Real.sqrt ((M0Shift nu0 a / a) ^ 2 + 4 * nu0 * (a⁻¹) ^ 2) := by
      filter_upwards [eventually_gt_atTop 0] with a ha
      rw [eq_comm, ← Real.sqrt_sq ha.le, ← Real.sqrt_div' _ (sq_nonneg a),
        Real.sqrt_sq ha.le]
      congr 1
      field_simp
    rw [tendsto_congr' h]
    have hinner : Tendsto (fun a : ℝ => (M0Shift nu0 a / a) ^ 2 + 4 * nu0 * (a⁻¹) ^ 2)
        atTop (𝓝 (2 ^ 2 + 4 * nu0 * 0 ^ 2)) :=
      (hm_div.pow 2).add ((tendsto_inv_atTop_zero.pow 2).const_mul _)
    have hval : Real.sqrt (2 ^ 2 + 4 * nu0 * 0 ^ 2) = 2 := by
      rw [show (2 : ℝ) ^ 2 + 4 * nu0 * 0 ^ 2 = 2 ^ 2 by ring]
      exact Real.sqrt_sq (by norm_num)
    rw [← hval]
    exact hinner.sqrt
  have h : ∀ᶠ a : ℝ in atTop,
      a * (M0 nu0 a - M0Leading nu0 a)
        = 2 / (Real.sqrt (M0Shift nu0 a ^ 2 + 4 * nu0) / a + M0Shift nu0 a / a) := by
    filter_upwards [eventually_gt_atTop 0] with a ha
    rw [M0_eq_leading_add_remainder nu0 a hnu0, add_sub_cancel_left, M0Remainder]
    have hden := M0Remainder_den_pos nu0 a hnu0
    rw [← add_div, div_div_eq_mul_div]
    field_simp
  rw [tendsto_congr' h]
  have hlim := (hsqrt_div.add hm_div)
  have h4 : (2 : ℝ) + 2 ≠ 0 := by norm_num
  convert (tendsto_const_nhds (x := (2 : ℝ))).div hlim h4 using 2
  norm_num

end ELVAE
