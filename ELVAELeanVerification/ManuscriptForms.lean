import Mathlib
import ELVAELeanVerification.WeightInvariance
import ELVAELeanVerification.OrdinalPrior

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Closed-form formulas in expanded form

This module states several closed-form formulas in an expanded arrangement and
proves that they coincide with the forms used elsewhere in the formalization.

* `manuscriptNIGKL`: the NIG KL divergence in an expanded
  arrangement; `manuscriptNIGKL_eq_closedForm` shows it equals `nigKLClosedForm`
  (for `β, β₀ > 0`), and `klDiv_eq_manuscriptNIGKL` that it is mathlib's `klDiv` on
  `(μ, σ²)`.
* `Rcan_eq_manuscript_closed_form`: the closed form of `R_can`.
* `integral_log_invGammaMeasure`, `integral_inv_invGammaMeasure`:
  `E[log x] = log β − ψ(α)` and `E[x⁻¹] = α/β` under `InvGamma(α, β)`.
* `offSection_diagnostics`: `δ_ν = log(ν/ν_can)` and
  `Δ_fib = KL[q_ν‖p₀] − KL[q_can‖p₀] ≥ 0`, both vanishing exactly on the section.
* `M0_tendsto_atTop_alpha0`: the ceiling is not uniformly bounded in
  `α₀`.
-/

namespace ELVAE

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Set
open scoped ENNReal

/-! ## The NIG KL in expanded arrangement -/

/-- The NIG KL divergence in expanded closed form. -/
noncomputable def manuscriptNIGKL (gamma nu alpha beta gamma0 nu0 alpha0 beta0 : ℝ) : ℝ :=
  alpha0 * Real.log (beta / beta0)
    - Real.log (Real.Gamma alpha) + Real.log (Real.Gamma alpha0)
    + (alpha - alpha0) * realDigamma alpha - alpha
    + alpha * beta0 / beta
    + (1 / 2) * (Real.log (nu / nu0) + nu0 / nu - 1
      + nu0 * alpha * (gamma - gamma0) ^ 2 / beta)

/-- The expanded form equals the closed form used in the formalization (for `β, β₀ > 0`). -/
theorem manuscriptNIGKL_eq_closedForm (gamma nu alpha beta gamma0 nu0 alpha0 beta0 : ℝ)
    (hbeta : 0 < beta) (hbeta0 : 0 < beta0) :
    manuscriptNIGKL gamma nu alpha beta gamma0 nu0 alpha0 beta0
      = nigKLClosedForm gamma nu alpha beta gamma0 nu0 alpha0 beta0 := by
  unfold manuscriptNIGKL nigKLClosedForm
  rw [Real.log_div hbeta.ne' hbeta0.ne']
  field_simp
  ring

/-- **Probability level.** `D_KL(q ‖ p₀)` on `(μ, σ²)` equals the expanded
formula. -/
theorem klDiv_eq_manuscriptNIGKL {gamma nu alpha beta gamma0 nu0 alpha0 beta0 : ℝ}
    (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0) :
    klDiv (nigMeasureMuSigma gamma nu alpha beta) (nigMeasureMuSigma gamma0 nu0 alpha0 beta0)
      = ENNReal.ofReal (manuscriptNIGKL gamma nu alpha beta gamma0 nu0 alpha0 beta0) := by
  rw [manuscriptNIGKL_eq_closedForm _ _ _ _ _ _ _ _ hbeta hbeta0]
  exact klDiv_nigMeasureMuSigma hnu halpha hbeta hnu0 halpha0 hbeta0

/-- `R_can(γ, α, c)` is the expanded NIG KL evaluated at `(ν_can, β_can)`. -/
theorem Rcan_eq_manuscript_closed_form {gamma0 nu0 alpha0 beta0 : ℝ}
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0)
    {θ : QuotientState} (hθ : θ ∈ admissibleQuotients) :
    Rcan gamma0 nu0 alpha0 beta0 θ
      = manuscriptNIGKL θ.gamma (θ.nuCan gamma0 nu0 alpha0 beta0) θ.alpha
          (betaCanFromParams θ.gamma θ.alpha θ.c gamma0 nu0 alpha0 beta0)
          gamma0 nu0 alpha0 beta0 := by
  have hnu := QuotientState.nuCan_mem gamma0 nu0 alpha0 beta0 hnu0 hbeta0 θ hθ
  have hbeta := betaCanFromParams_positive θ.gamma θ.alpha θ.c gamma0 nu0 alpha0 beta0
    hθ.1 hθ.2 hnu0 hbeta0
  rw [manuscriptNIGKL_eq_closedForm _ _ _ _ _ _ _ _ hbeta hbeta0, Rcan,
    fiberKL_eq_restrictedNIGKL hnu0 halpha0 hbeta0 hθ hnu]
  rfl

/-! ## Moments of the inverse-gamma law -/

/-- `∫ f dGamma(a, b) = ∫_{(0,∞)} f · gammaPDFReal`. -/
lemma integral_gammaMeasure_eq_setIntegral (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (f : ℝ → ℝ) :
    ∫ t, f t ∂(gammaMeasure a b) = ∫ t in Ioi 0, gammaPDFReal a b t * f t := by
  have hG : Measurable (gammaPDF a b) := (measurable_gammaPDFReal a b).ennreal_ofReal
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul hG
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hb _), smul_eq_mul]
  rw [← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae ?_
  filter_upwards [ae_ne_zero_real] with t ht
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · have h0 : gammaPDFReal a b t = 0 := by simp [gammaPDFReal, not_le.mpr hneg]
    simp [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from not_lt.mpr hneg.le), h0]
  · simp [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from hpos)]

/-- **First part.** `E[log x] = log β − ψ(α)` under `InvGamma(α, β)`. -/
theorem integral_log_invGammaMeasure (alpha beta : ℝ) (halpha : 0 < alpha) (hbeta : 0 < beta) :
    ∫ x, Real.log x ∂(invGammaMeasure alpha beta) = Real.log beta - realDigamma alpha := by
  rw [invGammaMeasure, integral_map measurable_inv.aemeasurable
      Real.measurable_log.aestronglyMeasurable,
    integral_gammaMeasure_eq_setIntegral _ _ halpha hbeta]
  simp_rw [Real.log_inv, mul_neg]
  rw [integral_neg]
  have h := integral_log_mul_gammaPDFReal halpha hbeta
  simp_rw [mul_comm (gammaPDFReal alpha beta _) (Real.log _)]
  rw [h]
  ring

/-- **Second part.** `E[x⁻¹] = α/β` under `InvGamma(α, β)`. -/
theorem integral_inv_invGammaMeasure (alpha beta : ℝ) (halpha : 0 < alpha) (hbeta : 0 < beta) :
    ∫ x, x⁻¹ ∂(invGammaMeasure alpha beta) = alpha / beta := by
  rw [invGammaMeasure, integral_map measurable_inv.aemeasurable
      measurable_inv.aestronglyMeasurable,
    integral_gammaMeasure_eq_setIntegral _ _ halpha hbeta]
  simp_rw [inv_inv, mul_comm (gammaPDFReal alpha beta _)]
  exact integral_mul_gammaPDFReal halpha hbeta

/-! ## Off-section diagnostics -/

/--
For an admissible quotient state and any fiber representative
`ν > 0`, with `δ_ν = log(ν/ν_can)` and
`Δ_fib = KL[q_ν ‖ p₀] − KL[q_can ‖ p₀]`:
`Δ_fib ≥ 0`, and each of `δ_ν = 0` and `Δ_fib = 0` holds exactly when `ν = ν_can`.
-/
theorem offSection_diagnostics {gamma0 nu0 alpha0 beta0 : ℝ}
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0)
    {θ : QuotientState} (hθ : θ ∈ admissibleQuotients) {nu : ℝ} (hnu : 0 < nu) :
    let νc := θ.nuCan gamma0 nu0 alpha0 beta0
    let Δ := fiberKL gamma0 nu0 alpha0 beta0 θ nu - fiberKL gamma0 nu0 alpha0 beta0 θ νc
    0 ≤ Δ ∧ (Δ = 0 ↔ nu = νc) ∧ (Real.log (nu / νc) = 0 ↔ nu = νc) := by
  intro νc Δ
  have hc : 0 < νc := QuotientState.nuCan_mem gamma0 nu0 alpha0 beta0 hnu0 hbeta0 θ hθ
  have hmin := klDiv_nig_fiber_min (gamma0 := gamma0) hnu0 halpha0 hbeta0 θ hθ nu hnu
  refine ⟨sub_nonneg.mpr hmin, ⟨fun h => ?_, fun h => by simp [Δ, h]⟩, ?_⟩
  · by_contra hne
    have := klDiv_nig_fiber_strict_min (gamma0 := gamma0) hnu0 halpha0 hbeta0 hθ hnu hne
    simp only [Δ] at h
    linarith
  · rw [Real.log_eq_zero, div_eq_one_iff_eq hc.ne']
    constructor
    · rintro (h | h | h)
      · exact absurd h (div_pos hnu hc).ne'
      · exact h
      · linarith [div_pos hnu hc]
    · intro h; right; left; exact h

/-! ## The ceiling is not uniformly bounded in `α₀` -/

/-- For fixed `ν₀ > 0`, `M₀(ν₀, α₀) → ∞` as `α₀ → ∞`; the ceiling is
finite for each prior but has no bound uniform in `α₀`. -/
theorem M0_tendsto_atTop_alpha0 (nu0 : ℝ) (hnu0 : 0 < nu0) :
    Tendsto (fun a => M0 nu0 a) atTop atTop := by
  have hlead : Tendsto (fun a => M0Leading nu0 a) atTop atTop := by
    unfold M0Leading
    have : Tendsto (fun a : ℝ => (2 * a + 1) / nu0) atTop atTop :=
      ((tendsto_id.const_mul_atTop two_pos).atTop_add tendsto_const_nhds).atTop_div_const hnu0
    exact this.atTop_add tendsto_const_nhds
  refine tendsto_atTop_mono (fun a => ?_) hlead
  rw [M0_eq_leading_add_remainder nu0 a hnu0]
  linarith [M0Remainder_pos nu0 a hnu0]

end ELVAE
