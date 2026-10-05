import Mathlib
import ELVAELeanVerification.GammaMoments
import ELVAELeanVerification.KLDensity

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# The NIG KL divergence from the measures (Level B)

The Normal–Inverse-Gamma law `NIG(γ, ν, α, β)` is the
joint law of `(μ, σ²)` with `σ² ~ InvGamma(α, β)` and `μ | σ² ~ N(γ, σ²/ν)`.
With precision `τ = 1/σ²`, the pair `(τ, μ)` has Lebesgue density

  q(τ, μ) = Gamma(τ; α, β) · N(μ; γ, 1/(ντ)).

Here `nigPrecMeasure` is the measure with density `q` on `ℝ × ℝ`, `nigMeasure` is
its image under `(τ, μ) ↦ (1/τ, μ)` (the law of `(σ², μ)`), and
`nigMeasureMuSigma` is the law of `(μ, σ²)` in the order `(μ, σ²)`.
KL divergence is the same for both orderings (`klDiv_nigMeasureMuSigma`).

Main theorem (`klDiv_nigMeasure`): for `ν, α, β, ν₀, α₀, β₀ > 0`,

  klDiv (NIG(γ,ν,α,β)) (NIG(γ₀,ν₀,α₀,β₀)) = nigKLClosedForm γ ν α β γ₀ ν₀ α₀ β₀,

which is the forward divergence `D_KL(q ‖ p₀)`,

where `klDiv` is mathlib's Kullback–Leibler divergence and `nigKLClosedForm` is the
closed-form expression of `RestrictedKLDivergence`. So the expression used in the
Level-A analysis and in exact partial minimization is the KL divergence of the two NIG laws.
-/

namespace ELVAE

open MeasureTheory ProbabilityTheory Real Set InformationTheory
open scoped ENNReal NNReal

/-- Conditional variance `1/(ντ)` of `z` given the precision `τ`. -/
noncomputable def precVar (nu t : ℝ) : ℝ≥0 := (1 / (nu * t)).toNNReal

lemma precVar_coe {nu t : ℝ} (hnu : 0 < nu) (ht : 0 < t) :
    (precVar nu t : ℝ) = 1 / (nu * t) :=
  Real.coe_toNNReal _ (by positivity)

lemma precVar_ne_zero {nu t : ℝ} (hnu : 0 < nu) (ht : 0 < t) : precVar nu t ≠ 0 := by
  rw [precVar, Ne, Real.toNNReal_eq_zero, not_le]; positivity

lemma precVar_eq_zero_of_nonpos {nu t : ℝ} (hnu : 0 < nu) (ht : t ≤ 0) : precVar nu t = 0 := by
  rw [precVar, Real.toNNReal_eq_zero]
  rcases ht.lt_or_eq with h | h
  · exact (div_neg_of_pos_of_neg one_pos (mul_neg_of_pos_of_neg hnu h)).le
  · simp [h]

/-- Precision-form NIG density `q(τ, z) = Gamma(τ; α, β) · N(z; γ, 1/(ντ))`. -/
noncomputable def nigPrecPDF (gamma nu alpha beta : ℝ) (p : ℝ × ℝ) : ℝ :=
  gammaPDFReal alpha beta p.1 * gaussianPDFReal gamma (precVar nu p.1) p.2

/-- Precision-form NIG law of `(τ, z)`. -/
noncomputable def nigPrecMeasure (gamma nu alpha beta : ℝ) : Measure (ℝ × ℝ) :=
  volume.withDensity fun p => ENNReal.ofReal (nigPrecPDF gamma nu alpha beta p)

/-- NIG law of `(σ², μ)`: the image of the precision form under `(τ, μ) ↦ (1/τ, μ)`. -/
noncomputable def nigMeasure (gamma nu alpha beta : ℝ) : Measure (ℝ × ℝ) :=
  (nigPrecMeasure gamma nu alpha beta).map fun p => (p.1⁻¹, p.2)

lemma nigPrecPDF_nonneg {gamma nu alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (p : ℝ × ℝ) : 0 ≤ nigPrecPDF gamma nu alpha beta p :=
  mul_nonneg (gammaPDFReal_nonneg halpha hbeta _) (gaussianPDFReal_nonneg _ _ _)

lemma measurable_precVar (nu : ℝ) : Measurable fun t : ℝ => precVar nu t := by
  unfold precVar; fun_prop

lemma measurable_nigPrecPDF (gamma nu alpha beta : ℝ) :
    Measurable (nigPrecPDF gamma nu alpha beta) := by
  have h2 : Measurable fun p : ℝ × ℝ => gaussianPDFReal gamma (precVar nu p.1) p.2 :=
    measurable_uncurry_gaussianPDFReal.comp
      (measurable_const.prodMk (((measurable_precVar nu).comp measurable_fst).prodMk
        measurable_snd))
  exact ((measurable_gammaPDFReal alpha beta).comp measurable_fst).mul h2

/-- For `τ ≤ 0` the density vanishes. -/
lemma nigPrecPDF_of_nonpos {gamma nu alpha beta : ℝ} (hnu : 0 < nu) {p : ℝ × ℝ}
    (hp : p.1 ≤ 0) : nigPrecPDF gamma nu alpha beta p = 0 := by
  unfold nigPrecPDF
  rcases hp.lt_or_eq with h | h
  · simp [gammaPDFReal, not_le.mpr h]
  · rw [precVar_eq_zero_of_nonpos hnu h.le, gaussianPDFReal_zero_var]
    simp

lemma ae_ne_zero_real : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
  have : (volume : Measure ℝ) {0} = 0 := measure_singleton 0
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp this] with t ht
  simpa using ht

/-- The precision-form NIG density integrates to one. -/
lemma lintegral_nigPrecPDF {gamma nu alpha beta : ℝ} (hnu : 0 < nu) (halpha : 0 < alpha)
    (hbeta : 0 < beta) :
    ∫⁻ p, ENNReal.ofReal (nigPrecPDF gamma nu alpha beta p) = 1 := by
  rw [Measure.volume_eq_prod, lintegral_prod _
    (measurable_nigPrecPDF gamma nu alpha beta).ennreal_ofReal.aemeasurable]
  have hinner : ∀ᵐ t ∂(volume : Measure ℝ),
      ∫⁻ z, ENNReal.ofReal (nigPrecPDF gamma nu alpha beta (t, z)) = gammaPDF alpha beta t := by
    filter_upwards [ae_ne_zero_real] with t ht
    rcases lt_or_gt_of_ne ht with hneg | hpos
    · have h0 : ∀ z, nigPrecPDF gamma nu alpha beta (t, z) = 0 := fun z =>
        nigPrecPDF_of_nonpos hnu (p := (t, z)) hneg.le
      simp [h0, gammaPDF_of_neg hneg]
    · simp only [nigPrecPDF]
      simp_rw [ENNReal.ofReal_mul (gammaPDFReal_nonneg halpha hbeta t)]
      rw [lintegral_const_mul _ (measurable_gaussianPDFReal _ _).ennreal_ofReal]
      have := lintegral_gaussianPDF_eq_one gamma (precVar_ne_zero hnu hpos)
      simp only [gaussianPDF] at this
      rw [this, mul_one, gammaPDF]
  rw [lintegral_congr_ae hinner, lintegral_gammaPDF_eq_one halpha hbeta]

lemma isProbabilityMeasure_nigPrecMeasure {gamma nu alpha beta : ℝ} (hnu : 0 < nu)
    (halpha : 0 < alpha) (hbeta : 0 < beta) :
    IsProbabilityMeasure (nigPrecMeasure gamma nu alpha beta) := by
  constructor
  rw [nigPrecMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact lintegral_nigPrecPDF hnu halpha hbeta

/-- Positivity of the density forces `τ > 0`. -/
lemma pos_of_nigPrecPDF_pos {gamma nu alpha beta : ℝ} (hnu : 0 < nu) {p : ℝ × ℝ}
    (hp : 0 < nigPrecPDF gamma nu alpha beta p) : 0 < p.1 := by
  by_contra h
  rw [nigPrecPDF_of_nonpos hnu (not_lt.mp h)] at hp
  exact lt_irrefl 0 hp

lemma nigPrecPDF_pos {gamma nu alpha beta : ℝ} (hnu : 0 < nu) (halpha : 0 < alpha)
    (hbeta : 0 < beta) {p : ℝ × ℝ} (hp : 0 < p.1) :
    0 < nigPrecPDF gamma nu alpha beta p :=
  mul_pos (gammaPDFReal_pos halpha hbeta hp) (gaussianPDFReal_pos _ _ _ (precVar_ne_zero hnu hp))

/-! ## Log-densities -/

lemma log_gammaPDFReal {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    Real.log (gammaPDFReal a b t)
      = a * Real.log b - Real.log (Real.Gamma a) + (a - 1) * Real.log t - b * t := by
  have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  rw [gammaPDFReal_of_pos ht, Real.log_mul (by positivity) (by positivity),
    Real.log_div (by positivity) hG.ne', Real.log_mul (by positivity) (Real.exp_pos _).ne',
    Real.log_rpow hb, Real.log_rpow ht, Real.log_exp]
  ring

lemma log_gaussianPDFReal {m v z : ℝ} (hv : 0 < v) :
    Real.log (gaussianPDFReal m v.toNNReal z)
      = -(1 / 2) * Real.log (2 * π * v) - (z - m) ^ 2 / (2 * v) := by
  rw [gaussianPDFReal, Real.coe_toNNReal _ hv.le,
    Real.log_mul (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))).ne' (Real.exp_pos _).ne',
    Real.log_inv, Real.log_sqrt (by positivity), Real.log_exp]
  ring

/-! ## The log-likelihood ratio -/

/-- Gamma part of `log(q/q₀)`. -/
noncomputable def nigLogRatioGamma (alpha beta alpha0 beta0 t : ℝ) : ℝ :=
  (alpha * Real.log beta - Real.log (Real.Gamma alpha))
    - (alpha0 * Real.log beta0 - Real.log (Real.Gamma alpha0))
    + (alpha - alpha0) * Real.log t - (beta - beta0) * t

/-- Gaussian part of `log(q/q₀)`. -/
noncomputable def nigLogRatioGauss (gamma nu gamma0 nu0 t z : ℝ) : ℝ :=
  (1 / 2) * (Real.log nu - Real.log nu0)
    - nu * t * (z - gamma) ^ 2 / 2 + nu0 * t * (z - gamma0) ^ 2 / 2

lemma log_two_pi_precVar {nu t : ℝ} (hnu : 0 < nu) (ht : 0 < t) :
    Real.log (2 * π * (1 / (nu * t))) = Real.log (2 * π) - Real.log nu - Real.log t := by
  rw [Real.log_mul (by positivity) (by positivity), one_div, Real.log_inv,
    Real.log_mul hnu.ne' ht.ne']
  ring

/-- For `τ > 0`, `log(q/q₀) = L_Γ(τ) + L_N(τ, z)`. -/
lemma log_nigPrecPDF_ratio {gamma nu alpha beta gamma0 nu0 alpha0 beta0 : ℝ}
    (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0)
    {p : ℝ × ℝ} (hp : 0 < p.1) :
    Real.log (nigPrecPDF gamma nu alpha beta p / nigPrecPDF gamma0 nu0 alpha0 beta0 p)
      = nigLogRatioGamma alpha beta alpha0 beta0 p.1
        + nigLogRatioGauss gamma nu gamma0 nu0 p.1 p.2 := by
  have hq := nigPrecPDF_pos (gamma := gamma) hnu halpha hbeta hp
  have hq0 := nigPrecPDF_pos (gamma := gamma0) hnu0 halpha0 hbeta0 hp
  rw [Real.log_div hq.ne' hq0.ne']
  unfold nigPrecPDF precVar
  have hg := gammaPDFReal_pos halpha hbeta hp
  have hg0 := gammaPDFReal_pos halpha0 hbeta0 hp
  have hv : 0 < 1 / (nu * p.1) := by positivity
  have hv0 : 0 < 1 / (nu0 * p.1) := by positivity
  rw [Real.log_mul hg.ne' (gaussianPDFReal_pos _ _ _ (by simpa using hv)).ne',
    Real.log_mul hg0.ne' (gaussianPDFReal_pos _ _ _ (by simpa using hv0)).ne',
    log_gammaPDFReal halpha hbeta hp, log_gammaPDFReal halpha0 hbeta0 hp,
    log_gaussianPDFReal hv, log_gaussianPDFReal hv0,
    log_two_pi_precVar hnu hp, log_two_pi_precVar hnu0 hp]
  unfold nigLogRatioGamma nigLogRatioGauss
  field_simp
  ring

/-- The KL integrand `q log(q/q₀)` equals `q · (L_Γ + L_N)` everywhere. -/
lemma nigPrecPDF_mul_log_ratio {gamma nu alpha beta gamma0 nu0 alpha0 beta0 : ℝ}
    (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0) (p : ℝ × ℝ) :
    nigPrecPDF gamma nu alpha beta p
        * Real.log (nigPrecPDF gamma nu alpha beta p / nigPrecPDF gamma0 nu0 alpha0 beta0 p)
      = nigPrecPDF gamma nu alpha beta p
        * (nigLogRatioGamma alpha beta alpha0 beta0 p.1
          + nigLogRatioGauss gamma nu gamma0 nu0 p.1 p.2) := by
  by_cases hp : 0 < p.1
  · rw [log_nigPrecPDF_ratio hnu halpha hbeta hnu0 halpha0 hbeta0 hp]
  · rw [nigPrecPDF_of_nonpos hnu (not_lt.mp hp), zero_mul, zero_mul]

/-! ## Inner (`z`) integrals for fixed `τ > 0` -/

section Inner

variable {gamma nu alpha beta gamma0 nu0 : ℝ}

/-- Generic inner integral: `∫ N(z)(A + B(z−γ)² + C(z−γ₀)²) dz`. -/
lemma integral_gauss_quadratic (hnu : 0 < nu) {t : ℝ} (ht : 0 < t) (A B C : ℝ) :
    ∫ z, gaussianPDFReal gamma (precVar nu t) z
        * (A + B * (z - gamma) ^ 2 + C * (z - gamma0) ^ 2)
      = A + B * (1 / (nu * t)) + C * (1 / (nu * t) + (gamma - gamma0) ^ 2) := by
  have hv : 0 < 1 / (nu * t) := by positivity
  have hN : Integrable (gaussianPDFReal gamma (precVar nu t)) :=
    integrable_gaussianPDFReal _ _
  have h1 := integrable_gaussianPDFReal_mul_sq_sub gamma gamma hv
  have h2 := integrable_gaussianPDFReal_mul_sq_sub gamma gamma0 hv
  have hsplit : (fun z => gaussianPDFReal gamma (precVar nu t) z
        * (A + B * (z - gamma) ^ 2 + C * (z - gamma0) ^ 2))
      = fun z => (A * gaussianPDFReal gamma (precVar nu t) z
          + B * (gaussianPDFReal gamma (1 / (nu * t)).toNNReal z * (z - gamma) ^ 2))
          + C * (gaussianPDFReal gamma (1 / (nu * t)).toNNReal z * (z - gamma0) ^ 2) := by
    funext z; unfold precVar; ring
  have hAB : Integrable fun z => A * gaussianPDFReal gamma (precVar nu t) z
      + B * (gaussianPDFReal gamma (1 / (nu * t)).toNNReal z * (z - gamma) ^ 2) :=
    (hN.const_mul A).add (h1.const_mul B)
  rw [hsplit, integral_add hAB (h2.const_mul C),
    integral_add (hN.const_mul A) (h1.const_mul B), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_gaussianPDFReal_eq_one _ (precVar_ne_zero hnu ht),
    integral_gaussianPDFReal_mul_sq_sub _ _ hv, integral_gaussianPDFReal_mul_sq_sub _ _ hv]
  ring

lemma integrable_gauss_quadratic (hnu : 0 < nu) {t : ℝ} (ht : 0 < t) (A B C : ℝ) :
    Integrable fun z => gaussianPDFReal gamma (precVar nu t) z
        * (A + B * (z - gamma) ^ 2 + C * (z - gamma0) ^ 2) := by
  have hv : 0 < 1 / (nu * t) := by positivity
  have hN : Integrable (gaussianPDFReal gamma (precVar nu t)) :=
    integrable_gaussianPDFReal _ _
  have h1 := integrable_gaussianPDFReal_mul_sq_sub gamma gamma hv
  have h2 := integrable_gaussianPDFReal_mul_sq_sub gamma gamma0 hv
  have h := ((hN.const_mul A).add (h1.const_mul B)).add (h2.const_mul C)
  refine h.congr (ae_of_all _ fun z => ?_)
  simp only [Pi.add_apply, precVar]
  ring

end Inner

/-! ## Integrability and value of the KL integrand -/

section Integrand

variable {gamma nu alpha beta gamma0 nu0 alpha0 beta0 : ℝ}

/-- The KL integrand `q · (L_Γ + L_N)`. -/
noncomputable def nigKLIntegrand (gamma nu alpha beta gamma0 nu0 alpha0 beta0 : ℝ)
    (p : ℝ × ℝ) : ℝ :=
  nigPrecPDF gamma nu alpha beta p
    * (nigLogRatioGamma alpha beta alpha0 beta0 p.1
      + nigLogRatioGauss gamma nu gamma0 nu0 p.1 p.2)

/-- Dominating function for the KL integrand. -/
noncomputable def nigKLBound (gamma nu alpha beta gamma0 nu0 alpha0 beta0 : ℝ)
    (p : ℝ × ℝ) : ℝ :=
  nigPrecPDF gamma nu alpha beta p
    * (|nigLogRatioGamma alpha beta alpha0 beta0 p.1| + |(1 / 2) * (Real.log nu - Real.log nu0)|
      + (nu * p.1 / 2) * (p.2 - gamma) ^ 2 + (nu0 * p.1 / 2) * (p.2 - gamma0) ^ 2)

lemma measurable_nigLogRatioGamma : Measurable (nigLogRatioGamma alpha beta alpha0 beta0) := by
  unfold nigLogRatioGamma; fun_prop

lemma measurable_nigKLIntegrand :
    Measurable (nigKLIntegrand gamma nu alpha beta gamma0 nu0 alpha0 beta0) := by
  unfold nigKLIntegrand nigLogRatioGauss
  exact (measurable_nigPrecPDF _ _ _ _).mul
    ((measurable_nigLogRatioGamma.comp measurable_fst).add (by fun_prop))

lemma measurable_nigKLBound :
    Measurable (nigKLBound gamma nu alpha beta gamma0 nu0 alpha0 beta0) := by
  unfold nigKLBound
  exact (measurable_nigPrecPDF _ _ _ _).mul
    ((((measurable_nigLogRatioGamma.comp measurable_fst).abs).add measurable_const).add
      (by fun_prop) |>.add (by fun_prop))

/-- Section of the density at `τ > 0` times a quadratic in `z`. -/
lemma nigPrecPDF_section (t z A B C : ℝ) :
    nigPrecPDF gamma nu alpha beta (t, z) * (A + B * (z - gamma) ^ 2 + C * (z - gamma0) ^ 2)
      = gammaPDFReal alpha beta t
        * (gaussianPDFReal gamma (precVar nu t) z
          * (A + B * (z - gamma) ^ 2 + C * (z - gamma0) ^ 2)) := by
  unfold nigPrecPDF; ring

lemma nigKLIntegrand_section (t z : ℝ) :
    nigKLIntegrand gamma nu alpha beta gamma0 nu0 alpha0 beta0 (t, z)
      = gammaPDFReal alpha beta t
        * (gaussianPDFReal gamma (precVar nu t) z
          * ((nigLogRatioGamma alpha beta alpha0 beta0 t + (1 / 2) * (Real.log nu - Real.log nu0))
            + (-(nu * t / 2)) * (z - gamma) ^ 2 + (nu0 * t / 2) * (z - gamma0) ^ 2)) := by
  rw [← nigPrecPDF_section]
  unfold nigKLIntegrand nigLogRatioGauss
  ring

lemma nigKLBound_section (t z : ℝ) :
    nigKLBound gamma nu alpha beta gamma0 nu0 alpha0 beta0 (t, z)
      = gammaPDFReal alpha beta t
        * (gaussianPDFReal gamma (precVar nu t) z
          * ((|nigLogRatioGamma alpha beta alpha0 beta0 t|
              + |(1 / 2) * (Real.log nu - Real.log nu0)|)
            + (nu * t / 2) * (z - gamma) ^ 2 + (nu0 * t / 2) * (z - gamma0) ^ 2)) := by
  rw [← nigPrecPDF_section]
  unfold nigKLBound
  ring

lemma nigKLBound_nonneg (hnu : 0 < nu) (hnu0 : 0 < nu0) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (p : ℝ × ℝ) : 0 ≤ nigKLBound gamma nu alpha beta gamma0 nu0 alpha0 beta0 p := by
  by_cases hp : 0 < p.1
  · unfold nigKLBound
    exact mul_nonneg (nigPrecPDF_nonneg halpha hbeta p) (by positivity)
  · unfold nigKLBound
    rw [nigPrecPDF_of_nonpos hnu (not_lt.mp hp), zero_mul]

lemma norm_nigKLIntegrand_le (hnu : 0 < nu) (hnu0 : 0 < nu0) (halpha : 0 < alpha)
    (hbeta : 0 < beta) (p : ℝ × ℝ) :
    ‖nigKLIntegrand gamma nu alpha beta gamma0 nu0 alpha0 beta0 p‖
      ≤ nigKLBound gamma nu alpha beta gamma0 nu0 alpha0 beta0 p := by
  by_cases hp : 0 < p.1
  · unfold nigKLIntegrand nigKLBound nigLogRatioGauss
    rw [norm_mul, Real.norm_of_nonneg (nigPrecPDF_nonneg halpha hbeta p), Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (nigPrecPDF_nonneg halpha hbeta p)
    have h1 : 0 ≤ nu * p.1 * (p.2 - gamma) ^ 2 / 2 := by positivity
    have h2 : 0 ≤ nu0 * p.1 * (p.2 - gamma0) ^ 2 / 2 := by positivity
    calc |nigLogRatioGamma alpha beta alpha0 beta0 p.1
          + ((1 / 2) * (Real.log nu - Real.log nu0) - nu * p.1 * (p.2 - gamma) ^ 2 / 2
            + nu0 * p.1 * (p.2 - gamma0) ^ 2 / 2)|
        ≤ |nigLogRatioGamma alpha beta alpha0 beta0 p.1|
          + (|(1 / 2) * (Real.log nu - Real.log nu0)| + |nu * p.1 * (p.2 - gamma) ^ 2 / 2|
            + |nu0 * p.1 * (p.2 - gamma0) ^ 2 / 2|) := by
          refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
          exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ = _ := by
          rw [abs_of_nonneg h1, abs_of_nonneg h2]
          ring
  · unfold nigKLIntegrand nigKLBound
    rw [nigPrecPDF_of_nonpos hnu (not_lt.mp hp), zero_mul, zero_mul, norm_zero]

/-- `τ ↦ E_N[L]` for the dominating function. -/
noncomputable def nigKLBoundMarginal (gamma nu alpha beta gamma0 nu0 alpha0 beta0 : ℝ)
    (t : ℝ) : ℝ :=
  gammaPDFReal alpha beta t
    * ((|nigLogRatioGamma alpha beta alpha0 beta0 t| + |(1 / 2) * (Real.log nu - Real.log nu0)|)
      + (nu * t / 2) * (1 / (nu * t)) + (nu0 * t / 2) * (1 / (nu * t) + (gamma - gamma0) ^ 2))

/-- `τ ↦ E_N[L]` for the KL integrand. -/
noncomputable def nigKLMarginal (gamma nu alpha beta gamma0 nu0 alpha0 beta0 : ℝ)
    (t : ℝ) : ℝ :=
  gammaPDFReal alpha beta t
    * ((nigLogRatioGamma alpha beta alpha0 beta0 t + (1 / 2) * (Real.log nu - Real.log nu0))
      + (-(nu * t / 2)) * (1 / (nu * t)) + (nu0 * t / 2) * (1 / (nu * t) + (gamma - gamma0) ^ 2))

lemma integral_nigKLBound_section (hnu : 0 < nu) (t : ℝ) :
    ∫ z, nigKLBound gamma nu alpha beta gamma0 nu0 alpha0 beta0 (t, z)
      = (Ioi (0 : ℝ)).indicator
          (nigKLBoundMarginal gamma nu alpha beta gamma0 nu0 alpha0 beta0) t := by
  by_cases ht : 0 < t
  · rw [indicator_of_mem (show t ∈ Ioi 0 from ht)]
    simp_rw [nigKLBound_section]
    rw [integral_const_mul, integral_gauss_quadratic hnu ht]
    rfl
  · rw [indicator_of_notMem (show t ∉ Ioi 0 from ht)]
    have h0 : ∀ z, nigKLBound gamma nu alpha beta gamma0 nu0 alpha0 beta0 (t, z) = 0 := by
      intro z; unfold nigKLBound
      rw [nigPrecPDF_of_nonpos hnu (p := (t, z)) (not_lt.mp ht), zero_mul]
    simp [h0]

lemma integral_nigKLIntegrand_section (hnu : 0 < nu) (t : ℝ) :
    ∫ z, nigKLIntegrand gamma nu alpha beta gamma0 nu0 alpha0 beta0 (t, z)
      = (Ioi (0 : ℝ)).indicator
          (nigKLMarginal gamma nu alpha beta gamma0 nu0 alpha0 beta0) t := by
  by_cases ht : 0 < t
  · rw [indicator_of_mem (show t ∈ Ioi 0 from ht)]
    simp_rw [nigKLIntegrand_section]
    rw [integral_const_mul, integral_gauss_quadratic hnu ht]
    rfl
  · rw [indicator_of_notMem (show t ∉ Ioi 0 from ht)]
    have h0 : ∀ z, nigKLIntegrand gamma nu alpha beta gamma0 nu0 alpha0 beta0 (t, z) = 0 := by
      intro z; unfold nigKLIntegrand
      rw [nigPrecPDF_of_nonpos hnu (p := (t, z)) (not_lt.mp ht), zero_mul]
    simp [h0]

/-- `τ ↦ Gamma(τ) · L_Γ(τ)` is integrable on `(0, ∞)`. -/
lemma integrableOn_gamma_mul_logRatioGamma (halpha : 0 < alpha) (hbeta : 0 < beta) :
    IntegrableOn (fun t => gammaPDFReal alpha beta t * nigLogRatioGamma alpha beta alpha0 beta0 t)
      (Ioi 0) := by
  set k0 := (alpha * Real.log beta - Real.log (Real.Gamma alpha))
    - (alpha0 * Real.log beta0 - Real.log (Real.Gamma alpha0))
  have h : IntegrableOn (fun t => k0 * gammaPDFReal alpha beta t
      + (alpha - alpha0) * (Real.log t * gammaPDFReal alpha beta t)
      - (beta - beta0) * (t * gammaPDFReal alpha beta t)) (Ioi 0) :=
    (((integrableOn_gammaPDFReal halpha hbeta).const_mul k0).add
      ((integrableOn_log_mul_gammaPDFReal halpha hbeta).const_mul (alpha - alpha0))).sub
      ((integrableOn_mul_gammaPDFReal halpha hbeta).const_mul (beta - beta0))
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [nigLogRatioGamma, k0]
  ring

lemma integrableOn_nigKLBoundMarginal (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta) :
    IntegrableOn (nigKLBoundMarginal gamma nu alpha beta gamma0 nu0 alpha0 beta0) (Ioi 0) := by
  have h : IntegrableOn (fun t =>
      ‖gammaPDFReal alpha beta t * nigLogRatioGamma alpha beta alpha0 beta0 t‖
        + (|(1 / 2) * (Real.log nu - Real.log nu0)| + 1 / 2 + nu0 / (2 * nu))
          * gammaPDFReal alpha beta t
        + nu0 * (gamma - gamma0) ^ 2 / 2 * (t * gammaPDFReal alpha beta t)) (Ioi 0) :=
    (((integrableOn_gamma_mul_logRatioGamma (alpha0 := alpha0) (beta0 := beta0)
      halpha hbeta).norm).add
      ((integrableOn_gammaPDFReal halpha hbeta).const_mul
        (|(1 / 2) * (Real.log nu - Real.log nu0)| + 1 / 2 + nu0 / (2 * nu)))).add
      ((integrableOn_mul_gammaPDFReal halpha hbeta).const_mul (nu0 * (gamma - gamma0) ^ 2 / 2))
  refine h.congr_fun (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
  have hg := gammaPDFReal_nonneg halpha hbeta t
  simp only [nigKLBoundMarginal, Real.norm_eq_abs, abs_mul, abs_of_nonneg hg]
  field_simp
  ring

/-- The dominating function is integrable on `ℝ × ℝ`. -/
lemma integrable_nigKLBound (hnu : 0 < nu) (hnu0 : 0 < nu0) (halpha : 0 < alpha)
    (hbeta : 0 < beta) :
    Integrable (nigKLBound gamma nu alpha beta gamma0 nu0 alpha0 beta0) := by
  rw [Measure.volume_eq_prod]
  refine (integrable_prod_iff measurable_nigKLBound.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · refine ae_of_all _ fun t => ?_
    by_cases ht : 0 < t
    · have hsec := (integrable_gauss_quadratic (gamma := gamma) (gamma0 := gamma0) hnu ht
        (|nigLogRatioGamma alpha beta alpha0 beta0 t| + |(1 / 2) * (Real.log nu - Real.log nu0)|)
        (nu * t / 2) (nu0 * t / 2)).const_mul (gammaPDFReal alpha beta t)
      refine hsec.congr (ae_of_all _ fun z => ?_)
      simp only
      rw [nigKLBound_section]
    · have h0 : (fun z => nigKLBound gamma nu alpha beta gamma0 nu0 alpha0 beta0 (t, z))
          = fun _ => 0 := by
        funext z; unfold nigKLBound
        rw [nigPrecPDF_of_nonpos hnu (p := (t, z)) (not_lt.mp ht), zero_mul]
      rw [h0]
      exact integrable_zero _ _ _
  · have hnorm : (fun t => ∫ z, ‖nigKLBound gamma nu alpha beta gamma0 nu0 alpha0 beta0 (t, z)‖)
        = (Ioi (0 : ℝ)).indicator
          (nigKLBoundMarginal gamma nu alpha beta gamma0 nu0 alpha0 beta0) := by
      funext t
      simp_rw [Real.norm_of_nonneg (nigKLBound_nonneg hnu hnu0 halpha hbeta _)]
      exact integral_nigKLBound_section hnu t
    rw [hnorm, integrable_indicator_iff measurableSet_Ioi]
    exact integrableOn_nigKLBoundMarginal hnu halpha hbeta

/-- The KL integrand is integrable on `ℝ × ℝ`. -/
lemma integrable_nigKLIntegrand (hnu : 0 < nu) (hnu0 : 0 < nu0) (halpha : 0 < alpha)
    (hbeta : 0 < beta) :
    Integrable (nigKLIntegrand gamma nu alpha beta gamma0 nu0 alpha0 beta0) :=
  (integrable_nigKLBound hnu hnu0 halpha hbeta).mono' measurable_nigKLIntegrand.aestronglyMeasurable
    (ae_of_all _ (norm_nigKLIntegrand_le hnu hnu0 halpha hbeta))

/-- Value of the `τ`-integral of the marginal. -/
lemma integral_nigKLMarginal (hnu : 0 < nu) (hnu0 : 0 < nu0) (halpha : 0 < alpha)
    (hbeta : 0 < beta) :
    ∫ t in Ioi 0, nigKLMarginal gamma nu alpha beta gamma0 nu0 alpha0 beta0 t
      = nigKLClosedForm gamma nu alpha beta gamma0 nu0 alpha0 beta0 := by
  set k0 := (alpha * Real.log beta - Real.log (Real.Gamma alpha))
    - (alpha0 * Real.log beta0 - Real.log (Real.Gamma alpha0))
  set K1 := k0 + (1 / 2) * (Real.log nu - Real.log nu0) - 1 / 2 + nu0 / (2 * nu)
  set K3 := nu0 * (gamma - gamma0) ^ 2 / 2 - (beta - beta0)
  have hpt : EqOn (nigKLMarginal gamma nu alpha beta gamma0 nu0 alpha0 beta0)
      (fun t => (K1 * gammaPDFReal alpha beta t
        + (alpha - alpha0) * (Real.log t * gammaPDFReal alpha beta t))
        + K3 * (t * gammaPDFReal alpha beta t)) (Ioi 0) := by
    intro t (ht : 0 < t)
    simp only [nigKLMarginal, nigLogRatioGamma, K1, K3, k0]
    field_simp
    ring
  have hI0 := integrableOn_gammaPDFReal halpha hbeta
  have hIl := integrableOn_log_mul_gammaPDFReal halpha hbeta
  have hIt := integrableOn_mul_gammaPDFReal halpha hbeta
  have hI01 : IntegrableOn (fun t => K1 * gammaPDFReal alpha beta t
      + (alpha - alpha0) * (Real.log t * gammaPDFReal alpha beta t)) (Ioi 0) :=
    (hI0.const_mul K1).add (hIl.const_mul _)
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_add hI01 (hIt.const_mul K3),
    integral_add (hI0.const_mul K1) (hIl.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_gammaPDFReal_Ioi halpha hbeta,
    integral_log_mul_gammaPDFReal halpha hbeta, integral_mul_gammaPDFReal halpha hbeta]
  unfold nigKLClosedForm
  rw [Real.log_div hnu.ne' hnu0.ne']
  simp only [K1, K3, k0]
  field_simp
  ring

/-- `∫ q (L_Γ + L_N) = nigKLClosedForm` (Fubini). -/
lemma integral_nigKLIntegrand (hnu : 0 < nu) (hnu0 : 0 < nu0) (halpha : 0 < alpha)
    (hbeta : 0 < beta) :
    ∫ p, nigKLIntegrand gamma nu alpha beta gamma0 nu0 alpha0 beta0 p
      = nigKLClosedForm gamma nu alpha beta gamma0 nu0 alpha0 beta0 := by
  have hint := integrable_nigKLIntegrand (gamma := gamma) (gamma0 := gamma0) (alpha0 := alpha0)
    (beta0 := beta0) hnu hnu0 halpha hbeta
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod _ hint]
  simp_rw [integral_nigKLIntegrand_section hnu]
  rw [integral_indicator measurableSet_Ioi, integral_nigKLMarginal hnu hnu0 halpha hbeta]

end Integrand

/-! ## Main theorems -/

section Main

variable {gamma nu alpha beta gamma0 nu0 alpha0 beta0 : ℝ}

lemma integrable_nigPrecPDF_mul_log_ratio (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0) :
    Integrable fun p => nigPrecPDF gamma nu alpha beta p
      * Real.log (nigPrecPDF gamma nu alpha beta p / nigPrecPDF gamma0 nu0 alpha0 beta0 p) :=
  (integrable_nigKLIntegrand (gamma0 := gamma0) (alpha0 := alpha0) (beta0 := beta0)
    hnu hnu0 halpha hbeta).congr
    (ae_of_all _ fun p => (nigPrecPDF_mul_log_ratio hnu halpha hbeta hnu0 halpha0 hbeta0 p).symm)

lemma integral_nigPrecPDF_mul_log_ratio (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0) :
    ∫ p, nigPrecPDF gamma nu alpha beta p
        * Real.log (nigPrecPDF gamma nu alpha beta p / nigPrecPDF gamma0 nu0 alpha0 beta0 p)
      = nigKLClosedForm gamma nu alpha beta gamma0 nu0 alpha0 beta0 := by
  rw [integral_congr_ae (ae_of_all _ fun p =>
    nigPrecPDF_mul_log_ratio hnu halpha hbeta hnu0 halpha0 hbeta0 p)]
  exact integral_nigKLIntegrand hnu hnu0 halpha hbeta

/--
**Level B (precision form).** The KL divergence between the precision-form NIG
laws equals the closed-form expression.
-/
theorem klDiv_nigPrecMeasure (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0) :
    klDiv (nigPrecMeasure gamma nu alpha beta) (nigPrecMeasure gamma0 nu0 alpha0 beta0)
      = ENNReal.ofReal (nigKLClosedForm gamma nu alpha beta gamma0 nu0 alpha0 beta0) := by
  have := isProbabilityMeasure_nigPrecMeasure (gamma := gamma) hnu halpha hbeta
  have := isProbabilityMeasure_nigPrecMeasure (gamma := gamma0) hnu0 halpha0 hbeta0
  unfold nigPrecMeasure at *
  rw [klDiv_withDensity_ofReal volume (measurable_nigPrecPDF _ _ _ _)
    (measurable_nigPrecPDF _ _ _ _) (nigPrecPDF_nonneg halpha hbeta)
    (fun p hp => nigPrecPDF_pos hnu0 halpha0 hbeta0 (pos_of_nigPrecPDF_pos hnu hp))
    (integrable_nigPrecPDF_mul_log_ratio hnu halpha hbeta hnu0 halpha0 hbeta0),
    integral_nigPrecPDF_mul_log_ratio hnu halpha hbeta hnu0 halpha0 hbeta0]

/--
**Gibbs inequality for the closed form.** The closed-form NIG KL expression is
nonnegative on the admissible parameter domain.
-/
theorem nigKLClosedForm_nonneg (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0) :
    0 ≤ nigKLClosedForm gamma nu alpha beta gamma0 nu0 alpha0 beta0 := by
  have := isProbabilityMeasure_nigPrecMeasure (gamma := gamma) hnu halpha hbeta
  have := isProbabilityMeasure_nigPrecMeasure (gamma := gamma0) hnu0 halpha0 hbeta0
  unfold nigPrecMeasure at *
  rw [← integral_nigPrecPDF_mul_log_ratio hnu halpha hbeta hnu0 halpha0 hbeta0]
  exact integral_mul_log_div_nonneg volume (measurable_nigPrecPDF _ _ _ _)
    (measurable_nigPrecPDF _ _ _ _) (nigPrecPDF_nonneg halpha hbeta)
    (fun p hp => nigPrecPDF_pos hnu0 halpha0 hbeta0 (pos_of_nigPrecPDF_pos hnu hp))
    (integrable_nigPrecPDF_mul_log_ratio hnu halpha hbeta hnu0 halpha0 hbeta0)

/-- KL divergence is invariant under a measurable involution. -/
lemma klDiv_map_involution {Y : Type*} [MeasurableSpace Y] (μ ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {φ : Y → Y} (hφ : Measurable φ)
    (hinv : ∀ y, φ (φ y) = y) :
    klDiv (μ.map φ) (ν.map φ) = klDiv μ ν := by
  refine le_antisymm (klDiv_map_le μ ν hφ) ?_
  have hid : φ ∘ φ = id := funext hinv
  calc klDiv μ ν = klDiv ((μ.map φ).map φ) ((ν.map φ).map φ) := by
        rw [Measure.map_map hφ hφ, Measure.map_map hφ hφ, hid, Measure.map_id, Measure.map_id]
    _ ≤ klDiv (μ.map φ) (ν.map φ) := klDiv_map_le _ _ hφ

lemma measurable_nigInvolution : Measurable fun p : ℝ × ℝ => (p.1⁻¹, p.2) :=
  measurable_fst.inv.prodMk measurable_snd

/--
**Level B.** For `ν, α, β, ν₀, α₀, β₀ > 0`,

  KL(NIG(γ, ν, α, β) ‖ NIG(γ₀, ν₀, α₀, β₀)) = nigKLClosedForm γ ν α β γ₀ ν₀ α₀ β₀,

where the NIG laws are the joint laws of `(σ², z)` and `klDiv` is mathlib's
Kullback–Leibler divergence.
-/
theorem klDiv_nigMeasure (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0) :
    klDiv (nigMeasure gamma nu alpha beta) (nigMeasure gamma0 nu0 alpha0 beta0)
      = ENNReal.ofReal (nigKLClosedForm gamma nu alpha beta gamma0 nu0 alpha0 beta0) := by
  have := isProbabilityMeasure_nigPrecMeasure (gamma := gamma) hnu halpha hbeta
  have := isProbabilityMeasure_nigPrecMeasure (gamma := gamma0) hnu0 halpha0 hbeta0
  rw [nigMeasure, nigMeasure, klDiv_map_involution _ _ measurable_nigInvolution
    (fun p => by simp), klDiv_nigPrecMeasure hnu halpha hbeta hnu0 halpha0 hbeta0]

/-- Real-valued form: `(KL(NIG ‖ NIG₀)).toReal = nigKLClosedForm`. -/
theorem toReal_klDiv_nigMeasure (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0) :
    (klDiv (nigMeasure gamma nu alpha beta) (nigMeasure gamma0 nu0 alpha0 beta0)).toReal
      = nigKLClosedForm gamma nu alpha beta gamma0 nu0 alpha0 beta0 := by
  rw [klDiv_nigMeasure hnu halpha hbeta hnu0 halpha0 hbeta0,
    ENNReal.toReal_ofReal (nigKLClosedForm_nonneg hnu halpha hbeta hnu0 halpha0 hbeta0)]

/-- NIG law of `(μ, σ²)`, in the order `(μ, σ²)`. -/
noncomputable def nigMeasureMuSigma (gamma nu alpha beta : ℝ) : Measure (ℝ × ℝ) :=
  (nigMeasure gamma nu alpha beta).map Prod.swap

/--
**Level B in the order `(μ, σ²)`.**
`D_KL(NIG(γ,ν,α,β) ‖ NIG(γ₀,ν₀,α₀,β₀))` on `(μ, σ²)` equals the closed form.
-/
theorem klDiv_nigMeasureMuSigma (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0) :
    klDiv (nigMeasureMuSigma gamma nu alpha beta) (nigMeasureMuSigma gamma0 nu0 alpha0 beta0)
      = ENNReal.ofReal (nigKLClosedForm gamma nu alpha beta gamma0 nu0 alpha0 beta0) := by
  have := isProbabilityMeasure_nigPrecMeasure (gamma := gamma) hnu halpha hbeta
  have := isProbabilityMeasure_nigPrecMeasure (gamma := gamma0) hnu0 halpha0 hbeta0
  have : IsProbabilityMeasure (nigMeasure gamma nu alpha beta) := by
    unfold nigMeasure; infer_instance
  have : IsProbabilityMeasure (nigMeasure gamma0 nu0 alpha0 beta0) := by
    unfold nigMeasure; infer_instance
  rw [nigMeasureMuSigma, nigMeasureMuSigma,
    klDiv_map_involution _ _ measurable_swap (fun p => Prod.swap_swap p),
    klDiv_nigMeasure hnu halpha hbeta hnu0 halpha0 hbeta0]

end Main

end ELVAE
