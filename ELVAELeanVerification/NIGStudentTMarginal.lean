import Mathlib

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# The marginal latent law of `z` is Student-t

The latent NIG hierarchy (identities of measures on `ℝ`):

  σ² ~ InvGamma(α, β)   (the law of 1/τ with τ ~ Gamma(shape α, rate β)),
  μ | σ² ~ Normal(γ, σ²/ν),
  z | μ, σ² ~ Normal(μ, σ²).

`nigMuMarginal` is the law of `μ` (first two layers); `nigZMarginal` is the law of
the latent variable `z` (all three layers).

Main results, for `ν, α, β > 0`:

* `nigZMarginal_eq_studentT`: the law of `z` is Student-t with
  `2α` degrees of freedom, location `γ` and squared scale `c/α`, where
  `c = β(1 + 1/ν)`;
* `nigZMarginal_fiber_invariant`: the law of `z` depends on `(ν, β)` only
  through `c = β(1 + 1/ν)` (it is constant on each fiber);
* `nigMuMarginal_eq_studentT`: the law of `μ` is Student-t with `2α`
  degrees of freedom, location `γ` and squared scale `β/(να)`;
* `gamma_mixture_gaussian_eq_studentT`: the Gamma scale mixture
  `∫ N(m, k/τ) Gamma(τ; a, b) dτ = t_{2a}(m, kb/a)` as an identity of measures;
* `gaussianReal_bind_gaussianReal`: the Gaussian hierarchy identity
  `μ ~ N(m, v₁), z | μ ~ N(μ, v₂) ⟹ z ~ N(m, v₁ + v₂)`.

Mathlib has no Student-t or inverse-gamma distribution. Student-t is defined
here by its standard density

  t_n(y; μ, s²) = Γ((n+1)/2) / (Γ(n/2) √(nπ s²)) · (1 + (y-μ)²/(n s²))^{-(n+1)/2},

and InvGamma(α, β) as the push-forward of mathlib's `gammaMeasure α β` under
`τ ↦ 1/τ`. Mathlib's `gaussianReal`, `gammaMeasure`, `Measure.bind` and
convolution are used unchanged.
-/

namespace ELVAE

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

/-- Student-t density: `n` degrees of freedom, location `μ`, squared scale `s2`. -/
noncomputable def studentTPDFReal (n μ s2 y : ℝ) : ℝ :=
  Real.Gamma ((n + 1) / 2) / (Real.Gamma (n / 2) * Real.sqrt (n * π * s2))
    * (1 + (y - μ) ^ 2 / (n * s2)) ^ (-((n + 1) / 2))

/-- Pointwise form of the mixture integrand on τ > 0. -/
lemma mixture_integrand_eq (a b k m y t : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) (ht : 0 < t) :
    gammaPDFReal a b t * gaussianPDFReal m (k / t).toNNReal y
      = (b ^ a / (Real.Gamma a * Real.sqrt (2 * π * k)))
          * (t ^ ((a + 1 / 2) - 1) * Real.exp (-((b + (y - m) ^ 2 / (2 * k)) * t))) := by
  have hkt : 0 ≤ k / t := by positivity
  simp only [gammaPDFReal, ht.le, ↓reduceIte]
  rw [gaussianPDFReal, Real.coe_toNNReal _ hkt]
  have hsq : Real.sqrt (2 * π * (k / t)) = Real.sqrt (2 * π * k) / Real.sqrt t := by
    rw [← Real.sqrt_div' _ ht.le]; congr 1; ring
  have hpow : t ^ ((a + 1 / 2) - 1) = t ^ (a - 1) * Real.sqrt t := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]; congr 1; ring
  have hexp : Real.exp (-(b * t)) * Real.exp (-(y - m) ^ 2 / (2 * (k / t)))
      = Real.exp (-((b + (y - m) ^ 2 / (2 * k)) * t)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [hsq, hpow, ← hexp]
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs2 : 0 < Real.sqrt (2 * π * k) := Real.sqrt_pos.mpr (by positivity)
  have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  field_simp

theorem mixture_integral (a b k m y : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    ∫ t in Ioi 0, gammaPDFReal a b t * gaussianPDFReal m (k / t).toNNReal y
      = studentTPDFReal (2 * a) m (k * b / a) y := by
  set u : ℝ := (y - m) ^ 2 / (2 * k * b) with hu
  have hu0 : 0 ≤ u := by positivity
  have hr : b + (y - m) ^ 2 / (2 * k) = b * (1 + u) := by
    rw [hu]; field_simp
  have hrpos : 0 < b + (y - m) ^ 2 / (2 * k) := by positivity
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => mixture_integrand_eq a b k m y t ha hb hk ht),
    integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hrpos, hr]
  have h1u : 0 < 1 + u := by linarith
  unfold studentTPDFReal
  have e1 : (2 * a + 1) / 2 = a + 1 / 2 := by ring
  have e2 : 2 * a / 2 = a := by ring
  have e3 : 2 * a * π * (k * b / a) = (2 * π * k) * b := by field_simp
  have e4 : (y - m) ^ 2 / (2 * a * (k * b / a)) = u := by rw [hu]; field_simp
  rw [e1, e2, e3, e4, Real.sqrt_mul (by positivity), one_div, Real.inv_rpow (by positivity),
    Real.mul_rpow hb.le h1u.le, Real.rpow_neg h1u.le]
  have hbp : b ^ (a + 1 / 2) = b ^ a * Real.sqrt b := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hb]
  rw [hbp]
  have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hs2 : 0 < Real.sqrt (2 * π * k) := Real.sqrt_pos.mpr (by positivity)
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hba : 0 < b ^ a := Real.rpow_pos_of_pos hb a
  have hup : 0 < (1 + u) ^ (a + 1 / 2) := Real.rpow_pos_of_pos h1u _
  field_simp
  rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * π * k),
    Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * π)]


lemma studentTPDFReal_pos (n μ s2 y : ℝ) (hn : 0 < n) (hs : 0 < s2) :
    0 < studentTPDFReal n μ s2 y := by
  unfold studentTPDFReal
  have h1 : 0 < Real.Gamma ((n + 1) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have h2 : 0 < Real.Gamma (n / 2) := Real.Gamma_pos_of_pos (by positivity)
  have h3 : 0 < Real.sqrt (n * π * s2) := Real.sqrt_pos.mpr (by positivity)
  have h4 : 0 < (1 + (y - μ) ^ 2 / (n * s2)) ^ (-((n + 1) / 2)) :=
    Real.rpow_pos_of_pos (by positivity) _
  positivity

lemma mixture_lintegral (a b k m y : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    ∫⁻ t, gammaPDF a b t * gaussianPDF m (k / t).toNNReal y
      = ENNReal.ofReal (studentTPDFReal (2 * a) m (k * b / a) y) := by
  have hf : (fun t => gammaPDF a b t * gaussianPDF m (k / t).toNNReal y)
      = fun t => ENNReal.ofReal (gammaPDFReal a b t * gaussianPDFReal m (k / t).toNNReal y) := by
    funext t
    rw [gammaPDF, gaussianPDF, ENNReal.ofReal_mul (gammaPDFReal_nonneg ha hb t)]
  rw [hf, ← lintegral_add_compl _ (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ))),
    Set.compl_Ioi]
  have hzero : ∫⁻ t in Iic 0,
      ENNReal.ofReal (gammaPDFReal a b t * gaussianPDFReal m (k / t).toNNReal y) = 0 := by
    rw [← setLIntegral_congr Iio_ae_eq_Iic]
    rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0)
      (fun t (ht : t < 0) => by simp [gammaPDFReal, not_le.mpr ht])]
    simp
  rw [hzero, add_zero]
  have hint_val := mixture_integral a b k m y ha hb hk
  have hpos := studentTPDFReal_pos (2 * a) m (k * b / a) y (by positivity) (by positivity)
  have hint : Integrable
      (fun t => gammaPDFReal a b t * gaussianPDFReal m (k / t).toNNReal y)
      (volume.restrict (Ioi 0)) :=
    Integrable.of_integral_ne_zero (by rw [hint_val]; exact hpos.ne')
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun t => mul_nonneg (gammaPDFReal_nonneg ha hb t)
      (gaussianPDFReal_nonneg _ _ _)), hint_val]

/-- Student-t probability measure: `n` degrees of freedom, location `μ`, squared scale `s2`. -/
noncomputable def studentTMeasure (n μ s2 : ℝ) : Measure ℝ :=
  volume.withDensity (fun y => ENNReal.ofReal (studentTPDFReal n μ s2 y))

lemma measurable_gaussian_kernel (m k : ℝ) :
    Measurable (fun t : ℝ => gaussianReal m (k / t).toNNReal) :=
  measurable_gaussianReal.comp
    (measurable_const.prodMk ((measurable_const.div measurable_id).real_toNNReal))

theorem gamma_mixture_gaussian_eq_studentT (a b k m : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    (gammaMeasure a b).bind (fun t => gaussianReal m (k / t).toNNReal)
      = studentTMeasure (2 * a) m (k * b / a) := by
  ext s hs
  have hmeasG : Measurable (gammaPDF a b) := (measurable_gammaPDFReal a b).ennreal_ofReal
  have hmk : Measurable (fun t : ℝ => gaussianReal m (k / t).toNNReal s) :=
    (Measure.measurable_coe hs).comp (measurable_gaussian_kernel m k)
  rw [Measure.bind_apply hs (measurable_gaussian_kernel m k).aemeasurable, studentTMeasure,
    withDensity_apply _ hs, gammaMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hmeasG hmk]
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
    have : (volume : Measure ℝ) {0} = 0 := measure_singleton 0
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp this] with t ht
    simpa using ht
  have hstep : ∀ᵐ t ∂(volume : Measure ℝ),
      (gammaPDF a b * fun t => gaussianReal m (k / t).toNNReal s) t
        = ∫⁻ y in s, gammaPDF a b t * gaussianPDF m (k / t).toNNReal y := by
    filter_upwards [hae] with t ht
    rcases lt_or_gt_of_ne ht with hneg | hpos
    · have h0 : gammaPDF a b t = 0 := gammaPDF_of_neg hneg
      simp [h0]
    · have hv : (k / t).toNNReal ≠ 0 := by
        rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
      simp only [Pi.mul_apply]
      rw [gaussianReal_apply _ hv, lintegral_const_mul _ (measurable_gaussianPDF _ _)]
  rw [lintegral_congr_ae hstep]
  have hmeas2 : Measurable (Function.uncurry
      (fun (t y : ℝ) => gammaPDF a b t * gaussianPDF m (k / t).toNNReal y)) := by
    refine (hmeasG.comp measurable_fst).mul ?_
    exact measurable_uncurry_gaussianPDF.comp (measurable_const.prodMk
      (((measurable_const.div measurable_fst).real_toNNReal).prodMk measurable_snd))
  rw [lintegral_lintegral_swap hmeas2.aemeasurable]
  refine lintegral_congr fun y => ?_
  exact mixture_lintegral a b k m y ha hb hk

/-- Binding a location family `x ↦ ν.map (x + ·)` is additive convolution. -/
lemma bind_map_const_add_eq_conv (μ ν : Measure ℝ) [SFinite ν]
    (hf : AEMeasurable (fun x : ℝ => ν.map (x + ·)) μ) :
    μ.bind (fun x => ν.map (x + ·)) = μ ∗ ν := by
  ext s hs
  rw [Measure.bind_apply hs hf, ← lintegral_indicator_one hs,
    Measure.lintegral_conv (measurable_one.indicator hs)]
  refine lintegral_congr fun x => ?_
  rw [Measure.map_apply (measurable_const_add x) hs,
    ← lintegral_indicator_one (measurable_const_add x hs)]
  rfl

/-- Gaussian hierarchy: `z ~ N(m, v₁)`, `y | z ~ N(z, v₂)` gives `y ~ N(m, v₁ + v₂)`. -/
theorem gaussianReal_bind_gaussianReal (m : ℝ) (v1 v2 : ℝ≥0) :
    (gaussianReal m v1).bind (fun z => gaussianReal z v2) = gaussianReal m (v1 + v2) := by
  have hk : (fun z : ℝ => gaussianReal z v2) = fun z => (gaussianReal 0 v2).map (z + ·) := by
    funext z
    rw [gaussianReal_map_const_add, zero_add]
  have hmeas : Measurable (fun z : ℝ => gaussianReal z v2) :=
    measurable_gaussianReal.comp (measurable_id.prodMk measurable_const)
  rw [hk, bind_map_const_add_eq_conv _ _ (hk ▸ hmeas.aemeasurable),
    gaussianReal_conv_gaussianReal, add_zero]

/-! ## The NIG hierarchy -/

/-- Inverse-gamma law: the law of `1/τ` for `τ ~ Gamma(shape α, rate β)`. -/
noncomputable def invGammaMeasure (alpha beta : ℝ) : Measure ℝ :=
  (gammaMeasure alpha beta).map (fun t => t⁻¹)

/-- Law of `μ`: `σ² ~ InvGamma(α, β)`, `μ | σ² ~ N(γ, σ²/ν)`. -/
noncomputable def nigMuMarginal (gamma nu alpha beta : ℝ) : Measure ℝ :=
  (invGammaMeasure alpha beta).bind (fun s => gaussianReal gamma (s / nu).toNNReal)

/-- Marginal latent law of `z`: in addition `z | μ, σ² ~ N(μ, σ²)`. -/
noncomputable def nigZMarginal (gamma nu alpha beta : ℝ) : Measure ℝ :=
  (invGammaMeasure alpha beta).bind
    (fun s => (gaussianReal gamma (s / nu).toNNReal).bind
      (fun m => gaussianReal m s.toNNReal))

lemma bind_map_eq_bind_comp {μ : Measure ℝ} {f : ℝ → ℝ} {g : ℝ → Measure ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    (μ.map f).bind g = μ.bind (g ∘ f) := by
  ext s hs
  rw [Measure.bind_apply hs hg.aemeasurable, Measure.bind_apply hs (hg.comp hf).aemeasurable,
    lintegral_map (f := fun a => g a s) ((Measure.measurable_coe hs).comp hg) hf]
  rfl

/-- The Gamma law is concentrated on `(0, ∞)`. -/
lemma gammaMeasure_ae_pos (a b : ℝ) : ∀ᵐ t ∂(gammaMeasure a b), 0 < t := by
  rw [ae_iff]
  have hset : {t : ℝ | ¬ 0 < t} = Iic 0 := by ext t; simp
  rw [hset, gammaMeasure, withDensity_apply _ measurableSet_Iic,
    ← setLIntegral_congr Iio_ae_eq_Iic]
  exact lintegral_gammaPDF_of_nonpos le_rfl

/-- A variance mixture over `InvGamma` is a precision mixture over `Gamma`. -/
lemma invGamma_bind_eq_gamma_bind (a b m k : ℝ) :
    (invGammaMeasure a b).bind (fun s => gaussianReal m (k * s).toNNReal)
      = (gammaMeasure a b).bind (fun t => gaussianReal m (k / t).toNNReal) := by
  have hg : Measurable (fun s : ℝ => gaussianReal m (k * s).toNNReal) :=
    measurable_gaussianReal.comp
      (measurable_const.prodMk ((measurable_const.mul measurable_id).real_toNNReal))
  rw [invGammaMeasure, bind_map_eq_bind_comp measurable_inv hg]
  rfl

/--
**Law of `μ`.** For `ν, α, β > 0`, `μ` is Student-t with `2α` degrees of
freedom, location `γ` and squared scale `β/(να)`.
-/
theorem nigMuMarginal_eq_studentT (gamma nu alpha beta : ℝ)
    (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta) :
    nigMuMarginal gamma nu alpha beta
      = studentTMeasure (2 * alpha) gamma (beta / (nu * alpha)) := by
  have hk : (fun s : ℝ => gaussianReal gamma (s / nu).toNNReal)
      = fun s => gaussianReal gamma (nu⁻¹ * s).toNNReal := by
    funext s; rw [div_eq_inv_mul]
  rw [nigMuMarginal, hk, invGamma_bind_eq_gamma_bind,
    gamma_mixture_gaussian_eq_studentT _ _ _ _ halpha hbeta (inv_pos.mpr hnu)]
  congr 1
  field_simp

/--
For `ν, α, β > 0`, the marginal law of the latent `z` in
the NIG hierarchy is Student-t with `2α` degrees of freedom, location `γ` and squared scale
`c/α`, where `c = β(1 + 1/ν)`.
-/
theorem nigZMarginal_eq_studentT (gamma nu alpha beta : ℝ)
    (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta) :
    nigZMarginal gamma nu alpha beta
      = studentTMeasure (2 * alpha) gamma (beta * (1 + 1 / nu) / alpha) := by
  -- Step 1: integrate out `μ` for every value of `σ²`.
  have hinner : (fun s : ℝ => (gaussianReal gamma (s / nu).toNNReal).bind
        (fun m => gaussianReal m s.toNNReal))
      = fun s => gaussianReal gamma ((s / nu).toNNReal + s.toNNReal) := by
    funext s
    exact gaussianReal_bind_gaussianReal gamma _ _
  have hg : Measurable (fun s : ℝ => gaussianReal gamma ((s / nu).toNNReal + s.toNNReal)) :=
    measurable_gaussianReal.comp (measurable_const.prodMk
      (((measurable_id.div_const nu).real_toNNReal).add measurable_id.real_toNNReal))
  -- Step 2: pass to the Gamma precision parameterization; a.e. `τ > 0`.
  rw [nigZMarginal, hinner, invGammaMeasure, bind_map_eq_bind_comp measurable_inv hg]
  have hae : (fun s : ℝ => gaussianReal gamma ((s / nu).toNNReal + s.toNNReal)) ∘ (fun t => t⁻¹)
      =ᵐ[gammaMeasure alpha beta]
        fun t => gaussianReal gamma ((1 + 1 / nu) / t).toNNReal := by
    filter_upwards [gammaMeasure_ae_pos alpha beta] with t ht
    have h1 : 0 ≤ t⁻¹ / nu := by positivity
    have h2 : 0 ≤ t⁻¹ := by positivity
    simp only [Function.comp_apply]
    rw [← Real.toNNReal_add h1 h2]
    congr 2
    field_simp
    ring
  -- Step 3: the Gamma scale mixture of Gaussians is Student-t.
  rw [Measure.bind_congr_right hae,
    gamma_mixture_gaussian_eq_studentT _ _ _ _ halpha hbeta (by positivity)]
  congr 1
  ring

/--
**Quotient structure.** The marginal law of `z` depends on `(ν, β)` only through
`c = β(1 + 1/ν)`: two NIG parameters on the same fiber give the same law.
-/
theorem nigZMarginal_fiber_invariant (gamma alpha nu1 beta1 nu2 beta2 : ℝ)
    (halpha : 0 < alpha) (hnu1 : 0 < nu1) (hbeta1 : 0 < beta1)
    (hnu2 : 0 < nu2) (hbeta2 : 0 < beta2)
    (hfiber : beta1 * (1 + 1 / nu1) = beta2 * (1 + 1 / nu2)) :
    nigZMarginal gamma nu1 alpha beta1 = nigZMarginal gamma nu2 alpha beta2 := by
  rw [nigZMarginal_eq_studentT _ _ _ _ hnu1 halpha hbeta1,
    nigZMarginal_eq_studentT _ _ _ _ hnu2 halpha hbeta2, hfiber]

/--
Fiber form of the Student-t marginal: along the fiber `β = c ν/(1+ν)` the law of `z` is
`t_{2α}(γ, c/α)` for every `ν > 0`.
-/
theorem nigZMarginal_on_fiber (gamma alpha c nu : ℝ)
    (halpha : 0 < alpha) (hc : 0 < c) (hnu : 0 < nu) :
    nigZMarginal gamma nu alpha (c * nu / (1 + nu))
      = studentTMeasure (2 * alpha) gamma (c / alpha) := by
  rw [nigZMarginal_eq_studentT _ _ _ _ hnu halpha (by positivity)]
  congr 2
  have h1 : 1 + nu ≠ 0 := by linarith
  field_simp
  ring

/-- The Student-t law with positive parameters is a probability measure. -/
theorem isProbabilityMeasure_studentTMeasure (n μ s2 : ℝ) (hn : 0 < n) (hs2 : 0 < s2) :
    IsProbabilityMeasure (studentTMeasure n μ s2) := by
  have hn2 : 2 * (n / 2) = n := by ring
  -- scale-mixture representation with squared scale `s2`
  have hmix2 := gamma_mixture_gaussian_eq_studentT (n / 2) (n / 2) s2 μ
    (by positivity) (by positivity) hs2
  rw [hn2, show s2 * (n / 2) / (n / 2) = s2 by field_simp] at hmix2
  rw [← hmix2]
  have : IsProbabilityMeasure (gammaMeasure (n / 2) (n / 2)) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by positivity)
  constructor
  rw [Measure.bind_apply MeasurableSet.univ (measurable_gaussian_kernel μ s2).aemeasurable]
  have h1 : ∀ t : ℝ, (gaussianReal μ (s2 / t).toNNReal) Set.univ = 1 := fun t => by
    have := instIsProbabilityMeasureGaussianReal μ (s2 / t).toNNReal
    exact measure_univ
  simp [h1]

end ELVAE
