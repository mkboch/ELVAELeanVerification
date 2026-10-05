import Mathlib
import Official.M03

/-!
# Finite hierarchical KL and its fiber formula

For all admissible parameters the complete hierarchical forward divergence
`K = KL[NIG(γ,ν,α,β) ‖ p₀]` (the model's `hierarchicalKL`) is finite and equals the
explicit expression below; on the fiber `F_x` it equals `F(x,t)`.
-/

noncomputable section

namespace NIGBottleneck

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

section Moments

/-- The model's inverse-gamma law is a probability measure. -/
theorem isProbabilityMeasure_inverseGammaLaw (a b : PositiveReal) :
    IsProbabilityMeasure (inverseGammaLaw a b) := by
  rw [inverseGammaLaw_eq_invGammaMeasure, invGammaMeasure]
  have := isProbabilityMeasure_gammaMeasure a.property b.property
  exact (Measure.isProbabilityMeasure_map_iff measurable_inv.aemeasurable).mpr inferInstance

lemma ofReal_inverseGammaDensity_toReal (a b : PositiveReal) (x : ℝ) :
    (ENNReal.ofReal (inverseGammaDensity a b x)).toReal = inverseGammaDensity a b x :=
  ENNReal.toReal_ofReal (inverseGammaDensity_nonneg _ _ _ a.property b.property.le)

/-- Integrals against the inverse-gamma law are integrals against its density. -/
lemma integral_inverseGammaLaw (a b : PositiveReal) (g : ℝ → ℝ) :
    ∫ x, g x ∂inverseGammaLaw a b = ∫ x, inverseGammaDensity a b x * g x := by
  rw [inverseGammaLaw, integral_withDensity_eq_integral_toReal_smul
    (measurable_inverseGammaDensity _ _).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  rw [ofReal_inverseGammaDensity_toReal, smul_eq_mul]

/-- Integrability against the inverse-gamma law is integrability against its density. -/
lemma integrable_inverseGammaLaw_iff (a b : PositiveReal) (g : ℝ → ℝ) :
    Integrable g (inverseGammaLaw a b) ↔
      Integrable (fun x => inverseGammaDensity a b x * g x) := by
  rw [inverseGammaLaw, integrable_withDensity_iff_integrable_smul'
    (measurable_inverseGammaDensity _ _).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have h : (fun x => (ENNReal.ofReal (inverseGammaDensity a b x)).toReal • g x)
      = fun x => inverseGammaDensity a b x * g x := by
    funext x
    rw [ofReal_inverseGammaDensity_toReal, smul_eq_mul]
  rw [h]

lemma integral_inverseGammaDensity (a b : PositiveReal) :
    ∫ x, inverseGammaDensity a b x = 1 := by
  have h := integral_inverseGammaLaw a b (fun _ => 1)
  have := isProbabilityMeasure_inverseGammaLaw a b
  simpa using h.symm

lemma integrable_inverseGammaDensity (a b : PositiveReal) :
    Integrable (inverseGammaDensity a b) := by
  have := isProbabilityMeasure_inverseGammaLaw a b
  have h := (integrable_inverseGammaLaw_iff a b (fun _ => (1 : ℝ))).mp (integrable_const 1)
  simpa using h

lemma integrable_sq_sub_gaussianReal (m c : ℝ) (v : ℝ≥0) :
    Integrable (fun z => (z - c) ^ 2) (gaussianReal m v) :=
  ((memLp_id_gaussianReal 2).sub (memLp_const c)).integrable_sq

lemma integral_sq_sub_gaussianReal (m c : ℝ) (v : ℝ≥0) :
    ∫ z, (z - c) ^ 2 ∂(gaussianReal m v) = v + (m - c) ^ 2 := by
  have hvar := variance_fun_id_gaussianReal (μ := m) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at hvar
  have hexp : (fun z : ℝ => (z - c) ^ 2)
      = fun z => (z - m) ^ 2 + (2 * (m - c)) * z + (-(2 * (m - c) * m) + (m - c) ^ 2) := by
    funext z; ring
  rw [hexp]
  have h1 : Integrable (fun z : ℝ => (z - m) ^ 2) (gaussianReal m v) :=
    integrable_sq_sub_gaussianReal m m v
  have h2 : Integrable (fun z : ℝ => (2 * (m - c)) * z) (gaussianReal m v) :=
    ((memLp_id_gaussianReal 1).integrable le_rfl).const_mul _
  have h12 : Integrable (fun z : ℝ => (z - m) ^ 2 + (2 * (m - c)) * z) (gaussianReal m v) :=
    h1.add h2
  rw [integral_add h12 (integrable_const _), integral_add h1 h2, integral_const_mul,
    integral_id_gaussianReal, hvar, integral_const]
  simp

lemma normalDensity_eq_gaussianPDFReal' (m v : ℝ) (hv : 0 ≤ v) :
    normalDensity m v = gaussianPDFReal m v.toNNReal := by
  funext z
  exact normalDensity_eq_gaussianPDFReal m v z hv

lemma integrable_normalDensity (m v : ℝ) (hv : 0 < v) : Integrable (normalDensity m v) := by
  rw [normalDensity_eq_gaussianPDFReal' m v hv.le]
  exact integrable_gaussianPDFReal _ _

lemma integral_normalDensity (m v : ℝ) (hv : 0 < v) : ∫ z, normalDensity m v z = 1 := by
  rw [normalDensity_eq_gaussianPDFReal' m v hv.le]
  exact integral_gaussianPDFReal_eq_one _ (by simpa using hv)

/-- `∫ N(z; m, v) (z − c)² dz = v + (m − c)²`. -/
lemma integral_normalDensity_mul_sq_sub (m c v : ℝ) (hv : 0 < v) :
    ∫ z, normalDensity m v z * (z - c) ^ 2 = v + (m - c) ^ 2 := by
  have hv' : v.toNNReal ≠ 0 := by simpa using hv
  have := integral_gaussianReal_eq_integral_smul (f := fun z => (z - c) ^ 2) (μ := m) hv'
  simp only [smul_eq_mul] at this
  rw [normalDensity_eq_gaussianPDFReal' m v hv.le, ← this, integral_sq_sub_gaussianReal,
    Real.coe_toNNReal _ hv.le]

lemma integrable_normalDensity_mul_sq_sub (m c v : ℝ) (hv : 0 < v) :
    Integrable (fun z => normalDensity m v z * (z - c) ^ 2) := by
  have hv' : v.toNNReal ≠ 0 := by simpa using hv
  have h := integrable_sq_sub_gaussianReal m c v.toNNReal
  rw [gaussianReal_of_var_ne_zero _ hv', integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (ae_of_all _ fun _ => gaussianPDF_lt_top)] at h
  rw [normalDensity_eq_gaussianPDFReal' m v hv.le]
  simpa [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)] using h

end Moments

section Fubini

variable (p : Parameters)

/-- Fubini for a function of `σ²` only against the NIG density: integrability. -/
lemma integrable_nig_mul_snd {u : ℝ → ℝ} (hum : Measurable u)
    (hu : Integrable (fun x => inverseGammaDensity p.alpha p.beta x * u x)) :
    Integrable (fun q : ℝ × ℝ => nigDensity p q * u q.2) := by
  rw [Measure.volume_eq_prod]
  have hmeas : AEStronglyMeasurable (fun q : ℝ × ℝ => nigDensity p q * u q.2)
      (volume.prod volume) :=
    ((measurable_nigDensity p).mul (hum.comp measurable_snd)).aestronglyMeasurable
  refine (integrable_prod_iff' hmeas).mpr ⟨ae_of_all _ fun x => ?_, ?_⟩
  · by_cases hx : 0 < x
    · simp only [nigDensity]
      exact ((integrable_normalDensity _ _ (div_pos hx p.nu_pos)).const_mul _).mul_const _
    · simp [nigDensity, inverseGammaDensity_of_nonpos _ _ _ hx]
  · have hfun : (fun x => ∫ m, ‖nigDensity p (m, x) * u x‖)
        = fun x => ‖inverseGammaDensity p.alpha p.beta x * u x‖ := by
      funext x
      by_cases hx : 0 < x
      · have hIG := inverseGammaDensity_nonneg p.alpha p.beta x p.alpha_pos p.beta_pos.le
        have hnorm : (fun m => ‖nigDensity p (m, x) * u x‖)
            = fun m => (inverseGammaDensity p.alpha p.beta x * |u x|)
                * normalDensity p.gamma (x / p.nu) m := by
          funext m
          simp only [nigDensity, Real.norm_eq_abs, abs_mul, abs_of_nonneg hIG,
            abs_of_nonneg (normalDensity_nonneg _ _ _)]
          ring
        rw [hnorm, integral_const_mul, integral_normalDensity _ _ (div_pos hx p.nu_pos), mul_one,
          Real.norm_eq_abs, abs_mul, abs_of_nonneg hIG]
      · simp [nigDensity, inverseGammaDensity_of_nonpos _ _ _ hx]
    rw [hfun]
    exact hu.norm

/-- Fubini for a function of `σ²` only against the NIG density: the integral. -/
lemma integral_nig_mul_snd {u : ℝ → ℝ} (hum : Measurable u)
    (hu : Integrable (fun x => inverseGammaDensity p.alpha p.beta x * u x)) :
    ∫ q : ℝ × ℝ, nigDensity p q * u q.2 = ∫ x, inverseGammaDensity p.alpha p.beta x * u x := by
  have hint := integrable_nig_mul_snd p hum hu
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod_symm _ hint]
  congr 1
  funext x
  by_cases hx : 0 < x
  · simp only [nigDensity]
    rw [integral_mul_const, integral_const_mul, integral_normalDensity _ _ (div_pos hx p.nu_pos),
      mul_one]
  · simp [nigDensity, inverseGammaDensity_of_nonpos _ _ _ hx]

/-- Fubini for `w(σ²) (μ − c)²` against the NIG density: integrability. -/
lemma integrable_nig_mul_sq {w : ℝ → ℝ} (hwm : Measurable w) (c : ℝ)
    (hw : Integrable (fun x => inverseGammaDensity p.alpha p.beta x * w x
      * (x / p.nu + (p.gamma - c) ^ 2))) :
    Integrable (fun q : ℝ × ℝ => nigDensity p q * (w q.2 * (q.1 - c) ^ 2)) := by
  rw [Measure.volume_eq_prod]
  have hmeas : AEStronglyMeasurable (fun q : ℝ × ℝ => nigDensity p q * (w q.2 * (q.1 - c) ^ 2))
      (volume.prod volume) := by
    have := measurable_nigDensity p
    exact (this.mul ((hwm.comp measurable_snd).mul
      ((measurable_fst.sub measurable_const).pow_const 2))).aestronglyMeasurable
  refine (integrable_prod_iff' hmeas).mpr ⟨ae_of_all _ fun x => ?_, ?_⟩
  · by_cases hx : 0 < x
    · have h := (integrable_normalDensity_mul_sq_sub p.gamma c _ (div_pos hx p.nu_pos)).const_mul
        (inverseGammaDensity p.alpha p.beta x * w x)
      refine h.congr (ae_of_all _ fun m => ?_)
      simp only [nigDensity]
      ring
    · simp [nigDensity, inverseGammaDensity_of_nonpos _ _ _ hx]
  · have hfun : (fun x => ∫ m, ‖nigDensity p (m, x) * (w x * (m - c) ^ 2)‖)
        = fun x => ‖inverseGammaDensity p.alpha p.beta x * w x
            * (x / p.nu + (p.gamma - c) ^ 2)‖ := by
      funext x
      by_cases hx : 0 < x
      · have hIG := inverseGammaDensity_nonneg p.alpha p.beta x p.alpha_pos p.beta_pos.le
        have hq : 0 ≤ x / p.nu + (p.gamma - c) ^ 2 := by
          have := div_pos hx p.nu_pos; positivity
        have hnorm : (fun m => ‖nigDensity p (m, x) * (w x * (m - c) ^ 2)‖)
            = fun m => (inverseGammaDensity p.alpha p.beta x * |w x|)
                * (normalDensity p.gamma (x / p.nu) m * (m - c) ^ 2) := by
          funext m
          simp only [nigDensity, Real.norm_eq_abs, abs_mul, abs_of_nonneg hIG,
            abs_of_nonneg (normalDensity_nonneg _ _ _), abs_of_nonneg (sq_nonneg (m - c))]
          ring
        rw [hnorm, integral_const_mul,
          integral_normalDensity_mul_sq_sub _ _ _ (div_pos hx p.nu_pos),
          Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hIG, abs_of_nonneg hq]
      · simp [nigDensity, inverseGammaDensity_of_nonpos _ _ _ hx]
    rw [hfun]
    exact hw.norm

/-- Fubini for `w(σ²) (μ − c)²` against the NIG density: the integral. -/
lemma integral_nig_mul_sq {w : ℝ → ℝ} (hwm : Measurable w) (c : ℝ)
    (hw : Integrable (fun x => inverseGammaDensity p.alpha p.beta x * w x
      * (x / p.nu + (p.gamma - c) ^ 2))) :
    ∫ q : ℝ × ℝ, nigDensity p q * (w q.2 * (q.1 - c) ^ 2)
      = ∫ x, inverseGammaDensity p.alpha p.beta x * w x * (x / p.nu + (p.gamma - c) ^ 2) := by
  have hint := integrable_nig_mul_sq p hwm c hw
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod_symm _ hint]
  congr 1
  funext x
  by_cases hx : 0 < x
  · have h : (fun m => nigDensity p (m, x) * (w x * (m - c) ^ 2))
        = fun m => (inverseGammaDensity p.alpha p.beta x * w x)
            * (normalDensity p.gamma (x / p.nu) m * (m - c) ^ 2) := by
      funext m
      simp only [nigDensity]
      ring
    rw [h, integral_const_mul, integral_normalDensity_mul_sq_sub _ _ _ (div_pos hx p.nu_pos)]
  · simp [nigDensity, inverseGammaDensity_of_nonpos _ _ _ hx]

end Fubini

section LogRatio

lemma log_inverseGammaDensity (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    Real.log (inverseGammaDensity a b x)
      = a * Real.log b - Real.log (Real.Gamma a) - (a + 1) * Real.log x - b * x⁻¹ := by
  have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have h1 : 0 < b ^ a := Real.rpow_pos_of_pos hb a
  have h2 : 0 < x ^ (-a - 1) := Real.rpow_pos_of_pos hx _
  simp only [inverseGammaDensity, hx, ↓reduceIte, Real.rpow_eq_pow]
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul (by positivity) h2.ne',
    Real.log_div h1.ne' hG.ne', Real.log_rpow hb, Real.log_rpow hx, Real.log_exp]
  ring

lemma log_normalDensity (m v z : ℝ) (hv : 0 < v) :
    Real.log (normalDensity m v z)
      = -(1 / 2) * (Real.log 2 + Real.log Real.pi + Real.log v) - (z - m) ^ 2 * (2 * v)⁻¹ := by
  have hs : 0 < Real.sqrt (2 * Real.pi * v) := Real.sqrt_pos.mpr (by positivity)
  simp only [normalDensity]
  rw [Real.log_mul (inv_pos.mpr hs).ne' (Real.exp_pos _).ne', Real.log_inv, Real.log_exp,
    Real.log_sqrt (by positivity), Real.log_mul (by positivity) hv.ne',
    Real.log_mul (by norm_num) Real.pi_pos.ne']
  ring

/-- The part of the log density ratio depending only on `σ² = x`. -/
def klTermU (p p₀ : Parameters) (x : ℝ) : ℝ :=
  (p.alpha * Real.log p.beta - p₀.alpha * Real.log p₀.beta)
    - (Real.log (Real.Gamma p.alpha) - Real.log (Real.Gamma p₀.alpha))
    + (1 / 2) * (Real.log p.nu - Real.log p₀.nu)
    - (p.alpha - p₀.alpha) * Real.log x - (p.beta - p₀.beta) * x⁻¹

/-- For `σ² = x > 0`, the log ratio of the two NIG densities. -/
lemma log_nigDensity_ratio (p p₀ : Parameters) (m x : ℝ) (hx : 0 < x) :
    Real.log (nigDensity p (m, x) / nigDensity p₀ (m, x))
      = klTermU p p₀ x + (-(p.nu / 2) * x⁻¹) * (m - p.gamma) ^ 2
          + ((p₀.nu / 2) * x⁻¹) * (m - p₀.gamma) ^ 2 := by
  have hIG : ∀ q : Parameters, 0 < inverseGammaDensity q.alpha q.beta x := fun q => by
    have hG : 0 < Real.Gamma q.alpha := Real.Gamma_pos_of_pos q.alpha_pos
    simp only [inverseGammaDensity, hx, ↓reduceIte, Real.rpow_eq_pow]
    have := Real.rpow_pos_of_pos q.beta_pos q.alpha
    have := Real.rpow_pos_of_pos hx (-q.alpha - 1)
    positivity
  have hN : ∀ q : Parameters, 0 < normalDensity q.gamma (x / q.nu) m := fun q => by
    have hs : 0 < Real.sqrt (2 * Real.pi * (x / q.nu)) :=
      Real.sqrt_pos.mpr (by have := div_pos hx q.nu_pos; positivity)
    simp only [normalDensity]
    exact mul_pos (inv_pos.mpr hs) (Real.exp_pos _)
  simp only [nigDensity]
  rw [Real.log_div (mul_pos (hIG p) (hN p)).ne' (mul_pos (hIG p₀) (hN p₀)).ne',
    Real.log_mul (hIG p).ne' (hN p).ne', Real.log_mul (hIG p₀).ne' (hN p₀).ne',
    log_inverseGammaDensity _ _ _ p.alpha_pos p.beta_pos hx,
    log_inverseGammaDensity _ _ _ p₀.alpha_pos p₀.beta_pos hx,
    log_normalDensity _ _ _ (div_pos hx p.nu_pos), log_normalDensity _ _ _ (div_pos hx p₀.nu_pos),
    Real.log_div hx.ne' p.nu_pos.ne', Real.log_div hx.ne' p₀.nu_pos.ne']
  unfold klTermU
  have hx0 := hx.ne'
  have hn0 := p.nu_pos.ne'
  have hn00 := p₀.nu_pos.ne'
  field_simp
  ring

end LogRatio

/-- The explicit value of `K(γ,ν,α,β) = KL[NIG(γ,ν,α,β) ‖ p₀]`, with
`A = α₀`, `n = ν₀`, `δ = γ − γ₀` and `ψ` the digamma function. -/
def nigKLClosedForm (p p₀ : Parameters) : ℝ :=
  p₀.alpha * Real.log (p.beta / p₀.beta)
    + Real.log (Real.Gamma p₀.alpha / Real.Gamma p.alpha)
    + (p.alpha - p₀.alpha) * digamma p.alpha - p.alpha + p.alpha * p₀.beta / p.beta
    + (1 / 2) * (p₀.nu / p.nu - 1 + Real.log (p.nu / p₀.nu)
      + p₀.nu * p.alpha * (p.gamma - p₀.gamma) ^ 2 / p.beta)

section Divergence

variable (p p₀ : Parameters)

lemma integral_inverseGammaDensity_params :
    ∫ x, inverseGammaDensity p.alpha p.beta x = 1 :=
  integral_inverseGammaDensity ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩

lemma measurable_klTermU : Measurable (klTermU p p₀) := by
  unfold klTermU
  fun_prop

private lemma igDensity_mul_inv_integrable :
    Integrable (fun x => inverseGammaDensity p.alpha p.beta x * x⁻¹) :=
  (integrable_inverseGammaLaw_iff ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩ _).mp
    (inverseGamma_integrable_inv _ _)

private lemma igDensity_mul_log_integrable :
    Integrable (fun x => inverseGammaDensity p.alpha p.beta x * Real.log x) :=
  (integrable_inverseGammaLaw_iff ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩ _).mp
    (inverseGamma_integrable_log _ _)

private lemma igDensity_integral_inv :
    ∫ x, inverseGammaDensity p.alpha p.beta x * x⁻¹ = p.alpha / p.beta := by
  rw [← integral_inverseGammaLaw ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩ (fun x => x⁻¹)]
  exact inverseGamma_integral_inv _ _

private lemma igDensity_integral_log :
    ∫ x, inverseGammaDensity p.alpha p.beta x * Real.log x
      = Real.log p.beta - digamma p.alpha := by
  rw [← integral_inverseGammaLaw ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩ Real.log]
  exact inverseGamma_integral_log _ _

private lemma igDensity_mul_klTermU_integrable :
    Integrable (fun x => inverseGammaDensity p.alpha p.beta x * klTermU p p₀ x) := by
  have h1 := integrable_inverseGammaDensity ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩
  have h2 := igDensity_mul_log_integrable p
  have h3 := igDensity_mul_inv_integrable p
  have h := ((h1.const_mul ((p.alpha * Real.log p.beta - p₀.alpha * Real.log p₀.beta)
    - (Real.log (Real.Gamma p.alpha) - Real.log (Real.Gamma p₀.alpha))
    + (1 / 2) * (Real.log p.nu - Real.log p₀.nu))).sub (h2.const_mul (p.alpha - p₀.alpha))).sub
    (h3.const_mul (p.beta - p₀.beta))
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [klTermU, Pi.sub_apply]
  ring

private lemma igDensity_integral_klTermU :
    ∫ x, inverseGammaDensity p.alpha p.beta x * klTermU p p₀ x
      = (p.alpha * Real.log p.beta - p₀.alpha * Real.log p₀.beta)
        - (Real.log (Real.Gamma p.alpha) - Real.log (Real.Gamma p₀.alpha))
        + (1 / 2) * (Real.log p.nu - Real.log p₀.nu)
        - (p.alpha - p₀.alpha) * (Real.log p.beta - digamma p.alpha)
        - (p.beta - p₀.beta) * (p.alpha / p.beta) := by
  have h1 := integrable_inverseGammaDensity ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩
  have h2 := igDensity_mul_log_integrable p
  have h3 := igDensity_mul_inv_integrable p
  set C := (p.alpha * Real.log p.beta - p₀.alpha * Real.log p₀.beta)
    - (Real.log (Real.Gamma p.alpha) - Real.log (Real.Gamma p₀.alpha))
    + (1 / 2) * (Real.log p.nu - Real.log p₀.nu) with hC
  have hfun : (fun x => inverseGammaDensity p.alpha p.beta x * klTermU p p₀ x)
      = fun x => (C * inverseGammaDensity p.alpha p.beta x
          - (p.alpha - p₀.alpha) * (inverseGammaDensity p.alpha p.beta x * Real.log x))
          - (p.beta - p₀.beta) * (inverseGammaDensity p.alpha p.beta x * x⁻¹) := by
    funext x
    simp only [klTermU, hC]
    ring
  have i1 : Integrable (fun x => C * inverseGammaDensity p.alpha p.beta x) := h1.const_mul C
  have i2 : Integrable (fun x => (p.alpha - p₀.alpha)
      * (inverseGammaDensity p.alpha p.beta x * Real.log x)) := h2.const_mul _
  have i3 : Integrable (fun x => (p.beta - p₀.beta)
      * (inverseGammaDensity p.alpha p.beta x * x⁻¹)) := h3.const_mul _
  have i12 : Integrable (fun x => C * inverseGammaDensity p.alpha p.beta x
      - (p.alpha - p₀.alpha) * (inverseGammaDensity p.alpha p.beta x * Real.log x)) := i1.sub i2
  rw [hfun, integral_sub i12 i3, integral_sub i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_inverseGammaDensity_params, igDensity_integral_log,
    igDensity_integral_inv, mul_one]

private lemma w1_pointwise (x : ℝ) :
    inverseGammaDensity p.alpha p.beta x * (-(p.nu / 2) * x⁻¹)
        * (x / p.nu + (p.gamma - p.gamma) ^ 2)
      = -(1 / 2) * inverseGammaDensity p.alpha p.beta x := by
  by_cases hx : x = 0
  · simp [hx, inverseGammaDensity_of_nonpos _ _ _ (lt_irrefl 0)]
  · have hn := p.nu_pos.ne'
    simp only [sub_self]
    field_simp
    ring

private lemma w2_pointwise (x : ℝ) :
    inverseGammaDensity p.alpha p.beta x * ((p₀.nu / 2) * x⁻¹)
        * (x / p.nu + (p.gamma - p₀.gamma) ^ 2)
      = p₀.nu / (2 * p.nu) * inverseGammaDensity p.alpha p.beta x
        + p₀.nu / 2 * (p.gamma - p₀.gamma) ^ 2 * (inverseGammaDensity p.alpha p.beta x * x⁻¹) := by
  by_cases hx : x = 0
  · simp [hx, inverseGammaDensity_of_nonpos _ _ _ (lt_irrefl 0)]
  · have hn := p.nu_pos.ne'
    field_simp

private lemma w1_integrable :
    Integrable (fun x => inverseGammaDensity p.alpha p.beta x * (-(p.nu / 2) * x⁻¹)
      * (x / p.nu + (p.gamma - p.gamma) ^ 2)) :=
  ((integrable_inverseGammaDensity ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩).const_mul
    (-(1 / 2) : ℝ)).congr (ae_of_all _ fun x => (w1_pointwise p x).symm)

private lemma w1_integral :
    ∫ x, inverseGammaDensity p.alpha p.beta x * (-(p.nu / 2) * x⁻¹)
      * (x / p.nu + (p.gamma - p.gamma) ^ 2) = -(1 / 2) := by
  simp_rw [w1_pointwise p]
  rw [integral_const_mul, integral_inverseGammaDensity_params, mul_one]

private lemma w2_integrable :
    Integrable (fun x => inverseGammaDensity p.alpha p.beta x * ((p₀.nu / 2) * x⁻¹)
      * (x / p.nu + (p.gamma - p₀.gamma) ^ 2)) :=
  (((integrable_inverseGammaDensity ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩).const_mul
    (p₀.nu / (2 * p.nu))).add ((igDensity_mul_inv_integrable p).const_mul
    (p₀.nu / 2 * (p.gamma - p₀.gamma) ^ 2))).congr
    (ae_of_all _ fun x => (w2_pointwise p p₀ x).symm)

private lemma w2_integral :
    ∫ x, inverseGammaDensity p.alpha p.beta x * ((p₀.nu / 2) * x⁻¹)
      * (x / p.nu + (p.gamma - p₀.gamma) ^ 2)
      = p₀.nu / (2 * p.nu) + p₀.nu / 2 * (p.gamma - p₀.gamma) ^ 2 * (p.alpha / p.beta) := by
  simp_rw [w2_pointwise p p₀]
  have i1 : Integrable (fun x => p₀.nu / (2 * p.nu) * inverseGammaDensity p.alpha p.beta x) :=
    (integrable_inverseGammaDensity ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩).const_mul _
  have i2 : Integrable (fun x => p₀.nu / 2 * (p.gamma - p₀.gamma) ^ 2
      * (inverseGammaDensity p.alpha p.beta x * x⁻¹)) :=
    (igDensity_mul_inv_integrable p).const_mul _
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_inverseGammaDensity_params, igDensity_integral_inv, mul_one]

/-- The integrand `f · log (f/g)` agrees everywhere with its explicit form. -/
private lemma nig_mul_logRatio_eq (q : ℝ × ℝ) :
    nigDensity p q * Real.log (nigDensity p q / nigDensity p₀ q)
      = nigDensity p q * klTermU p p₀ q.2
        + nigDensity p q * ((-(p.nu / 2) * q.2⁻¹) * (q.1 - p.gamma) ^ 2)
        + nigDensity p q * (((p₀.nu / 2) * q.2⁻¹) * (q.1 - p₀.gamma) ^ 2) := by
  by_cases hx : 0 < q.2
  · have h := log_nigDensity_ratio p p₀ q.1 q.2 hx
    rw [show ((q.1, q.2) : ℝ × ℝ) = q from rfl] at h
    rw [h]
    ring
  · simp [nigDensity_of_nonpos p q hx]

/-- The complete hierarchical forward divergence is finite: its
log-density-ratio integrand is integrable under `NIG(γ,ν,α,β)`. -/
theorem integrable_nigLogRatio :
    Integrable (fun h => Real.log (nigDensity p h / nigDensity p₀ h)) (nigLaw p) := by
  have hmeas : Measurable fun q => ENNReal.ofReal (nigDensity p q) :=
    (measurable_nigDensity p).ennreal_ofReal
  rw [nigLaw, integrable_withDensity_iff_integrable_smul' hmeas
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hU := integrable_nig_mul_snd p (measurable_klTermU p p₀)
    (igDensity_mul_klTermU_integrable p p₀)
  have hW1 := integrable_nig_mul_sq p (w := fun x => -(p.nu / 2) * x⁻¹) (by fun_prop) p.gamma
    (w1_integrable p)
  have hW2 := integrable_nig_mul_sq p (w := fun x => (p₀.nu / 2) * x⁻¹) (by fun_prop) p₀.gamma
    (w2_integrable p p₀)
  refine ((hU.add hW1).add hW2).congr (ae_of_all _ fun q => ?_)
  simp only [Pi.add_apply, smul_eq_mul,
    ENNReal.toReal_ofReal (nigDensity_nonneg p q)]
  rw [nig_mul_logRatio_eq]

/-- The complete hierarchical forward divergence equals the explicit
expression `K(γ,ν,α,β)`. -/
theorem hierarchicalKL_eq_closedForm :
    hierarchicalKL p p₀ = nigKLClosedForm p p₀ := by
  have hmeas : Measurable fun q => ENNReal.ofReal (nigDensity p q) :=
    (measurable_nigDensity p).ennreal_ofReal
  have hU := integrable_nig_mul_snd p (measurable_klTermU p p₀)
    (igDensity_mul_klTermU_integrable p p₀)
  have hW1 := integrable_nig_mul_sq p (w := fun x => -(p.nu / 2) * x⁻¹) (by fun_prop) p.gamma
    (w1_integrable p)
  have hW2 := integrable_nig_mul_sq p (w := fun x => (p₀.nu / 2) * x⁻¹) (by fun_prop) p₀.gamma
    (w2_integrable p p₀)
  rw [hierarchicalKL, nigLaw, integral_withDensity_eq_integral_toReal_smul hmeas
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hfun : (fun q => (ENNReal.ofReal (nigDensity p q)).toReal
      • Real.log (nigDensity p q / nigDensity p₀ q))
      = fun q => nigDensity p q * klTermU p p₀ q.2
        + nigDensity p q * ((-(p.nu / 2) * q.2⁻¹) * (q.1 - p.gamma) ^ 2)
        + nigDensity p q * (((p₀.nu / 2) * q.2⁻¹) * (q.1 - p₀.gamma) ^ 2) := by
    funext q
    rw [smul_eq_mul, ENNReal.toReal_ofReal (nigDensity_nonneg p q), nig_mul_logRatio_eq]
  have hUW : Integrable (fun q : ℝ × ℝ => nigDensity p q * klTermU p p₀ q.2
      + nigDensity p q * ((-(p.nu / 2) * q.2⁻¹) * (q.1 - p.gamma) ^ 2)) := hU.add hW1
  rw [hfun, integral_add hUW hW2, integral_add hU hW1,
    integral_nig_mul_snd p (measurable_klTermU p p₀) (igDensity_mul_klTermU_integrable p p₀),
    integral_nig_mul_sq p (w := fun x => -(p.nu / 2) * x⁻¹) (by fun_prop) p.gamma
      (w1_integrable p),
    integral_nig_mul_sq p (w := fun x => (p₀.nu / 2) * x⁻¹) (by fun_prop) p₀.gamma
      (w2_integrable p p₀),
    igDensity_integral_klTermU, w1_integral, w2_integral]
  have hb := p.beta_pos.ne'
  have hn := p.nu_pos.ne'
  have hG := (Real.Gamma_pos_of_pos p.alpha_pos).ne'
  have hG0 := (Real.Gamma_pos_of_pos p₀.alpha_pos).ne'
  rw [nigKLClosedForm, Real.log_div hb p₀.beta_pos.ne', Real.log_div hG0 hG,
    Real.log_div hn p₀.nu_pos.ne']
  field_simp
  ring

/-- `B = β₀ + (n/2) δ²` with `n = ν₀` and `δ = γ − γ₀`. -/
def priorB (p₀ : Parameters) (x : QuotientState) : ℝ :=
  p₀.beta + p₀.nu / 2 * (x.gamma - p₀.gamma) ^ 2

/-- `B > 0`. -/
theorem priorB_pos (p₀ : Parameters) (x : QuotientState) : 0 < priorB p₀ x := by
  have := p₀.beta_pos
  have := p₀.nu_pos
  unfold priorB
  positivity

/-- The divergence on the fiber `F_x`,
`F(x,t) = K(γ, 1/t, α, s/(1+t))` for `t > 0`. -/
def fiberKL (p₀ : Parameters) (x : QuotientState) (t : PositiveReal) : ℝ :=
  hierarchicalKL (fiberParameters x t) p₀

/-- The explicit right-hand side of the fiber formula, as a real function
of `t`. -/
def fiberKLFormula (p₀ : Parameters) (x : QuotientState) (t : ℝ) : ℝ :=
  p₀.alpha * Real.log (x.s / p₀.beta) + Real.log (Real.Gamma p₀.alpha / Real.Gamma x.alpha)
    + (x.alpha - p₀.alpha) * digamma x.alpha - x.alpha - p₀.alpha * Real.log (1 + t)
    + x.alpha * priorB p₀ x / x.s * (1 + t) + (1 / 2) * (p₀.nu * t - 1 - Real.log (p₀.nu * t))

/-- On the fiber, the divergence is
`F(x,t) = A log(s/β₀) + log(Γ(A)/Γ(α)) + (α−A)ψ(α) − α − A log(1+t) + (αB/s)(1+t)
 + ½ [n t − 1 − log(n t)]`, `t > 0`. -/
theorem fiberKL_eq (p₀ : Parameters) (x : QuotientState) (t : PositiveReal) :
    fiberKL p₀ x t = fiberKLFormula p₀ x t := by
  have ht : 0 < (t : ℝ) := t.property
  have h1t : 0 < 1 + (t : ℝ) := by linarith
  have hs := x.s_pos
  have hb0 := p₀.beta_pos
  have hn0 := p₀.nu_pos
  rw [fiberKL, hierarchicalKL_eq_closedForm, nigKLClosedForm, fiberKLFormula, priorB]
  simp only [fiberParameters]
  rw [Real.log_div (div_pos hs h1t).ne' hb0.ne', Real.log_div hs.ne' h1t.ne',
    Real.log_div (one_div_pos.mpr ht).ne' hn0.ne', Real.log_div hs.ne' hb0.ne',
    Real.log_mul hn0.ne' ht.ne',
    show Real.log (1 / (t : ℝ)) = -Real.log t by rw [one_div, Real.log_inv]]
  field_simp
  ring

end Divergence

end NIGBottleneck
