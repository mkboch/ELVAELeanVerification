import Mathlib
import ELVAELeanVerification.NIGKLDivergence
import ELVAELeanVerification.NIGStudentTMarginal

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Consistency of the two NIG constructions

`NIGStudentTMarginal` builds the NIG hierarchy with `Measure.bind`
(`σ² ~ InvGamma(α, β)`, `μ | σ² ~ N(γ, σ²/ν)`), while `NIGKLDivergence` defines the
joint NIG law `nigMeasure` of `(σ², μ)` through its density. This module checks
that both describe the same law:

* `nigMeasure_map_fst`: the `σ²`-marginal of `nigMeasure` is `invGammaMeasure α β`;
* `nigMeasure_map_snd`: the `μ`-marginal of `nigMeasure` is `nigMuMarginal`,
  hence Student-t by `nigMuMarginal_eq_studentT`.
-/

namespace ELVAE

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

variable {gamma nu alpha beta : ℝ}

/-- Inner `μ`-integral of the density over a measurable set. -/
lemma lintegral_nigPrecPDF_section (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta)
    {s : Set ℝ} (hs : MeasurableSet s) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      ∫⁻ z, s.indicator (fun z => ENNReal.ofReal (nigPrecPDF gamma nu alpha beta (t, z))) z
        = gammaPDF alpha beta t * gaussianReal gamma (precVar nu t) s := by
  filter_upwards [ae_ne_zero_real] with t ht
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · have h0 : ∀ z, nigPrecPDF gamma nu alpha beta (t, z) = 0 := fun z =>
      nigPrecPDF_of_nonpos hnu (p := (t, z)) hneg.le
    simp [h0, gammaPDF_of_neg hneg]
  · rw [lintegral_indicator hs, gaussianReal_apply _ (precVar_ne_zero hnu hpos)]
    simp only [nigPrecPDF]
    simp_rw [ENNReal.ofReal_mul (gammaPDFReal_nonneg halpha hbeta t)]
    rw [lintegral_const_mul _ (measurable_gaussianPDFReal _ _).ennreal_ofReal, gammaPDF]
    rfl

/-- The `τ`-marginal of the precision-form law is `Gamma(α, β)`. -/
lemma nigPrecMeasure_map_fst (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta) :
    (nigPrecMeasure gamma nu alpha beta).map Prod.fst = gammaMeasure alpha beta := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs, nigPrecMeasure,
    withDensity_apply _ (measurable_fst hs), gammaMeasure, withDensity_apply _ hs,
    ← lintegral_indicator (measurable_fst hs), ← lintegral_indicator hs,
    Measure.volume_eq_prod, lintegral_prod _
      (((measurable_nigPrecPDF _ _ _ _).ennreal_ofReal.indicator
        (measurable_fst hs)).aemeasurable)]
  have h : ∀ᵐ t ∂(volume : Measure ℝ),
      ∫⁻ z, (Prod.fst ⁻¹' s).indicator
          (fun p => ENNReal.ofReal (nigPrecPDF gamma nu alpha beta p)) (t, z)
        = s.indicator (gammaPDF alpha beta) t := by
    filter_upwards [lintegral_nigPrecPDF_section (gamma := gamma) hnu halpha hbeta
      MeasurableSet.univ] with t ht
    by_cases hts : t ∈ s
    · simp only [indicator_of_mem hts]
      have hmem : ∀ z : ℝ, (t, z) ∈ Prod.fst ⁻¹' s := fun z => hts
      simp_rw [indicator_of_mem (hmem _)]
      simp only [indicator_univ] at ht
      rw [ht, measure_univ, mul_one]
    · simp only [indicator_of_notMem hts]
      have hmem : ∀ z : ℝ, (t, z) ∉ Prod.fst ⁻¹' s := fun z => hts
      simp_rw [indicator_of_notMem (hmem _)]
      simp
  exact lintegral_congr_ae h

/-- The `μ`-marginal of the precision-form law is the Gamma mixture of Gaussians. -/
lemma nigPrecMeasure_map_snd (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta) :
    (nigPrecMeasure gamma nu alpha beta).map Prod.snd
      = (gammaMeasure alpha beta).bind fun t => gaussianReal gamma (precVar nu t) := by
  have hk : Measurable fun t : ℝ => gaussianReal gamma (precVar nu t) :=
    measurable_gaussianReal.comp (measurable_const.prodMk (measurable_precVar nu))
  have hG : Measurable (gammaPDF alpha beta) := (measurable_gammaPDFReal alpha beta).ennreal_ofReal
  ext s hs
  have hmk : Measurable fun t : ℝ => gaussianReal gamma (precVar nu t) s :=
    (Measure.measurable_coe hs).comp hk
  rw [Measure.map_apply measurable_snd hs, nigPrecMeasure,
    withDensity_apply _ (measurable_snd hs), ← lintegral_indicator (measurable_snd hs),
    Measure.volume_eq_prod, lintegral_prod _
      (((measurable_nigPrecPDF _ _ _ _).ennreal_ofReal.indicator
        (measurable_snd hs)).aemeasurable),
    Measure.bind_apply hs hk.aemeasurable, gammaMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hG hmk]
  refine lintegral_congr_ae ?_
  filter_upwards [lintegral_nigPrecPDF_section (gamma := gamma) hnu halpha hbeta hs] with t ht
  rw [Pi.mul_apply, ← ht]
  rfl

/-- The `σ²`-marginal of the NIG law is `InvGamma(α, β)`. -/
theorem nigMeasure_map_fst (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta) :
    (nigMeasure gamma nu alpha beta).map Prod.fst = invGammaMeasure alpha beta := by
  rw [nigMeasure, Measure.map_map measurable_fst measurable_nigInvolution,
    show (Prod.fst ∘ fun p : ℝ × ℝ => (p.1⁻¹, p.2)) = (fun t : ℝ => t⁻¹) ∘ Prod.fst from rfl,
    ← Measure.map_map measurable_inv measurable_fst, nigPrecMeasure_map_fst hnu halpha hbeta,
    invGammaMeasure]

/-- The `μ`-marginal of the NIG law is the law of `μ` in the NIG hierarchy. -/
theorem nigMeasure_map_snd (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta) :
    (nigMeasure gamma nu alpha beta).map Prod.snd = nigMuMarginal gamma nu alpha beta := by
  rw [nigMeasure, Measure.map_map measurable_snd measurable_nigInvolution,
    show (Prod.snd ∘ fun p : ℝ × ℝ => (p.1⁻¹, p.2)) = Prod.snd from rfl,
    nigPrecMeasure_map_snd hnu halpha hbeta, nigMuMarginal]
  have hk : (fun s : ℝ => gaussianReal gamma (s / nu).toNNReal)
      = fun s => gaussianReal gamma (nu⁻¹ * s).toNNReal := by
    funext s; rw [div_eq_inv_mul]
  rw [hk, invGamma_bind_eq_gamma_bind]
  congr 1
  funext t
  rw [precVar]
  congr 2
  field_simp

end ELVAE
