import Mathlib

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# KL divergence between density measures; Gaussian density moments

* `klDiv_withDensity_ofReal`: for probability densities `f, g` with respect to a
  σ-finite measure `m` such that `f > 0 ⇒ g > 0`,
  `KL(f·m ‖ g·m) = ∫ f log(f/g) dm` (mathlib's `InformationTheory.klDiv`);
* `integral_mul_log_div_nonneg`: Gibbs' inequality `∫ f log(f/g) dm ≥ 0`.
* Gaussian moments in density form:
  `∫ N(z; m, v)(z − c)² dz = v + (m − c)²`, with integrability.
-/

namespace ELVAE

open MeasureTheory ProbabilityTheory Real Set InformationTheory
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]


/-- A density measure `f·m` is concentrated where `f > 0`. -/
lemma ae_withDensity_ofReal_pos (m : Measure X) {f : X → ℝ} (hf : Measurable f) :
    ∀ᵐ x ∂(m.withDensity fun x => ENNReal.ofReal (f x)), 0 < f x := by
  rw [ae_withDensity_iff hf.ennreal_ofReal]
  exact ae_of_all _ fun x hx => by
    by_contra h
    exact hx (ENNReal.ofReal_eq_zero.mpr (not_lt.mp h))

/--
KL divergence between two density measures `f·m` and `g·m` of probability
laws, where `f > 0 ⇒ g > 0`:

  KL(f·m ‖ g·m) = ∫ f log(f/g) dm.
-/
theorem llr_withDensity_ofReal (m : Measure X) [SigmaFinite m] {f g : X → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x)
    (hfg : ∀ x, 0 < f x → 0 < g x)
    (hint : Integrable (fun x => f x * Real.log (f x / g x)) m) :
    (m.withDensity fun x => ENNReal.ofReal (f x)) ≪ (m.withDensity fun x => ENNReal.ofReal (g x))
    ∧ Integrable (llr (m.withDensity fun x => ENNReal.ofReal (f x))
        (m.withDensity fun x => ENNReal.ofReal (g x))) (m.withDensity fun x => ENNReal.ofReal (f x))
    ∧ ∫ x, llr (m.withDensity fun x => ENNReal.ofReal (f x))
        (m.withDensity fun x => ENNReal.ofReal (g x)) x
          ∂(m.withDensity fun x => ENNReal.ofReal (f x))
      = ∫ x, f x * Real.log (f x / g x) ∂m := by
  set μ := m.withDensity fun x => ENNReal.ofReal (f x) with hμ
  set ν := m.withDensity fun x => ENNReal.ofReal (g x) with hν
  have hF : Measurable fun x => ENNReal.ofReal (f x) := hf.ennreal_ofReal
  have hG : Measurable fun x => ENNReal.ofReal (g x) := hg.ennreal_ofReal
  -- absolute continuity
  have hac : μ ≪ ν := by
    refine Measure.AbsolutelyContinuous.mk fun s hs hνs => ?_
    rw [hν, withDensity_apply _ hs, lintegral_eq_zero_iff hG] at hνs
    rw [hμ, withDensity_apply _ hs, lintegral_eq_zero_iff hF]
    filter_upwards [hνs] with x hx
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hx ⊢
    by_contra h
    exact absurd (hfg x (not_le.mp h)) (not_lt.mpr hx)
  have hμm : μ ≪ m := withDensity_absolutelyContinuous m _
  have hνm : ν ≪ m := withDensity_absolutelyContinuous m _
  -- the log-likelihood ratio
  have hrn : μ.rnDeriv ν =ᵐ[μ] fun x => ENNReal.ofReal (f x) / ENNReal.ofReal (g x) := by
    have h1 := Measure.rnDeriv_eq_div hμm hνm
    have h2 : μ.rnDeriv m =ᵐ[m] fun x => ENNReal.ofReal (f x) := Measure.rnDeriv_withDensity m hF
    have h3 : ν.rnDeriv m =ᵐ[m] fun x => ENNReal.ofReal (g x) := Measure.rnDeriv_withDensity m hG
    refine hac.ae_le ?_
    filter_upwards [h1, hνm.ae_le h2, hνm.ae_le h3] with x hx1 hx2 hx3
    rw [hx1, hx2, hx3]
  have hllr : llr μ ν =ᵐ[μ] fun x => Real.log (f x / g x) := by
    filter_upwards [hrn, ae_withDensity_ofReal_pos m hf] with x hx hpos
    have hgpos := hfg x hpos
    rw [llr_def]
    simp only
    rw [hx, ENNReal.toReal_div, ENNReal.toReal_ofReal hpos.le, ENNReal.toReal_ofReal hgpos.le]
  have hsmul : ∀ x, (ENNReal.ofReal (f x)).toReal • Real.log (f x / g x)
      = f x * Real.log (f x / g x) := fun x => by
    rw [ENNReal.toReal_ofReal (hf0 x), smul_eq_mul]
  have hint' : Integrable (llr μ ν) μ := by
    refine (integrable_congr hllr).mpr ?_
    rw [hμ, integrable_withDensity_iff_integrable_smul' hF
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp_rw [hsmul]
    exact hint
  refine ⟨hac, hint', ?_⟩
  rw [integral_congr_ae hllr, hμ,
    integral_withDensity_eq_integral_toReal_smul hF (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [hsmul]

/--
KL divergence between two density measures `f·m` and `g·m` of probability
laws, where `f > 0 ⇒ g > 0`:

  KL(f·m ‖ g·m) = ∫ f log(f/g) dm.
-/
theorem klDiv_withDensity_ofReal (m : Measure X) [SigmaFinite m] {f g : X → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x)
    (hfg : ∀ x, 0 < f x → 0 < g x)
    [IsProbabilityMeasure (m.withDensity fun x => ENNReal.ofReal (f x))]
    [IsProbabilityMeasure (m.withDensity fun x => ENNReal.ofReal (g x))]
    (hint : Integrable (fun x => f x * Real.log (f x / g x)) m) :
    klDiv (m.withDensity fun x => ENNReal.ofReal (f x))
        (m.withDensity fun x => ENNReal.ofReal (g x))
      = ENNReal.ofReal (∫ x, f x * Real.log (f x / g x) ∂m) := by
  obtain ⟨hac, hint', hval⟩ := llr_withDensity_ofReal m hf hg hf0 hfg hint
  rw [klDiv_of_ac_of_integrable hac hint', hval]
  simp [measureReal_def]

/-- **Gibbs inequality** in density form: `∫ f log(f/g) dm ≥ 0`. -/
theorem integral_mul_log_div_nonneg (m : Measure X) [SigmaFinite m] {f g : X → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x)
    (hfg : ∀ x, 0 < f x → 0 < g x)
    [IsProbabilityMeasure (m.withDensity fun x => ENNReal.ofReal (f x))]
    [IsProbabilityMeasure (m.withDensity fun x => ENNReal.ofReal (g x))]
    (hint : Integrable (fun x => f x * Real.log (f x / g x)) m) :
    0 ≤ ∫ x, f x * Real.log (f x / g x) ∂m := by
  obtain ⟨hac, hint', hval⟩ := llr_withDensity_ofReal m hf hg hf0 hfg hint
  have h := integral_llr_add_sub_measure_univ_nonneg hac hint'
  rw [hval] at h
  simpa [measureReal_def] using h

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

lemma gaussianPDFReal_toNNReal_pos {m v z : ℝ} (hv : 0 < v) :
    0 < gaussianPDFReal m v.toNNReal z :=
  gaussianPDFReal_pos _ _ _ (by simpa using hv)

/-- Density form: `∫ N(z; m, v) (z − c)² dz = v + (m − c)²`. -/
lemma integral_gaussianPDFReal_mul_sq_sub (m c : ℝ) {v : ℝ} (hv : 0 < v) :
    ∫ z, gaussianPDFReal m v.toNNReal z * (z - c) ^ 2 = v + (m - c) ^ 2 := by
  have hv' : v.toNNReal ≠ 0 := by simpa using hv
  have := integral_gaussianReal_eq_integral_smul (f := fun z => (z - c) ^ 2) (μ := m) hv'
  simp only [smul_eq_mul] at this
  rw [← this, integral_sq_sub_gaussianReal, Real.coe_toNNReal _ hv.le]

lemma integrable_gaussianPDFReal_mul_sq_sub (m c : ℝ) {v : ℝ} (hv : 0 < v) :
    Integrable (fun z => gaussianPDFReal m v.toNNReal z * (z - c) ^ 2) := by
  have hv' : v.toNNReal ≠ 0 := by simpa using hv
  have h := integrable_sq_sub_gaussianReal m c v.toNNReal
  rw [gaussianReal_of_var_ne_zero _ hv', integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (ae_of_all _ fun _ => gaussianPDF_lt_top)] at h
  simpa [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)] using h

end ELVAE
