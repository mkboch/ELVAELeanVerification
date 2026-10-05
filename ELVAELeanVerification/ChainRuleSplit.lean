import Mathlib
import ELVAELeanVerification.ManuscriptForms

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# The chain-rule split of the NIG KL divergence

The NIG KL divergence decomposes through the chain rule:

  D_KL(q ‖ p₀) = D_KL[IG(α, β) ‖ IG(α₀, β₀)]
               + E_{q(σ²)} D_KL[N(γ, σ²/ν) ‖ N(γ₀, σ²/ν₀)].

This module proves each term in closed form with mathlib's `klDiv`, and the
decomposition itself:

* `klDiv_gaussianReal`:
  `D_KL[N(m₁, v₁) ‖ N(m₂, v₂)] = ½(v₁/v₂ − 1 − log(v₁/v₂)) + (m₁ − m₂)²/(2v₂)`;
* `klDiv_gammaMeasure`, `klDiv_invGammaMeasure`: the (inverse-)gamma KL divergence;
* `integral_klDiv_gaussian_invGamma`: the averaged conditional term;
* `klDiv_chain_rule_split`: the sum of the two terms is `D_KL(q ‖ p₀)`.
-/

namespace ELVAE

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped ENNReal NNReal

/-! ## Gaussian KL -/

/-- Closed-form Gaussian KL. -/
noncomputable def gaussKL (m1 v1 m2 v2 : ℝ) : ℝ :=
  (1 / 2) * (v1 / v2 - 1 - Real.log (v1 / v2)) + (m1 - m2) ^ 2 / (2 * v2)

lemma gaussKL_nonneg {m1 v1 m2 v2 : ℝ} (hv1 : 0 < v1) (hv2 : 0 < v2) :
    0 ≤ gaussKL m1 v1 m2 v2 := by
  unfold gaussKL
  have h := Real.log_le_sub_one_of_pos (div_pos hv1 hv2)
  have : 0 ≤ (m1 - m2) ^ 2 / (2 * v2) := by positivity
  nlinarith

lemma integrable_gaussianPDFReal_quadratic (m m2 : ℝ) {v : ℝ} (hv : 0 < v) (A B C : ℝ) :
    Integrable fun x => gaussianPDFReal m v.toNNReal x
        * (A + B * (x - m) ^ 2 + C * (x - m2) ^ 2) := by
  have hN : Integrable (gaussianPDFReal m v.toNNReal) := integrable_gaussianPDFReal _ _
  have h1 := integrable_gaussianPDFReal_mul_sq_sub m m hv
  have h2 := integrable_gaussianPDFReal_mul_sq_sub m m2 hv
  have h := ((hN.const_mul A).add (h1.const_mul B)).add (h2.const_mul C)
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply]
  ring

lemma integral_gaussianPDFReal_quadratic (m m2 : ℝ) {v : ℝ} (hv : 0 < v) (A B C : ℝ) :
    ∫ x, gaussianPDFReal m v.toNNReal x * (A + B * (x - m) ^ 2 + C * (x - m2) ^ 2)
      = A + B * v + C * (v + (m - m2) ^ 2) := by
  have hv' : v.toNNReal ≠ 0 := by simpa using hv
  have hN : Integrable (gaussianPDFReal m v.toNNReal) := integrable_gaussianPDFReal _ _
  have h1 := integrable_gaussianPDFReal_mul_sq_sub m m hv
  have h2 := integrable_gaussianPDFReal_mul_sq_sub m m2 hv
  have hsplit : (fun x => gaussianPDFReal m v.toNNReal x * (A + B * (x - m) ^ 2 + C * (x - m2) ^ 2))
      = fun x => (A * gaussianPDFReal m v.toNNReal x
          + B * (gaussianPDFReal m v.toNNReal x * (x - m) ^ 2))
          + C * (gaussianPDFReal m v.toNNReal x * (x - m2) ^ 2) := by
    funext x; ring
  have hAB : Integrable fun x => A * gaussianPDFReal m v.toNNReal x
      + B * (gaussianPDFReal m v.toNNReal x * (x - m) ^ 2) :=
    (hN.const_mul A).add (h1.const_mul B)
  rw [hsplit, integral_add hAB (h2.const_mul C), integral_add (hN.const_mul A) (h1.const_mul B),
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_gaussianPDFReal_eq_one _ hv', integral_gaussianPDFReal_mul_sq_sub _ _ hv,
    integral_gaussianPDFReal_mul_sq_sub _ _ hv]
  ring

/-- **Gaussian KL.** `D_KL[N(m₁, v₁) ‖ N(m₂, v₂)]` in closed form (`v₁, v₂ > 0`). -/
theorem klDiv_gaussianReal (m1 m2 : ℝ) {v1 v2 : ℝ} (hv1 : 0 < v1) (hv2 : 0 < v2) :
    klDiv (gaussianReal m1 v1.toNNReal) (gaussianReal m2 v2.toNNReal)
      = ENNReal.ofReal (gaussKL m1 v1 m2 v2) := by
  have hv1' : v1.toNNReal ≠ 0 := by simpa using hv1
  have hv2' : v2.toNNReal ≠ 0 := by simpa using hv2
  have hpt : ∀ x, gaussianPDFReal m1 v1.toNNReal x
      * Real.log (gaussianPDFReal m1 v1.toNNReal x / gaussianPDFReal m2 v2.toNNReal x)
      = gaussianPDFReal m1 v1.toNNReal x
        * ((1 / 2) * (Real.log v2 - Real.log v1) + (-(1 / (2 * v1))) * (x - m1) ^ 2
          + (1 / (2 * v2)) * (x - m2) ^ 2) := by
    intro x
    rw [Real.log_div (gaussianPDFReal_pos _ _ _ hv1').ne' (gaussianPDFReal_pos _ _ _ hv2').ne',
      log_gaussianPDFReal hv1, log_gaussianPDFReal hv2,
      Real.log_mul (by positivity) hv1.ne', Real.log_mul (by positivity) hv2.ne']
    field_simp
    ring
  have hint : Integrable fun x => gaussianPDFReal m1 v1.toNNReal x
      * Real.log (gaussianPDFReal m1 v1.toNNReal x / gaussianPDFReal m2 v2.toNNReal x) :=
    (integrable_gaussianPDFReal_quadratic m1 m2 hv1 _ _ _).congr
      (ae_of_all _ fun x => (hpt x).symm)
  have hP1 : IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal m1 v1.toNNReal x)) := by
    have := instIsProbabilityMeasureGaussianReal m1 v1.toNNReal
    rwa [gaussianReal_of_var_ne_zero _ hv1'] at this
  have hP2 : IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal m2 v2.toNNReal x)) := by
    have := instIsProbabilityMeasureGaussianReal m2 v2.toNNReal
    rwa [gaussianReal_of_var_ne_zero _ hv2'] at this
  rw [gaussianReal_of_var_ne_zero _ hv1', gaussianReal_of_var_ne_zero _ hv2']
  change klDiv (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal m1 v1.toNNReal x))
    (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal m2 v2.toNNReal x)) = _
  rw [klDiv_withDensity_ofReal volume (measurable_gaussianPDFReal _ _)
    (measurable_gaussianPDFReal _ _) (gaussianPDFReal_nonneg _ _)
    (fun x _ => gaussianPDFReal_pos _ _ _ hv2') hint, integral_congr_ae (ae_of_all _ hpt),
    integral_gaussianPDFReal_quadratic m1 m2 hv1]
  congr 1
  unfold gaussKL
  rw [Real.log_div hv1.ne' hv2.ne']
  field_simp
  ring

/-! ## Gamma and inverse-gamma KL -/

/-- The gamma density set to zero on `(−∞, 0]` (a.e. equal to `gammaPDFReal`). -/
noncomputable def gammaPDFPos (a b x : ℝ) : ℝ := if 0 < x then gammaPDFReal a b x else 0

lemma gammaMeasure_eq_withDensity_pos (a b : ℝ) :
    gammaMeasure a b = volume.withDensity fun x => ENNReal.ofReal (gammaPDFPos a b x) := by
  rw [gammaMeasure]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_ne_zero_real] with x hx
  rcases lt_or_gt_of_ne hx with h | h
  · simp [gammaPDF, gammaPDFPos, gammaPDFReal, not_lt.mpr h.le, not_le.mpr h]
  · simp [gammaPDF, gammaPDFPos, h]

/-- Closed-form gamma KL, `D_KL[Gamma(a, b) ‖ Gamma(a₀, b₀)]` (rates `b`, `b₀`). -/
noncomputable def gammaKL (a b a0 b0 : ℝ) : ℝ :=
  (a * Real.log b - Real.log (Real.Gamma a)) - (a0 * Real.log b0 - Real.log (Real.Gamma a0))
    + (a - a0) * (realDigamma a - Real.log b) - (b - b0) * (a / b)

lemma gammaPDFPos_mul_log_ratio {a b a0 b0 : ℝ} (ha : 0 < a) (hb : 0 < b) (ha0 : 0 < a0)
    (hb0 : 0 < b0) (x : ℝ) :
    gammaPDFPos a b x * Real.log (gammaPDFPos a b x / gammaPDFPos a0 b0 x)
      = (Ioi (0 : ℝ)).indicator
          (fun t => gammaPDFReal a b t * nigLogRatioGamma a b a0 b0 t) x := by
  by_cases hx : 0 < x
  · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
    simp only [gammaPDFPos, hx, ↓reduceIte]
    rw [Real.log_div (gammaPDFReal_pos ha hb hx).ne' (gammaPDFReal_pos ha0 hb0 hx).ne',
      log_gammaPDFReal ha hb hx, log_gammaPDFReal ha0 hb0 hx]
    unfold nigLogRatioGamma
    ring
  · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx)]
    simp [gammaPDFPos, hx]

lemma integral_gamma_mul_logRatioGamma {a b a0 b0 : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ t in Ioi 0, gammaPDFReal a b t * nigLogRatioGamma a b a0 b0 t = gammaKL a b a0 b0 := by
  set k0 := (a * Real.log b - Real.log (Real.Gamma a))
    - (a0 * Real.log b0 - Real.log (Real.Gamma a0))
  have hpt : EqOn (fun t => gammaPDFReal a b t * nigLogRatioGamma a b a0 b0 t)
      (fun t => (k0 * gammaPDFReal a b t + (a - a0) * (Real.log t * gammaPDFReal a b t))
        - (b - b0) * (t * gammaPDFReal a b t)) (Ioi 0) := by
    intro t _
    simp only [nigLogRatioGamma, k0]
    ring
  have hI0 := integrableOn_gammaPDFReal ha hb
  have hIl := integrableOn_log_mul_gammaPDFReal ha hb
  have hIt := integrableOn_mul_gammaPDFReal ha hb
  have h01 : IntegrableOn (fun t => k0 * gammaPDFReal a b t
      + (a - a0) * (Real.log t * gammaPDFReal a b t)) (Ioi 0) :=
    (hI0.const_mul k0).add (hIl.const_mul _)
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub h01 (hIt.const_mul _),
    integral_add (hI0.const_mul k0) (hIl.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_gammaPDFReal_Ioi ha hb, integral_log_mul_gammaPDFReal ha hb,
    integral_mul_gammaPDFReal ha hb]
  unfold gammaKL
  ring

/-- **Gamma KL.** `D_KL[Gamma(a, b) ‖ Gamma(a₀, b₀)] = gammaKL a b a₀ b₀`, and it is `≥ 0`. -/
theorem klDiv_gammaMeasure {a b a0 b0 : ℝ} (ha : 0 < a) (hb : 0 < b) (ha0 : 0 < a0)
    (hb0 : 0 < b0) :
    klDiv (gammaMeasure a b) (gammaMeasure a0 b0) = ENNReal.ofReal (gammaKL a b a0 b0)
      ∧ 0 ≤ gammaKL a b a0 b0 := by
  have hmeas : ∀ a b : ℝ, Measurable (gammaPDFPos a b) := fun a b => by
    unfold gammaPDFPos
    exact Measurable.ite measurableSet_Ioi (measurable_gammaPDFReal a b) measurable_const
  have hnn : ∀ x, 0 ≤ gammaPDFPos a b x := fun x => by
    unfold gammaPDFPos; split_ifs
    · exact gammaPDFReal_nonneg ha hb x
    · exact le_rfl
  have hpos : ∀ x, 0 < gammaPDFPos a b x → 0 < gammaPDFPos a0 b0 x := fun x hx => by
    unfold gammaPDFPos at hx ⊢
    split_ifs at hx ⊢ with h
    · exact gammaPDFReal_pos ha0 hb0 h
    · exact absurd hx (lt_irrefl 0)
  have hP1 : IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (gammaPDFPos a b x)) := by
    rw [← gammaMeasure_eq_withDensity_pos]; exact isProbabilityMeasure_gammaMeasure ha hb
  have hP2 : IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (gammaPDFPos a0 b0 x)) := by
    rw [← gammaMeasure_eq_withDensity_pos]; exact isProbabilityMeasure_gammaMeasure ha0 hb0
  have hint : Integrable fun x => gammaPDFPos a b x
      * Real.log (gammaPDFPos a b x / gammaPDFPos a0 b0 x) := by
    refine ((integrable_indicator_iff measurableSet_Ioi).mpr
      (integrableOn_gamma_mul_logRatioGamma (alpha0 := a0) (beta0 := b0) ha hb)).congr
      (ae_of_all _ fun x => (gammaPDFPos_mul_log_ratio ha hb ha0 hb0 x).symm)
  have hval : ∫ x, gammaPDFPos a b x * Real.log (gammaPDFPos a b x / gammaPDFPos a0 b0 x)
      = gammaKL a b a0 b0 := by
    rw [integral_congr_ae (ae_of_all _ (gammaPDFPos_mul_log_ratio ha hb ha0 hb0)),
      integral_indicator measurableSet_Ioi, integral_gamma_mul_logRatioGamma ha hb]
  refine ⟨?_, ?_⟩
  · rw [gammaMeasure_eq_withDensity_pos, gammaMeasure_eq_withDensity_pos,
      klDiv_withDensity_ofReal volume (hmeas a b) (hmeas a0 b0) hnn hpos hint, hval]
  · rw [← hval]
    exact integral_mul_log_div_nonneg volume (hmeas a b) (hmeas a0 b0) hnn hpos hint

/-- **Inverse-gamma KL.** `D_KL[IG(α, β) ‖ IG(α₀, β₀)] = gammaKL α β α₀ β₀`. -/
theorem klDiv_invGammaMeasure {a b a0 b0 : ℝ} (ha : 0 < a) (hb : 0 < b) (ha0 : 0 < a0)
    (hb0 : 0 < b0) :
    klDiv (invGammaMeasure a b) (invGammaMeasure a0 b0)
      = ENNReal.ofReal (gammaKL a b a0 b0) := by
  have := isProbabilityMeasure_gammaMeasure ha hb
  have := isProbabilityMeasure_gammaMeasure ha0 hb0
  rw [invGammaMeasure, invGammaMeasure,
    klDiv_map_involution _ _ measurable_inv (fun x => inv_inv x),
    (klDiv_gammaMeasure ha hb ha0 hb0).1]

/-! ## The averaged conditional Gaussian KL -/

/-- `E_{σ² ~ IG(α,β)} D_KL[N(γ, σ²/ν) ‖ N(γ₀, σ²/ν₀)]` in closed form. -/
theorem integral_klDiv_gaussian_invGamma {gamma nu alpha beta gamma0 nu0 : ℝ}
    (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta) (hnu0 : 0 < nu0) :
    ∫ s, (klDiv (gaussianReal gamma (s / nu).toNNReal)
        (gaussianReal gamma0 (s / nu0).toNNReal)).toReal ∂(invGammaMeasure alpha beta)
      = (1 / 2) * (nu0 / nu - 1 + Real.log (nu / nu0))
        + nu0 * (gamma - gamma0) ^ 2 / 2 * (alpha / beta) := by
  set K := (1 / 2) * (nu0 / nu - 1 + Real.log (nu / nu0))
  set L := nu0 * (gamma - gamma0) ^ 2 / 2
  have hae : (fun s => (klDiv (gaussianReal gamma (s / nu).toNNReal)
        (gaussianReal gamma0 (s / nu0).toNNReal)).toReal)
      =ᵐ[invGammaMeasure alpha beta] fun s => K + L * s⁻¹ := by
    filter_upwards [invGammaMeasure_ae_pos alpha beta] with s hs
    have h1 : 0 < s / nu := div_pos hs hnu
    have h2 : 0 < s / nu0 := div_pos hs hnu0
    rw [klDiv_gaussianReal _ _ h1 h2, ENNReal.toReal_ofReal (gaussKL_nonneg h1 h2)]
    unfold gaussKL
    have hratio : s / nu / (s / nu0) = nu0 / nu := by field_simp
    rw [hratio, Real.log_div hnu0.ne' hnu.ne']
    simp only [K, L]
    rw [Real.log_div hnu.ne' hnu0.ne']
    field_simp
    ring
  have hP : IsProbabilityMeasure (invGammaMeasure alpha beta) := by
    have := isProbabilityMeasure_gammaMeasure halpha hbeta
    unfold invGammaMeasure; infer_instance
  have hinv : Integrable (fun s : ℝ => s⁻¹) (invGammaMeasure alpha beta) :=
    Integrable.of_integral_ne_zero (by
      rw [integral_inv_invGammaMeasure alpha beta halpha hbeta]
      exact (div_pos halpha hbeta).ne')
  rw [integral_congr_ae hae, integral_add (integrable_const K) (hinv.const_mul L),
    integral_const, probReal_univ, one_smul, integral_const_mul,
    integral_inv_invGammaMeasure alpha beta halpha hbeta]

/-! ## Chain-rule split -/

/--
**Chain-rule split.** For `ν, α, β, ν₀, α₀, β₀ > 0`,

  D_KL(q ‖ p₀) = D_KL[IG(α,β) ‖ IG(α₀,β₀)] + E_{q(σ²)} D_KL[N(γ, σ²/ν) ‖ N(γ₀, σ²/ν₀)],

with all three divergences computed by mathlib's `klDiv` (as real numbers).
-/
theorem klDiv_chain_rule_split {gamma nu alpha beta gamma0 nu0 alpha0 beta0 : ℝ}
    (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0) :
    (klDiv (nigMeasureMuSigma gamma nu alpha beta)
        (nigMeasureMuSigma gamma0 nu0 alpha0 beta0)).toReal
      = (klDiv (invGammaMeasure alpha beta) (invGammaMeasure alpha0 beta0)).toReal
        + ∫ s, (klDiv (gaussianReal gamma (s / nu).toNNReal)
            (gaussianReal gamma0 (s / nu0).toNNReal)).toReal ∂(invGammaMeasure alpha beta) := by
  rw [klDiv_eq_manuscriptNIGKL hnu halpha hbeta hnu0 halpha0 hbeta0,
    klDiv_invGammaMeasure halpha hbeta halpha0 hbeta0,
    integral_klDiv_gaussian_invGamma hnu halpha hbeta hnu0,
    ENNReal.toReal_ofReal (by
      rw [manuscriptNIGKL_eq_closedForm _ _ _ _ _ _ _ _ hbeta hbeta0]
      exact nigKLClosedForm_nonneg hnu halpha hbeta hnu0 halpha0 hbeta0),
    ENNReal.toReal_ofReal (klDiv_gammaMeasure halpha hbeta halpha0 hbeta0).2]
  unfold manuscriptNIGKL gammaKL
  rw [Real.log_div hbeta.ne' hbeta0.ne']
  field_simp
  ring

end ELVAE
