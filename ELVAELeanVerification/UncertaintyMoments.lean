import Mathlib
import ELVAELeanVerification.NIGStudentTMarginal
import ELVAELeanVerification.VarianceAllocation

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Uncertainty decomposition from the NIG law

For the NIG hierarchy of `NIGStudentTMarginal`
(`σ² ~ InvGamma(α, β)`, `μ | σ² ~ N(γ, σ²/ν)`, `z | μ, σ² ~ N(μ, σ²)`)
with `α > 1`, this module computes the moments behind the uncertainty
decomposition:

  E[σ²]          = β/(α − 1),
  E[(μ − γ)²]    = β/((α − 1) ν),
  E[(z − γ)²]    = β(1 + 1/ν)/(α − 1) = c/(α − 1).

On the fiber `β = c ν/(1 + ν)` these are exactly the algebraic quantities of
`VarianceAllocation`:

  E[σ²] = u_var(c, α, ν),  E[(μ − γ)²] = u_epi(c, α, ν),
  E[(z − γ)²] = u_var + u_epi = c/(α − 1),

matching the uncertainty components (`u_var = E[σ² | y]`,
`u_epi = Var(μ | y)`).

Thus the identities of `VarianceAllocation` are derived from the NIG law,
not just postulated.
-/

namespace ELVAE

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

/-- `∫⁻ τ⁻¹ dGamma(α, β) = β/(α − 1)` for `α > 1`. -/
lemma lintegral_inv_gammaMeasure (a b : ℝ) (ha : 1 < a) (hb : 0 < b) :
    ∫⁻ t, ENNReal.ofReal t⁻¹ ∂(gammaMeasure a b) = ENNReal.ofReal (b / (a - 1)) := by
  have hmeasG : Measurable (gammaPDF a b) := (measurable_gammaPDFReal a b).ennreal_ofReal
  rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ hmeasG
    measurable_inv.ennreal_ofReal]
  have hf : (gammaPDF a b * fun t => ENNReal.ofReal t⁻¹)
      = fun t => ENNReal.ofReal (gammaPDFReal a b t * t⁻¹) := by
    funext t
    simp only [Pi.mul_apply]
    rw [gammaPDF, ENNReal.ofReal_mul (gammaPDFReal_nonneg (by linarith) hb t)]
  rw [hf, ← lintegral_add_compl _ (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ))),
    Set.compl_Ioi]
  have hzero : ∫⁻ t in Iic 0, ENNReal.ofReal (gammaPDFReal a b t * t⁻¹) = 0 := by
    rw [← setLIntegral_congr Iio_ae_eq_Iic]
    rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0)
      (fun t (ht : t < 0) => by simp [gammaPDFReal, not_le.mpr ht])]
    simp
  rw [hzero, add_zero]
  -- On `(0, ∞)` the integrand is `bᵃ/Γ(a) · t^((a-1)-1) e^{-bt}`.
  have hpt : EqOn (fun t => gammaPDFReal a b t * t⁻¹)
      (fun t => b ^ a / Real.Gamma a * (t ^ ((a - 1) - 1) * Real.exp (-(b * t)))) (Ioi 0) := by
    intro t (ht : 0 < t)
    simp only [gammaPDFReal, ht.le, ↓reduceIte]
    rw [Real.rpow_sub ht (a - 1) 1, Real.rpow_one]
    field_simp
  have hGa : Real.Gamma a = (a - 1) * Real.Gamma (a - 1) := by
    have := Real.Gamma_add_one (s := a - 1) (by linarith)
    rw [sub_add_cancel] at this
    exact this
  have hval : ∫ t in Ioi 0, gammaPDFReal a b t * t⁻¹ = b / (a - 1) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
      integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hb, hGa]
    have hG1 : 0 < Real.Gamma (a - 1) := Real.Gamma_pos_of_pos (by linarith)
    have hb1 : (1 / b) ^ (a - 1) = (b ^ (a - 1))⁻¹ := by
      rw [one_div, Real.inv_rpow hb.le]
    have hba : b ^ a = b ^ (a - 1) * b := by
      rw [← Real.rpow_add_one hb.ne', sub_add_cancel]
    have hbpos : 0 < b ^ (a - 1) := Real.rpow_pos_of_pos hb _
    have ha1 : a - 1 ≠ 0 := by linarith
    rw [hb1, hba]
    field_simp
  have hint : Integrable (fun t => gammaPDFReal a b t * t⁻¹) (volume.restrict (Ioi 0)) :=
    Integrable.of_integral_ne_zero (by rw [hval]; exact (div_pos hb (by linarith)).ne')
  rw [← ofReal_integral_eq_lintegral_ofReal hint, hval]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  exact mul_nonneg (gammaPDFReal_nonneg (by linarith) hb t) (inv_nonneg.mpr ht.le)

/-- The inverse-gamma law is concentrated on `(0, ∞)`. -/
lemma invGammaMeasure_ae_pos (a b : ℝ) : ∀ᵐ s ∂(invGammaMeasure a b), 0 < s := by
  have hm : Measurable (fun t : ℝ => t⁻¹) := measurable_inv
  have hS : MeasurableSet {s : ℝ | 0 < s} := measurableSet_Ioi
  rw [invGammaMeasure, ae_map_iff hm.aemeasurable hS]
  filter_upwards [gammaMeasure_ae_pos a b] with t ht
  exact inv_pos.mpr ht

/-- `E[σ²] = β/(α − 1)` under `InvGamma(α, β)`, as a lower Lebesgue integral. -/
lemma lintegral_invGammaMeasure (a b : ℝ) (ha : 1 < a) (hb : 0 < b) :
    ∫⁻ s, ENNReal.ofReal s ∂(invGammaMeasure a b) = ENNReal.ofReal (b / (a - 1)) := by
  rw [invGammaMeasure, lintegral_map (f := fun s => ENNReal.ofReal s)
    (g := fun t : ℝ => t⁻¹) ENNReal.measurable_ofReal measurable_inv]
  exact lintegral_inv_gammaMeasure a b ha hb

/-- **Mean of the inverse-gamma law.** `E[σ²] = β/(α − 1)` for `α > 1`. -/
theorem integral_invGammaMeasure (a b : ℝ) (ha : 1 < a) (hb : 0 < b) :
    ∫ s, s ∂(invGammaMeasure a b) = b / (a - 1) := by
  have hnn : 0 ≤ᵐ[invGammaMeasure a b] fun s => s := by
    filter_upwards [invGammaMeasure_ae_pos a b] with s hs
    exact hs.le
  rw [integral_eq_lintegral_of_nonneg_ae hnn measurable_id.aestronglyMeasurable,
    lintegral_invGammaMeasure a b ha hb, ENNReal.toReal_ofReal (div_pos hb (by linarith)).le]

/-- Second central moment of a Gaussian, as a lower Lebesgue integral. -/
lemma lintegral_sq_sub_gaussianReal (m : ℝ) (v : ℝ≥0) :
    ∫⁻ z, ENNReal.ofReal ((z - m) ^ 2) ∂(gaussianReal m v) = ENNReal.ofReal v := by
  have hvar := variance_fun_id_gaussianReal (μ := m) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at hvar
  have hint : Integrable (fun z => (z - m) ^ 2) (gaussianReal m v) :=
    ((memLp_id_gaussianReal 2).sub (memLp_const m)).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun z => sq_nonneg _), hvar]

/-- `∫⁻ (μ − γ)² d(law of μ) = β/((α − 1) ν)`. -/
lemma lintegral_sq_sub_nigMuMarginal (gamma nu alpha beta : ℝ)
    (hnu : 0 < nu) (halpha : 1 < alpha) (hbeta : 0 < beta) :
    ∫⁻ m, ENNReal.ofReal ((m - gamma) ^ 2) ∂(nigMuMarginal gamma nu alpha beta)
      = ENNReal.ofReal (beta / ((alpha - 1) * nu)) := by
  have hk : Measurable (fun s : ℝ => gaussianReal gamma (s / nu).toNNReal) :=
    measurable_gaussianReal.comp
      (measurable_const.prodMk ((measurable_id.div_const nu).real_toNNReal))
  have hf : Measurable (fun z : ℝ => ENNReal.ofReal ((z - gamma) ^ 2)) := by fun_prop
  rw [nigMuMarginal, Measure.lintegral_bind hk.aemeasurable hf.aemeasurable]
  simp_rw [lintegral_sq_sub_gaussianReal]
  have hae : (fun s : ℝ => ENNReal.ofReal ((s / nu).toNNReal : ℝ))
      =ᵐ[invGammaMeasure alpha beta] fun s => ENNReal.ofReal (nu⁻¹) * ENNReal.ofReal s := by
    filter_upwards [invGammaMeasure_ae_pos alpha beta] with s hs
    rw [Real.coe_toNNReal _ (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    ring_nf
  rw [lintegral_congr_ae hae,
    lintegral_const_mul (f := fun s => ENNReal.ofReal s) _ ENNReal.measurable_ofReal,
    lintegral_invGammaMeasure alpha beta halpha hbeta,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- `∫⁻ (z − γ)² d(law of z) = β(1 + 1/ν)/(α − 1)`. -/
lemma lintegral_sq_sub_nigZMarginal (gamma nu alpha beta : ℝ)
    (hnu : 0 < nu) (halpha : 1 < alpha) (hbeta : 0 < beta) :
    ∫⁻ z, ENNReal.ofReal ((z - gamma) ^ 2) ∂(nigZMarginal gamma nu alpha beta)
      = ENNReal.ofReal (beta * (1 + 1 / nu) / (alpha - 1)) := by
  have hinner : (fun s : ℝ => (gaussianReal gamma (s / nu).toNNReal).bind
        (fun m => gaussianReal m s.toNNReal))
      = fun s => gaussianReal gamma ((s / nu).toNNReal + s.toNNReal) := by
    funext s
    exact gaussianReal_bind_gaussianReal gamma _ _
  have hk : Measurable (fun s : ℝ => gaussianReal gamma ((s / nu).toNNReal + s.toNNReal)) :=
    measurable_gaussianReal.comp (measurable_const.prodMk
      (((measurable_id.div_const nu).real_toNNReal).add measurable_id.real_toNNReal))
  have hf : Measurable (fun z : ℝ => ENNReal.ofReal ((z - gamma) ^ 2)) := by fun_prop
  rw [nigZMarginal, hinner, Measure.lintegral_bind hk.aemeasurable hf.aemeasurable]
  simp_rw [lintegral_sq_sub_gaussianReal]
  have hae : (fun s : ℝ => ENNReal.ofReal (((s / nu).toNNReal + s.toNNReal : ℝ≥0) : ℝ))
      =ᵐ[invGammaMeasure alpha beta]
        fun s => ENNReal.ofReal (1 + 1 / nu) * ENNReal.ofReal s := by
    filter_upwards [invGammaMeasure_ae_pos alpha beta] with s hs
    rw [NNReal.coe_add, Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ hs.le,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    ring
  rw [lintegral_congr_ae hae,
    lintegral_const_mul (f := fun s => ENNReal.ofReal s) _ ENNReal.measurable_ofReal,
    lintegral_invGammaMeasure alpha beta halpha hbeta,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- Converts a lower-integral identity for a nonnegative function into a real one. -/
lemma integral_eq_of_lintegral_ofReal {μ : Measure ℝ} {f : ℝ → ℝ} {r : ℝ}
    (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x) (hr : 0 ≤ r)
    (h : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ENNReal.ofReal r) :
    ∫ x, f x ∂μ = r := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hf.aestronglyMeasurable, h,
    ENNReal.toReal_ofReal hr]

/-- **Epistemic moment.** `E[(μ − γ)²] = β/((α − 1) ν)`. -/
theorem integral_sq_sub_nigMuMarginal (gamma nu alpha beta : ℝ)
    (hnu : 0 < nu) (halpha : 1 < alpha) (hbeta : 0 < beta) :
    ∫ m, (m - gamma) ^ 2 ∂(nigMuMarginal gamma nu alpha beta)
      = beta / ((alpha - 1) * nu) :=
  integral_eq_of_lintegral_ofReal (by fun_prop) (fun _ => sq_nonneg _)
    (div_pos hbeta (mul_pos (by linarith) hnu)).le
    (lintegral_sq_sub_nigMuMarginal gamma nu alpha beta hnu halpha hbeta)

/-- **Total latent moment.** `E[(z − γ)²] = β(1 + 1/ν)/(α − 1)`. -/
theorem integral_sq_sub_nigZMarginal (gamma nu alpha beta : ℝ)
    (hnu : 0 < nu) (halpha : 1 < alpha) (hbeta : 0 < beta) :
    ∫ z, (z - gamma) ^ 2 ∂(nigZMarginal gamma nu alpha beta)
      = beta * (1 + 1 / nu) / (alpha - 1) := by
  have hpos : 0 < beta * (1 + 1 / nu) / (alpha - 1) := by
    have : 0 < alpha - 1 := by linarith
    positivity
  exact integral_eq_of_lintegral_ofReal (by fun_prop) (fun _ => sq_nonneg _) hpos.le
    (lintegral_sq_sub_nigZMarginal gamma nu alpha beta hnu halpha hbeta)

/--
**Uncertainty decomposition on the fiber.** For `β = c ν/(1 + ν)` with
`c, ν > 0` and `α > 1`:

* `E[σ²] = u_var(c, α, ν)` (aleatoric),
* `E[(μ − γ)²] = u_epi(c, α, ν)` (epistemic),
* `E[(z − γ)²] = c/(α − 1) = u_var + u_epi` (total, fiber-invariant).
-/
theorem nig_uncertainty_decomposition_on_fiber (gamma alpha c nu : ℝ)
    (halpha : 1 < alpha) (hc : 0 < c) (hnu : 0 < nu) :
    ∫ s, s ∂(invGammaMeasure alpha (c * nu / (1 + nu))) = uVar c alpha nu
    ∧ ∫ m, (m - gamma) ^ 2 ∂(nigMuMarginal gamma nu alpha (c * nu / (1 + nu)))
        = uEpi c alpha nu
    ∧ ∫ z, (z - gamma) ^ 2 ∂(nigZMarginal gamma nu alpha (c * nu / (1 + nu)))
        = c / (alpha - 1)
    ∧ uVar c alpha nu + uEpi c alpha nu = c / (alpha - 1) := by
  have hbeta : 0 < c * nu / (1 + nu) := by positivity
  have ha1 : alpha - 1 ≠ 0 := by linarith
  have h1nu : 1 + nu ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_, variance_budget c alpha nu halpha hnu⟩
  · rw [integral_invGammaMeasure alpha _ halpha hbeta, uVar]
    field_simp
  · rw [integral_sq_sub_nigMuMarginal gamma nu alpha _ hnu halpha hbeta, uEpi]
    field_simp
  · rw [integral_sq_sub_nigZMarginal gamma nu alpha _ hnu halpha hbeta]
    field_simp
    ring

end ELVAE
