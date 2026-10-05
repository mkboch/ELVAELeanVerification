import Mathlib
import ELVAELeanVerification.UncertaintyMoments
import ELVAELeanVerification.GeometricTransfer

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Latent variance, the variance form of `T`, and the collapsed hierarchy

Hierarchy: `σ² ~ InvGamma(α, β)`, `μ | σ² ~ N(γ, σ²/ν)`,
`z | μ, σ² ~ N(μ, σ²)`; `nigMuMarginal` is the law of `μ`, `nigZMarginal` the law
of `z`.

* `integral_id_nigZMarginal`, `variance_nigZMarginal`: for `α > 1`,
  `E[z | y] = γ` and `Var(z | y) = c/(α − 1)` with `c = β(1 + 1/ν)`
  (mathlib's `ProbabilityTheory.variance`). The same for `μ` with `β/((α−1)ν)`.
* `TFromParams_eq_variance_form`: for `α > 1`,
  `T = ((α − 1)/α) · Var(z | y) / ((γ − γ₀)² + ρ₀)`.
* `nigZMarginal_eq_collapsed`: the law of `z` equals that of the
  collapsed hierarchy `ω² ~ InvGamma(α, c)`, `z | ω² ~ N(γ, ω²)`, which contains no
  fiber coordinate; `gaussian_collapse` gives `z | σ² ~ N(γ, σ²(1 + 1/ν))`.
* `functional_fiber_invariant`: every
  functional of the law of `z` is constant on fibers.
-/

namespace ELVAE

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

/-! ## Symmetry of the Student-t law -/

lemma studentTPDFReal_reflect (n m s2 y : ℝ) :
    studentTPDFReal n m s2 (2 * m - y) = studentTPDFReal n m s2 y := by
  unfold studentTPDFReal
  congr 3
  ring

/-- The Student-t law is centred at its location: `∫ (y − m) = 0`. -/
lemma integral_sub_studentTMeasure (n m s2 : ℝ) :
    ∫ y, (y - m) ∂(studentTMeasure n m s2) = 0 := by
  have hmeas : Measurable fun y => ENNReal.ofReal (studentTPDFReal n m s2 y) := by
    unfold studentTPDFReal; fun_prop
  rw [studentTMeasure, integral_withDensity_eq_integral_toReal_smul hmeas
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  set g : ℝ → ℝ := fun y => (ENNReal.ofReal (studentTPDFReal n m s2 y)).toReal • (y - m)
  have hrefl : ∀ y, g (2 * m - y) = -g y := by
    intro y
    simp only [g, studentTPDFReal_reflect, smul_eq_mul]
    ring
  have h := integral_sub_left_eq_self g volume (2 * m)
  simp_rw [hrefl, integral_neg] at h
  change ∫ y, g y = 0
  linarith

/-! ## Means and variances of `μ` and `z` -/

section Moments

variable {gamma nu alpha beta : ℝ}

lemma isProbabilityMeasure_nigZMarginal (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta) :
    IsProbabilityMeasure (nigZMarginal gamma nu alpha beta) := by
  rw [nigZMarginal_eq_studentT _ _ _ _ hnu halpha hbeta]
  exact isProbabilityMeasure_studentTMeasure _ _ _ (by positivity) (by positivity)

lemma isProbabilityMeasure_nigMuMarginal (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta) :
    IsProbabilityMeasure (nigMuMarginal gamma nu alpha beta) := by
  rw [nigMuMarginal_eq_studentT _ _ _ _ hnu halpha hbeta]
  exact isProbabilityMeasure_studentTMeasure _ _ _ (by positivity) (by positivity)

/-- A finite lower second moment about `m` gives `x ↦ x − m ∈ L²`. -/
lemma memLp_sub_of_lintegral_sq {μ : Measure ℝ} {m r : ℝ}
    (h : ∫⁻ x, ENNReal.ofReal ((x - m) ^ 2) ∂μ = ENNReal.ofReal r) :
    MemLp (fun x => x - m) 2 μ := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _), h]
  exact ENNReal.ofReal_lt_top

lemma memLp_sub_nigZMarginal (hnu : 0 < nu) (halpha : 1 < alpha) (hbeta : 0 < beta) :
    MemLp (fun z => z - gamma) 2 (nigZMarginal gamma nu alpha beta) :=
  memLp_sub_of_lintegral_sq (lintegral_sq_sub_nigZMarginal gamma nu alpha beta hnu halpha hbeta)

lemma memLp_sub_nigMuMarginal (hnu : 0 < nu) (halpha : 1 < alpha) (hbeta : 0 < beta) :
    MemLp (fun m => m - gamma) 2 (nigMuMarginal gamma nu alpha beta) :=
  memLp_sub_of_lintegral_sq (lintegral_sq_sub_nigMuMarginal gamma nu alpha beta hnu halpha hbeta)

/-- Mean from centring and integrability. -/
lemma integral_id_of_centred {μ : Measure ℝ} [IsProbabilityMeasure μ] {m : ℝ}
    (hL : MemLp (fun x => x - m) 2 μ) (h0 : ∫ x, (x - m) ∂μ = 0) :
    ∫ x, x ∂μ = m := by
  have hint : Integrable (fun x => x - m) μ := hL.integrable (by norm_num)
  have hid : Integrable (fun x : ℝ => x) μ := by
    have h := hint.add (integrable_const m)
    refine h.congr (ae_of_all _ fun x => ?_)
    simp
  rw [integral_sub hid (integrable_const m), integral_const, probReal_univ, one_smul] at h0
  linarith

/-- `E[z | y] = γ` (`α > 1`). -/
theorem integral_id_nigZMarginal (hnu : 0 < nu) (halpha : 1 < alpha) (hbeta : 0 < beta) :
    ∫ z, z ∂(nigZMarginal gamma nu alpha beta) = gamma := by
  have := isProbabilityMeasure_nigZMarginal (gamma := gamma) (nu := nu) (alpha := alpha)
    (beta := beta) hnu (by linarith) hbeta
  refine integral_id_of_centred (memLp_sub_nigZMarginal hnu halpha hbeta) ?_
  rw [nigZMarginal_eq_studentT _ _ _ _ hnu (by linarith) hbeta]
  exact integral_sub_studentTMeasure _ _ _

/-- `E[μ | y] = γ` (`α > 1`). -/
theorem integral_id_nigMuMarginal (hnu : 0 < nu) (halpha : 1 < alpha) (hbeta : 0 < beta) :
    ∫ m, m ∂(nigMuMarginal gamma nu alpha beta) = gamma := by
  have := isProbabilityMeasure_nigMuMarginal (gamma := gamma) (nu := nu) (alpha := alpha)
    (beta := beta) hnu (by linarith) hbeta
  refine integral_id_of_centred (memLp_sub_nigMuMarginal hnu halpha hbeta) ?_
  rw [nigMuMarginal_eq_studentT _ _ _ _ hnu (by linarith) hbeta]
  exact integral_sub_studentTMeasure _ _ _

/-- **Latent variance.** `Var(z | y) = β(1 + 1/ν)/(α − 1) = c/(α − 1)` (`α > 1`). -/
theorem variance_nigZMarginal (hnu : 0 < nu) (halpha : 1 < alpha) (hbeta : 0 < beta) :
    Var[fun z => z; nigZMarginal gamma nu alpha beta] = beta * (1 + 1 / nu) / (alpha - 1) := by
  rw [variance_eq_integral measurable_id'.aemeasurable,
    integral_id_nigZMarginal hnu halpha hbeta]
  exact integral_sq_sub_nigZMarginal gamma nu alpha beta hnu halpha hbeta

/-- **Epistemic variance.** `Var(μ | y) = β/((α − 1)ν)` (`α > 1`). -/
theorem variance_nigMuMarginal (hnu : 0 < nu) (halpha : 1 < alpha) (hbeta : 0 < beta) :
    Var[fun m => m; nigMuMarginal gamma nu alpha beta] = beta / ((alpha - 1) * nu) := by
  rw [variance_eq_integral measurable_id'.aemeasurable,
    integral_id_nigMuMarginal hnu halpha hbeta]
  exact integral_sq_sub_nigMuMarginal gamma nu alpha beta hnu halpha hbeta

end Moments

/-- **Uncertainty components as variances.** On the fiber `β = cν/(1+ν)` with `α > 1`:
`u_var = E[σ² | y]`, `u_epi = Var(μ | y)`, `Var(z | y) = u_var + u_epi = c/(α − 1)`. -/
theorem nig_variance_decomposition_on_fiber (gamma alpha c nu : ℝ)
    (halpha : 1 < alpha) (hc : 0 < c) (hnu : 0 < nu) :
    ∫ s, s ∂(invGammaMeasure alpha (c * nu / (1 + nu))) = uVar c alpha nu
    ∧ Var[fun m => m; nigMuMarginal gamma nu alpha (c * nu / (1 + nu))] = uEpi c alpha nu
    ∧ Var[fun z => z; nigZMarginal gamma nu alpha (c * nu / (1 + nu))] = c / (alpha - 1)
    ∧ uVar c alpha nu + uEpi c alpha nu = c / (alpha - 1) := by
  have hbeta : 0 < c * nu / (1 + nu) := by positivity
  obtain ⟨h1, _, _, h4⟩ := nig_uncertainty_decomposition_on_fiber gamma alpha c nu halpha hc hnu
  have ha1 : alpha - 1 ≠ 0 := by linarith
  have h1nu : 1 + nu ≠ 0 := by linarith
  refine ⟨h1, ?_, ?_, h4⟩
  · rw [variance_nigMuMarginal hnu halpha hbeta, uEpi]
    field_simp
  · rw [variance_nigZMarginal hnu halpha hbeta]
    field_simp
    ring

/--
For `α > 1`, the quotient-geometric coordinate can be written with the
actual latent variance, for any representative `(ν, β = cν/(1+ν))` of the fiber:

  T = ((α − 1)/α) · Var(z | y) / ((γ − γ₀)² + ρ₀).
-/
theorem TFromParams_eq_variance_form (gamma alpha c gamma0 nu0 beta0 nu : ℝ)
    (halpha : 1 < alpha) (hc : 0 < c) (hnu : 0 < nu) (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0) :
    TFromParams gamma alpha c gamma0 nu0 beta0
      = (alpha - 1) / alpha
        * Var[fun z => z; nigZMarginal gamma nu alpha (c * nu / (1 + nu))]
        / ((gamma - gamma0) ^ 2 + rho0FromPrior nu0 beta0) := by
  obtain ⟨_, _, hvar, _⟩ := nig_variance_decomposition_on_fiber gamma alpha c nu halpha hc hnu
  rw [hvar, TFromParams]
  have hrho := rho0FromPrior_positive nu0 beta0 hnu0 hbeta0
  have hden : 0 < (gamma - gamma0) ^ 2 + rho0FromPrior nu0 beta0 := by positivity
  have ha1 : alpha - 1 ≠ 0 := by linarith
  have ha : alpha ≠ 0 := by linarith
  field_simp

/-! ## The collapsed hierarchy -/

/-- Conditional collapse: given `σ² ≥ 0`, integrating out `μ` gives
`z | σ² ~ N(γ, σ²(1 + 1/ν))`. -/
theorem gaussian_collapse (gamma nu s : ℝ) (hnu : 0 < nu) (hs : 0 ≤ s) :
    (gaussianReal gamma (s / nu).toNNReal).bind (fun m => gaussianReal m s.toNNReal)
      = gaussianReal gamma (s * (1 + 1 / nu)).toNNReal := by
  rw [gaussianReal_bind_gaussianReal, ← Real.toNNReal_add (by positivity) hs]
  congr 2
  field_simp
  ring

/-- Collapsed latent law: `ω² ~ InvGamma(α, c)`, `z | ω² ~ N(γ, ω²)`. -/
noncomputable def collapsedZMarginal (gamma alpha c : ℝ) : Measure ℝ :=
  (invGammaMeasure alpha c).bind fun w => gaussianReal gamma w.toNNReal

/-- The collapsed hierarchy has the Student-t law `t_{2α}(γ, c/α)`. -/
theorem collapsedZMarginal_eq_studentT (gamma alpha c : ℝ) (halpha : 0 < alpha) (hc : 0 < c) :
    collapsedZMarginal gamma alpha c = studentTMeasure (2 * alpha) gamma (c / alpha) := by
  have hk : (fun w : ℝ => gaussianReal gamma w.toNNReal)
      = fun w => gaussianReal gamma (1 * w).toNNReal := by
    funext w; rw [one_mul]
  rw [collapsedZMarginal, hk, invGamma_bind_eq_gamma_bind,
    gamma_mixture_gaussian_eq_studentT _ _ _ _ halpha hc one_pos, one_mul]

/--
The law of `z` in the NIG hierarchy equals that of the collapsed hierarchy with
`c = β(1 + 1/ν)`, which contains no fiber coordinate.
-/
theorem nigZMarginal_eq_collapsed (gamma nu alpha beta : ℝ)
    (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta) :
    nigZMarginal gamma nu alpha beta = collapsedZMarginal gamma alpha (beta * (1 + 1 / nu)) := by
  rw [nigZMarginal_eq_studentT _ _ _ _ hnu halpha hbeta,
    collapsedZMarginal_eq_studentT _ _ _ halpha (by positivity)]

/--
**Consequence.** Every functional `F` of the marginal law of `z` depends
on `(γ, ν, α, β)` only through `(γ, α, c)`: it is constant on each fiber.
-/
theorem functional_fiber_invariant {X : Type*} (F : Measure ℝ → X)
    (gamma alpha nu1 beta1 nu2 beta2 : ℝ)
    (halpha : 0 < alpha) (hnu1 : 0 < nu1) (hbeta1 : 0 < beta1)
    (hnu2 : 0 < nu2) (hbeta2 : 0 < beta2)
    (hfiber : beta1 * (1 + 1 / nu1) = beta2 * (1 + 1 / nu2)) :
    F (nigZMarginal gamma nu1 alpha beta1) = F (nigZMarginal gamma nu2 alpha beta2) := by
  rw [nigZMarginal_fiber_invariant gamma alpha nu1 beta1 nu2 beta2 halpha hnu1 hbeta1
    hnu2 hbeta2 hfiber]

end ELVAE
