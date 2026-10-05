import Mathlib
import ELVAELeanVerification.KLTheorem2
import ELVAELeanVerification.NIGConsistency
import ELVAELeanVerification.LatentVariance
import ELVAELeanVerification.PriorSelfConsistency

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Conditional weight invariance (and why it is only conditional)

For fixed `(γ, α, c)`, multiplication of the fiber regularizer by any `λ > 0`
does not change its minimizer, so `ν_can` is conditionally weight-invariant; the
outer optimum of `(γ, α, c)` may still depend on `λ`.

* `fiber_argmin_weight_invariant`: for every `λ > 0` the set of minimizers over
  `ν > 0` of `λ · KL(NIG(γ, ν, α, cν/(1+ν)) ‖ p₀)` is exactly `{ν_can}`.
* `outer_optimum_depends_on_weight`: the outer optimum is **not** weight-invariant
  in general. For every valid prior there is a reconstruction term `L` and an
  admissible quotient state that minimizes `J₃` for `λ = 1` but not for `λ = 2`.

Supporting facts: `Rcan_nonneg`, `Rcan_prior_eq_zero`, and `Rcan_pos_of_gamma_ne`
(`R_can(θ) > 0` whenever `γ ≠ γ₀`, for `α > 1`).
-/

namespace ELVAE

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal

variable {gamma0 nu0 alpha0 beta0 : ℝ}

/-- **Conditional weight invariance.** For any `λ > 0`, the minimizers over
`ν > 0` of `λ · KL` along the fiber of an admissible `θ` are exactly `{ν_can(θ)}`. -/
theorem fiber_argmin_weight_invariant (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0)
    (hbeta0 : 0 < beta0) {lam : ℝ} (hlam : 0 < lam)
    {θ : QuotientState} (hθ : θ ∈ admissibleQuotients) :
    {nu : ℝ | 0 < nu ∧ ∀ nu' : ℝ, 0 < nu' →
        lam * fiberKL gamma0 nu0 alpha0 beta0 θ nu ≤ lam * fiberKL gamma0 nu0 alpha0 beta0 θ nu'}
      = {θ.nuCan gamma0 nu0 alpha0 beta0} := by
  have hcan := QuotientState.nuCan_mem gamma0 nu0 alpha0 beta0 hnu0 hbeta0 θ hθ
  ext nu
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨hnu, hmin⟩
    by_contra hne
    have hlt := klDiv_nig_fiber_strict_min hnu0 halpha0 hbeta0 hθ hnu hne
    have hle := hmin _ hcan
    have := (mul_le_mul_iff_of_pos_left hlam).mp hle
    linarith
  · rintro rfl
    refine ⟨hcan, fun nu' hnu' => ?_⟩
    exact mul_le_mul_of_nonneg_left (klDiv_nig_fiber_min hnu0 halpha0 hbeta0 θ hθ nu' hnu')
      hlam.le

/-- The canonical regularizer `R_can(θ) = KL` at the canonical representative. -/
noncomputable def Rcan (gamma0 nu0 alpha0 beta0 : ℝ) (θ : QuotientState) : ℝ :=
  fiberKL gamma0 nu0 alpha0 beta0 θ (θ.nuCan gamma0 nu0 alpha0 beta0)

lemma Rcan_nonneg (θ : QuotientState) : 0 ≤ Rcan gamma0 nu0 alpha0 beta0 θ :=
  ENNReal.toReal_nonneg

lemma Rcan_prior_eq_zero (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0) :
    Rcan gamma0 nu0 alpha0 beta0 (priorQuotient gamma0 nu0 alpha0 beta0) = 0 := by
  have hθ : priorQuotient gamma0 nu0 alpha0 beta0 ∈ admissibleQuotients :=
    ⟨halpha0, priorC0_positive nu0 beta0 hnu0 hbeta0⟩
  unfold Rcan
  rw [fiberKL_eq_restrictedNIGKL hnu0 halpha0 hbeta0 hθ
    (QuotientState.nuCan_mem gamma0 nu0 alpha0 beta0 hnu0 hbeta0 _ hθ)]
  exact Rcan_at_prior gamma0 nu0 alpha0 beta0 hnu0 halpha0 hbeta0

/-- If the NIG KL divergence vanishes, the two NIG laws coincide. -/
lemma nigMeasure_eq_of_nigKL_eq_zero {gamma nu alpha beta : ℝ}
    (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0)
    (h : nigKL gamma nu alpha beta gamma0 nu0 alpha0 beta0 = 0) :
    nigMeasure gamma nu alpha beta = nigMeasure gamma0 nu0 alpha0 beta0 := by
  have := isProbabilityMeasure_nigPrecMeasure (gamma := gamma) hnu halpha hbeta
  have := isProbabilityMeasure_nigPrecMeasure (gamma := gamma0) hnu0 halpha0 hbeta0
  have : IsProbabilityMeasure (nigMeasure gamma nu alpha beta) := by
    unfold nigMeasure; infer_instance
  have : IsProbabilityMeasure (nigMeasure gamma0 nu0 alpha0 beta0) := by
    unfold nigMeasure; infer_instance
  rw [← klDiv_eq_zero_iff]
  rw [nigKL, klDiv_nigMeasure hnu halpha hbeta hnu0 halpha0 hbeta0,
    ENNReal.toReal_ofReal (nigKLClosedForm_nonneg hnu halpha hbeta hnu0 halpha0 hbeta0)] at h
  rw [klDiv_nigMeasure hnu halpha hbeta hnu0 halpha0 hbeta0, h, ENNReal.ofReal_zero]

/-- `R_can(θ) > 0` for an admissible state with `α > 1` and `γ ≠ γ₀`. -/
theorem Rcan_pos_of_gamma_ne (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0)
    {θ : QuotientState} (hθ : θ ∈ admissibleQuotients) (halpha : 1 < θ.alpha)
    (hγ : θ.gamma ≠ gamma0) :
    0 < Rcan gamma0 nu0 alpha0 beta0 θ := by
  refine lt_of_le_of_ne (Rcan_nonneg θ) (Ne.symm fun h0 => hγ ?_)
  set nu := θ.nuCan gamma0 nu0 alpha0 beta0
  have hnu : 0 < nu := QuotientState.nuCan_mem gamma0 nu0 alpha0 beta0 hnu0 hbeta0 θ hθ
  have hbeta : 0 < θ.c * nu / (1 + nu) := beta_positive _ _ hθ.2 hnu
  have heq := nigMeasure_eq_of_nigKL_eq_zero hnu hθ.1 hbeta hnu0 halpha0 hbeta0 h0
  -- equal μ-marginals
  have hmu : nigMuMarginal θ.gamma nu θ.alpha (θ.c * nu / (1 + nu))
      = nigMuMarginal gamma0 nu0 alpha0 beta0 := by
    rw [← nigMeasure_map_snd hnu hθ.1 hbeta, ← nigMeasure_map_snd hnu0 halpha0 hbeta0, heq]
  -- mean under the posterior side is γ
  have hmean := integral_id_nigMuMarginal (gamma := θ.gamma) hnu halpha hbeta
  have hL := memLp_sub_nigMuMarginal (gamma := θ.gamma) hnu halpha hbeta
  -- centring under the prior side is γ₀
  have hcent : ∫ m, (m - gamma0) ∂(nigMuMarginal gamma0 nu0 alpha0 beta0) = 0 := by
    rw [nigMuMarginal_eq_studentT _ _ _ _ hnu0 halpha0 hbeta0]
    exact integral_sub_studentTMeasure _ _ _
  rw [hmu] at hmean hL
  have := isProbabilityMeasure_nigMuMarginal (gamma := gamma0) (nu := nu0) (alpha := alpha0)
    (beta := beta0) hnu0 halpha0 hbeta0
  have hid : Integrable (fun m : ℝ => m) (nigMuMarginal gamma0 nu0 alpha0 beta0) := by
    have h := (hL.integrable (by norm_num)).add (integrable_const θ.gamma)
    exact h.congr (ae_of_all _ fun m => by simp)
  rw [integral_sub hid (integrable_const _), hmean, integral_const, probReal_univ,
    one_smul] at hcent
  linarith

/--
**The outer optimum may depend on `λ`.** For every valid prior there is a
reconstruction term `L` (a function of the quotient state) and an admissible quotient
state `θ` that minimizes `J₃ = L + λ R_can` over admissible states for `λ = 1` but not
for `λ = 2`. So conditional weight invariance of `ν_can` does not extend to the outer
optimization.
-/
theorem outer_optimum_depends_on_weight (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0)
    (hbeta0 : 0 < beta0) :
    ∃ (L : QuotientState → ℝ) (θ : QuotientState), θ ∈ admissibleQuotients
      ∧ (∀ θ' ∈ admissibleQuotients,
          partialJ3 L (fiberKL gamma0 nu0 alpha0 beta0)
              (QuotientState.nuCan gamma0 nu0 alpha0 beta0) 1 θ
            ≤ partialJ3 L (fiberKL gamma0 nu0 alpha0 beta0)
              (QuotientState.nuCan gamma0 nu0 alpha0 beta0) 1 θ')
      ∧ ¬ (∀ θ' ∈ admissibleQuotients,
          partialJ3 L (fiberKL gamma0 nu0 alpha0 beta0)
              (QuotientState.nuCan gamma0 nu0 alpha0 beta0) 2 θ
            ≤ partialJ3 L (fiberKL gamma0 nu0 alpha0 beta0)
              (QuotientState.nuCan gamma0 nu0 alpha0 beta0) 2 θ') := by
  set L : QuotientState → ℝ := fun θ => -Rcan gamma0 nu0 alpha0 beta0 θ
  set θ1 : QuotientState := ⟨gamma0 + 1, 2, 1⟩
  have hθ1 : θ1 ∈ admissibleQuotients := ⟨by norm_num, by norm_num⟩
  have hpos : 0 < Rcan gamma0 nu0 alpha0 beta0 θ1 :=
    Rcan_pos_of_gamma_ne hnu0 halpha0 hbeta0 hθ1 (by norm_num) (by simp [θ1])
  have hθ0 : priorQuotient gamma0 nu0 alpha0 beta0 ∈ admissibleQuotients :=
    ⟨halpha0, priorC0_positive nu0 beta0 hnu0 hbeta0⟩
  refine ⟨L, θ1, hθ1, fun θ' _ => ?_, fun h => ?_⟩
  · simp only [partialJ3, L, Rcan, one_mul, neg_add_cancel, le_refl]
  · have := h _ hθ0
    simp only [partialJ3, L] at this
    change -Rcan gamma0 nu0 alpha0 beta0 θ1 + 2 * Rcan gamma0 nu0 alpha0 beta0 θ1
      ≤ -Rcan gamma0 nu0 alpha0 beta0 (priorQuotient gamma0 nu0 alpha0 beta0)
        + 2 * Rcan gamma0 nu0 alpha0 beta0 (priorQuotient gamma0 nu0 alpha0 beta0) at this
    rw [Rcan_prior_eq_zero hnu0 halpha0 hbeta0] at this
    linarith

end ELVAE
