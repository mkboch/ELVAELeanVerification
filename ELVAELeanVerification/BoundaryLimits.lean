import Mathlib
import ELVAELeanVerification.RestrictedKLDivergence

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Boundary behaviour of the fiber objective

For the fiber objective

  R̃(ν) = (α₀ + 1/2) log ν − α₀ log(1 + ν) + B/ν

this module proves

  R̃(ν) → +∞  as ν → 0⁺   (requires only B > 0; any real α₀),
  R̃(ν) → +∞  as ν → +∞   (holds for every real α₀ and B),

and transfers both limits to `R̃ + C` for any constant `C`, and to the
literal fiber-restricted closed-form NIG KL divergence.
-/

namespace ELVAE

open Filter Topology

/-- `log(1 + x)` is continuous at `0`. -/
theorem continuousAt_log_one_add_zero :
    ContinuousAt (fun x : ℝ => Real.log (1 + x)) 0 :=
  (continuousAt_const.add continuousAt_id).log (by norm_num)

/-- `ν log ν → 0` as `ν → 0⁺`. -/
theorem tendsto_mul_log_nhdsGT_zero :
    Tendsto (fun x : ℝ => x * Real.log x) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.continuous_mul_log.tendsto 0).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simpa using h

/-- `ν log(1 + ν) → 0` as `ν → 0⁺`. -/
theorem tendsto_mul_log_one_add_nhdsGT_zero :
    Tendsto (fun x : ℝ => x * Real.log (1 + x)) (𝓝[>] 0) (𝓝 0) := by
  have h : ContinuousAt (fun x : ℝ => x * Real.log (1 + x)) 0 :=
    continuousAt_id.mul continuousAt_log_one_add_zero
  simpa using h.tendsto.mono_left nhdsWithin_le_nhds

/--
**Left endpoint.** For `B > 0` (and any real `α₀`),

  R̃(ν) → +∞  as ν → 0⁺.
-/
theorem fiberObjective_tendsto_atTop_nhdsGT_zero
    (alpha0 B : ℝ) (hB : 0 < B) :
    Tendsto (fun nu : ℝ => fiberObjective alpha0 B nu) (𝓝[>] 0) atTop := by
  -- R̃(ν) = (B + (α₀+1/2)·ν log ν − α₀·ν log(1+ν)) · ν⁻¹ for ν > 0.
  have hg : Tendsto
      (fun x : ℝ => B + (alpha0 + 1 / 2) * (x * Real.log x)
        - alpha0 * (x * Real.log (1 + x))) (𝓝[>] 0) (𝓝 B) := by
    have := ((tendsto_mul_log_nhdsGT_zero.const_mul (alpha0 + 1 / 2)).const_add B).sub
      (tendsto_mul_log_one_add_nhdsGT_zero.const_mul alpha0)
    simpa using this
  have hprod := Tendsto.pos_mul_atTop hB hg tendsto_inv_nhdsGT_zero
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := (Set.mem_Ioi.mp hx).ne'
  unfold fiberObjective
  field_simp
  ring

/--
**Right endpoint.** For every real `α₀` and `B`,

  R̃(ν) → +∞  as ν → +∞.
-/
theorem fiberObjective_tendsto_atTop_atTop
    (alpha0 B : ℝ) :
    Tendsto (fun nu : ℝ => fiberObjective alpha0 B nu) atTop atTop := by
  -- R̃(ν) = (1/2) log ν + (−α₀ log(1 + ν⁻¹) + B ν⁻¹) for ν > 0.
  have hlog : Tendsto (fun x : ℝ => (1 / 2 : ℝ) * Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop (by norm_num)
  have hlog1 : Tendsto (fun x : ℝ => Real.log (1 + x⁻¹)) atTop (𝓝 0) := by
    have h := continuousAt_log_one_add_zero.tendsto.comp tendsto_inv_atTop_zero
    simpa [Function.comp_def] using h
  have hrest : Tendsto (fun x : ℝ => -alpha0 * Real.log (1 + x⁻¹) + B * x⁻¹)
      atTop (𝓝 0) := by
    have := (hlog1.const_mul (-alpha0)).add (tendsto_inv_atTop_zero.const_mul B)
    simpa using this
  refine (hlog.atTop_add hrest).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hx0 : x ≠ 0 := hx.ne'
  have hsplit : Real.log (1 + x) = Real.log x + Real.log (1 + x⁻¹) := by
    rw [← Real.log_mul hx0 (by positivity)]
    congr 1
    field_simp
    ring
  unfold fiberObjective
  rw [hsplit, div_eq_mul_inv]
  ring

/-- Both limits persist after adding any `ν`-independent constant `C`. -/
theorem fiberObjective_add_const_boundary
    (alpha0 B C : ℝ) (hB : 0 < B) :
    Tendsto (fun nu : ℝ => fiberObjective alpha0 B nu + C) (𝓝[>] 0) atTop
      ∧ Tendsto (fun nu : ℝ => fiberObjective alpha0 B nu + C) atTop atTop :=
  ⟨(fiberObjective_tendsto_atTop_nhdsGT_zero alpha0 B hB).atTop_add tendsto_const_nhds,
    (fiberObjective_tendsto_atTop_atTop alpha0 B).atTop_add tendsto_const_nhds⟩

/--
**Boundary behaviour of the literal fiber-restricted closed-form NIG KL.** For every
admissible quotient state (`α > 0`, `c > 0`) and valid prior (`ν₀, β₀ > 0`),

  KL(NIG(γ, ν, α, cν/(1+ν)) ‖ p₀) → +∞  as ν → 0⁺ and as ν → +∞.
-/
theorem restrictedNIGKL_boundary
    (gamma0 nu0 alpha0 beta0 : ℝ) (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0)
    {θ : QuotientState} (hθ : θ ∈ admissibleQuotients) :
    Tendsto (restrictedNIGKL gamma0 nu0 alpha0 beta0 θ) (𝓝[>] 0) atTop
      ∧ Tendsto (restrictedNIGKL gamma0 nu0 alpha0 beta0 θ) atTop atTop := by
  have hB : 0 < θ.B gamma0 nu0 beta0 :=
    BFromParams_positive _ _ _ _ _ _ hθ.1 hθ.2 hnu0 hbeta0
  obtain ⟨h0, hinf⟩ := fiberObjective_add_const_boundary alpha0 (θ.B gamma0 nu0 beta0)
    (restrictedKLConstant θ.gamma θ.alpha θ.c gamma0 nu0 alpha0 beta0) hB
  have heq : ∀ nu : ℝ, 0 < nu →
      fiberObjective alpha0 (θ.B gamma0 nu0 beta0) nu
          + restrictedKLConstant θ.gamma θ.alpha θ.c gamma0 nu0 alpha0 beta0
        = restrictedNIGKL gamma0 nu0 alpha0 beta0 θ nu := fun nu hnu =>
    (nigKL_on_fiber _ _ _ _ _ _ _ _ hθ.2 hnu0 hnu).symm
  refine ⟨h0.congr' ?_, hinf.congr' ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact heq x hx
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact heq x hx

end ELVAE
