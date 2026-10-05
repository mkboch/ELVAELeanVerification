import Mathlib
import ELVAELeanVerification.ManuscriptForms
import ELVAELeanVerification.PriorGaugeWitnesses

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# The joint KL with a shared conditional

* `conditional_kl_vanishes`, `joint_kl_eq_manuscriptNIGKL`: when
  the variational conditional of `z` equals the generative one,
  `q(z | μ, σ², y) = p(z | μ, σ²) = N(μ, σ²)`, the KL divergence of the joint laws
  of `(μ, σ², z)` equals `D_KL[q(μ, σ² | y) ‖ p₀]`: the conditional `z`-level KL
  term vanishes identically. The joint laws are the composition products of the NIG
  law with the kernel `(μ, σ²) ↦ N(μ, σ²)`.
* **Nonlinear aggregation** (`nonlinear_aggregation_can_reverse_ranks`): averaging coordinatewise
  scores can destroy rank equivalence even under a common prior. Averaging `T`
  and averaging `1/ν_can` over two latent coordinates rank two inputs oppositely.
-/

namespace ELVAE

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

/-! ## The conditional `z`-level KL term vanishes -/

/-- The generative conditional `z | μ, σ² ~ N(μ, σ²)` as a Markov kernel on `(μ, σ²)`. -/
noncomputable def zKernel : Kernel (ℝ × ℝ) ℝ where
  toFun p := gaussianReal p.1 p.2.toNNReal
  measurable' := measurable_gaussianReal.comp (measurable_fst.prodMk measurable_snd.real_toNNReal)

instance : IsMarkovKernel zKernel := ⟨fun p => by
  change IsProbabilityMeasure (gaussianReal p.1 p.2.toNNReal)
  infer_instance⟩

lemma isProbabilityMeasure_nigMeasureMuSigma {gamma nu alpha beta : ℝ}
    (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta) :
    IsProbabilityMeasure (nigMeasureMuSigma gamma nu alpha beta) := by
  have := isProbabilityMeasure_nigPrecMeasure (gamma := gamma) hnu halpha hbeta
  unfold nigMeasureMuSigma nigMeasure
  infer_instance

/--
With the shared conditional `z | μ, σ² ~ N(μ, σ²)`, the KL divergence
between the joint laws of `(μ, σ², z)` equals the KL divergence between the laws of
`(μ, σ²)`: the conditional `z`-level term vanishes identically.
-/
theorem conditional_kl_vanishes {gamma nu alpha beta gamma0 nu0 alpha0 beta0 : ℝ}
    (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0) :
    klDiv (nigMeasureMuSigma gamma nu alpha beta ⊗ₘ zKernel)
        (nigMeasureMuSigma gamma0 nu0 alpha0 beta0 ⊗ₘ zKernel)
      = klDiv (nigMeasureMuSigma gamma nu alpha beta)
          (nigMeasureMuSigma gamma0 nu0 alpha0 beta0) := by
  have := isProbabilityMeasure_nigMeasureMuSigma (gamma := gamma) hnu halpha hbeta
  have := isProbabilityMeasure_nigMeasureMuSigma (gamma := gamma0) hnu0 halpha0 hbeta0
  exact klDiv_compProd_left _ _ _

/-- Consequently the joint KL equals the expanded closed form `manuscriptNIGKL`. -/
theorem joint_kl_eq_manuscriptNIGKL {gamma nu alpha beta gamma0 nu0 alpha0 beta0 : ℝ}
    (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0) :
    klDiv (nigMeasureMuSigma gamma nu alpha beta ⊗ₘ zKernel)
        (nigMeasureMuSigma gamma0 nu0 alpha0 beta0 ⊗ₘ zKernel)
      = ENNReal.ofReal (manuscriptNIGKL gamma nu alpha beta gamma0 nu0 alpha0 beta0) := by
  rw [conditional_kl_vanishes hnu halpha hbeta hnu0 halpha0 hbeta0,
    klDiv_eq_manuscriptNIGKL hnu halpha hbeta hnu0 halpha0 hbeta0]

/-! ## Nonlinear aggregation can destroy rank equivalence -/

/-- Common prior `(γ₀, ν₀, α₀, β₀) = (0, 2, 1/2, 1)`; states `(γ, α, c) = (0, 1, c)`. -/
lemma aggregation_T (c : ℝ) : TFromParams 0 1 c 0 2 1 = c := by
  unfold TFromParams rho0FromPrior
  norm_num

lemma aggregation_g_8_7 : invNuCan (1 / 2) (BFromParams 0 1 (8 / 7) 0 2 1) = 1 / 3 := by
  have hB : BFromParams 0 1 (8 / 7) 0 2 1 = 15 / 8 := by unfold BFromParams; norm_num
  rw [hB, invNuCan, nuCan, sqrt_eq_of_sq (y := 17 / 8) (by norm_num) (by norm_num)]
  norm_num

lemma aggregation_g_3 : invNuCan (1 / 2) (BFromParams 0 1 3 0 2 1) = 1 / 2 := by
  have hB : BFromParams 0 1 3 0 2 1 = 4 / 3 := by unfold BFromParams; norm_num
  rw [hB, invNuCan, nuCan, sqrt_eq_of_sq (y := 5 / 3) (by norm_num) (by norm_num)]
  norm_num

lemma aggregation_g_11_49 : invNuCan (1 / 2) (BFromParams 0 1 (11 / 49) 0 2 1) = 1 / 10 := by
  have hB : BFromParams 0 1 (11 / 49) 0 2 1 = 60 / 11 := by unfold BFromParams; norm_num
  rw [hB, invNuCan, nuCan, sqrt_eq_of_sq (y := 61 / 11) (by norm_num) (by norm_num)]
  norm_num

/--
**Nonlinear aggregation can destroy rank equivalence.** Under one common prior
(`(γ₀, ν₀, α₀, β₀) = (0, 2, 1/2, 1)`), input A has two latent coordinates in state
`(0, 1, 8/7)` and input B has coordinates in states `(0, 1, 3)` and `(0, 1, 11/49)`.
Averaging `T` ranks A below B, while averaging `1/ν_can` ranks A above B; coordinatewise,
each ordering is preserved.
-/
theorem nonlinear_aggregation_can_reverse_ranks :
    let T := fun c : ℝ => TFromParams 0 1 c 0 2 1
    let g := fun c : ℝ => invNuCan (1 / 2) (BFromParams 0 1 c 0 2 1)
    (T (8 / 7) + T (8 / 7)) / 2 < (T 3 + T (11 / 49)) / 2
      ∧ (g 3 + g (11 / 49)) / 2 < (g (8 / 7) + g (8 / 7)) / 2 := by
  intro T g
  simp only [T, g, aggregation_T, aggregation_g_8_7, aggregation_g_3, aggregation_g_11_49]
  norm_num

end ELVAE
