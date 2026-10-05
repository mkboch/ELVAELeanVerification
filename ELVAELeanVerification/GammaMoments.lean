import Mathlib
import ELVAELeanVerification.RestrictedKLDivergence

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Moments of the Gamma law

For `τ ~ Gamma(shape a, rate b)` with density `gammaPDFReal a b` (mathlib), and
`a, b > 0`:

* `integral_gammaPDFReal_Ioi`: `∫ p = 1`;
* `integral_mul_gammaPDFReal`: `E[τ] = a/b`;
* `integral_log_mul_gammaPDFReal`: `E[log τ] = ψ(a) − log b`, where `ψ` is the
  real digamma function `realDigamma = logDeriv Real.Gamma`;

together with the integrability facts needed to use them. The log-moment rests
on mathlib's `Real.hasDerivAt_Gamma_of_pos`
(`Γ'(a) = ∫ t^(a−1) log t e^{−t} dt`) and the substitution `t ↦ b t`.
-/

namespace ELVAE

open MeasureTheory ProbabilityTheory Real Set

lemma abs_log_le_rpow_add {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) :
    |Real.log t| ≤ (t ^ δ + t ^ (-δ)) / δ := by
  have h1 : Real.log t ≤ t ^ δ / δ := Real.log_le_rpow_div ht.le hδ
  have h2 : -Real.log t ≤ t ^ (-δ) / δ := by
    have := Real.log_le_rpow_div (inv_pos.mpr ht).le hδ
    rwa [Real.log_inv, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le] at this
  have h3 : 0 ≤ t ^ δ / δ := by positivity
  have h4 : 0 ≤ t ^ (-δ) / δ := by positivity
  rw [add_div, abs_le]
  constructor <;> linarith

lemma integrableOn_rpow_mul_exp_neg_Ioi {s : ℝ} (hs : -1 < s) :
    IntegrableOn (fun t : ℝ => t ^ s * Real.exp (-t)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow hs one_pos one_pos
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp

/-- `t^(a-1) log t e^{-t}` is integrable on `(0, ∞)` for `a > 0`. -/
lemma integrableOn_rpow_mul_log_mul_exp_neg {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * (Real.log t * Real.exp (-t))) (Ioi 0) := by
  set δ := a / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hg : IntegrableOn (fun t : ℝ =>
      (1 / δ) * (t ^ (a - 1 + δ) * Real.exp (-t) + t ^ (a - 1 - δ) * Real.exp (-t))) (Ioi 0) :=
    ((integrableOn_rpow_mul_exp_neg_Ioi (by linarith)).add
      (integrableOn_rpow_mul_exp_neg_Ioi (by linarith))).const_mul _
  refine hg.mono' ?_ ?_
  · exact (by fun_prop : Measurable
      (fun t : ℝ => t ^ (a - 1) * (Real.log t * Real.exp (-t)))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    have hb := abs_log_le_rpow_add ht hδ
    have he : 0 < Real.exp (-t) := Real.exp_pos _
    have hp : 0 < t ^ (a - 1) := Real.rpow_pos_of_pos ht _
    rw [norm_mul, norm_mul, Real.norm_of_nonneg hp.le, Real.norm_of_nonneg he.le,
      Real.norm_eq_abs]
    have hsplit : t ^ (a - 1) * ((t ^ δ + t ^ (-δ)) / δ * Real.exp (-t))
        = (1 / δ) * (t ^ (a - 1 + δ) * Real.exp (-t) + t ^ (a - 1 - δ) * Real.exp (-t)) := by
      rw [Real.rpow_add ht, sub_eq_add_neg (a - 1) δ, Real.rpow_add ht]
      field_simp
    rw [← hsplit]
    gcongr

/-- `E[log τ] = ψ(a) − log b` under `Gamma(a, b)`. -/
theorem integral_log_mul_gammaPDFReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ t in Ioi 0, Real.log t * gammaPDFReal a b t = realDigamma a - Real.log b := by
  have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  set G : ℝ → ℝ := fun u =>
    (b / Real.Gamma a) * (u ^ (a - 1) * (Real.log u * Real.exp (-u))
      - Real.log b * (Real.exp (-u) * u ^ (a - 1))) with hGdef
  have hcomp : EqOn (fun t => Real.log t * gammaPDFReal a b t) (fun t => G (b * t)) (Ioi 0) := by
    intro t (ht : 0 < t)
    simp only [gammaPDFReal, ht.le, ↓reduceIte, hGdef]
    rw [Real.log_mul hb.ne' ht.ne', Real.mul_rpow hb.le ht.le]
    have hba : b ^ a = b * b ^ (a - 1) := by
      rw [← Real.rpow_one_add' hb.le (by linarith)]; congr 1; ring
    rw [hba]
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcomp, integral_comp_mul_left_Ioi G 0 hb,
    mul_zero, smul_eq_mul]
  have hI1 := integrableOn_rpow_mul_log_mul_exp_neg ha
  have hI2 := Real.GammaIntegral_convergent ha
  simp only [hGdef]
  rw [integral_const_mul, integral_sub hI1 (hI2.const_mul _), integral_const_mul,
    ← Real.Gamma_eq_integral ha, ← (Real.hasDerivAt_Gamma_of_pos ha).deriv]
  unfold realDigamma
  rw [logDeriv_apply]
  field_simp

lemma gammaPDFReal_of_pos {a b t : ℝ} (ht : 0 < t) :
    gammaPDFReal a b t = b ^ a / Real.Gamma a * (t ^ (a - 1) * Real.exp (-(b * t))) := by
  simp only [gammaPDFReal, ht.le, ↓reduceIte]
  ring

/-- `t^s e^{-bt}` is integrable on `(0,∞)` for `s > -1`, `b > 0`. -/
lemma integrableOn_rpow_mul_exp_neg_mul_Ioi {s b : ℝ} (hs : -1 < s) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ s * Real.exp (-(b * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow hs one_pos hb
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp

lemma integrableOn_rpow_mul_gammaPDFReal {a b s : ℝ} (hb : 0 < b) (hs : -a < s) :
    IntegrableOn (fun t : ℝ => t ^ s * gammaPDFReal a b t) (Ioi 0) := by
  have h : IntegrableOn (fun t : ℝ =>
      b ^ a / Real.Gamma a * (t ^ (s + (a - 1)) * Real.exp (-(b * t)))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_Ioi (s := s + (a - 1)) (by linarith) hb).const_mul _
  refine h.congr_fun (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
  dsimp only
  rw [gammaPDFReal_of_pos ht, Real.rpow_add ht]
  ring

lemma integrableOn_gammaPDFReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (gammaPDFReal a b) (Ioi 0) := by
  have h := integrableOn_rpow_mul_gammaPDFReal (a := a) hb (s := 0) (by linarith)
  refine h.congr_fun (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
  simp

lemma integrableOn_mul_gammaPDFReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t * gammaPDFReal a b t) (Ioi 0) := by
  have h := integrableOn_rpow_mul_gammaPDFReal (a := a) hb (s := 1) (by linarith)
  refine h.congr_fun (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
  simp

lemma integrableOn_log_mul_gammaPDFReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => Real.log t * gammaPDFReal a b t) (Ioi 0) := by
  set δ := a / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hδa : δ < a := by rw [hδdef]; linarith
  have hg : IntegrableOn (fun t : ℝ =>
      (1 / δ) * (t ^ δ * gammaPDFReal a b t + t ^ (-δ) * gammaPDFReal a b t)) (Ioi 0) :=
    ((integrableOn_rpow_mul_gammaPDFReal (a := a) hb (by linarith)).add
      (integrableOn_rpow_mul_gammaPDFReal (a := a) hb (by linarith))).const_mul _
  refine hg.mono' ?_ ?_
  · exact (by fun_prop : Measurable
      (fun t : ℝ => Real.log t * gammaPDFReal a b t)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    have hp := gammaPDFReal_nonneg ha hb t
    rw [norm_mul, Real.norm_of_nonneg hp, Real.norm_eq_abs]
    have hb' := abs_log_le_rpow_add ht hδ
    calc |Real.log t| * gammaPDFReal a b t
        ≤ (t ^ δ + t ^ (-δ)) / δ * gammaPDFReal a b t := by gcongr
      _ = _ := by ring

theorem integral_gammaPDFReal_Ioi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ t in Ioi 0, gammaPDFReal a b t = 1 := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t (ht : 0 < t) => gammaPDFReal_of_pos ht),
    integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi ha hb]
  have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  rw [one_div, Real.inv_rpow hb.le]
  have : 0 < b ^ a := Real.rpow_pos_of_pos hb a
  field_simp

theorem integral_mul_gammaPDFReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ t in Ioi 0, t * gammaPDFReal a b t = a / b := by
  have hpt : EqOn (fun t => t * gammaPDFReal a b t)
      (fun t => b ^ a / Real.Gamma a * (t ^ ((a + 1) - 1) * Real.exp (-(b * t)))) (Ioi 0) := by
    intro t (ht : 0 < t)
    dsimp only
    rw [gammaPDFReal_of_pos ht, show a + 1 - 1 = (a - 1) + 1 by ring, Real.rpow_add_one ht.ne']
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hb, Real.Gamma_add_one ha.ne']
  have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  rw [one_div, Real.inv_rpow hb.le, Real.rpow_add_one hb.ne']
  have : 0 < b ^ a := Real.rpow_pos_of_pos hb a
  field_simp

end ELVAE
