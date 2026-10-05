import Mathlib
import ELVAELeanVerification.NIGStudentTMarginal
import ELVAELeanVerification.GammaMoments

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# The inverse-gamma law has the standard density

The formalization defines `InvGamma(α, β)` as the push-forward of mathlib's
`Gamma(shape α, rate β)` under `τ ↦ 1/τ` (`invGammaMeasure`). The standard
definition is by its density:

  p(x | α, β) = β^α / Γ(α) · x^{−α−1} · exp(−β/x),   x > 0.

`invGammaMeasure_eq_withDensity` proves that the two definitions give the same
measure, by the change of variables `x = 1/t` on `(0, ∞)`.
-/

namespace ELVAE

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

/-- The inverse-gamma density, zero for `x ≤ 0`. -/
noncomputable def invGammaPDFReal (alpha beta x : ℝ) : ℝ :=
  if 0 < x then beta ^ alpha / Real.Gamma alpha * x ^ (-alpha - 1) * Real.exp (-(beta / x))
  else 0

lemma gammaPDF_Iic_zero (a b : ℝ) : ∫⁻ t in Iic (0 : ℝ), gammaPDF a b t = 0 := by
  rw [← setLIntegral_congr Iio_ae_eq_Iic]
  exact lintegral_gammaPDF_of_nonpos le_rfl

/-- Restricting a gamma-density integral to the positive half-line loses nothing. -/
lemma setLIntegral_gammaPDF_inter_Ioi (a b : ℝ) (A : Set ℝ) :
    ∫⁻ t in A, gammaPDF a b t = ∫⁻ t in A ∩ Ioi 0, gammaPDF a b t := by
  rw [← lintegral_inter_add_sdiff _ A (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
  have hzero : ∫⁻ t in A \ Ioi 0, gammaPDF a b t = 0 := by
    refine le_antisymm ?_ bot_le
    calc ∫⁻ t in A \ Ioi 0, gammaPDF a b t ≤ ∫⁻ t in Iic 0, gammaPDF a b t :=
          lintegral_mono_set fun t ht => by
            simpa using ht.2
      _ = 0 := gammaPDF_Iic_zero a b
  rw [hzero, add_zero]

/--
For `α > 0` (and any `β`; the identity is a pure change of variables),
the push-forward definition of `InvGamma(α, β)` agrees
with the density definition.
-/
theorem invGammaMeasure_eq_withDensity (alpha beta : ℝ) (halpha : 0 < alpha) :
    invGammaMeasure alpha beta
      = volume.withDensity fun x => ENNReal.ofReal (invGammaPDFReal alpha beta x) := by
  have hmeasIG : Measurable fun x => ENNReal.ofReal (invGammaPDFReal alpha beta x) := by
    unfold invGammaPDFReal
    refine Measurable.ennreal_ofReal (Measurable.ite measurableSet_Ioi ?_ measurable_const)
    fun_prop
  ext s hs
  rw [invGammaMeasure, Measure.map_apply measurable_inv hs, gammaMeasure,
    withDensity_apply _ (measurable_inv hs), withDensity_apply _ hs,
    setLIntegral_gammaPDF_inter_Ioi alpha beta _]
  -- the density side, restricted to `(0, ∞)`
  have hRHS : ∫⁻ x in s, ENNReal.ofReal (invGammaPDFReal alpha beta x)
      = ∫⁻ x in s ∩ Ioi 0, ENNReal.ofReal (invGammaPDFReal alpha beta x) := by
    rw [← lintegral_inter_add_sdiff _ s (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    have hzero : ∫⁻ x in s \ Ioi 0, ENNReal.ofReal (invGammaPDFReal alpha beta x) = 0 := by
      rw [setLIntegral_congr_fun (hs.diff measurableSet_Ioi) (g := fun _ => 0)
        (fun x hx => by
          have hx2 : ¬ 0 < x := hx.2
          simp [invGammaPDFReal, hx2])]
      simp
    rw [hzero, add_zero]
  rw [hRHS]
  -- change of variables `x = t⁻¹` on `S = inv⁻¹' s ∩ (0, ∞)`
  set S := (fun t : ℝ => t⁻¹) ⁻¹' s ∩ Ioi 0 with hS
  have hSmeas : MeasurableSet S := (measurable_inv hs).inter measurableSet_Ioi
  have himage : (fun t : ℝ => t⁻¹) '' S = s ∩ Ioi 0 := by
    ext x
    constructor
    · rintro ⟨t, ⟨ht, (htpos : 0 < t)⟩, rfl⟩
      exact ⟨ht, inv_pos.mpr htpos⟩
    · rintro ⟨hx, (hxpos : 0 < x)⟩
      exact ⟨x⁻¹, ⟨by simpa using hx, inv_pos.mpr hxpos⟩, inv_inv x⟩
  have hderiv : ∀ t ∈ S, HasDerivWithinAt (fun t : ℝ => t⁻¹) (-(t ^ 2)⁻¹) S t :=
    fun t ht => (hasDerivAt_inv (ne_of_gt ht.2)).hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => t⁻¹) S := fun a _ b _ h => inv_injective h
  rw [← himage, lintegral_image_eq_lintegral_abs_deriv_mul hSmeas hderiv hinj]
  refine setLIntegral_congr_fun hSmeas fun t ht => ?_
  have htpos : 0 < t := ht.2
  have hG : 0 < Real.Gamma alpha := Real.Gamma_pos_of_pos halpha
  rw [gammaPDF, gammaPDFReal_of_pos htpos, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  simp only [invGammaPDFReal, inv_pos.mpr htpos, ↓reduceIte, abs_neg,
    abs_of_pos (inv_pos.mpr (pow_pos htpos 2)), div_inv_eq_mul]
  rw [Real.inv_rpow htpos.le, ← Real.rpow_neg htpos.le, neg_sub, sub_neg_eq_add]
  have hpow : t ^ (alpha - 1) = (t ^ 2)⁻¹ * t ^ (1 + alpha) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg htpos.le, ← Real.rpow_add htpos]
    congr 1
    push_cast
    ring
  rw [hpow]
  ring

/-- Measurability of the inverse-gamma density. -/
lemma measurable_invGammaPDF (alpha beta : ℝ) :
    Measurable fun x => ENNReal.ofReal (invGammaPDFReal alpha beta x) := by
  unfold invGammaPDFReal
  refine Measurable.ennreal_ofReal (Measurable.ite measurableSet_Ioi ?_ measurable_const)
  fun_prop

/--
**Inverse-gamma scale property.** For `k > 0`,
if `σ² ~ InvGamma(α, β)` then `k σ² ~ InvGamma(α, k β)`. With `k = 1 + 1/ν` this is
`ω² = σ²(1 + 1/ν) ~ InvGamma(α, c)`.
-/
theorem invGammaMeasure_map_const_mul (alpha beta k : ℝ) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hk : 0 < k) :
    (invGammaMeasure alpha beta).map (fun x => k * x) = invGammaMeasure alpha (k * beta) := by
  have hg : Measurable fun x : ℝ => k * x := measurable_const_mul k
  rw [invGammaMeasure_eq_withDensity alpha beta halpha,
    invGammaMeasure_eq_withDensity alpha (k * beta) halpha]
  ext s hs
  rw [Measure.map_apply hg hs, withDensity_apply _ (hg hs), withDensity_apply _ hs]
  set S := (fun x : ℝ => k * x) ⁻¹' s with hS
  have himage : (fun x : ℝ => k * x) '' S = s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy
      exact ⟨y / k, by simpa [S, mul_div_cancel₀ y hk.ne'] using hy, mul_div_cancel₀ y hk.ne'⟩
  have hderiv : ∀ x ∈ S, HasDerivWithinAt (fun x : ℝ => k * x) k S x := fun x _ => by
    simpa using ((hasDerivAt_id x).const_mul k).hasDerivWithinAt
  have hinj : InjOn (fun x : ℝ => k * x) S := fun a _ b _ h => mul_left_cancel₀ hk.ne' h
  rw [← himage, lintegral_image_eq_lintegral_abs_deriv_mul (hg hs) hderiv hinj]
  refine setLIntegral_congr_fun (hg hs) fun x _ => ?_
  rw [abs_of_pos hk, ← ENNReal.ofReal_mul hk.le]
  congr 1
  by_cases hx : 0 < x
  · have hkx : 0 < k * x := mul_pos hk hx
    simp only [invGammaPDFReal, hx, hkx, ↓reduceIte]
    rw [Real.mul_rpow hk.le hbeta.le, Real.mul_rpow hk.le hx.le]
    have hexp : Real.exp (-(k * beta / (k * x))) = Real.exp (-(beta / x)) := by
      congr 2; field_simp
    have hkpow : k * k ^ alpha * k ^ (-alpha - 1) = 1 := by
      rw [show k * k ^ alpha * k ^ (-alpha - 1) = k ^ ((1 : ℝ) + alpha + (-alpha - 1)) by
        rw [Real.rpow_add hk, Real.rpow_add hk, Real.rpow_one]]
      rw [show (1 : ℝ) + alpha + (-alpha - 1) = 0 by ring, Real.rpow_zero]
    rw [hexp]
    calc beta ^ alpha / Real.Gamma alpha * x ^ (-alpha - 1) * Real.exp (-(beta / x))
        = (k * k ^ alpha * k ^ (-alpha - 1)) * (beta ^ alpha / Real.Gamma alpha
            * x ^ (-alpha - 1) * Real.exp (-(beta / x))) := by rw [hkpow, one_mul]
      _ = _ := by ring
  · have hkx : ¬ 0 < k * x := fun h => hx (pos_of_mul_pos_right h hk.le)
    simp [invGammaPDFReal, hx, hkx]

end ELVAE
