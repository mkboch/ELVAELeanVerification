import Mathlib
import Official.M03

/-!
# Nonredundant inverse-gamma mixture representation

Every predictive law `f_{γ,α,s}` of `Official.M03` is the law of `z` in the
hierarchy `V ~ IG(α, s)`, `z | V ~ N(γ, V)`, which is indexed exactly by the identifiable triple
`(γ, α, s)` and has no redundant parameter coordinate.
-/

noncomputable section

namespace NIGBottleneck

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

/-- The model's normal law is Mathlib's Gaussian law. -/
theorem normalLaw_eq_gaussianReal (m : ℝ) (v : PositiveReal) :
    normalLaw m v = gaussianReal m (v : ℝ).toNNReal := by
  have hv : (v : ℝ).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; exact v.property
  rw [normalLaw, gaussianReal_of_var_ne_zero _ hv]
  congr 1
  funext z
  rw [gaussianPDF, normalDensity_eq_gaussianPDFReal _ _ _ v.property.le]

/-- The nonredundant hierarchy `V ~ IG(α, s)`, `z | V ~ N(γ, V)`,
as the law of `z`. -/
def nonredundantLaw (x : QuotientState) : Measure ℝ :=
  (inverseGammaLaw ⟨x.alpha, x.alpha_pos⟩ ⟨x.s, x.s_pos⟩).bind
    (fun v => gaussianReal x.gamma v.toNNReal)

/-- The nonredundant hierarchy has the joint law of `(V, z)` with density
`IG(V; α, s) · N(z; γ, V)`. -/
def nonredundantJointLaw (x : QuotientState) : Measure (ℝ × ℝ) :=
  volume.withDensity (fun q => ENNReal.ofReal
    (inverseGammaDensity x.alpha x.s q.1 * normalDensity x.gamma q.1 q.2))

lemma measurable_gaussian_variance_kernel (m : ℝ) :
    Measurable (fun v : ℝ => gaussianReal m v.toNNReal) :=
  measurable_gaussianReal.comp (measurable_const.prodMk measurable_id.real_toNNReal)

/-- Every law in the predictive-density family has the hierarchical
representation `V ~ IG(α, s)`, `z | V ~ N(γ, V)`. -/
theorem nonredundantLaw_eq_quotientLaw (x : QuotientState) :
    nonredundantLaw x = quotientLaw x := by
  have hk : Measurable (fun v : ℝ => gaussianReal x.gamma v.toNNReal) :=
    measurable_gaussian_variance_kernel x.gamma
  rw [nonredundantLaw, inverseGammaLaw_eq_invGammaMeasure, invGammaMeasure,
    bind_map_eq_bind_comp measurable_inv hk]
  have hcomp : ((fun v : ℝ => gaussianReal x.gamma v.toNNReal) ∘ fun t : ℝ => t⁻¹)
      = fun t => gaussianReal x.gamma (1 / t).toNNReal := by
    funext t
    simp [one_div]
  rw [hcomp, gamma_mixture_gaussian_eq_studentT _ _ _ _ x.alpha_pos x.s_pos one_pos,
    studentTMeasure, quotientLaw, one_mul]
  congr 1
  funext z
  congr 1
  exact studentTPDFReal_eq_displayedPredictiveDensity x z

/-- The marginal law of `z` of the original four-parameter hierarchy is the
law of `z` in the nonredundant hierarchy with the triple `(γ, α, s)` of `Official.M03`. -/
theorem predictiveLaw_eq_nonredundantLaw (p : Parameters) :
    predictiveLaw p = nonredundantLaw (quotientCoordinates p) := by
  rw [predictiveLaw_eq_quotientLaw, nonredundantLaw_eq_quotientLaw]

/-- The representation has no redundant parameter coordinate: distinct
triples `(γ, α, s)` give distinct marginal laws. -/
theorem nonredundantLaw_injective : Function.Injective nonredundantLaw := by
  intro x y h
  rw [nonredundantLaw_eq_quotientLaw, nonredundantLaw_eq_quotientLaw] at h
  exact quotientLaw_injective h

/-- The representation uses exactly the identifiable triple: it is indexed
by `Q = ℝ × (0,∞) × (0,∞)`, every triple is realized by an admissible quadruple, and two
quadruples give the same law exactly when their triples agree. -/
theorem nonredundantLaw_uses_exactly_triple :
    Function.Injective nonredundantLaw ∧
      (∀ x : QuotientState, ∃ p : Parameters, predictiveLaw p = nonredundantLaw x) ∧
      (∀ p q : Parameters, predictiveLaw p = predictiveLaw q ↔
        quotientCoordinates p = quotientCoordinates q) := by
  refine ⟨nonredundantLaw_injective, fun x => ?_, predictiveLaw_eq_iff⟩
  obtain ⟨p, hp⟩ := quotientCoordinates_surjective x
  exact ⟨p, by rw [predictiveLaw_eq_nonredundantLaw, hp]⟩

/-- The joint law of `(V, z)` has marginal law `nonredundantLaw x` for `z` (the density form of the
two-layer hierarchy). -/
theorem nonredundantJointLaw_map_snd (x : QuotientState) :
    (nonredundantJointLaw x).map Prod.snd = nonredundantLaw x := by
  have hk : Measurable (fun v : ℝ => gaussianReal x.gamma v.toNNReal) :=
    measurable_gaussian_variance_kernel x.gamma
  have hIG := measurable_inverseGammaDensity x.alpha x.s
  have hdens : Measurable (fun q : ℝ × ℝ =>
      inverseGammaDensity x.alpha x.s q.1 * normalDensity x.gamma q.1 q.2) := by
    unfold normalDensity
    fun_prop
  ext s hs
  rw [Measure.map_apply measurable_snd hs, nonredundantJointLaw,
    withDensity_apply _ (measurable_snd hs), nonredundantLaw, Measure.bind_apply hs hk.aemeasurable,
    inverseGammaLaw, lintegral_withDensity_eq_lintegral_mul _ hIG.ennreal_ofReal
      (g := fun v => gaussianReal x.gamma v.toNNReal s) ((Measure.measurable_coe hs).comp hk),
    ← lintegral_indicator (measurable_snd hs), Measure.volume_eq_prod,
    lintegral_prod _ ((hdens.ennreal_ofReal.indicator (measurable_snd hs)).aemeasurable)]
  refine lintegral_congr fun v => ?_
  by_cases hv : 0 < v
  · have hv' : v.toNNReal ≠ 0 := by
      rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hv
    have hfun : (fun z => (Prod.snd ⁻¹' s).indicator (fun q : ℝ × ℝ => ENNReal.ofReal
        (inverseGammaDensity x.alpha x.s q.1 * normalDensity x.gamma q.1 q.2)) (v, z))
        = s.indicator (fun z => ENNReal.ofReal (inverseGammaDensity x.alpha x.s v)
            * gaussianPDF x.gamma v.toNNReal z) := by
      funext z
      by_cases hz : z ∈ s
      · rw [Set.indicator_of_mem (show (v, z) ∈ Prod.snd ⁻¹' s from hz), Set.indicator_of_mem hz,
          gaussianPDF, ← ENNReal.ofReal_mul
          (inverseGammaDensity_nonneg _ _ _ x.alpha_pos x.s_pos.le),
          normalDensity_eq_gaussianPDFReal _ _ _ hv.le]
      · rw [Set.indicator_of_notMem (show (v, z) ∉ Prod.snd ⁻¹' s from hz),
          Set.indicator_of_notMem hz]
    rw [hfun, lintegral_indicator hs, lintegral_const_mul _ (measurable_gaussianPDF _ _)]
    change _ = ENNReal.ofReal (inverseGammaDensity x.alpha x.s v)
      * gaussianReal x.gamma v.toNNReal s
    rw [gaussianReal_apply _ hv']
  · have h0 : inverseGammaDensity x.alpha x.s v = 0 := inverseGammaDensity_of_nonpos _ _ _ hv
    have hfun : (fun z => (Prod.snd ⁻¹' s).indicator (fun q : ℝ × ℝ => ENNReal.ofReal
        (inverseGammaDensity x.alpha x.s q.1 * normalDensity x.gamma q.1 q.2)) (v, z))
        = fun _ => 0 := by
      funext z
      simp [Set.indicator, h0]
    simp [hfun, h0]

end NIGBottleneck
