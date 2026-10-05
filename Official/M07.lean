import Mathlib
import Official.M06

/-!
# Prior self-consistency and the zero-divergence characterization

With `s₀ = β₀(1 + 1/n)` and `x₀ = (γ₀, A, s₀)`, the selected representative of
`F_{x₀}` is exactly the complete prior (`t_*(x₀) = 1/n`, `(γ, ν_sel, α, β_sel) = (γ₀, n, A, β₀)`),
and the minimized divergence is zero precisely at `x₀`.
-/

noncomputable section

namespace NIGBottleneck

open MeasureTheory ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal

section KLDensity

variable {X : Type*} [MeasurableSpace X]

/-- A density measure `f·m` is concentrated where `f > 0`. -/
lemma ae_withDensity_ofReal_pos (m : Measure X) {f : X → ℝ} (hf : Measurable f) :
    ∀ᵐ x ∂(m.withDensity fun x => ENNReal.ofReal (f x)), 0 < f x := by
  rw [ae_withDensity_iff hf.ennreal_ofReal]
  exact ae_of_all _ fun x hx => by
    by_contra h
    exact hx (ENNReal.ofReal_eq_zero.mpr (not_lt.mp h))

/-- KL divergence between density measures `f·m` and `g·m` when `f > 0 ⇒ g > 0`. -/
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

/-- `KL(f·m ‖ g·m) = ∫ f log(f/g) dm` for probability densities with `f > 0 ⇒ g > 0`. -/
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

end KLDensity

section NIGKL

/-- The NIG law of the model is a probability measure. -/
theorem isProbabilityMeasure_nigLaw (p : Parameters) : IsProbabilityMeasure (nigLaw p) := by
  constructor
  have hint : Integrable (fun q : ℝ × ℝ => nigDensity p q * (fun _ : ℝ => (1 : ℝ)) q.2) :=
    integrable_nig_mul_snd p measurable_const (by
      simpa using integrable_inverseGammaDensity ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩)
  have hval : ∫ q : ℝ × ℝ, nigDensity p q * (fun _ : ℝ => (1 : ℝ)) q.2 = 1 := by
    rw [integral_nig_mul_snd p measurable_const (by
      simpa using integrable_inverseGammaDensity ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩)]
    simpa using integral_inverseGammaDensity_params p
  simp only [mul_one] at hint hval
  rw [nigLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun q => nigDensity_nonneg p q), hval,
    ENNReal.ofReal_one]

lemma nigDensity_pos_of_pos (p p₀ : Parameters) (q : ℝ × ℝ) (h : 0 < nigDensity p q) :
    0 < nigDensity p₀ q := by
  have hx : 0 < q.2 := by
    by_contra hx
    rw [nigDensity_of_nonpos p q hx] at h
    exact lt_irrefl 0 h
  have hG : 0 < Real.Gamma p₀.alpha := Real.Gamma_pos_of_pos p₀.alpha_pos
  have hs : 0 < Real.sqrt (2 * Real.pi * (q.2 / p₀.nu)) :=
    Real.sqrt_pos.mpr (by have := div_pos hx p₀.nu_pos; positivity)
  have h1 := Real.rpow_pos_of_pos p₀.beta_pos p₀.alpha
  have h2 := Real.rpow_pos_of_pos hx (-p₀.alpha - 1)
  simp only [nigDensity, inverseGammaDensity, hx, ↓reduceIte, normalDensity, Real.rpow_eq_pow]
  exact mul_pos (by positivity) (mul_pos (inv_pos.mpr hs) (Real.exp_pos _))

/-- The volume-level integrability of `f log(f/g)` for the two NIG densities. -/
lemma integrable_nig_mul_logRatio (p p₀ : Parameters) :
    Integrable (fun q : ℝ × ℝ => nigDensity p q * Real.log (nigDensity p q / nigDensity p₀ q)) := by
  have h := integrable_nigLogRatio p p₀
  rw [nigLaw, integrable_withDensity_iff_integrable_smul' (measurable_nigDensity p).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at h
  refine h.congr (ae_of_all _ fun q => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (nigDensity_nonneg p q)]

/-- The model's hierarchical KL is the real value of Mathlib's KL divergence of the two
NIG laws. -/
theorem hierarchicalKL_eq_toReal_klDiv (p p₀ : Parameters) :
    hierarchicalKL p p₀ = (klDiv (nigLaw p) (nigLaw p₀)).toReal := by
  have hP : IsProbabilityMeasure (volume.withDensity fun q => ENNReal.ofReal (nigDensity p q)) :=
    isProbabilityMeasure_nigLaw p
  have hP0 : IsProbabilityMeasure (volume.withDensity fun q => ENNReal.ofReal (nigDensity p₀ q)) :=
    isProbabilityMeasure_nigLaw p₀
  have hint := integrable_nig_mul_logRatio p p₀
  have hkl := klDiv_withDensity_ofReal volume (measurable_nigDensity p) (measurable_nigDensity p₀)
    (nigDensity_nonneg p) (nigDensity_pos_of_pos p p₀) hint
  have hval : ∫ q : ℝ × ℝ, nigDensity p q * Real.log (nigDensity p q / nigDensity p₀ q)
      = hierarchicalKL p p₀ := by
    rw [hierarchicalKL, nigLaw, integral_withDensity_eq_integral_toReal_smul
      (measurable_nigDensity p).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    congr 1
    funext q
    rw [smul_eq_mul, ENNReal.toReal_ofReal (nigDensity_nonneg p q)]
  have hnn : 0 ≤ hierarchicalKL p p₀ := by
    obtain ⟨hac, hint', hv⟩ := llr_withDensity_ofReal volume (measurable_nigDensity p)
      (measurable_nigDensity p₀) (nigDensity_nonneg p) (nigDensity_pos_of_pos p p₀) hint
    have h0 := integral_llr_add_sub_measure_univ_nonneg hac hint'
    rw [hv, hval, probReal_univ, probReal_univ] at h0
    linarith
  change hierarchicalKL p p₀ = (klDiv (volume.withDensity fun q => ENNReal.ofReal (nigDensity p q))
    (volume.withDensity fun q => ENNReal.ofReal (nigDensity p₀ q))).toReal
  rw [hkl, hval, ENNReal.toReal_ofReal hnn]

/-- The hierarchical KL divergence is nonnegative. -/
theorem hierarchicalKL_nonneg (p p₀ : Parameters) : 0 ≤ hierarchicalKL p p₀ := by
  rw [hierarchicalKL_eq_toReal_klDiv]
  exact ENNReal.toReal_nonneg

/-- The hierarchical KL divergence vanishes exactly when the two NIG laws coincide. -/
theorem hierarchicalKL_eq_zero_iff (p p₀ : Parameters) :
    hierarchicalKL p p₀ = 0 ↔ nigLaw p = nigLaw p₀ := by
  have := isProbabilityMeasure_nigLaw p
  have := isProbabilityMeasure_nigLaw p₀
  have hP : IsProbabilityMeasure (volume.withDensity fun q => ENNReal.ofReal (nigDensity p q)) :=
    isProbabilityMeasure_nigLaw p
  have hP0 : IsProbabilityMeasure (volume.withDensity fun q => ENNReal.ofReal (nigDensity p₀ q)) :=
    isProbabilityMeasure_nigLaw p₀
  have hfin : klDiv (nigLaw p) (nigLaw p₀) ≠ ⊤ := by
    have hint := integrable_nig_mul_logRatio p p₀
    change klDiv (volume.withDensity fun q => ENNReal.ofReal (nigDensity p q))
      (volume.withDensity fun q => ENNReal.ofReal (nigDensity p₀ q)) ≠ ⊤
    rw [klDiv_withDensity_ofReal volume (measurable_nigDensity p) (measurable_nigDensity p₀)
      (nigDensity_nonneg p) (nigDensity_pos_of_pos p p₀) hint]
    exact ENNReal.ofReal_ne_top
  rw [hierarchicalKL_eq_toReal_klDiv, ENNReal.toReal_eq_zero_iff, or_iff_left hfin,
    klDiv_eq_zero_iff]

/-- Equal NIG laws give equal hierarchy laws, hence equal marginal laws of `z`. -/
theorem predictiveLaw_eq_of_nigLaw_eq {p q : Parameters} (h : nigLaw p = nigLaw q) :
    predictiveLaw p = predictiveLaw q := by
  have hmp := (measurable_nigDensity p).ennreal_ofReal
  have hmq := (measurable_nigDensity q).ennreal_ofReal
  have hae : (fun r => ENNReal.ofReal (nigDensity p r)) =ᵐ[volume]
      fun r => ENNReal.ofReal (nigDensity q r) :=
    (withDensity_eq_iff_of_sigmaFinite hmp.aemeasurable hmq.aemeasurable).mp h
  have hae' : (fun h : HierarchySpace => ENNReal.ofReal (hierarchyDensity p h)) =ᵐ[volume]
      fun h => ENNReal.ofReal (hierarchyDensity q h) := by
    rw [Measure.volume_eq_prod]
    have hnull : (volume.prod volume) ({r : ℝ × ℝ | ENNReal.ofReal (nigDensity p r)
        ≠ ENNReal.ofReal (nigDensity q r)} ×ˢ (univ : Set ℝ)) = 0 := by
      rw [Measure.prod_prod, (ae_iff).mp hae, zero_mul]
    refine measure_mono_null (fun h hh => ?_) hnull
    refine ⟨?_, mem_univ _⟩
    intro heq
    apply hh
    change ENNReal.ofReal (nigDensity p h.1 * normalDensity (meanCoordinate h)
        (varianceCoordinate h) (latentCoordinate h))
      = ENNReal.ofReal (nigDensity q h.1 * normalDensity (meanCoordinate h)
        (varianceCoordinate h) (latentCoordinate h))
    rw [ENNReal.ofReal_mul (nigDensity_nonneg p _), ENNReal.ofReal_mul (nigDensity_nonneg q _), heq]
  rw [predictiveLaw, predictiveLaw, hierarchyLaw, hierarchyLaw, withDensity_congr_ae hae']

end NIGKL

section SelfConsistency

variable (p₀ : Parameters)

/-- The prior quotient state `x₀ = (γ₀, A, s₀)` with `s₀ = β₀(1 + 1/n)`. -/
def priorQuotient : QuotientState := quotientCoordinates p₀

/-- `s₀ = β₀(1 + 1/n)`. -/
theorem priorQuotient_s : (priorQuotient p₀).s = p₀.beta * (1 + 1 / p₀.nu) := rfl

/-- The minimized divergence `F(x, t_*(x))`. -/
def minimizedKL (x : QuotientState) : ℝ := fiberKL p₀ x (selTPos p₀ x)

lemma parameters_ext {p q : Parameters} (h1 : p.gamma = q.gamma) (h2 : p.nu = q.nu)
    (h3 : p.alpha = q.alpha) (h4 : p.beta = q.beta) : p = q := by
  cases p
  cases q
  simp_all

/-- `t_*(x₀) = 1/n`. -/
theorem selT_priorQuotient : selT p₀ (priorQuotient p₀) = 1 / p₀.nu := by
  have hn := p₀.nu_pos
  have hb := p₀.beta_pos
  symm
  refine (selT_unique_solution p₀ (priorQuotient p₀) (1 / p₀.nu) (one_div_pos.mpr hn)).mp ?_
  simp only [selD, priorB, priorQuotient, quotientCoordinates, quotientScale, sub_self]
  field_simp
  ring

/-- The selected representative of `F_{x₀}` is exactly the complete prior,
`(γ, ν_sel, α, β_sel) = (γ₀, n, A, β₀)`. -/
theorem selected_priorQuotient :
    fiberParameters (priorQuotient p₀) (selTPos p₀ (priorQuotient p₀)) = p₀ := by
  have hn := p₀.nu_pos
  have hb := p₀.beta_pos
  have ht : (selTPos p₀ (priorQuotient p₀) : ℝ) = 1 / p₀.nu := selT_priorQuotient p₀
  apply parameters_ext
  · rfl
  · simp only [fiberParameters, ht]
    field_simp
  · rfl
  · simp only [fiberParameters]
    rw [ht]
    simp only [priorQuotient, quotientCoordinates, quotientScale]
    field_simp

/-- `(γ, ν_sel, α, β_sel) = (γ₀, n, A, β₀)` at `x₀`. -/
theorem selected_priorQuotient_coords :
    (priorQuotient p₀).gamma = p₀.gamma ∧ selNu p₀ (priorQuotient p₀) = p₀.nu ∧
      (priorQuotient p₀).alpha = p₀.alpha ∧ selBeta p₀ (priorQuotient p₀) = p₀.beta := by
  have h := congrArg (fun q : Parameters => (q.gamma, q.nu, q.alpha, q.beta))
    (selected_priorQuotient p₀)
  obtain ⟨-, h2, -, h4⟩ := selectedParameters_eq p₀ (priorQuotient p₀)
  simp only [Prod.mk.injEq] at h
  exact ⟨rfl, h2 ▸ h.2.1, rfl, h4 ▸ h.2.2.2⟩

/-- The minimized divergence is nonnegative. -/
theorem minimizedKL_nonneg (x : QuotientState) : 0 ≤ minimizedKL p₀ x :=
  hierarchicalKL_nonneg _ _

/-- The minimized divergence vanishes at `x₀`. -/
theorem minimizedKL_priorQuotient : minimizedKL p₀ (priorQuotient p₀) = 0 := by
  rw [minimizedKL, fiberKL, selected_priorQuotient, hierarchicalKL_eq_zero_iff]

/-- The minimized divergence is zero precisely at `x₀`. -/
theorem minimizedKL_eq_zero_iff (x : QuotientState) :
    minimizedKL p₀ x = 0 ↔ x = priorQuotient p₀ := by
  constructor
  · intro h
    rw [minimizedKL, fiberKL, hierarchicalKL_eq_zero_iff] at h
    have hpred := predictiveLaw_eq_of_nigLaw_eq h
    rw [predictiveLaw_eq_iff, quotientCoordinates_fiberParameters] at hpred
    exact hpred
  · rintro rfl
    exact minimizedKL_priorQuotient p₀

end SelfConsistency

end NIGBottleneck
