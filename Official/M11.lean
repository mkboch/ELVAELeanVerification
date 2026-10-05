import Mathlib
import Official.M06

/-!
# Uncertainty decomposition

For `α > 1` the aleatoric part `u_var = E[X]`, the epistemic part
`u_epi = Var(μ)` and the total `V_z = Var(z)` are computed from the specified laws:
`u_var = s/((α−1)(1+t))`, `u_epi = st/((α−1)(1+t))`, `V_z = u_var + u_epi = s/(α−1)` on the fiber
`F_x`; at the selected representative the ratios are `t_*`, `t_*/(1+t_*)` and `1/(1+t_*)`. The
total is determined by the marginal law of `z`; the split is not.
-/

noncomputable section

namespace NIGBottleneck

open MeasureTheory ProbabilityTheory

section Generic

variable {Ω : Type*} [MeasurableSpace Ω]

/-- If `E[(Y − c)²] = K + (m − c)²` for every `c`, then `E[Y] = m` and `Var(Y) = K`. -/
lemma mean_variance_of_sq_moments (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : AEMeasurable Y μ) (m K : ℝ) (hint : ∀ c, Integrable (fun ω => (Y ω - c) ^ 2) μ)
    (hval : ∀ c, ∫ ω, (Y ω - c) ^ 2 ∂μ = K + (m - c) ^ 2) :
    ∫ ω, Y ω ∂μ = m ∧ Var[Y; μ] = K := by
  have hmean : ∫ ω, Y ω ∂μ = m := by
    have h : ∫ ω, Y ω ∂μ
        = ∫ ω, (m + ((Y ω - (m - 1)) ^ 2 - (Y ω - (m + 1)) ^ 2) / 4) ∂μ :=
      integral_congr_ae (ae_of_all _ fun ω => by ring)
    have i1 : Integrable (fun ω => ((Y ω - (m - 1)) ^ 2 - (Y ω - (m + 1)) ^ 2) / 4) μ :=
      ((hint _).sub (hint _)).div_const 4
    have i2 : ∫ ω, ((Y ω - (m - 1)) ^ 2 - (Y ω - (m + 1)) ^ 2) ∂μ
        = ∫ ω, (Y ω - (m - 1)) ^ 2 ∂μ - ∫ ω, (Y ω - (m + 1)) ^ 2 ∂μ :=
      integral_sub (hint _) (hint _)
    rw [h, integral_add (integrable_const m) i1, integral_const, probReal_univ, one_smul,
      integral_div, i2, hval, hval]
    ring
  refine ⟨hmean, ?_⟩
  rw [variance_eq_integral hY, hmean, hval]
  ring

end Generic

section Laws

variable (p : Parameters)

lemma hierarchyDensity_nonneg (h : HierarchySpace) : 0 ≤ hierarchyDensity p h :=
  mul_nonneg (nigDensity_nonneg p h.1) (normalDensity_nonneg _ _ _)

lemma integral_nigLaw (g : ℝ × ℝ → ℝ) :
    ∫ q, g q ∂nigLaw p = ∫ q, nigDensity p q * g q := by
  rw [nigLaw, integral_withDensity_eq_integral_toReal_smul
    (measurable_nigDensity p).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext q
  rw [smul_eq_mul, ENNReal.toReal_ofReal (nigDensity_nonneg p q)]

lemma integrable_nigLaw_iff (g : ℝ × ℝ → ℝ) :
    Integrable g (nigLaw p) ↔ Integrable (fun q => nigDensity p q * g q) := by
  rw [nigLaw, integrable_withDensity_iff_integrable_smul' (measurable_nigDensity p).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have h : (fun q => (ENNReal.ofReal (nigDensity p q)).toReal • g q)
      = fun q => nigDensity p q * g q := by
    funext q
    rw [smul_eq_mul, ENNReal.toReal_ofReal (nigDensity_nonneg p q)]
  rw [h]

lemma integral_predictiveLaw {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ z, g z ∂predictiveLaw p = ∫ h, hierarchyDensity p h * g h.2 := by
  have hlat : Measurable latentCoordinate := measurable_snd
  rw [predictiveLaw, integral_map hlat.aemeasurable hg.aestronglyMeasurable, hierarchyLaw,
    integral_withDensity_eq_integral_toReal_smul (measurable_hierarchyDensity p).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext h
  rw [smul_eq_mul, ENNReal.toReal_ofReal (hierarchyDensity_nonneg p h)]
  rfl

lemma integrable_predictiveLaw_iff {g : ℝ → ℝ} (hg : Measurable g) :
    Integrable g (predictiveLaw p) ↔ Integrable (fun h => hierarchyDensity p h * g h.2) := by
  have hlat : Measurable latentCoordinate := measurable_snd
  rw [predictiveLaw, integrable_map_measure hg.aestronglyMeasurable hlat.aemeasurable, hierarchyLaw,
    integrable_withDensity_iff_integrable_smul' (measurable_hierarchyDensity p).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have h : (fun h => (ENNReal.ofReal (hierarchyDensity p h)).toReal • (g ∘ latentCoordinate) h)
      = fun h => hierarchyDensity p h * g h.2 := by
    funext h
    rw [smul_eq_mul, ENNReal.toReal_ofReal (hierarchyDensity_nonneg p h)]
    rfl
  rw [h]

theorem isProbabilityMeasure_nigLaw' : IsProbabilityMeasure (nigLaw p) := by
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

end Laws

section Moments

variable (p : Parameters) (ha : 1 < p.alpha)
include ha

lemma integrable_ig_mul_id :
    Integrable (fun x => inverseGammaDensity p.alpha p.beta x * x) :=
  (integrable_inverseGammaLaw_iff ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩ (fun x => x)).mp
    (inverseGamma_integrable_id _ _ ha)

lemma integral_ig_mul_id :
    ∫ x, inverseGammaDensity p.alpha p.beta x * x = p.beta / (p.alpha - 1) :=
  (integral_inverseGammaLaw ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩ (fun x => x)).symm.trans
    (inverseGamma_integral_id _ _ ha)

lemma integrable_ig_mul_affine (a b : ℝ) :
    Integrable (fun x => inverseGammaDensity p.alpha p.beta x * 1 * (x / a + b)) := by
  have h1 := (integrable_ig_mul_id p ha).div_const a
  have h2 :=
    (integrable_inverseGammaDensity ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩).mul_const b
  refine (h1.add h2).congr (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply]
  ring

lemma integral_ig_mul_affine (a b : ℝ) :
    ∫ x, inverseGammaDensity p.alpha p.beta x * 1 * (x / a + b)
      = p.beta / (p.alpha - 1) / a + b := by
  have h1 := (integrable_ig_mul_id p ha).div_const a
  have h2 :=
    (integrable_inverseGammaDensity ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩).mul_const b
  have h : (fun x => inverseGammaDensity p.alpha p.beta x * 1 * (x / a + b))
      = fun x => inverseGammaDensity p.alpha p.beta x * x / a
        + inverseGammaDensity p.alpha p.beta x * b := by
    funext x
    ring
  rw [h, integral_add h1 h2, integral_div, integral_mul_const, integral_ig_mul_id p ha,
    integral_inverseGammaDensity_params]
  ring

/-- `E[X] = β/(α−1)` under `NIG(γ,ν,α,β)`. -/
lemma integral_nigLaw_snd : ∫ q, q.2 ∂nigLaw p = p.beta / (p.alpha - 1) := by
  rw [integral_nigLaw]
  exact (integral_nig_mul_snd p (u := fun x => x) measurable_id (integrable_ig_mul_id p ha)).trans
    (integral_ig_mul_id p ha)

lemma integrable_nigLaw_sq (c : ℝ) : Integrable (fun q : ℝ × ℝ => (q.1 - c) ^ 2) (nigLaw p) := by
  rw [integrable_nigLaw_iff]
  have h := integrable_nig_mul_sq p (w := fun _ => 1) measurable_const c
    (integrable_ig_mul_affine p ha p.nu _)
  simpa using h

lemma integral_nigLaw_sq (c : ℝ) :
    ∫ q, (q.1 - c) ^ 2 ∂nigLaw p = p.beta / (p.alpha - 1) / p.nu + (p.gamma - c) ^ 2 := by
  rw [integral_nigLaw]
  have h := integral_nig_mul_sq p (w := fun _ => 1) measurable_const c
    (integrable_ig_mul_affine p ha p.nu _)
  rw [integral_ig_mul_affine p ha] at h
  simpa using h

/-- Fubini for `(z − c)²` against the hierarchy density: integrability. -/
lemma integrable_hierarchy_sq (c : ℝ) :
    Integrable (fun h : HierarchySpace => hierarchyDensity p h * (h.2 - c) ^ 2) := by
  rw [Measure.volume_eq_prod]
  have hmeas : AEStronglyMeasurable (fun h : HierarchySpace => hierarchyDensity p h * (h.2 - c) ^ 2)
      (volume.prod volume) :=
    ((measurable_hierarchyDensity p).mul
      ((measurable_snd.sub measurable_const).pow_const 2)).aestronglyMeasurable
  refine (integrable_prod_iff hmeas).mpr ⟨ae_of_all _ fun q => ?_, ?_⟩
  · by_cases hq : 0 < q.2
    · have h := (integrable_normalDensity_mul_sq_sub q.1 c q.2 hq).const_mul (nigDensity p q)
      refine h.congr (ae_of_all _ fun z => ?_)
      simp only [hierarchyDensity, meanCoordinate, varianceCoordinate, latentCoordinate]
      ring
    · simp [hierarchyDensity, nigDensity_of_nonpos p q hq]
  · have hfun : (fun q : ℝ × ℝ => ∫ z, ‖hierarchyDensity p (q, z) * (z - c) ^ 2‖)
        = fun q => nigDensity p q * ((fun x => x) q.2) + nigDensity p q * ((fun _ => 1) q.2
          * (q.1 - c) ^ 2) := by
      funext q
      by_cases hq : 0 < q.2
      · have hnorm : (fun z => ‖hierarchyDensity p (q, z) * (z - c) ^ 2‖)
            = fun z => nigDensity p q * (normalDensity q.1 q.2 z * (z - c) ^ 2) := by
          funext z
          simp only [hierarchyDensity, meanCoordinate, varianceCoordinate, latentCoordinate,
            Real.norm_eq_abs, abs_mul, abs_of_nonneg (nigDensity_nonneg p q),
            abs_of_nonneg (normalDensity_nonneg _ _ _), abs_of_nonneg (sq_nonneg (z - c))]
          ring
        rw [hnorm, integral_const_mul, integral_normalDensity_mul_sq_sub _ _ _ hq]
        ring
      · simp [hierarchyDensity, nigDensity_of_nonpos p q hq]
    rw [hfun]
    exact (integrable_nig_mul_snd p measurable_id (integrable_ig_mul_id p ha)).add
      (integrable_nig_mul_sq p measurable_const c (integrable_ig_mul_affine p ha p.nu _))

/-- Fubini for `(z − c)²` against the hierarchy density: the integral. -/
lemma integral_hierarchy_sq (c : ℝ) :
    ∫ h : HierarchySpace, hierarchyDensity p h * (h.2 - c) ^ 2
      = p.beta / (p.alpha - 1) + (p.beta / (p.alpha - 1) / p.nu + (p.gamma - c) ^ 2) := by
  have hint := integrable_hierarchy_sq p ha c
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod _ hint]
  have hfun : (fun q : ℝ × ℝ => ∫ z, hierarchyDensity p (q, z) * (z - c) ^ 2)
      = fun q => nigDensity p q * ((fun x => x) q.2) + nigDensity p q * ((fun _ => 1) q.2
        * (q.1 - c) ^ 2) := by
    funext q
    by_cases hq : 0 < q.2
    · have h : (fun z => hierarchyDensity p (q, z) * (z - c) ^ 2)
          = fun z => nigDensity p q * (normalDensity q.1 q.2 z * (z - c) ^ 2) := by
        funext z
        simp only [hierarchyDensity, meanCoordinate, varianceCoordinate, latentCoordinate]
        ring
      rw [h, integral_const_mul, integral_normalDensity_mul_sq_sub _ _ _ hq]
      ring
    · simp [hierarchyDensity, nigDensity_of_nonpos p q hq]
  rw [hfun, integral_add
      (integrable_nig_mul_snd p (u := fun x => x) measurable_id (integrable_ig_mul_id p ha))
      (integrable_nig_mul_sq p (w := fun _ => 1) measurable_const c
        (integrable_ig_mul_affine p ha p.nu _)),
    integral_nig_mul_snd p (u := fun x => x) measurable_id (integrable_ig_mul_id p ha),
    integral_nig_mul_sq p (w := fun _ => 1) measurable_const c
      (integrable_ig_mul_affine p ha p.nu _),
    integral_ig_mul_affine p ha]
  exact congrArg (· + _) (integral_ig_mul_id p ha)

end Moments

section Uncertainty

/-- The aleatoric (variance) part `u_var = E[X]` of `q(μ,X|y)`. -/
def uVar (p : Parameters) : ℝ := ∫ q, q.2 ∂nigLaw p

/-- The epistemic part `u_epi = Var(μ)` of `q(μ,X|y)`. -/
def uEpi (p : Parameters) : ℝ := Var[fun q : ℝ × ℝ => q.1; nigLaw p]

/-- The total uncertainty `V_z = Var(z | y)` of the marginal law of `z`. -/
def totalVar (p : Parameters) : ℝ := Var[id; predictiveLaw p]

variable (p : Parameters) (ha : 1 < p.alpha)
include ha

theorem uVar_eq : uVar p = p.beta / (p.alpha - 1) := integral_nigLaw_snd p ha

/-- `E[μ] = γ` and `Var(μ) = E[X]/ν`. -/
theorem mean_and_uEpi :
    ∫ q, q.1 ∂nigLaw p = p.gamma ∧ uEpi p = p.beta / (p.alpha - 1) / p.nu := by
  have := isProbabilityMeasure_nigLaw' p
  exact mean_variance_of_sq_moments (nigLaw p) measurable_fst.aemeasurable p.gamma _
    (integrable_nigLaw_sq p ha) (integral_nigLaw_sq p ha)

theorem uEpi_eq : uEpi p = p.beta / (p.alpha - 1) / p.nu := (mean_and_uEpi p ha).2

/-- `E[z] = γ` and `Var(z) = E[X] + Var(μ)`. -/
theorem mean_and_totalVar :
    ∫ z, z ∂predictiveLaw p = p.gamma
      ∧ totalVar p = p.beta / (p.alpha - 1) + p.beta / (p.alpha - 1) / p.nu := by
  have := isProbabilityMeasure_predictiveLaw p
  have hint : ∀ c, Integrable (fun z : ℝ => (id z - c) ^ 2) (predictiveLaw p) := fun c =>
    (integrable_predictiveLaw_iff p (g := fun z => (z - c) ^ 2) (by fun_prop)).mpr
      (integrable_hierarchy_sq p ha c)
  have hval : ∀ c, ∫ z, (id z - c) ^ 2 ∂predictiveLaw p
      = (p.beta / (p.alpha - 1) + p.beta / (p.alpha - 1) / p.nu) + (p.gamma - c) ^ 2 := by
    intro c
    rw [integral_predictiveLaw p (g := fun z => (id z - c) ^ 2) (by fun_prop)]
    simp only [id]
    rw [integral_hierarchy_sq p ha c]
    ring
  exact mean_variance_of_sq_moments (predictiveLaw p) measurable_id.aemeasurable p.gamma _ hint hval

/-- `V_z = u_var + u_epi`. -/
theorem totalVar_eq_add : totalVar p = uVar p + uEpi p := by
  rw [(mean_and_totalVar p ha).2, uVar_eq p ha, uEpi_eq p ha]

/-- `V_z = s/(α−1)` with `s = β(1 + 1/ν)`. -/
theorem totalVar_eq : totalVar p = quotientScale p / (p.alpha - 1) := by
  rw [(mean_and_totalVar p ha).2, quotientScale]
  ring

end Uncertainty

section Fiber

variable (x : QuotientState) (ha : 1 < x.alpha)
include ha

/-- On the fiber, `u_var = s/((α−1)(1+t))`. -/
theorem uVar_fiber (t : PositiveReal) :
    uVar (fiberParameters x t) = x.s / ((x.alpha - 1) * (1 + (t : ℝ))) := by
  rw [uVar_eq _ ha]
  simp only [fiberParameters]
  rw [div_div, mul_comm (1 + (t : ℝ))]

/-- On the fiber, `u_epi = st/((α−1)(1+t))`. -/
theorem uEpi_fiber (t : PositiveReal) :
    uEpi (fiberParameters x t) = x.s * t / ((x.alpha - 1) * (1 + (t : ℝ))) := by
  have ht : (t : ℝ) ≠ 0 := t.property.ne'
  have h1 : 1 + (t : ℝ) ≠ 0 := by linarith [t.property]
  have h2 : x.alpha - 1 ≠ 0 := by linarith
  rw [uEpi_eq _ ha]
  simp only [fiberParameters]
  field_simp

/-- On the fiber, `V_z = u_var + u_epi = s/(α−1)`. -/
theorem totalVar_fiber (t : PositiveReal) :
    totalVar (fiberParameters x t) = uVar (fiberParameters x t) + uEpi (fiberParameters x t)
      ∧ totalVar (fiberParameters x t) = x.s / (x.alpha - 1) := by
  refine ⟨totalVar_eq_add _ ha, ?_⟩
  rw [totalVar_eq_add _ ha, uVar_fiber x ha, uEpi_fiber x ha]
  have h1 : 1 + (t : ℝ) ≠ 0 := by linarith [t.property]
  have h2 : x.alpha - 1 ≠ 0 := by linarith
  field_simp

/-- At the selected representative, `u_epi/u_var = t_* = 1/ν_sel`,
`u_epi/V_z = t_*/(1+t_*)` and `u_var/V_z = 1/(1+t_*)`. -/
theorem selected_ratios (p₀ : Parameters) :
    uEpi (fiberParameters x (selTPos p₀ x)) / uVar (fiberParameters x (selTPos p₀ x))
        = selT p₀ x
      ∧ selT p₀ x = 1 / selNu p₀ x
      ∧ uEpi (fiberParameters x (selTPos p₀ x)) / totalVar (fiberParameters x (selTPos p₀ x))
        = selT p₀ x / (1 + selT p₀ x)
      ∧ uVar (fiberParameters x (selTPos p₀ x)) / totalVar (fiberParameters x (selTPos p₀ x))
        = 1 / (1 + selT p₀ x) := by
  have ht := selT_pos p₀ x
  have hs := x.s_pos
  have h1 : 1 + selT p₀ x ≠ 0 := by linarith
  have h2 : x.alpha - 1 ≠ 0 := by linarith
  have hT := (totalVar_fiber x ha (selTPos p₀ x)).2
  rw [uEpi_fiber x ha, uVar_fiber x ha, hT]
  simp only [selTPos]
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp
  · rw [selNu_eq_inv_selT, one_div_one_div]
  · field_simp
  · field_simp

omit ha in
/-- The total uncertainty is determined by the marginal law of `z` alone. -/
theorem totalVar_determined_by_predictiveLaw (p q : Parameters)
    (h : predictiveLaw p = predictiveLaw q) : totalVar p = totalVar q := by
  rw [totalVar, totalVar, h]

/-- The split is not determined by the marginal law: over the same fiber,
every split of `V_z = s/(α−1)` into two strictly positive summands occurs. -/
theorem every_split_occurs (a b : ℝ) (hapos : 0 < a) (hbpos : 0 < b)
    (hab : a + b = x.s / (x.alpha - 1)) :
    ∃ t : PositiveReal, uVar (fiberParameters x t) = a ∧ uEpi (fiberParameters x t) = b := by
  refine ⟨⟨b / a, div_pos hbpos hapos⟩, ?_, ?_⟩
  · rw [uVar_fiber x ha]
    have h2 : x.alpha - 1 ≠ 0 := by linarith
    have hs : x.s = (a + b) * (x.alpha - 1) := by field_simp at hab; linarith
    simp only
    rw [hs]
    field_simp
  · rw [uEpi_fiber x ha]
    have h2 : x.alpha - 1 ≠ 0 := by linarith
    have hs : x.s = (a + b) * (x.alpha - 1) := by field_simp at hab; linarith
    simp only
    rw [hs]
    field_simp

end Fiber

end NIGBottleneck
