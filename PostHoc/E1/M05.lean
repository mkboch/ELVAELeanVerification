import Mathlib
import PostHoc.E1.M03

/-! -/

noncomputable section

namespace NS1

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

section S40

theorem thm_087 (a b : abb_001) :
    IsProbabilityMeasure (def_002 a b) := by
  rw [thm_062, def_033]
  have := isProbabilityMeasure_gammaMeasure a.property b.property
  exact (Measure.isProbabilityMeasure_map_iff measurable_inv.aemeasurable).mpr inferInstance

lemma lem_020 (a b : abb_001) (x : ℝ) :
    (ENNReal.ofReal (def_001 a b x)).toReal = def_001 a b x :=
  ENNReal.toReal_ofReal (thm_013 _ _ _ a.property b.property.le)

lemma lem_021 (a b : abb_001) (g : ℝ → ℝ) :
    ∫ x, g x ∂def_002 a b = ∫ x, def_001 a b x * g x := by
  rw [def_002, integral_withDensity_eq_integral_toReal_smul
    (lem_009 _ _).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  rw [lem_020, smul_eq_mul]

lemma lem_022 (a b : abb_001) (g : ℝ → ℝ) :
    Integrable g (def_002 a b) ↔
      Integrable (fun x => def_001 a b x * g x) := by
  rw [def_002, integrable_withDensity_iff_integrable_smul'
    (lem_009 _ _).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have h : (fun x => (ENNReal.ofReal (def_001 a b x)).toReal • g x)
      = fun x => def_001 a b x * g x := by
    funext x
    rw [lem_020, smul_eq_mul]
  rw [h]

lemma lem_023 (a b : abb_001) :
    ∫ x, def_001 a b x = 1 := by
  have h := lem_021 a b (fun _ => 1)
  have := thm_087 a b
  simpa using h.symm

lemma lem_024 (a b : abb_001) :
    Integrable (def_001 a b) := by
  have := thm_087 a b
  have h := (lem_022 a b (fun _ => (1 : ℝ))).mp (integrable_const 1)
  simpa using h

lemma lem_025 (m c : ℝ) (v : ℝ≥0) :
    Integrable (fun z => (z - c) ^ 2) (gaussianReal m v) :=
  ((memLp_id_gaussianReal 2).sub (memLp_const c)).integrable_sq

lemma lem_026 (m c : ℝ) (v : ℝ≥0) :
    ∫ z, (z - c) ^ 2 ∂(gaussianReal m v) = v + (m - c) ^ 2 := by
  have hvar := variance_fun_id_gaussianReal (μ := m) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at hvar
  have hexp : (fun z : ℝ => (z - c) ^ 2)
      = fun z => (z - m) ^ 2 + (2 * (m - c)) * z + (-(2 * (m - c) * m) + (m - c) ^ 2) := by
    funext z; ring
  rw [hexp]
  have h1 : Integrable (fun z : ℝ => (z - m) ^ 2) (gaussianReal m v) :=
    lem_025 m m v
  have h2 : Integrable (fun z : ℝ => (2 * (m - c)) * z) (gaussianReal m v) :=
    ((memLp_id_gaussianReal 1).integrable le_rfl).const_mul _
  have h12 : Integrable (fun z : ℝ => (z - m) ^ 2 + (2 * (m - c)) * z) (gaussianReal m v) :=
    h1.add h2
  rw [integral_add h12 (integrable_const _), integral_add h1 h2, integral_const_mul,
    integral_id_gaussianReal, hvar, integral_const]
  simp

lemma lem_027 (m v : ℝ) (hv : 0 ≤ v) :
    def_003 m v = gaussianPDFReal m v.toNNReal := by
  funext z
  exact lem_012 m v z hv

lemma lem_028 (m v : ℝ) (hv : 0 < v) : Integrable (def_003 m v) := by
  rw [lem_027 m v hv.le]
  exact integrable_gaussianPDFReal _ _

lemma lem_029 (m v : ℝ) (hv : 0 < v) : ∫ z, def_003 m v z = 1 := by
  rw [lem_027 m v hv.le]
  exact integral_gaussianPDFReal_eq_one _ (by simpa using hv)

lemma lem_030 (m c v : ℝ) (hv : 0 < v) :
    ∫ z, def_003 m v z * (z - c) ^ 2 = v + (m - c) ^ 2 := by
  have hv' : v.toNNReal ≠ 0 := by simpa using hv
  have := integral_gaussianReal_eq_integral_smul (f := fun z => (z - c) ^ 2) (μ := m) hv'
  simp only [smul_eq_mul] at this
  rw [lem_027 m v hv.le, ← this, lem_026,
    Real.coe_toNNReal _ hv.le]

lemma lem_031 (m c v : ℝ) (hv : 0 < v) :
    Integrable (fun z => def_003 m v z * (z - c) ^ 2) := by
  have hv' : v.toNNReal ≠ 0 := by simpa using hv
  have h := lem_025 m c v.toNNReal
  rw [gaussianReal_of_var_ne_zero _ hv', integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (ae_of_all _ fun _ => gaussianPDF_lt_top)] at h
  rw [lem_027 m v hv.le]
  simpa [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)] using h

end S40

section S26

variable (p : str_001)

lemma lem_032 {u : ℝ → ℝ} (hum : Measurable u)
    (hu : Integrable (fun x => def_001 p.alpha p.beta x * u x)) :
    Integrable (fun q : ℝ × ℝ => def_008 p q * u q.2) := by
  rw [Measure.volume_eq_prod]
  have hmeas : AEStronglyMeasurable (fun q : ℝ × ℝ => def_008 p q * u q.2)
      (volume.prod volume) :=
    ((lem_015 p).mul (hum.comp measurable_snd)).aestronglyMeasurable
  refine (integrable_prod_iff' hmeas).mpr ⟨ae_of_all _ fun x => ?_, ?_⟩
  · by_cases hx : 0 < x
    · simp only [def_008]
      exact ((lem_028 _ _ (div_pos hx p.nu_pos)).const_mul _).mul_const _
    · simp [def_008, lem_010 _ _ _ hx]
  · have hfun : (fun x => ∫ m, ‖def_008 p (m, x) * u x‖)
        = fun x => ‖def_001 p.alpha p.beta x * u x‖ := by
      funext x
      by_cases hx : 0 < x
      · have hIG := thm_013 p.alpha p.beta x p.alpha_pos p.beta_pos.le
        have hnorm : (fun m => ‖def_008 p (m, x) * u x‖)
            = fun m => (def_001 p.alpha p.beta x * |u x|)
                * def_003 p.gamma (x / p.nu) m := by
          funext m
          simp only [def_008, Real.norm_eq_abs, abs_mul, abs_of_nonneg hIG,
            abs_of_nonneg (lem_011 _ _ _)]
          ring
        rw [hnorm, integral_const_mul, lem_029 _ _ (div_pos hx p.nu_pos), mul_one,
          Real.norm_eq_abs, abs_mul, abs_of_nonneg hIG]
      · simp [def_008, lem_010 _ _ _ hx]
    rw [hfun]
    exact hu.norm

lemma lem_033 {u : ℝ → ℝ} (hum : Measurable u)
    (hu : Integrable (fun x => def_001 p.alpha p.beta x * u x)) :
    ∫ q : ℝ × ℝ, def_008 p q * u q.2 = ∫ x, def_001 p.alpha p.beta x * u x := by
  have hint := lem_032 p hum hu
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod_symm _ hint]
  congr 1
  funext x
  by_cases hx : 0 < x
  · simp only [def_008]
    rw [integral_mul_const, integral_const_mul, lem_029 _ _ (div_pos hx p.nu_pos),
      mul_one]
  · simp [def_008, lem_010 _ _ _ hx]

lemma lem_034 {w : ℝ → ℝ} (hwm : Measurable w) (c : ℝ)
    (hw : Integrable (fun x => def_001 p.alpha p.beta x * w x
      * (x / p.nu + (p.gamma - c) ^ 2))) :
    Integrable (fun q : ℝ × ℝ => def_008 p q * (w q.2 * (q.1 - c) ^ 2)) := by
  rw [Measure.volume_eq_prod]
  have hmeas : AEStronglyMeasurable (fun q : ℝ × ℝ => def_008 p q * (w q.2 * (q.1 - c) ^ 2))
      (volume.prod volume) := by
    have := lem_015 p
    exact (this.mul ((hwm.comp measurable_snd).mul
      ((measurable_fst.sub measurable_const).pow_const 2))).aestronglyMeasurable
  refine (integrable_prod_iff' hmeas).mpr ⟨ae_of_all _ fun x => ?_, ?_⟩
  · by_cases hx : 0 < x
    · have h := (lem_031 p.gamma c _ (div_pos hx p.nu_pos)).const_mul
        (def_001 p.alpha p.beta x * w x)
      refine h.congr (ae_of_all _ fun m => ?_)
      simp only [def_008]
      ring
    · simp [def_008, lem_010 _ _ _ hx]
  · have hfun : (fun x => ∫ m, ‖def_008 p (m, x) * (w x * (m - c) ^ 2)‖)
        = fun x => ‖def_001 p.alpha p.beta x * w x
            * (x / p.nu + (p.gamma - c) ^ 2)‖ := by
      funext x
      by_cases hx : 0 < x
      · have hIG := thm_013 p.alpha p.beta x p.alpha_pos p.beta_pos.le
        have hq : 0 ≤ x / p.nu + (p.gamma - c) ^ 2 := by
          have := div_pos hx p.nu_pos; positivity
        have hnorm : (fun m => ‖def_008 p (m, x) * (w x * (m - c) ^ 2)‖)
            = fun m => (def_001 p.alpha p.beta x * |w x|)
                * (def_003 p.gamma (x / p.nu) m * (m - c) ^ 2) := by
          funext m
          simp only [def_008, Real.norm_eq_abs, abs_mul, abs_of_nonneg hIG,
            abs_of_nonneg (lem_011 _ _ _), abs_of_nonneg (sq_nonneg (m - c))]
          ring
        rw [hnorm, integral_const_mul,
          lem_030 _ _ _ (div_pos hx p.nu_pos),
          Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hIG, abs_of_nonneg hq]
      · simp [def_008, lem_010 _ _ _ hx]
    rw [hfun]
    exact hw.norm

lemma lem_035 {w : ℝ → ℝ} (hwm : Measurable w) (c : ℝ)
    (hw : Integrable (fun x => def_001 p.alpha p.beta x * w x
      * (x / p.nu + (p.gamma - c) ^ 2))) :
    ∫ q : ℝ × ℝ, def_008 p q * (w q.2 * (q.1 - c) ^ 2)
      = ∫ x, def_001 p.alpha p.beta x * w x * (x / p.nu + (p.gamma - c) ^ 2) := by
  have hint := lem_034 p hwm c hw
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod_symm _ hint]
  congr 1
  funext x
  by_cases hx : 0 < x
  · have h : (fun m => def_008 p (m, x) * (w x * (m - c) ^ 2))
        = fun m => (def_001 p.alpha p.beta x * w x)
            * (def_003 p.gamma (x / p.nu) m * (m - c) ^ 2) := by
      funext m
      simp only [def_008]
      ring
    rw [h, integral_const_mul, lem_030 _ _ _ (div_pos hx p.nu_pos)]
  · simp [def_008, lem_010 _ _ _ hx]

end S26

section S36

lemma lem_036 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    Real.log (def_001 a b x)
      = a * Real.log b - Real.log (Real.Gamma a) - (a + 1) * Real.log x - b * x⁻¹ := by
  have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have h1 : 0 < b ^ a := Real.rpow_pos_of_pos hb a
  have h2 : 0 < x ^ (-a - 1) := Real.rpow_pos_of_pos hx _
  simp only [def_001, hx, ↓reduceIte, Real.rpow_eq_pow]
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul (by positivity) h2.ne',
    Real.log_div h1.ne' hG.ne', Real.log_rpow hb, Real.log_rpow hx, Real.log_exp]
  ring

lemma lem_037 (m v z : ℝ) (hv : 0 < v) :
    Real.log (def_003 m v z)
      = -(1 / 2) * (Real.log 2 + Real.log Real.pi + Real.log v) - (z - m) ^ 2 * (2 * v)⁻¹ := by
  have hs : 0 < Real.sqrt (2 * Real.pi * v) := Real.sqrt_pos.mpr (by positivity)
  simp only [def_003]
  rw [Real.log_mul (inv_pos.mpr hs).ne' (Real.exp_pos _).ne', Real.log_inv, Real.log_exp,
    Real.log_sqrt (by positivity), Real.log_mul (by positivity) hv.ne',
    Real.log_mul (by norm_num) Real.pi_pos.ne']
  ring

def def_038 (p p₀ : str_001) (x : ℝ) : ℝ :=
  (p.alpha * Real.log p.beta - p₀.alpha * Real.log p₀.beta)
    - (Real.log (Real.Gamma p.alpha) - Real.log (Real.Gamma p₀.alpha))
    + (1 / 2) * (Real.log p.nu - Real.log p₀.nu)
    - (p.alpha - p₀.alpha) * Real.log x - (p.beta - p₀.beta) * x⁻¹

lemma lem_038 (p p₀ : str_001) (m x : ℝ) (hx : 0 < x) :
    Real.log (def_008 p (m, x) / def_008 p₀ (m, x))
      = def_038 p p₀ x + (-(p.nu / 2) * x⁻¹) * (m - p.gamma) ^ 2
          + ((p₀.nu / 2) * x⁻¹) * (m - p₀.gamma) ^ 2 := by
  have hIG : ∀ q : str_001, 0 < def_001 q.alpha q.beta x := fun q => by
    have hG : 0 < Real.Gamma q.alpha := Real.Gamma_pos_of_pos q.alpha_pos
    simp only [def_001, hx, ↓reduceIte, Real.rpow_eq_pow]
    have := Real.rpow_pos_of_pos q.beta_pos q.alpha
    have := Real.rpow_pos_of_pos hx (-q.alpha - 1)
    positivity
  have hN : ∀ q : str_001, 0 < def_003 q.gamma (x / q.nu) m := fun q => by
    have hs : 0 < Real.sqrt (2 * Real.pi * (x / q.nu)) :=
      Real.sqrt_pos.mpr (by have := div_pos hx q.nu_pos; positivity)
    simp only [def_003]
    exact mul_pos (inv_pos.mpr hs) (Real.exp_pos _)
  simp only [def_008]
  rw [Real.log_div (mul_pos (hIG p) (hN p)).ne' (mul_pos (hIG p₀) (hN p₀)).ne',
    Real.log_mul (hIG p).ne' (hN p).ne', Real.log_mul (hIG p₀).ne' (hN p₀).ne',
    lem_036 _ _ _ p.alpha_pos p.beta_pos hx,
    lem_036 _ _ _ p₀.alpha_pos p₀.beta_pos hx,
    lem_037 _ _ _ (div_pos hx p.nu_pos), lem_037 _ _ _ (div_pos hx p₀.nu_pos),
    Real.log_div hx.ne' p.nu_pos.ne', Real.log_div hx.ne' p₀.nu_pos.ne']
  unfold def_038
  have hx0 := hx.ne'
  have hn0 := p.nu_pos.ne'
  have hn00 := p₀.nu_pos.ne'
  field_simp
  ring

end S36

def def_039 (p p₀ : str_001) : ℝ :=
  p₀.alpha * Real.log (p.beta / p₀.beta)
    + Real.log (Real.Gamma p₀.alpha / Real.Gamma p.alpha)
    + (p.alpha - p₀.alpha) * def_019 p.alpha - p.alpha + p.alpha * p₀.beta / p.beta
    + (1 / 2) * (p₀.nu / p.nu - 1 + Real.log (p.nu / p₀.nu)
      + p₀.nu * p.alpha * (p.gamma - p₀.gamma) ^ 2 / p.beta)

section S16

variable (p p₀ : str_001)

lemma lem_039 :
    ∫ x, def_001 p.alpha p.beta x = 1 :=
  lem_023 ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩

lemma lem_040 : Measurable (def_038 p p₀) := by
  unfold def_038
  fun_prop

private lemma lem_041 :
    Integrable (fun x => def_001 p.alpha p.beta x * x⁻¹) :=
  (lem_022 ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩ _).mp
    (thm_024 _ _)

private lemma lem_042 :
    Integrable (fun x => def_001 p.alpha p.beta x * Real.log x) :=
  (lem_022 ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩ _).mp
    (thm_022 _ _)

private lemma lem_043 :
    ∫ x, def_001 p.alpha p.beta x * x⁻¹ = p.alpha / p.beta := by
  rw [← lem_021 ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩ (fun x => x⁻¹)]
  exact thm_018 _ _

private lemma lem_044 :
    ∫ x, def_001 p.alpha p.beta x * Real.log x
      = Real.log p.beta - def_019 p.alpha := by
  rw [← lem_021 ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩ Real.log]
  exact thm_020 _ _

private lemma lem_045 :
    Integrable (fun x => def_001 p.alpha p.beta x * def_038 p p₀ x) := by
  have h1 := lem_024 ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩
  have h2 := lem_042 p
  have h3 := lem_041 p
  have h := ((h1.const_mul ((p.alpha * Real.log p.beta - p₀.alpha * Real.log p₀.beta)
    - (Real.log (Real.Gamma p.alpha) - Real.log (Real.Gamma p₀.alpha))
    + (1 / 2) * (Real.log p.nu - Real.log p₀.nu))).sub (h2.const_mul (p.alpha - p₀.alpha))).sub
    (h3.const_mul (p.beta - p₀.beta))
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [def_038, Pi.sub_apply]
  ring

private lemma lem_046 :
    ∫ x, def_001 p.alpha p.beta x * def_038 p p₀ x
      = (p.alpha * Real.log p.beta - p₀.alpha * Real.log p₀.beta)
        - (Real.log (Real.Gamma p.alpha) - Real.log (Real.Gamma p₀.alpha))
        + (1 / 2) * (Real.log p.nu - Real.log p₀.nu)
        - (p.alpha - p₀.alpha) * (Real.log p.beta - def_019 p.alpha)
        - (p.beta - p₀.beta) * (p.alpha / p.beta) := by
  have h1 := lem_024 ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩
  have h2 := lem_042 p
  have h3 := lem_041 p
  set C := (p.alpha * Real.log p.beta - p₀.alpha * Real.log p₀.beta)
    - (Real.log (Real.Gamma p.alpha) - Real.log (Real.Gamma p₀.alpha))
    + (1 / 2) * (Real.log p.nu - Real.log p₀.nu) with hC
  have hfun : (fun x => def_001 p.alpha p.beta x * def_038 p p₀ x)
      = fun x => (C * def_001 p.alpha p.beta x
          - (p.alpha - p₀.alpha) * (def_001 p.alpha p.beta x * Real.log x))
          - (p.beta - p₀.beta) * (def_001 p.alpha p.beta x * x⁻¹) := by
    funext x
    simp only [def_038, hC]
    ring
  have i1 : Integrable (fun x => C * def_001 p.alpha p.beta x) := h1.const_mul C
  have i2 : Integrable (fun x => (p.alpha - p₀.alpha)
      * (def_001 p.alpha p.beta x * Real.log x)) := h2.const_mul _
  have i3 : Integrable (fun x => (p.beta - p₀.beta)
      * (def_001 p.alpha p.beta x * x⁻¹)) := h3.const_mul _
  have i12 : Integrable (fun x => C * def_001 p.alpha p.beta x
      - (p.alpha - p₀.alpha) * (def_001 p.alpha p.beta x * Real.log x)) := i1.sub i2
  rw [hfun, integral_sub i12 i3, integral_sub i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, lem_039, lem_044,
    lem_043, mul_one]

private lemma lem_047 (x : ℝ) :
    def_001 p.alpha p.beta x * (-(p.nu / 2) * x⁻¹)
        * (x / p.nu + (p.gamma - p.gamma) ^ 2)
      = -(1 / 2) * def_001 p.alpha p.beta x := by
  by_cases hx : x = 0
  · simp [hx, lem_010 _ _ _ (lt_irrefl 0)]
  · have hn := p.nu_pos.ne'
    simp only [sub_self]
    field_simp
    ring

private lemma lem_048 (x : ℝ) :
    def_001 p.alpha p.beta x * ((p₀.nu / 2) * x⁻¹)
        * (x / p.nu + (p.gamma - p₀.gamma) ^ 2)
      = p₀.nu / (2 * p.nu) * def_001 p.alpha p.beta x
        + p₀.nu / 2 * (p.gamma - p₀.gamma) ^ 2 * (def_001 p.alpha p.beta x * x⁻¹) := by
  by_cases hx : x = 0
  · simp [hx, lem_010 _ _ _ (lt_irrefl 0)]
  · have hn := p.nu_pos.ne'
    field_simp

private lemma lem_049 :
    Integrable (fun x => def_001 p.alpha p.beta x * (-(p.nu / 2) * x⁻¹)
      * (x / p.nu + (p.gamma - p.gamma) ^ 2)) :=
  ((lem_024 ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩).const_mul
    (-(1 / 2) : ℝ)).congr (ae_of_all _ fun x => (lem_047 p x).symm)

private lemma lem_050 :
    ∫ x, def_001 p.alpha p.beta x * (-(p.nu / 2) * x⁻¹)
      * (x / p.nu + (p.gamma - p.gamma) ^ 2) = -(1 / 2) := by
  simp_rw [lem_047 p]
  rw [integral_const_mul, lem_039, mul_one]

private lemma lem_051 :
    Integrable (fun x => def_001 p.alpha p.beta x * ((p₀.nu / 2) * x⁻¹)
      * (x / p.nu + (p.gamma - p₀.gamma) ^ 2)) :=
  (((lem_024 ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩).const_mul
    (p₀.nu / (2 * p.nu))).add ((lem_041 p).const_mul
    (p₀.nu / 2 * (p.gamma - p₀.gamma) ^ 2))).congr
    (ae_of_all _ fun x => (lem_048 p p₀ x).symm)

private lemma lem_052 :
    ∫ x, def_001 p.alpha p.beta x * ((p₀.nu / 2) * x⁻¹)
      * (x / p.nu + (p.gamma - p₀.gamma) ^ 2)
      = p₀.nu / (2 * p.nu) + p₀.nu / 2 * (p.gamma - p₀.gamma) ^ 2 * (p.alpha / p.beta) := by
  simp_rw [lem_048 p p₀]
  have i1 : Integrable (fun x => p₀.nu / (2 * p.nu) * def_001 p.alpha p.beta x) :=
    (lem_024 ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩).const_mul _
  have i2 : Integrable (fun x => p₀.nu / 2 * (p.gamma - p₀.gamma) ^ 2
      * (def_001 p.alpha p.beta x * x⁻¹)) :=
    (lem_041 p).const_mul _
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul,
    lem_039, lem_043, mul_one]

private lemma lem_053 (q : ℝ × ℝ) :
    def_008 p q * Real.log (def_008 p q / def_008 p₀ q)
      = def_008 p q * def_038 p p₀ q.2
        + def_008 p q * ((-(p.nu / 2) * q.2⁻¹) * (q.1 - p.gamma) ^ 2)
        + def_008 p q * (((p₀.nu / 2) * q.2⁻¹) * (q.1 - p₀.gamma) ^ 2) := by
  by_cases hx : 0 < q.2
  · have h := lem_038 p p₀ q.1 q.2 hx
    rw [show ((q.1, q.2) : ℝ × ℝ) = q from rfl] at h
    rw [h]
    ring
  · simp [lem_014 p q hx]

theorem thm_088 :
    Integrable (fun h => Real.log (def_008 p h / def_008 p₀ h)) (def_009 p) := by
  have hmeas : Measurable fun q => ENNReal.ofReal (def_008 p q) :=
    (lem_015 p).ennreal_ofReal
  rw [def_009, integrable_withDensity_iff_integrable_smul' hmeas
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hU := lem_032 p (lem_040 p p₀)
    (lem_045 p p₀)
  have hW1 := lem_034 p (w := fun x => -(p.nu / 2) * x⁻¹) (by fun_prop) p.gamma
    (lem_049 p)
  have hW2 := lem_034 p (w := fun x => (p₀.nu / 2) * x⁻¹) (by fun_prop) p₀.gamma
    (lem_051 p p₀)
  refine ((hU.add hW1).add hW2).congr (ae_of_all _ fun q => ?_)
  simp only [Pi.add_apply, smul_eq_mul,
    ENNReal.toReal_ofReal (lem_013 p q)]
  rw [lem_053]

theorem thm_089 :
    def_017 p p₀ = def_039 p p₀ := by
  have hmeas : Measurable fun q => ENNReal.ofReal (def_008 p q) :=
    (lem_015 p).ennreal_ofReal
  have hU := lem_032 p (lem_040 p p₀)
    (lem_045 p p₀)
  have hW1 := lem_034 p (w := fun x => -(p.nu / 2) * x⁻¹) (by fun_prop) p.gamma
    (lem_049 p)
  have hW2 := lem_034 p (w := fun x => (p₀.nu / 2) * x⁻¹) (by fun_prop) p₀.gamma
    (lem_051 p p₀)
  rw [def_017, def_009, integral_withDensity_eq_integral_toReal_smul hmeas
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hfun : (fun q => (ENNReal.ofReal (def_008 p q)).toReal
      • Real.log (def_008 p q / def_008 p₀ q))
      = fun q => def_008 p q * def_038 p p₀ q.2
        + def_008 p q * ((-(p.nu / 2) * q.2⁻¹) * (q.1 - p.gamma) ^ 2)
        + def_008 p q * (((p₀.nu / 2) * q.2⁻¹) * (q.1 - p₀.gamma) ^ 2) := by
    funext q
    rw [smul_eq_mul, ENNReal.toReal_ofReal (lem_013 p q), lem_053]
  have hUW : Integrable (fun q : ℝ × ℝ => def_008 p q * def_038 p p₀ q.2
      + def_008 p q * ((-(p.nu / 2) * q.2⁻¹) * (q.1 - p.gamma) ^ 2)) := hU.add hW1
  rw [hfun, integral_add hUW hW2, integral_add hU hW1,
    lem_033 p (lem_040 p p₀) (lem_045 p p₀),
    lem_035 p (w := fun x => -(p.nu / 2) * x⁻¹) (by fun_prop) p.gamma
      (lem_049 p),
    lem_035 p (w := fun x => (p₀.nu / 2) * x⁻¹) (by fun_prop) p₀.gamma
      (lem_051 p p₀),
    lem_046, lem_050, lem_052]
  have hb := p.beta_pos.ne'
  have hn := p.nu_pos.ne'
  have hG := (Real.Gamma_pos_of_pos p.alpha_pos).ne'
  have hG0 := (Real.Gamma_pos_of_pos p₀.alpha_pos).ne'
  rw [def_039, Real.log_div hb p₀.beta_pos.ne', Real.log_div hG0 hG,
    Real.log_div hn p₀.nu_pos.ne']
  field_simp
  ring

def def_040 (p₀ : str_001) (x : str_002) : ℝ :=
  p₀.beta + p₀.nu / 2 * (x.gamma - p₀.gamma) ^ 2

theorem thm_090 (p₀ : str_001) (x : str_002) : 0 < def_040 p₀ x := by
  have := p₀.beta_pos
  have := p₀.nu_pos
  unfold def_040
  positivity

def def_041 (p₀ : str_001) (x : str_002) (t : abb_001) : ℝ :=
  def_017 (def_026 x t) p₀

def def_042 (p₀ : str_001) (x : str_002) (t : ℝ) : ℝ :=
  p₀.alpha * Real.log (x.s / p₀.beta) + Real.log (Real.Gamma p₀.alpha / Real.Gamma x.alpha)
    + (x.alpha - p₀.alpha) * def_019 x.alpha - x.alpha - p₀.alpha * Real.log (1 + t)
    + x.alpha * def_040 p₀ x / x.s * (1 + t) + (1 / 2) * (p₀.nu * t - 1 - Real.log (p₀.nu * t))

theorem thm_091 (p₀ : str_001) (x : str_002) (t : abb_001) :
    def_041 p₀ x t = def_042 p₀ x t := by
  have ht : 0 < (t : ℝ) := t.property
  have h1t : 0 < 1 + (t : ℝ) := by linarith
  have hs := x.s_pos
  have hb0 := p₀.beta_pos
  have hn0 := p₀.nu_pos
  rw [def_041, thm_089, def_039, def_042, def_040]
  simp only [def_026]
  rw [Real.log_div (div_pos hs h1t).ne' hb0.ne', Real.log_div hs.ne' h1t.ne',
    Real.log_div (one_div_pos.mpr ht).ne' hn0.ne', Real.log_div hs.ne' hb0.ne',
    Real.log_mul hn0.ne' ht.ne',
    show Real.log (1 / (t : ℝ)) = -Real.log t by rw [one_div, Real.log_inv]]
  field_simp
  ring

end S16

end NS1
