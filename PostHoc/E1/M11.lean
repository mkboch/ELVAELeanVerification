import Mathlib
import PostHoc.E1.M06

/-! -/

noncomputable section

namespace NS1

open MeasureTheory ProbabilityTheory

section S29

variable {Ω : Type*} [MeasurableSpace Ω]

lemma lem_101 (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ}
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

end S29

section S34

variable (p : str_001)

lemma lem_102 (h : abb_002) : 0 ≤ def_014 p h :=
  mul_nonneg (lem_013 p h.1) (lem_011 _ _ _)

lemma lem_103 (g : ℝ × ℝ → ℝ) :
    ∫ q, g q ∂def_009 p = ∫ q, def_008 p q * g q := by
  rw [def_009, integral_withDensity_eq_integral_toReal_smul
    (lem_015 p).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext q
  rw [smul_eq_mul, ENNReal.toReal_ofReal (lem_013 p q)]

lemma lem_104 (g : ℝ × ℝ → ℝ) :
    Integrable g (def_009 p) ↔ Integrable (fun q => def_008 p q * g q) := by
  rw [def_009, integrable_withDensity_iff_integrable_smul' (lem_015 p).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have h : (fun q => (ENNReal.ofReal (def_008 p q)).toReal • g q)
      = fun q => def_008 p q * g q := by
    funext q
    rw [smul_eq_mul, ENNReal.toReal_ofReal (lem_013 p q)]
  rw [h]

lemma lem_105 {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ z, g z ∂def_016 p = ∫ h, def_014 p h * g h.2 := by
  have hlat : Measurable def_013 := measurable_snd
  rw [def_016, integral_map hlat.aemeasurable hg.aestronglyMeasurable, def_015,
    integral_withDensity_eq_integral_toReal_smul (lem_016 p).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext h
  rw [smul_eq_mul, ENNReal.toReal_ofReal (lem_102 p h)]
  rfl

lemma lem_106 {g : ℝ → ℝ} (hg : Measurable g) :
    Integrable g (def_016 p) ↔ Integrable (fun h => def_014 p h * g h.2) := by
  have hlat : Measurable def_013 := measurable_snd
  rw [def_016, integrable_map_measure hg.aestronglyMeasurable hlat.aemeasurable, def_015,
    integrable_withDensity_iff_integrable_smul' (lem_016 p).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have h : (fun h => (ENNReal.ofReal (def_014 p h)).toReal • (g ∘ def_013) h)
      = fun h => def_014 p h * g h.2 := by
    funext h
    rw [smul_eq_mul, ENNReal.toReal_ofReal (lem_102 p h)]
    rfl
  rw [h]

theorem thm_165 : IsProbabilityMeasure (def_009 p) := by
  constructor
  have hint : Integrable (fun q : ℝ × ℝ => def_008 p q * (fun _ : ℝ => (1 : ℝ)) q.2) :=
    lem_032 p measurable_const (by
      simpa using lem_024 ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩)
  have hval : ∫ q : ℝ × ℝ, def_008 p q * (fun _ : ℝ => (1 : ℝ)) q.2 = 1 := by
    rw [lem_033 p measurable_const (by
      simpa using lem_024 ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩)]
    simpa using lem_039 p
  simp only [mul_one] at hint hval
  rw [def_009, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun q => lem_013 p q), hval,
    ENNReal.ofReal_one]

end S34

section S40

variable (p : str_001) (ha : 1 < p.alpha)
include ha

lemma lem_107 :
    Integrable (fun x => def_001 p.alpha p.beta x * x) :=
  (lem_022 ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩ (fun x => x)).mp
    (thm_025 _ _ ha)

lemma lem_108 :
    ∫ x, def_001 p.alpha p.beta x * x = p.beta / (p.alpha - 1) :=
  (lem_021 ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩ (fun x => x)).symm.trans
    (thm_023 _ _ ha)

lemma lem_109 (a b : ℝ) :
    Integrable (fun x => def_001 p.alpha p.beta x * 1 * (x / a + b)) := by
  have h1 := (lem_107 p ha).div_const a
  have h2 :=
    (lem_024 ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩).mul_const b
  refine (h1.add h2).congr (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply]
  ring

lemma lem_110 (a b : ℝ) :
    ∫ x, def_001 p.alpha p.beta x * 1 * (x / a + b)
      = p.beta / (p.alpha - 1) / a + b := by
  have h1 := (lem_107 p ha).div_const a
  have h2 :=
    (lem_024 ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩).mul_const b
  have h : (fun x => def_001 p.alpha p.beta x * 1 * (x / a + b))
      = fun x => def_001 p.alpha p.beta x * x / a
        + def_001 p.alpha p.beta x * b := by
    funext x
    ring
  rw [h, integral_add h1 h2, integral_div, integral_mul_const, lem_108 p ha,
    lem_039]
  ring

lemma lem_111 : ∫ q, q.2 ∂def_009 p = p.beta / (p.alpha - 1) := by
  rw [lem_103]
  exact (lem_033 p (u := fun x => x) measurable_id (lem_107 p ha)).trans
    (lem_108 p ha)

lemma lem_112 (c : ℝ) : Integrable (fun q : ℝ × ℝ => (q.1 - c) ^ 2) (def_009 p) := by
  rw [lem_104]
  have h := lem_034 p (w := fun _ => 1) measurable_const c
    (lem_109 p ha p.nu _)
  simpa using h

lemma lem_113 (c : ℝ) :
    ∫ q, (q.1 - c) ^ 2 ∂def_009 p = p.beta / (p.alpha - 1) / p.nu + (p.gamma - c) ^ 2 := by
  rw [lem_103]
  have h := lem_035 p (w := fun _ => 1) measurable_const c
    (lem_109 p ha p.nu _)
  rw [lem_110 p ha] at h
  simpa using h

lemma lem_114 (c : ℝ) :
    Integrable (fun h : abb_002 => def_014 p h * (h.2 - c) ^ 2) := by
  rw [Measure.volume_eq_prod]
  have hmeas : AEStronglyMeasurable (fun h : abb_002 => def_014 p h * (h.2 - c) ^ 2)
      (volume.prod volume) :=
    ((lem_016 p).mul
      ((measurable_snd.sub measurable_const).pow_const 2)).aestronglyMeasurable
  refine (integrable_prod_iff hmeas).mpr ⟨ae_of_all _ fun q => ?_, ?_⟩
  · by_cases hq : 0 < q.2
    · have h := (lem_031 q.1 c q.2 hq).const_mul (def_008 p q)
      refine h.congr (ae_of_all _ fun z => ?_)
      simp only [def_014, def_012, def_011, def_013]
      ring
    · simp [def_014, lem_014 p q hq]
  · have hfun : (fun q : ℝ × ℝ => ∫ z, ‖def_014 p (q, z) * (z - c) ^ 2‖)
        = fun q => def_008 p q * ((fun x => x) q.2) + def_008 p q * ((fun _ => 1) q.2
          * (q.1 - c) ^ 2) := by
      funext q
      by_cases hq : 0 < q.2
      · have hnorm : (fun z => ‖def_014 p (q, z) * (z - c) ^ 2‖)
            = fun z => def_008 p q * (def_003 q.1 q.2 z * (z - c) ^ 2) := by
          funext z
          simp only [def_014, def_012, def_011, def_013,
            Real.norm_eq_abs, abs_mul, abs_of_nonneg (lem_013 p q),
            abs_of_nonneg (lem_011 _ _ _), abs_of_nonneg (sq_nonneg (z - c))]
          ring
        rw [hnorm, integral_const_mul, lem_030 _ _ _ hq]
        ring
      · simp [def_014, lem_014 p q hq]
    rw [hfun]
    exact (lem_032 p measurable_id (lem_107 p ha)).add
      (lem_034 p measurable_const c (lem_109 p ha p.nu _))

lemma lem_115 (c : ℝ) :
    ∫ h : abb_002, def_014 p h * (h.2 - c) ^ 2
      = p.beta / (p.alpha - 1) + (p.beta / (p.alpha - 1) / p.nu + (p.gamma - c) ^ 2) := by
  have hint := lem_114 p ha c
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod _ hint]
  have hfun : (fun q : ℝ × ℝ => ∫ z, def_014 p (q, z) * (z - c) ^ 2)
      = fun q => def_008 p q * ((fun x => x) q.2) + def_008 p q * ((fun _ => 1) q.2
        * (q.1 - c) ^ 2) := by
    funext q
    by_cases hq : 0 < q.2
    · have h : (fun z => def_014 p (q, z) * (z - c) ^ 2)
          = fun z => def_008 p q * (def_003 q.1 q.2 z * (z - c) ^ 2) := by
        funext z
        simp only [def_014, def_012, def_011, def_013]
        ring
      rw [h, integral_const_mul, lem_030 _ _ _ hq]
      ring
    · simp [def_014, lem_014 p q hq]
  rw [hfun, integral_add
      (lem_032 p (u := fun x => x) measurable_id (lem_107 p ha))
      (lem_034 p (w := fun _ => 1) measurable_const c
        (lem_109 p ha p.nu _)),
    lem_033 p (u := fun x => x) measurable_id (lem_107 p ha),
    lem_035 p (w := fun _ => 1) measurable_const c
      (lem_109 p ha p.nu _),
    lem_110 p ha]
  exact congrArg (· + _) (lem_108 p ha)

end S40

section S57

def def_079 (p : str_001) : ℝ := ∫ q, q.2 ∂def_009 p

def def_080 (p : str_001) : ℝ := Var[fun q : ℝ × ℝ => q.1; def_009 p]

def def_081 (p : str_001) : ℝ := Var[id; def_016 p]

variable (p : str_001) (ha : 1 < p.alpha)
include ha

theorem thm_166 : def_079 p = p.beta / (p.alpha - 1) := lem_111 p ha

theorem thm_167 :
    ∫ q, q.1 ∂def_009 p = p.gamma ∧ def_080 p = p.beta / (p.alpha - 1) / p.nu := by
  have := thm_165 p
  exact lem_101 (def_009 p) measurable_fst.aemeasurable p.gamma _
    (lem_112 p ha) (lem_113 p ha)

theorem thm_168 : def_080 p = p.beta / (p.alpha - 1) / p.nu := (thm_167 p ha).2

theorem thm_169 :
    ∫ z, z ∂def_016 p = p.gamma
      ∧ def_081 p = p.beta / (p.alpha - 1) + p.beta / (p.alpha - 1) / p.nu := by
  have := thm_070 p
  have hint : ∀ c, Integrable (fun z : ℝ => (id z - c) ^ 2) (def_016 p) := fun c =>
    (lem_106 p (g := fun z => (z - c) ^ 2) (by fun_prop)).mpr
      (lem_114 p ha c)
  have hval : ∀ c, ∫ z, (id z - c) ^ 2 ∂def_016 p
      = (p.beta / (p.alpha - 1) + p.beta / (p.alpha - 1) / p.nu) + (p.gamma - c) ^ 2 := by
    intro c
    rw [lem_105 p (g := fun z => (id z - c) ^ 2) (by fun_prop)]
    simp only [id]
    rw [lem_115 p ha c]
    ring
  exact lem_101 (def_016 p) measurable_id.aemeasurable p.gamma _ hint hval

theorem thm_170 : def_081 p = def_079 p + def_080 p := by
  rw [(thm_169 p ha).2, thm_166 p ha, thm_168 p ha]

theorem thm_171 : def_081 p = def_022 p / (p.alpha - 1) := by
  rw [(thm_169 p ha).2, def_022]
  ring

end S57

section S23

variable (x : str_002) (ha : 1 < x.alpha)
include ha

theorem thm_172 (t : abb_001) :
    def_079 (def_026 x t) = x.s / ((x.alpha - 1) * (1 + (t : ℝ))) := by
  rw [thm_166 _ ha]
  simp only [def_026]
  rw [div_div, mul_comm (1 + (t : ℝ))]

theorem thm_173 (t : abb_001) :
    def_080 (def_026 x t) = x.s * t / ((x.alpha - 1) * (1 + (t : ℝ))) := by
  have ht : (t : ℝ) ≠ 0 := t.property.ne'
  have h1 : 1 + (t : ℝ) ≠ 0 := by linarith [t.property]
  have h2 : x.alpha - 1 ≠ 0 := by linarith
  rw [thm_168 _ ha]
  simp only [def_026]
  field_simp

theorem thm_174 (t : abb_001) :
    def_081 (def_026 x t) = def_079 (def_026 x t) + def_080 (def_026 x t)
      ∧ def_081 (def_026 x t) = x.s / (x.alpha - 1) := by
  refine ⟨thm_170 _ ha, ?_⟩
  rw [thm_170 _ ha, thm_172 x ha, thm_173 x ha]
  have h1 : 1 + (t : ℝ) ≠ 0 := by linarith [t.property]
  have h2 : x.alpha - 1 ≠ 0 := by linarith
  field_simp

theorem thm_175 (p₀ : str_001) :
    def_080 (def_026 x (def_050 p₀ x)) / def_079 (def_026 x (def_050 p₀ x))
        = def_047 p₀ x
      ∧ def_047 p₀ x = 1 / def_048 p₀ x
      ∧ def_080 (def_026 x (def_050 p₀ x)) / def_081 (def_026 x (def_050 p₀ x))
        = def_047 p₀ x / (1 + def_047 p₀ x)
      ∧ def_079 (def_026 x (def_050 p₀ x)) / def_081 (def_026 x (def_050 p₀ x))
        = 1 / (1 + def_047 p₀ x) := by
  have ht := thm_100 p₀ x
  have hs := x.s_pos
  have h1 : 1 + def_047 p₀ x ≠ 0 := by linarith
  have h2 : x.alpha - 1 ≠ 0 := by linarith
  have hT := (thm_174 x ha (def_050 p₀ x)).2
  rw [thm_173 x ha, thm_172 x ha, hT]
  simp only [def_050]
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp
  · rw [thm_101, one_div_one_div]
  · field_simp
  · field_simp

omit ha in
theorem thm_176 (p q : str_001)
    (h : def_016 p = def_016 q) : def_081 p = def_081 q := by
  rw [def_081, def_081, h]

theorem thm_177 (a b : ℝ) (hapos : 0 < a) (hbpos : 0 < b)
    (hab : a + b = x.s / (x.alpha - 1)) :
    ∃ t : abb_001, def_079 (def_026 x t) = a ∧ def_080 (def_026 x t) = b := by
  refine ⟨⟨b / a, div_pos hbpos hapos⟩, ?_, ?_⟩
  · rw [thm_172 x ha]
    have h2 : x.alpha - 1 ≠ 0 := by linarith
    have hs : x.s = (a + b) * (x.alpha - 1) := by field_simp at hab; linarith
    simp only
    rw [hs]
    field_simp
  · rw [thm_173 x ha]
    have h2 : x.alpha - 1 ≠ 0 := by linarith
    have hs : x.s = (a + b) * (x.alpha - 1) := by field_simp at hab; linarith
    simp only
    rw [hs]
    field_simp

end S23

end NS1
