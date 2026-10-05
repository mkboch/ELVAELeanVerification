import Mathlib
import PostHoc.E1.M06

/-! -/

noncomputable section

namespace NS1

open MeasureTheory ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal

section S33

variable {X : Type*} [MeasurableSpace X]

lemma lem_071 (m : Measure X) {f : X → ℝ} (hf : Measurable f) :
    ∀ᵐ x ∂(m.withDensity fun x => ENNReal.ofReal (f x)), 0 < f x := by
  rw [ae_withDensity_iff hf.ennreal_ofReal]
  exact ae_of_all _ fun x hx => by
    by_contra h
    exact hx (ENNReal.ofReal_eq_zero.mpr (not_lt.mp h))

theorem thm_118 (m : Measure X) [SigmaFinite m] {f g : X → ℝ}
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
    filter_upwards [hrn, lem_071 m hf] with x hx hpos
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

theorem thm_119 (m : Measure X) [SigmaFinite m] {f g : X → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x)
    (hfg : ∀ x, 0 < f x → 0 < g x)
    [IsProbabilityMeasure (m.withDensity fun x => ENNReal.ofReal (f x))]
    [IsProbabilityMeasure (m.withDensity fun x => ENNReal.ofReal (g x))]
    (hint : Integrable (fun x => f x * Real.log (f x / g x)) m) :
    klDiv (m.withDensity fun x => ENNReal.ofReal (f x))
        (m.withDensity fun x => ENNReal.ofReal (g x))
      = ENNReal.ofReal (∫ x, f x * Real.log (f x / g x) ∂m) := by
  obtain ⟨hac, hint', hval⟩ := thm_118 m hf hg hf0 hfg hint
  rw [klDiv_of_ac_of_integrable hac hint', hval]
  simp [measureReal_def]

end S33

section S42

theorem thm_120 (p : str_001) : IsProbabilityMeasure (def_009 p) := by
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

lemma lem_072 (p p₀ : str_001) (q : ℝ × ℝ) (h : 0 < def_008 p q) :
    0 < def_008 p₀ q := by
  have hx : 0 < q.2 := by
    by_contra hx
    rw [lem_014 p q hx] at h
    exact lt_irrefl 0 h
  have hG : 0 < Real.Gamma p₀.alpha := Real.Gamma_pos_of_pos p₀.alpha_pos
  have hs : 0 < Real.sqrt (2 * Real.pi * (q.2 / p₀.nu)) :=
    Real.sqrt_pos.mpr (by have := div_pos hx p₀.nu_pos; positivity)
  have h1 := Real.rpow_pos_of_pos p₀.beta_pos p₀.alpha
  have h2 := Real.rpow_pos_of_pos hx (-p₀.alpha - 1)
  simp only [def_008, def_001, hx, ↓reduceIte, def_003, Real.rpow_eq_pow]
  exact mul_pos (by positivity) (mul_pos (inv_pos.mpr hs) (Real.exp_pos _))

lemma lem_073 (p p₀ : str_001) :
    Integrable (fun q : ℝ × ℝ => def_008 p q * Real.log (def_008 p q / def_008 p₀ q)) := by
  have h := thm_088 p p₀
  rw [def_009, integrable_withDensity_iff_integrable_smul' (lem_015 p).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at h
  refine h.congr (ae_of_all _ fun q => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (lem_013 p q)]

theorem thm_121 (p p₀ : str_001) :
    def_017 p p₀ = (klDiv (def_009 p) (def_009 p₀)).toReal := by
  have hP : IsProbabilityMeasure (volume.withDensity fun q => ENNReal.ofReal (def_008 p q)) :=
    thm_120 p
  have hP0 : IsProbabilityMeasure (volume.withDensity fun q => ENNReal.ofReal (def_008 p₀ q)) :=
    thm_120 p₀
  have hint := lem_073 p p₀
  have hkl := thm_119 volume (lem_015 p) (lem_015 p₀)
    (lem_013 p) (lem_072 p p₀) hint
  have hval : ∫ q : ℝ × ℝ, def_008 p q * Real.log (def_008 p q / def_008 p₀ q)
      = def_017 p p₀ := by
    rw [def_017, def_009, integral_withDensity_eq_integral_toReal_smul
      (lem_015 p).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    congr 1
    funext q
    rw [smul_eq_mul, ENNReal.toReal_ofReal (lem_013 p q)]
  have hnn : 0 ≤ def_017 p p₀ := by
    obtain ⟨hac, hint', hv⟩ := thm_118 volume (lem_015 p)
      (lem_015 p₀) (lem_013 p) (lem_072 p p₀) hint
    have h0 := integral_llr_add_sub_measure_univ_nonneg hac hint'
    rw [hv, hval, probReal_univ, probReal_univ] at h0
    linarith
  change def_017 p p₀ = (klDiv (volume.withDensity fun q => ENNReal.ofReal (def_008 p q))
    (volume.withDensity fun q => ENNReal.ofReal (def_008 p₀ q))).toReal
  rw [hkl, hval, ENNReal.toReal_ofReal hnn]

theorem thm_122 (p p₀ : str_001) : 0 ≤ def_017 p p₀ := by
  rw [thm_121]
  exact ENNReal.toReal_nonneg

theorem thm_123 (p p₀ : str_001) :
    def_017 p p₀ = 0 ↔ def_009 p = def_009 p₀ := by
  have := thm_120 p
  have := thm_120 p₀
  have hP : IsProbabilityMeasure (volume.withDensity fun q => ENNReal.ofReal (def_008 p q)) :=
    thm_120 p
  have hP0 : IsProbabilityMeasure (volume.withDensity fun q => ENNReal.ofReal (def_008 p₀ q)) :=
    thm_120 p₀
  have hfin : klDiv (def_009 p) (def_009 p₀) ≠ ⊤ := by
    have hint := lem_073 p p₀
    change klDiv (volume.withDensity fun q => ENNReal.ofReal (def_008 p q))
      (volume.withDensity fun q => ENNReal.ofReal (def_008 p₀ q)) ≠ ⊤
    rw [thm_119 volume (lem_015 p) (lem_015 p₀)
      (lem_013 p) (lem_072 p p₀) hint]
    exact ENNReal.ofReal_ne_top
  rw [thm_121, ENNReal.toReal_eq_zero_iff, or_iff_left hfin,
    klDiv_eq_zero_iff]

theorem thm_124 {p q : str_001} (h : def_009 p = def_009 q) :
    def_016 p = def_016 q := by
  have hmp := (lem_015 p).ennreal_ofReal
  have hmq := (lem_015 q).ennreal_ofReal
  have hae : (fun r => ENNReal.ofReal (def_008 p r)) =ᵐ[volume]
      fun r => ENNReal.ofReal (def_008 q r) :=
    (withDensity_eq_iff_of_sigmaFinite hmp.aemeasurable hmq.aemeasurable).mp h
  have hae' : (fun h : abb_002 => ENNReal.ofReal (def_014 p h)) =ᵐ[volume]
      fun h => ENNReal.ofReal (def_014 q h) := by
    rw [Measure.volume_eq_prod]
    have hnull : (volume.prod volume) ({r : ℝ × ℝ | ENNReal.ofReal (def_008 p r)
        ≠ ENNReal.ofReal (def_008 q r)} ×ˢ (univ : Set ℝ)) = 0 := by
      rw [Measure.prod_prod, (ae_iff).mp hae, zero_mul]
    refine measure_mono_null (fun h hh => ?_) hnull
    refine ⟨?_, mem_univ _⟩
    intro heq
    apply hh
    change ENNReal.ofReal (def_008 p h.1 * def_003 (def_012 h)
        (def_011 h) (def_013 h))
      = ENNReal.ofReal (def_008 q h.1 * def_003 (def_012 h)
        (def_011 h) (def_013 h))
    rw [ENNReal.ofReal_mul (lem_013 p _), ENNReal.ofReal_mul (lem_013 q _), heq]
  rw [def_016, def_016, def_015, def_015, withDensity_congr_ae hae']

end S42

section S53

variable (p₀ : str_001)

def def_057 : str_002 := def_024 p₀

theorem thm_125 : (def_057 p₀).s = p₀.beta * (1 + 1 / p₀.nu) := rfl

def def_058 (x : str_002) : ℝ := def_041 p₀ x (def_050 p₀ x)

lemma lem_074 {p q : str_001} (h1 : p.gamma = q.gamma) (h2 : p.nu = q.nu)
    (h3 : p.alpha = q.alpha) (h4 : p.beta = q.beta) : p = q := by
  cases p
  cases q
  simp_all

theorem thm_126 : def_047 p₀ (def_057 p₀) = 1 / p₀.nu := by
  have hn := p₀.nu_pos
  have hb := p₀.beta_pos
  symm
  refine (thm_103 p₀ (def_057 p₀) (1 / p₀.nu) (one_div_pos.mpr hn)).mp ?_
  simp only [def_046, def_040, def_057, def_024, def_022, sub_self]
  field_simp
  ring

theorem thm_127 :
    def_026 (def_057 p₀) (def_050 p₀ (def_057 p₀)) = p₀ := by
  have hn := p₀.nu_pos
  have hb := p₀.beta_pos
  have ht : (def_050 p₀ (def_057 p₀) : ℝ) = 1 / p₀.nu := thm_126 p₀
  apply lem_074
  · rfl
  · simp only [def_026, ht]
    field_simp
  · rfl
  · simp only [def_026]
    rw [ht]
    simp only [def_057, def_024, def_022]
    field_simp

theorem thm_128 :
    (def_057 p₀).gamma = p₀.gamma ∧ def_048 p₀ (def_057 p₀) = p₀.nu ∧
      (def_057 p₀).alpha = p₀.alpha ∧ def_049 p₀ (def_057 p₀) = p₀.beta := by
  have h := congrArg (fun q : str_001 => (q.gamma, q.nu, q.alpha, q.beta))
    (thm_127 p₀)
  obtain ⟨-, h2, -, h4⟩ := thm_102 p₀ (def_057 p₀)
  simp only [Prod.mk.injEq] at h
  exact ⟨rfl, h2 ▸ h.2.1, rfl, h4 ▸ h.2.2.2⟩

theorem thm_129 (x : str_002) : 0 ≤ def_058 p₀ x :=
  thm_122 _ _

theorem thm_130 : def_058 p₀ (def_057 p₀) = 0 := by
  rw [def_058, def_041, thm_127, thm_123]

theorem thm_131 (x : str_002) :
    def_058 p₀ x = 0 ↔ x = def_057 p₀ := by
  constructor
  · intro h
    rw [def_058, def_041, thm_123] at h
    have hpred := thm_124 h
    rw [thm_073, thm_036] at hpred
    exact hpred
  · rintro rfl
    exact thm_130 p₀

end S53

end NS1
