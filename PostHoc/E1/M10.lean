import Mathlib
import PostHoc.E1.M05
import PostHoc.E1.M08

/-! -/

noncomputable section

namespace NS1

open MeasureTheory

section S38

theorem thm_160 (p : str_001) :
    (def_015 p).map Prod.fst = def_009 p := by
  have hH := lem_016 p
  ext s hs
  rw [Measure.map_apply measurable_fst hs, def_015, withDensity_apply _ (measurable_fst hs),
    ← lintegral_indicator (measurable_fst hs), Measure.volume_eq_prod,
    lintegral_prod _ ((hH.ennreal_ofReal.indicator (measurable_fst hs)).aemeasurable), def_009,
    withDensity_apply _ hs, ← lintegral_indicator hs]
  refine lintegral_congr fun q => ?_
  have h1 := lem_017 p MeasurableSet.univ q
  simp only [Set.indicator_univ, measure_univ, mul_one] at h1
  by_cases hq : q ∈ s
  · have : ∀ z, (Prod.fst ⁻¹' s).indicator (fun h => ENNReal.ofReal (def_014 p h)) (q, z)
        = ENNReal.ofReal (def_014 p (q, z)) := fun z =>
      Set.indicator_of_mem (by exact hq) _
    simp only [this, h1, Set.indicator_of_mem hq]
  · have : ∀ z, (Prod.fst ⁻¹' s).indicator (fun h => ENNReal.ofReal (def_014 p h)) (q, z)
        = 0 := fun z => Set.indicator_of_notMem (by exact hq) _
    simp only [this, lintegral_zero, Set.indicator_of_notMem hq]

instance ins_001 (p : str_001) :
    IsProbabilityMeasure (def_015 p) := by
  have := thm_120 p
  constructor
  have h := congrArg (fun μ : Measure (ℝ × ℝ) => μ Set.univ) (thm_160 p)
  simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ,
    measure_univ] at h
  exact h

lemma lem_093 (p : str_001) {g : ℝ × ℝ → ℝ}
    (hg : AEStronglyMeasurable g (def_009 p)) :
    ∫ h, g h.1 ∂(def_015 p) = ∫ q, g q ∂(def_009 p) := by
  rw [← thm_160] at hg ⊢
  exact (integral_map measurable_fst.aemeasurable hg).symm

lemma lem_094 (p : str_001) {g : ℝ × ℝ → ℝ}
    (hg : Integrable g (def_009 p)) :
    Integrable (fun h : abb_002 => g h.1) (def_015 p) := by
  rw [← thm_160] at hg
  exact hg.comp_measurable measurable_fst

lemma lem_095 (p : str_001) {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (def_016 p)) :
    ∫ h, g h.2 ∂(def_015 p) = ∫ z, g z ∂(def_016 p) :=
  (integral_map (measurable_snd (α := ℝ × ℝ) (β := ℝ)).aemeasurable hg).symm

lemma lem_096 (p : str_001) {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (def_016 p)) :
    Integrable (fun h : abb_002 => g h.2) (def_015 p)
      ↔ Integrable g (def_016 p) :=
  (integrable_map_measure hg (measurable_snd (α := ℝ × ℝ) (β := ℝ)).aemeasurable).symm

end S38

section S17

variable (p₀ : str_001) (lik : ℝ → ℝ)

def def_072 (h : abb_002) : ℝ := def_014 p₀ h * lik h.2

def def_073 : ℝ := ∫ h, def_072 p₀ lik h

def def_074 (h : abb_002) : ℝ := def_072 p₀ lik h / def_073 p₀ lik

def def_075 (p : str_001) : ℝ :=
  ∫ h, Real.log (def_072 p₀ lik h / def_014 p h) ∂(def_015 p)

def def_076 (p : str_001) : ℝ :=
  ∫ h, Real.log (def_014 p h / def_074 p₀ lik h) ∂(def_015 p)

def def_077 (μ : Measure ℝ) : ℝ := -∫ z, Real.log (lik z) ∂μ

def def_078 : abb_003 Unit :=
  fun μ _ => ((def_077 lik μ : ℝ) : EReal)

variable {p₀ lik}

lemma lem_097 {p : str_001} {h : abb_002}
    (hh : 0 < def_014 p h) :
    0 < def_008 p h.1
      ∧ 0 < def_003 (def_012 h) (def_011 h) (def_013 h) := by
  have hq0 := lem_013 p h.1
  have hN0 := lem_011 (def_012 h) (def_011 h) (def_013 h)
  refine ⟨hq0.lt_of_ne fun h' => ?_, hN0.lt_of_ne fun h' => ?_⟩
  · rw [def_014, ← h', zero_mul] at hh; exact lt_irrefl 0 hh
  · rw [def_014, ← h', mul_zero] at hh; exact lt_irrefl 0 hh

lemma lem_098 (p p₀ : str_001) (h : abb_002)
    (hh : 0 < def_014 p h) : 0 < def_014 p₀ h := by
  obtain ⟨hq, hN⟩ := lem_097 hh
  exact mul_pos (lem_072 p p₀ h.1 hq) hN

lemma lem_099 {p : str_001} {h : abb_002} (hh : 0 < def_014 p h)
    (hl : 0 < lik h.2) :
    Real.log (def_072 p₀ lik h / def_014 p h)
      = Real.log (lik h.2) - Real.log (def_008 p h.1 / def_008 p₀ h.1) := by
  obtain ⟨hq, hN⟩ := lem_097 hh
  have hq₀ := lem_072 p p₀ h.1 hq
  rw [def_072, def_014, def_014,
    show def_008 p₀ h.1 * def_003 (def_012 h) (def_011 h)
        (def_013 h) * lik h.2
        / (def_008 p h.1 * def_003 (def_012 h) (def_011 h)
          (def_013 h)) = lik h.2 * (def_008 p h.1 / def_008 p₀ h.1)⁻¹ by
      field_simp,
    Real.log_mul hl.ne' (inv_pos.mpr (div_pos hq hq₀)).ne', Real.log_inv, sub_eq_add_neg]

lemma lem_100 (p : str_001) :
    ∀ᵐ h ∂(def_015 p), 0 < def_014 p h :=
  lem_071 _ (lem_016 p)

variable (hlm : Measurable lik)
include hlm

theorem thm_161 (p : str_001) (hpos : ∀ᵐ h ∂(def_015 p), 0 < lik h.2)
    (hint : Integrable (fun z => Real.log (lik z)) (def_016 p)) :
    -def_075 p₀ lik p
      = def_077 lik (def_035 (def_024 p)) + def_017 p p₀ := by
  have hlog : AEStronglyMeasurable (fun z => Real.log (lik z)) (def_016 p) :=
    (Real.measurable_log.comp hlm).aestronglyMeasurable
  have hKm : AEStronglyMeasurable (fun q => Real.log (def_008 p q / def_008 p₀ q))
      (def_009 p) :=
    (thm_088 p p₀).aestronglyMeasurable
  have hae : (fun h => Real.log (def_072 p₀ lik h / def_014 p h)) =ᵐ[def_015 p]
      fun h => Real.log (lik h.2) - Real.log (def_008 p h.1 / def_008 p₀ h.1) := by
    filter_upwards [lem_100 p, hpos] with h hh hl
    exact lem_099 (p₀ := p₀) (lik := lik) hh hl
  have i1 : Integrable (fun h : abb_002 => Real.log (lik h.2)) (def_015 p) :=
    (lem_096 p (g := fun z => Real.log (lik z)) hlog).mpr hint
  have i2 : Integrable (fun h : abb_002 => Real.log (def_008 p h.1 / def_008 p₀ h.1))
      (def_015 p) := lem_094 p
      (g := fun q => Real.log (def_008 p q / def_008 p₀ q)) (thm_088 p p₀)
  have e1 := lem_095 p (g := fun z => Real.log (lik z)) hlog
  have e2 := lem_093 p
    (g := fun q => Real.log (def_008 p q / def_008 p₀ q)) hKm
  rw [def_075, integral_congr_ae hae, integral_sub i1 i2, e1, e2, def_077,
    ← thm_068, def_017]
  ring

theorem thm_162 (p : str_001)
    (hpos : ∀ᵐ h ∂(def_015 p), 0 < lik h.2)
    (hint : Integrable (fun z => Real.log (lik z)) (def_016 p)) :
    ((-def_075 p₀ lik p : ℝ) : EReal)
      = def_018 (def_078 lik) p p₀ ⟨1, one_pos⟩ () := by
  rw [thm_161 hlm p hpos hint, def_018, def_078,
    thm_068, one_mul, EReal.coe_add]

theorem thm_163 (p : str_001) (hev : 0 < def_073 p₀ lik)
    (hpos : ∀ᵐ h ∂(def_015 p), 0 < lik h.2)
    (hint : Integrable (fun z => Real.log (lik z)) (def_016 p)) :
    -def_075 p₀ lik p = def_076 p₀ lik p - Real.log (def_073 p₀ lik) := by
  have hlog : AEStronglyMeasurable (fun z => Real.log (lik z)) (def_016 p) :=
    (Real.measurable_log.comp hlm).aestronglyMeasurable
  have hae : (fun h => Real.log (def_014 p h / def_074 p₀ lik h))
      =ᵐ[def_015 p]
      fun h => -Real.log (def_072 p₀ lik h / def_014 p h)
        + Real.log (def_073 p₀ lik) := by
    filter_upwards [lem_100 p, hpos] with h hh hl
    have hj : 0 < def_072 p₀ lik h :=
      mul_pos (lem_098 p p₀ h hh) hl
    rw [def_074, div_div_eq_mul_div, Real.log_div (mul_pos hh hev).ne' hj.ne',
      Real.log_mul hh.ne' hev.ne', Real.log_div hj.ne' hh.ne']
    ring
  have i1 : Integrable (fun h => Real.log (def_072 p₀ lik h / def_014 p h))
      (def_015 p) := by
    have hae' : (fun h => Real.log (def_072 p₀ lik h / def_014 p h))
        =ᵐ[def_015 p]
        fun h => Real.log (lik h.2) - Real.log (def_008 p h.1 / def_008 p₀ h.1) := by
      filter_upwards [lem_100 p, hpos] with h hh hl
      exact lem_099 (p₀ := p₀) (lik := lik) hh hl
    refine Integrable.congr ?_ hae'.symm
    exact ((lem_096 p (g := fun z => Real.log (lik z)) hlog).mpr hint).sub
      (lem_094 p
      (g := fun q => Real.log (def_008 p q / def_008 p₀ q)) (thm_088 p p₀))
  have i1' : Integrable (fun h => -Real.log (def_072 p₀ lik h / def_014 p h))
      (def_015 p) := i1.neg
  rw [def_076, integral_congr_ae hae, integral_add i1' (integrable_const _), integral_neg,
    integral_const, probReal_univ, one_smul, def_075]
  ring

theorem thm_164 (x : str_002) (p : str_001) (hx : def_024 p = x)
    (hpos : ∀ᵐ z ∂(def_035 x), 0 < lik z)
    (hint : Integrable (fun z => Real.log (lik z)) (def_035 x)) :
    def_075 p₀ lik p ≤ def_075 p₀ lik (def_026 x (def_050 p₀ x))
      ∧ (def_075 p₀ lik p = def_075 p₀ lik (def_026 x (def_050 p₀ x))
          ↔ p = def_026 x (def_050 p₀ x)) := by
  set p' := def_026 x (def_050 p₀ x)
  have hint₁ : Integrable (fun z => Real.log (lik z)) (def_016 p) := by
    rwa [thm_068, hx]
  have hint₂ : Integrable (fun z => Real.log (lik z)) (def_016 p') := by
    rwa [thm_076]
  have hpos₁ : ∀ᵐ h ∂(def_015 p), 0 < lik h.2 := by
    refine ae_of_ae_map (f := def_013) (μ := def_015 p) (p := fun z => 0 < lik z)
      measurable_snd.aemeasurable ?_
    rw [← def_016, thm_068, hx]
    exact hpos
  have hpos₂ : ∀ᵐ h ∂(def_015 p'), 0 < lik h.2 := by
    refine ae_of_ae_map (f := def_013) (μ := def_015 p') (p := fun z => 0 < lik z)
      measurable_snd.aemeasurable ?_
    rw [← def_016, thm_076]
    exact hpos
  have e1 := thm_161 (p₀ := p₀) hlm p hpos₁ hint₁
  have e2 := thm_161 (p₀ := p₀) hlm p' hpos₂ hint₂
  rw [thm_036] at e2
  rw [hx] at e1
  have hK : def_017 p p₀ = def_041 p₀ x (def_025 p) := by
    rw [thm_135, hx]
  have hK' : def_017 p' p₀ = def_041 p₀ x (def_050 p₀ x) := rfl
  have hp : p = def_026 x (def_025 p) := by
    conv_lhs => rw [← thm_038 p]
    rw [hx]
  constructor
  · by_cases h : (def_025 p : ℝ) = def_047 p₀ x
    · have : def_025 p = def_050 p₀ x := Subtype.ext h
      rw [hp, this]
    · have := thm_108 p₀ x (def_025 p) h
      linarith
  · constructor
    · intro heq
      by_contra hne
      have h : (def_025 p : ℝ) ≠ def_047 p₀ x := by
        intro h'
        have : def_025 p = def_050 p₀ x := Subtype.ext h'
        exact hne (hp.trans (by rw [this]))
      have := thm_108 p₀ x (def_025 p) h
      linarith
    · intro h
      rw [h]

end S17

end NS1
