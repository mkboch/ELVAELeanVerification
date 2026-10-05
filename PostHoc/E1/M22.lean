import Mathlib
import PostHoc.E1.M04
import PostHoc.E1.M05
import PostHoc.E1.M07
import PostHoc.E1.M08
import PostHoc.E1.M21

/-! -/

noncomputable section

namespace NS1

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal

section S28

variable {α : Type*} [MeasurableSpace α]

def def_122 (m v : α → ℝ) (hm : Measurable m) (hv : Measurable v) : Kernel α ℝ where
  toFun a := gaussianReal (m a) (v a).toNNReal
  measurable' := measurable_gaussianReal.comp (hm.prodMk hv.real_toNNReal)

instance (m v : α → ℝ) (hm : Measurable m) (hv : Measurable v) :
    IsMarkovKernel (def_122 m v hm hv) :=
  ⟨fun a => by
    change IsProbabilityMeasure (gaussianReal (m a) (v a).toNNReal)
    infer_instance⟩

lemma lem_149 (c : ℝ) (hc : 0 ≤ c) (m v : ℝ) (hcv : c ≠ 0 → 0 < v)
    {s : Set ℝ} (hs : MeasurableSet s) :
    ∫⁻ z, s.indicator (fun z => ENNReal.ofReal (c * def_003 m v z)) z
      = ENNReal.ofReal c * gaussianReal m v.toNNReal s := by
  rcases eq_or_ne c 0 with h0 | h0
  · subst h0
    simp
  · have hv := hcv h0
    have hv' : v.toNNReal ≠ 0 := by
      rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hv
    have hfun : (fun z => ENNReal.ofReal (c * def_003 m v z))
        = fun z => ENNReal.ofReal c * gaussianPDF m v.toNNReal z := by
      funext z
      rw [gaussianPDF, ← ENNReal.ofReal_mul hc, lem_012 _ _ _ hv.le]
    rw [hfun, lintegral_indicator hs, lintegral_const_mul _ (measurable_gaussianPDF _ _),
      gaussianReal_apply _ hv']

theorem thm_299 (μ : Measure α) [SFinite μ] {c m v : α → ℝ}
    (hc : Measurable c) (hm : Measurable m) (hv : Measurable v) (hc0 : ∀ a, 0 ≤ c a)
    (hcv : ∀ a, c a ≠ 0 → 0 < v a) :
    (μ.prod volume).withDensity
        (fun p : α × ℝ => ENNReal.ofReal (c p.1 * def_003 (m p.1) (v p.1) p.2))
      = (μ.withDensity fun a => ENNReal.ofReal (c a)) ⊗ₘ def_122 m v hm hv := by
  have hF : Measurable
      (fun p : α × ℝ => ENNReal.ofReal (c p.1 * def_003 (m p.1) (v p.1) p.2)) := by
    unfold def_003
    fun_prop
  ext S hS
  rw [withDensity_apply _ hS, ← lintegral_indicator hS,
    lintegral_prod _ (hF.indicator hS).aemeasurable, Measure.compProd_apply hS,
    lintegral_withDensity_eq_lintegral_mul _ hc.ennreal_ofReal
      (Kernel.measurable_kernel_prodMk_left hS)]
  refine lintegral_congr fun a => ?_
  change _ = ENNReal.ofReal (c a) * gaussianReal (m a) (v a).toNNReal (Prod.mk a ⁻¹' S)
  rw [← lem_149 (c a) (hc0 a) (m a) (v a) (hcv a) (measurable_prodMk_left hS)]
  rfl

end S28

section S31

instance (p : str_001) : IsProbabilityMeasure (def_009 p) := thm_120 p

instance (p : str_001) : IsProbabilityMeasure (def_016 p) :=
  thm_070 p

instance (x : str_002) : IsProbabilityMeasure (def_035 x) := by
  rw [← thm_076 x ⟨1, one_pos⟩]
  infer_instance

def def_123 : Kernel (ℝ × ℝ) ℝ := def_122 Prod.fst Prod.snd measurable_fst measurable_snd

instance : IsMarkovKernel def_123 := by
  unfold def_123
  infer_instance

theorem thm_300 (p : str_001) : def_015 p = def_009 p ⊗ₘ def_123 := by
  rw [def_015, Measure.volume_eq_prod]
  exact thm_299 volume (lem_015 p) measurable_fst
    measurable_snd (lem_013 p) fun q hq => by
      by_contra h
      exact hq (lem_014 p q h)

theorem thm_301 (p : str_001) : def_016 p = def_123 ∘ₘ def_009 p := by
  rw [def_016, thm_300]
  exact Measure.snd_compProd (def_009 p) def_123

theorem thm_302 (p p₀ : str_001) :
    klDiv (def_009 p) (def_009 p₀) = ENNReal.ofReal (def_017 p p₀) := by
  have hP : IsProbabilityMeasure (volume.withDensity fun q => ENNReal.ofReal (def_008 p q)) :=
    thm_120 p
  have hP0 : IsProbabilityMeasure (volume.withDensity fun q => ENNReal.ofReal (def_008 p₀ q)) :=
    thm_120 p₀
  have hkl := thm_119 volume (lem_015 p) (lem_015 p₀)
    (lem_013 p) (lem_072 p p₀) (lem_073 p p₀)
  have hval : ∫ q : ℝ × ℝ, def_008 p q * Real.log (def_008 p q / def_008 p₀ q)
      = def_017 p p₀ := by
    rw [def_017, def_009, integral_withDensity_eq_integral_toReal_smul
      (lem_015 p).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    congr 1
    funext q
    rw [smul_eq_mul, ENNReal.toReal_ofReal (lem_013 p q)]
  change klDiv (volume.withDensity fun q => ENNReal.ofReal (def_008 p q))
    (volume.withDensity fun q => ENNReal.ofReal (def_008 p₀ q)) = _
  rw [hkl, hval]

theorem thm_303 {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (μ ν : Measure (β × γ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map Prod.swap) (ν.map Prod.swap) = klDiv μ ν := by
  refine le_antisymm (klDiv_map_le μ ν measurable_swap) ?_
  have h := klDiv_map_le (μ.map Prod.swap) (ν.map Prod.swap) measurable_swap
  rwa [Measure.map_map measurable_swap measurable_swap, Measure.map_map measurable_swap
    measurable_swap, Prod.swap_swap_eq, Measure.map_id, Measure.map_id] at h

end S31

section S14

variable (p₀ : str_001)

def def_124 (x : str_002) : ℝ≥0∞ :=
  klDiv (def_035 x) (def_035 (def_057 p₀))

theorem thm_304 (p : str_001) :
    klDiv (def_016 p) (def_016 p₀) ≤ ENNReal.ofReal (def_017 p p₀) := by
  have := thm_120 p
  have := thm_120 p₀
  rw [thm_301, thm_301, ← thm_302]
  exact klDiv_comp_right_le _ _ _

lemma lem_150 (x : str_002) :
    def_035 x = def_016 (def_026 x (def_050 p₀ x))
      ∧ def_035 (def_057 p₀) = def_016 p₀ :=
  ⟨(thm_076 x _).symm, (thm_068 p₀).symm⟩

theorem thm_305 (x : str_002) :
    def_124 p₀ x ≠ ⊤ ∧ (def_124 p₀ x).toReal ≤ def_060 p₀ x := by
  have h := thm_304 p₀ (def_026 x (def_050 p₀ x))
  rw [← (lem_150 p₀ x).1, ← (lem_150 p₀ x).2] at h
  have hR : def_060 p₀ x = def_017 (def_026 x (def_050 p₀ x)) p₀ := rfl
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top h, ?_⟩
  rw [hR]
  exact ENNReal.toReal_le_of_le_ofReal (thm_122 _ _) h

end S14

section S19

def def_125 (p p₀ : str_001) (q : ℝ × ℝ) : ℝ := def_008 p q / def_008 p₀ q

lemma lem_151 (p p₀ : str_001) : Measurable (def_125 p p₀) :=
  (lem_015 p).div (lem_015 p₀)

lemma lem_152 (p p₀ : str_001) (q : ℝ × ℝ) :
    def_008 p q = def_008 p₀ q * def_125 p p₀ q := by
  rcases (lem_013 p₀ q).lt_or_eq with h | h
  · rw [def_125]
    field_simp
  · have : def_008 p q = 0 := by
      rcases (lem_013 p q).lt_or_eq with h' | h'
      · exact absurd (lem_072 p p₀ q h') (by rw [← h]; exact lt_irrefl 0)
      · exact h'.symm
    rw [this, ← h, zero_mul]

theorem thm_306 (p p₀ : str_001) :
    def_009 p = (def_009 p₀).withDensity fun q => ENNReal.ofReal (def_125 p p₀ q) := by
  rw [def_009, def_009, ← withDensity_mul _ (lem_015 p₀).ennreal_ofReal
    (lem_151 p p₀).ennreal_ofReal]
  congr 1
  funext q
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (lem_013 p₀ q), lem_152 p p₀ q]

lemma lem_153 {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure (β × γ)) {F : β × γ → ℝ≥0∞} (hF : Measurable F) :
    (μ.withDensity F).map Prod.swap = (μ.map Prod.swap).withDensity (F ∘ Prod.swap) := by
  ext S hS
  rw [Measure.map_apply measurable_swap hS, withDensity_apply _ (measurable_swap hS),
    withDensity_apply _ hS, setLIntegral_map hS (hF.comp measurable_swap) measurable_swap]
  rfl

theorem thm_307 (p p₀ : str_001)
    (h : klDiv (def_016 p) (def_016 p₀) = ENNReal.ofReal (def_017 p p₀)) :
    def_009 p = def_009 p₀ := by
  have hP := thm_120 p
  have hP0 := thm_120 p₀
  set P := def_009 p with hPdef
  set P0 := def_009 p₀ with hP0def
  set H := P ⊗ₘ def_123 with hH
  set H0 := P0 ⊗ₘ def_123 with hH0
  set ρ := H.map Prod.swap with hρ
  set ρ0 := H0.map Prod.swap with hρ0
  have hHP : IsProbabilityMeasure H := by rw [hH]; infer_instance
  have hH0P : IsProbabilityMeasure H0 := by rw [hH0]; infer_instance
  have hρP : IsProbabilityMeasure ρ :=
    (Measure.isProbabilityMeasure_map_iff measurable_swap.aemeasurable).mpr hHP
  have hρ0P : IsProbabilityMeasure ρ0 :=
    (Measure.isProbabilityMeasure_map_iff measurable_swap.aemeasurable).mpr hH0P
  have hfst : ρ.fst = def_016 p := by
    rw [hρ, Measure.fst_map_swap, thm_301]
    exact Measure.snd_compProd P def_123
  have hfst0 : ρ0.fst = def_016 p₀ := by
    rw [hρ0, Measure.fst_map_swap, thm_301]
    exact Measure.snd_compProd P0 def_123
  have hKL : klDiv ρ ρ0 = ENNReal.ofReal (def_017 p p₀) := by
    rw [hρ, hρ0, thm_303, hH, hH0, klDiv_compProd_left, thm_302]
  have hchain := klDiv_compProd_eq_add ρ.fst ρ0.fst ρ.condKernel ρ0.condKernel
  rw [ρ.disintegrate ρ.condKernel, ρ0.disintegrate ρ0.condKernel, hKL] at hchain
  have hf : klDiv ρ.fst ρ0.fst = ENNReal.ofReal (def_017 p p₀) := by
    rw [hfst, hfst0, h]
  rw [hf] at hchain
  have hzero : klDiv ρ (ρ.fst ⊗ₘ ρ0.condKernel) = 0 :=
    (ENNReal.add_right_inj ENNReal.ofReal_ne_top).mp (hchain.symm.trans (add_zero _).symm)
  rw [klDiv_eq_zero_iff] at hzero
  have h1 := ProbabilityTheory.rnDeriv_measure_compProd_left ρ.fst ρ0.fst ρ0.condKernel
  rw [← hzero, ρ0.disintegrate ρ0.condKernel] at h1
  have hHwd : H = H0.withDensity fun w => ENNReal.ofReal (def_125 p p₀ w.1) := by
    rw [hH, hH0, hPdef, thm_306 p p₀,
      Measure.withDensity_compProd (lem_151 p p₀).ennreal_ofReal]
  have hρwd : ρ = ρ0.withDensity fun w => ENNReal.ofReal (def_125 p p₀ w.2) := by
    rw [hρ, hρ0, hHwd, lem_153 H0
      (F := fun w : (ℝ × ℝ) × ℝ => ENNReal.ofReal (def_125 p p₀ w.1))
      ((lem_151 p p₀).ennreal_ofReal.comp measurable_fst)]
    rfl
  have h2 : ρ.rnDeriv ρ0 =ᵐ[ρ0] fun w => ENNReal.ofReal (def_125 p p₀ w.2) := by
    conv_lhs => rw [hρwd]
    exact Measure.rnDeriv_withDensity ρ0
      ((lem_151 p p₀).ennreal_ofReal.comp measurable_snd)
  set g := ρ.fst.rnDeriv ρ0.fst with hg
  have hae : ∀ᵐ w ∂ρ0, ENNReal.ofReal (def_125 p p₀ w.2) = g w.1 := by
    filter_upwards [h1, h2] with w hw1 hw2
    rw [← hw2, hw1]
  have hae' : ∀ᵐ w ∂H0, ENNReal.ofReal (def_125 p p₀ w.1) = g w.2 :=
    ae_of_ae_map measurable_swap.aemeasurable hae
  have hmeasSet : MeasurableSet {w : (ℝ × ℝ) × ℝ | ENNReal.ofReal (def_125 p p₀ w.1) = g w.2} :=
    measurableSet_eq_fun ((lem_151 p p₀).ennreal_ofReal.comp measurable_fst)
      ((Measure.measurable_rnDeriv _ _).comp measurable_snd)
  rw [hH0, Measure.ae_compProd_iff hmeasSet] at hae'
  have hpos : ∀ᵐ q ∂P0, 0 < q.2 := by
    filter_upwards [lem_071 volume (lem_015 p₀)] with q hq
    by_contra hc
    rw [lem_014 p₀ q hc] at hq
    exact lt_irrefl 0 hq
  have hgood : ∀ᵐ q ∂P0, ∀ᵐ z ∂(volume : Measure ℝ), ENNReal.ofReal (def_125 p p₀ q) = g z := by
    filter_upwards [hae', hpos] with q hq hq2
    have hv : q.2.toNNReal ≠ 0 := by
      rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hq2
    exact (gaussianReal_absolutelyContinuous' q.1 hv).ae_le hq
  have hne : (ae P0).NeBot := ae_neBot.mpr (IsProbabilityMeasure.ne_zero P0)
  obtain ⟨q₀, hq₀⟩ := hgood.exists
  have hconst : ∀ᵐ q ∂P0, ENNReal.ofReal (def_125 p p₀ q) = ENNReal.ofReal (def_125 p p₀ q₀) := by
    filter_upwards [hgood] with q hq
    obtain ⟨z, hz, hz₀⟩ := (hq.and hq₀).exists
    rw [hz, hz₀]
  have hPc : P = ENNReal.ofReal (def_125 p p₀ q₀) • P0 := by
    rw [hPdef, thm_306 p p₀, ← hP0def, withDensity_congr_ae hconst,
      withDensity_const]
  have hc1 : ENNReal.ofReal (def_125 p p₀ q₀) = 1 := by
    have := congrArg (fun μ : Measure (ℝ × ℝ) => μ univ) hPc
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] at this
    exact this.symm
  rw [hPc, hc1, one_smul]

variable (p₀ : str_001)

theorem thm_308 (x : str_002) :
    (def_124 p₀ x).toReal = def_060 p₀ x ↔ x = def_057 p₀ := by
  constructor
  · intro h
    set p := def_026 x (def_050 p₀ x)
    have hfin := (thm_305 p₀ x).1
    have hR : def_060 p₀ x = def_017 p p₀ := rfl
    have hkl : klDiv (def_016 p) (def_016 p₀)
        = ENNReal.ofReal (def_017 p p₀) := by
      rw [← (lem_150 p₀ x).1, ← (lem_150 p₀ x).2, ← hR, ← h]
      exact (ENNReal.ofReal_toReal hfin).symm
    have hnig := thm_307 p p₀ hkl
    have hpred := thm_124 hnig
    rw [← (lem_150 p₀ x).1, ← (lem_150 p₀ x).2] at hpred
    exact thm_072 hpred
  · rintro rfl
    rw [def_124, klDiv_self, ENNReal.toReal_zero]
    exact (thm_130 p₀).symm

end S19

section S39

def def_126 (x : str_002) : Measure ℝ :=
  def_002 ⟨x.alpha, x.alpha_pos⟩ ⟨x.s, x.s_pos⟩

instance (x : str_002) : IsProbabilityMeasure (def_126 x) :=
  thm_087 _ _

def def_127 (x x₀ : str_002) : ℝ≥0∞ := klDiv (def_126 x) (def_126 x₀)

def def_128 (x x₀ : str_002) : ℝ≥0∞ :=
  klDiv (def_037 x) (def_037 x₀)

theorem thm_309 (x x' x₀ : str_002) (ha : x.alpha = x'.alpha)
    (hs : x.s = x'.s) :
    def_127 x x₀ = def_127 x' x₀ := by
  have : def_126 x = def_126 x' := by
    simp only [def_126]
    congr 2
  rw [def_127, def_127, this]

def def_129 (x : str_002) : str_001 :=
  ⟨x.gamma, 1, x.alpha, x.s, one_pos, x.alpha_pos, x.s_pos⟩

theorem thm_310 (x : str_002) :
    def_037 x = (def_009 (def_129 x)).map Prod.swap := by
  rw [def_009, lem_153 _ (lem_015 _).ennreal_ofReal,
    Measure.volume_eq_prod, Measure.prod_swap, ← Measure.volume_eq_prod, def_037]
  congr 1
  funext q
  simp only [Function.comp, def_008, def_129, Prod.fst_swap, Prod.snd_swap, div_one]

theorem thm_311 (x : str_002) :
    def_037 x = def_126 x ⊗ₘ def_122 (fun _ => x.gamma) id measurable_const
      measurable_id := by
  rw [def_037, Measure.volume_eq_prod]
  exact thm_299 volume (lem_009 _ _)
    measurable_const measurable_id
    (fun V => thm_013 _ _ _ x.alpha_pos x.s_pos.le) fun V hV => by
      by_contra h
      exact hV (lem_010 _ _ _ h)

def def_130 (x x₀ : str_002) : ℝ :=
  x₀.alpha * Real.log (x.s / x₀.s) + Real.log (Real.Gamma x₀.alpha / Real.Gamma x.alpha)
    + (x.alpha - x₀.alpha) * def_019 x.alpha - x.alpha + x.alpha * x₀.s / x.s

theorem thm_312 (x x₀ : str_002) :
    def_128 x x₀ = ENNReal.ofReal (def_017 (def_129 x) (def_129 x₀)) := by
  have := thm_120 (def_129 x)
  have := thm_120 (def_129 x₀)
  rw [def_128, thm_310, thm_310, thm_303,
    thm_302]

theorem thm_313 (x x₀ : str_002) :
    def_127 x x₀ = ENNReal.ofReal (def_130 x x₀) ∧ 0 ≤ def_130 x x₀ := by
  let x' : str_002 := ⟨x₀.gamma, x.alpha, x.s, x.alpha_pos, x.s_pos⟩
  have hmix : def_126 x' = def_126 x := rfl
  have hIG := thm_087 ⟨x.alpha, x.alpha_pos⟩ ⟨x.s, x.s_pos⟩
  have hIG0 := thm_087 ⟨x₀.alpha, x₀.alpha_pos⟩ ⟨x₀.s, x₀.s_pos⟩
  have h1 : def_128 x' x₀ = def_127 x x₀ := by
    rw [def_128, thm_311, thm_311, hmix]
    exact klDiv_compProd_left _ _ _
  have hform : def_017 (def_129 x') (def_129 x₀) = def_130 x x₀ := by
    rw [thm_089, def_039, def_130]
    simp only [def_129, x', sub_self, div_one, Real.log_one]
    ring
  rw [← h1, thm_312, hform]
  exact ⟨rfl, hform ▸ thm_122 _ _⟩

theorem thm_314 (x x₀ : str_002) :
    def_128 x x₀
      = def_127 x x₀ + ENNReal.ofReal (x.alpha * (x.gamma - x₀.gamma) ^ 2 / (2 * x.s)) := by
  obtain ⟨hV, hV0⟩ := thm_313 x x₀
  have hs := x.s_pos
  have hform : def_017 (def_129 x) (def_129 x₀)
      = def_130 x x₀ + x.alpha * (x.gamma - x₀.gamma) ^ 2 / (2 * x.s) := by
    rw [thm_089, def_039, def_130]
    simp only [def_129, div_one, Real.log_one]
    field_simp
    ring
  rw [thm_312, hform, hV, ENNReal.ofReal_add hV0 (by have := x.alpha_pos; positivity)]

theorem thm_315 (p₀ p₀' : str_001)
    (h : def_016 p₀ = def_016 p₀') (x : str_002) :
    def_127 x (def_057 p₀) = def_127 x (def_057 p₀')
      ∧ def_128 x (def_057 p₀) = def_128 x (def_057 p₀') := by
  have hq : def_057 p₀ = def_057 p₀' := (thm_073 p₀ p₀').mp h
  rw [hq]
  exact ⟨rfl, rfl⟩

theorem thm_316 (x₀ x : str_002) (hγ : x.gamma ≠ x₀.gamma) :
    ∃ (n : ℝ) (hn : 0 < n), def_057 (def_089 x₀ n hn) = x₀
      ∧ def_060 (def_089 x₀ n hn) x ≠ (def_127 x x₀).toReal
      ∧ def_060 (def_089 x₀ n hn) x ≠ (def_128 x x₀).toReal := by
  obtain ⟨N, hN⟩ := thm_297 x₀ x hγ
    (max (def_127 x x₀).toReal (def_128 x x₀).toReal)
  refine ⟨max N 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    thm_203 x₀ _ _, ?_, ?_⟩
  · have := hN (max N 1) (lt_of_lt_of_le one_pos (le_max_right _ _)) (le_max_left _ _)
    exact (lt_of_le_of_lt (le_max_left _ _) this).ne'
  · have := hN (max N 1) (lt_of_lt_of_le one_pos (le_max_right _ _)) (le_max_left _ _)
    exact (lt_of_le_of_lt (le_max_right _ _) this).ne'

end S39

end NS1
