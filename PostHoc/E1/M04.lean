import Mathlib
import PostHoc.E1.M03

/-! -/

noncomputable section

namespace NS1

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

theorem thm_081 (m : ℝ) (v : abb_001) :
    def_004 m v = gaussianReal m (v : ℝ).toNNReal := by
  have hv : (v : ℝ).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; exact v.property
  rw [def_004, gaussianReal_of_var_ne_zero _ hv]
  congr 1
  funext z
  rw [gaussianPDF, lem_012 _ _ _ v.property.le]

def def_036 (x : str_002) : Measure ℝ :=
  (def_002 ⟨x.alpha, x.alpha_pos⟩ ⟨x.s, x.s_pos⟩).bind
    (fun v => gaussianReal x.gamma v.toNNReal)

def def_037 (x : str_002) : Measure (ℝ × ℝ) :=
  volume.withDensity (fun q => ENNReal.ofReal
    (def_001 x.alpha x.s q.1 * def_003 x.gamma q.1 q.2))

lemma lem_019 (m : ℝ) :
    Measurable (fun v : ℝ => gaussianReal m v.toNNReal) :=
  measurable_gaussianReal.comp (measurable_const.prodMk measurable_id.real_toNNReal)

theorem thm_082 (x : str_002) :
    def_036 x = def_035 x := by
  have hk : Measurable (fun v : ℝ => gaussianReal x.gamma v.toNNReal) :=
    lem_019 x.gamma
  rw [def_036, thm_062, def_033,
    lem_006 measurable_inv hk]
  have hcomp : ((fun v : ℝ => gaussianReal x.gamma v.toNNReal) ∘ fun t : ℝ => t⁻¹)
      = fun t => gaussianReal x.gamma (1 / t).toNNReal := by
    funext t
    simp [one_div]
  rw [hcomp, thm_058 _ _ _ _ x.alpha_pos x.s_pos one_pos,
    def_032, def_035, one_mul]
  congr 1
  funext z
  congr 1
  exact thm_066 x z

theorem thm_083 (p : str_001) :
    def_016 p = def_036 (def_024 p) := by
  rw [thm_068, thm_082]

theorem thm_084 : Function.Injective def_036 := by
  intro x y h
  rw [thm_082, thm_082] at h
  exact thm_072 h

theorem thm_085 :
    Function.Injective def_036 ∧
      (∀ x : str_002, ∃ p : str_001, def_016 p = def_036 x) ∧
      (∀ p q : str_001, def_016 p = def_016 q ↔
        def_024 p = def_024 q) := by
  refine ⟨thm_084, fun x => ?_, thm_073⟩
  obtain ⟨p, hp⟩ := thm_039 x
  exact ⟨p, by rw [thm_083, hp]⟩

theorem thm_086 (x : str_002) :
    (def_037 x).map Prod.snd = def_036 x := by
  have hk : Measurable (fun v : ℝ => gaussianReal x.gamma v.toNNReal) :=
    lem_019 x.gamma
  have hIG := lem_009 x.alpha x.s
  have hdens : Measurable (fun q : ℝ × ℝ =>
      def_001 x.alpha x.s q.1 * def_003 x.gamma q.1 q.2) := by
    unfold def_003
    fun_prop
  ext s hs
  rw [Measure.map_apply measurable_snd hs, def_037,
    withDensity_apply _ (measurable_snd hs), def_036, Measure.bind_apply hs hk.aemeasurable,
    def_002, lintegral_withDensity_eq_lintegral_mul _ hIG.ennreal_ofReal
      (g := fun v => gaussianReal x.gamma v.toNNReal s) ((Measure.measurable_coe hs).comp hk),
    ← lintegral_indicator (measurable_snd hs), Measure.volume_eq_prod,
    lintegral_prod _ ((hdens.ennreal_ofReal.indicator (measurable_snd hs)).aemeasurable)]
  refine lintegral_congr fun v => ?_
  by_cases hv : 0 < v
  · have hv' : v.toNNReal ≠ 0 := by
      rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hv
    have hfun : (fun z => (Prod.snd ⁻¹' s).indicator (fun q : ℝ × ℝ => ENNReal.ofReal
        (def_001 x.alpha x.s q.1 * def_003 x.gamma q.1 q.2)) (v, z))
        = s.indicator (fun z => ENNReal.ofReal (def_001 x.alpha x.s v)
            * gaussianPDF x.gamma v.toNNReal z) := by
      funext z
      by_cases hz : z ∈ s
      · rw [Set.indicator_of_mem (show (v, z) ∈ Prod.snd ⁻¹' s from hz), Set.indicator_of_mem hz,
          gaussianPDF, ← ENNReal.ofReal_mul
          (thm_013 _ _ _ x.alpha_pos x.s_pos.le),
          lem_012 _ _ _ hv.le]
      · rw [Set.indicator_of_notMem (show (v, z) ∉ Prod.snd ⁻¹' s from hz),
          Set.indicator_of_notMem hz]
    rw [hfun, lintegral_indicator hs, lintegral_const_mul _ (measurable_gaussianPDF _ _)]
    change _ = ENNReal.ofReal (def_001 x.alpha x.s v)
      * gaussianReal x.gamma v.toNNReal s
    rw [gaussianReal_apply _ hv']
  · have h0 : def_001 x.alpha x.s v = 0 := lem_010 _ _ _ hv
    have hfun : (fun z => (Prod.snd ⁻¹' s).indicator (fun q : ℝ × ℝ => ENNReal.ofReal
        (def_001 x.alpha x.s q.1 * def_003 x.gamma q.1 q.2)) (v, z))
        = fun _ => 0 := by
      funext z
      simp [Set.indicator, h0]
    simp [hfun, h0]

end NS1
