import Mathlib
import PostHoc.E1.M03
import PostHoc.E1.M05
import PostHoc.E1.M06
import PostHoc.E1.M08
import PostHoc.E1.M11
import PostHoc.E1.M15

/-! -/

noncomputable section

namespace NS1

open Filter Set

section S45

lemma lem_154 {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v ≤ 1) :
    v - 1 - Real.log v < u - 1 - Real.log u := by
  have hv0 : 0 < v := by linarith
  have h := Real.log_lt_sub_one_of_pos (div_pos hu hv0) (by
    intro h; rw [div_eq_one_iff_eq hv0.ne'] at h; linarith)
  rw [Real.log_div hu.ne' hv0.ne'] at h
  have : (u / v - 1) ≤ u - v := by
    rw [div_sub_one hv0.ne', div_le_iff₀ hv0]
    nlinarith
  linarith

lemma lem_155 {u v : ℝ} (hu : 1 ≤ u) (huv : u < v) :
    u - 1 - Real.log u < v - 1 - Real.log v := by
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have h := Real.log_lt_sub_one_of_pos (div_pos hv0 hu0) (by
    intro h; rw [div_eq_one_iff_eq hu0.ne'] at h; linarith)
  rw [Real.log_div hv0.ne' hu0.ne'] at h
  have : (v / u - 1) ≤ v - u := by
    rw [div_sub_one hu0.ne', div_le_iff₀ hu0]
    nlinarith
  linarith

end S45

variable (p₀ : str_001) (x : str_002)

theorem thm_317 (t t' : ℝ) (ht : 0 < t)
    (hbetween : (t < t' ∧ t' ≤ def_047 p₀ x) ∨ (def_047 p₀ x ≤ t' ∧ t' < t)) :
    def_051 p₀ x t' < def_051 p₀ x t := by
  have hts := thm_100 p₀ x
  have hA := p₀.alpha_pos
  have h1 : 0 < 1 + def_047 p₀ x := by linarith
  unfold def_051
  rcases hbetween with ⟨h, h'⟩ | ⟨h, h'⟩
  · have ht' : 0 < t' := by linarith
    have e1 := lem_154 (u := (1 + t) / (1 + def_047 p₀ x)) (v := (1 + t') / (1 + def_047 p₀ x))
      (by positivity) (div_lt_div_of_pos_right (by linarith) h1)
      (by rw [div_le_one h1]; linarith)
    have e2 := lem_154 (u := t / def_047 p₀ x) (v := t' / def_047 p₀ x) (by positivity)
      (div_lt_div_of_pos_right h hts) (by rw [div_le_one hts]; linarith)
    nlinarith
  · have e1 := lem_155 (u := (1 + t') / (1 + def_047 p₀ x)) (v := (1 + t) / (1 + def_047 p₀ x))
      (by rw [le_div_iff₀ h1]; linarith) (div_lt_div_of_pos_right (by linarith) h1)
    have e2 := lem_155 (u := t' / def_047 p₀ x) (v := t / def_047 p₀ x)
      (by rw [le_div_iff₀ hts]; linarith) (div_lt_div_of_pos_right h' hts)
    nlinarith

variable {Y : Type*} (L : abb_003 Y) (w : abb_001) (y : Y)

theorem thm_318 (t t' : abb_001) :
    L (def_016 (def_026 x t)) y = L (def_016 (def_026 x t')) y := by
  rw [thm_076, thm_076]

omit L w y in
theorem thm_319 (hα : 1 < x.alpha) (t : abb_001) :
    def_080 (def_026 x t) / def_079 (def_026 x t) = t := by
  have ht := t.property
  have hs := x.s_pos
  have h1 : 1 + (t : ℝ) ≠ 0 := by linarith
  have h2 : x.alpha - 1 ≠ 0 := by linarith
  rw [thm_173 x hα, thm_172 x hα]
  field_simp

lemma lem_156 (hfin : L (def_035 x) y ≠ ⊥ ∧ L (def_035 x) y ≠ ⊤)
    (t : abb_001) :
    def_018 L (def_026 x t) p₀ w y
      = ((L (def_035 x) y).toReal + w.val * def_060 p₀ x
          + w.val * def_051 p₀ x t : ℝ) := by
  rw [thm_140, thm_141, def_061, def_059,
    EReal.coe_add, EReal.coe_add, EReal.coe_toReal hfin.2 hfin.1]

theorem thm_320 (hfin : L (def_035 x) y ≠ ⊥ ∧ L (def_035 x) y ≠ ⊤)
    (t : abb_001) :
    def_018 L (def_026 x t) p₀ w y
        = def_018 L (def_026 x (def_050 p₀ x)) p₀ w y
          + ((w.val * def_051 p₀ x t : ℝ) : EReal)
      ∧ ((t : ℝ) ≠ def_047 p₀ x → def_018 L (def_026 x (def_050 p₀ x)) p₀ w y
          < def_018 L (def_026 x t) p₀ w y) := by
  have hsel : def_018 L (def_026 x (def_050 p₀ x)) p₀ w y
      = ((L (def_035 x) y).toReal + w.val * def_060 p₀ x : ℝ) := by
    rw [thm_137, def_061, def_059, EReal.coe_add,
      EReal.coe_toReal hfin.2 hfin.1]
  have hfib := lem_156 p₀ x L w y hfin t
  refine ⟨by rw [hfib, hsel, ← EReal.coe_add], fun hne => ?_⟩
  rw [hsel, hfib, EReal.coe_lt_coe_iff]
  have := thm_105 p₀ x t t.property hne
  have := mul_pos w.property this
  linarith

theorem thm_321 (hfin : L (def_035 x) y ≠ ⊥ ∧ L (def_035 x) y ≠ ⊤)
    (t : abb_001) (hne : (t : ℝ) ≠ def_047 p₀ x) (ε : ℝ) (hε : 0 < ε) :
    ∃ t' : abb_001, |(t' : ℝ) - t| < ε
      ∧ def_018 L (def_026 x t') p₀ w y
        < def_018 L (def_026 x t) p₀ w y := by
  have ht := t.property
  have hts := thm_100 p₀ x
  set δ := min (ε / 2) (|def_047 p₀ x - t| / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by
    have : def_047 p₀ x - t ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    positivity)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδd : δ ≤ |def_047 p₀ x - t| / 2 := min_le_right _ _
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have habs : |def_047 p₀ x - t| = def_047 p₀ x - t := abs_of_pos (by linarith)
    refine ⟨⟨t + δ, by linarith⟩, by simp [abs_of_pos hδ0, hδε], ?_⟩
    rw [lem_156 p₀ x L w y hfin, lem_156 p₀ x L w y hfin,
      EReal.coe_lt_coe_iff]
    have := mul_lt_mul_of_pos_left (thm_317 p₀ x t (t + δ) ht
      (Or.inl ⟨by linarith, by linarith⟩)) w.property
    simp only
    linarith
  · have habs : |def_047 p₀ x - t| = t - def_047 p₀ x := by
      rw [abs_sub_comm]; exact abs_of_pos (by linarith)
    refine ⟨⟨t - δ, by linarith⟩, by simp [abs_of_pos hδ0, hδε], ?_⟩
    rw [lem_156 p₀ x L w y hfin, lem_156 p₀ x L w y hfin,
      EReal.coe_lt_coe_iff]
    have := mul_lt_mul_of_pos_left (thm_317 p₀ x t (t - δ) ht
      (Or.inr ⟨by linarith, by linarith⟩)) w.property
    simp only
    linarith

theorem thm_322
    (hfin : L (def_035 x) y ≠ ⊥ ∧ L (def_035 x) y ≠ ⊤)
    (t : abb_001) (hne : (t : ℝ) ≠ def_047 p₀ x) (ε : ℝ) (hε : 0 < ε) :
    ∃ t' : abb_001, |(def_026 x t').nu - (def_026 x t).nu| < ε
      ∧ |(def_026 x t').beta - (def_026 x t).beta| < ε
      ∧ def_018 L (def_026 x t') p₀ w y
        < def_018 L (def_026 x t) p₀ w y := by
  have ht := t.property
  have hc1 : ContinuousAt (fun u : ℝ => 1 / u) t := continuousAt_const.div continuousAt_id ht.ne'
  have hc2 : ContinuousAt (fun u : ℝ => x.s / (1 + u)) t :=
    continuousAt_const.div (continuousAt_const.add continuousAt_id) (by linarith)
  obtain ⟨δ1, hδ1, h1⟩ := Metric.continuousAt_iff.mp hc1 ε hε
  obtain ⟨δ2, hδ2, h2⟩ := Metric.continuousAt_iff.mp hc2 ε hε
  obtain ⟨t', ht', hlt⟩ :=
    thm_321 p₀ x L w y hfin t hne (min δ1 δ2) (lt_min hδ1 hδ2)
  refine ⟨t', ?_, ?_, hlt⟩
  · have := h1 (x := (t' : ℝ)) (by rw [Real.dist_eq]; exact lt_of_lt_of_le ht' (min_le_left _ _))
    rw [Real.dist_eq] at this
    exact this
  · have := h2 (x := (t' : ℝ)) (by rw [Real.dist_eq]; exact lt_of_lt_of_le ht' (min_le_right _ _))
    rw [Real.dist_eq] at this
    exact this

omit L w y in
theorem thm_323 (t : abb_001) :
    def_024 (def_026 x t) = x
      ∧ def_016 (def_026 x t) = def_035 x
      ∧ MeasureTheory.Integrable
          (fun h => Real.log (def_008 (def_026 x t) h / def_008 p₀ h))
          (def_009 (def_026 x t)) :=
  ⟨thm_036 x t, thm_076 x t,
    thm_088 _ p₀⟩

omit L w y in
theorem thm_324 (hα : 1 < x.alpha) (K : ℝ) :
    ∃ t : abb_001, K < def_080 (def_026 x t) / def_079 (def_026 x t)
      ∧ (def_099 p₀.alpha p₀.nu < def_080 (def_026 x t) / def_079 (def_026 x t)
          → (t : ℝ) ≠ def_047 p₀ x) := by
  refine ⟨⟨|K| + 1, by positivity⟩, ?_, ?_⟩
  · rw [thm_319 x hα]
    have := le_abs_self K
    change K < |K| + 1
    linarith
  · intro h heq
    rw [thm_319 x hα, heq] at h
    exact absurd h (not_lt.mpr (thm_232 p₀ x).2.le)

theorem thm_325 (hbot : L (def_035 x) y = ⊥) (t : abb_001) :
    def_018 L (def_026 x t) p₀ w y = ⊥
      ∧ def_018 L (def_026 x t) p₀ w y = ⨅ q, def_018 L q p₀ w y := by
  have h : def_018 L (def_026 x t) p₀ w y = ⊥ := by
    rw [def_018, thm_076, hbot, EReal.bot_add]
  exact ⟨h, le_antisymm (h ▸ bot_le) (iInf_le _ _)⟩

theorem thm_326 (htop : ∀ μ, L μ y = ⊤) (p : str_001) :
    def_018 L p p₀ w y = ⊤
      ∧ def_018 L p p₀ w y = ⨅ q, def_018 L q p₀ w y := by
  have h : ∀ q, def_018 L q p₀ w y = ⊤ := fun q => by
    rw [def_018, htop, EReal.top_add_coe]
  refine ⟨h p, ?_⟩
  rw [h p]
  exact (iInf_eq_top.mpr fun q => h q).symm

end NS1
