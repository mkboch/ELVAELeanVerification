import Mathlib
import PostHoc.E1.M02
import PostHoc.E1.M08
import PostHoc.E1.M11
import PostHoc.E1.M12

/-! -/

noncomputable section

namespace NS1

open Set

section S10

variable (κ : ℝ) (hκ : κ ≠ 0)

def def_112 (p : str_001) : str_001 where
  gamma := κ * p.gamma
  nu := p.nu
  alpha := p.alpha
  beta := κ ^ 2 * p.beta
  nu_pos := p.nu_pos
  alpha_pos := p.alpha_pos
  beta_pos := by have := p.beta_pos; positivity

def def_113 (x : str_002) : str_002 where
  gamma := κ * x.gamma
  alpha := x.alpha
  s := κ ^ 2 * x.s
  alpha_pos := x.alpha_pos
  s_pos := by have := x.s_pos; positivity

include hκ

theorem thm_273 (p : str_001) :
    def_024 (def_112 κ hκ p) = def_113 κ hκ (def_024 p) := by
  apply str_002.ext
  · rfl
  · rfl
  · change κ ^ 2 * p.beta * (1 + 1 / p.nu) = κ ^ 2 * (p.beta * (1 + 1 / p.nu))
    ring

theorem thm_274 (p₀ : str_001) (x : str_002) :
    (def_113 κ hκ x).s = κ ^ 2 * x.s
      ∧ (def_113 κ hκ x).s / (def_113 κ hκ x).alpha = κ ^ 2 * (x.s / x.alpha)
      ∧ def_082 (def_112 κ hκ p₀) = κ ^ 2 * def_082 p₀ := by
  refine ⟨rfl, ?_, ?_⟩
  · simp only [def_113]
    ring
  · simp only [def_082, def_112]
    ring

theorem thm_275 (p₀ : str_001) (x : str_002) :
    def_084 (def_112 κ hκ p₀) (def_113 κ hκ x) = def_084 p₀ x := by
  have hk : κ ^ 2 ≠ 0 := pow_ne_zero 2 hκ
  have := x.s_pos
  simp only [def_084, def_113, def_112, def_082]
  field_simp

theorem thm_276 (p₀ : str_001) (x : str_002) :
    def_047 (def_112 κ hκ p₀) (def_113 κ hκ x) = def_047 p₀ x
      ∧ def_048 (def_112 κ hκ p₀) (def_113 κ hκ x) = def_048 p₀ x := by
  rw [(thm_184 _ _).1, (thm_184 _ _).2, (thm_184 p₀ x).1,
    (thm_184 p₀ x).2, thm_275 κ hκ]
  exact ⟨rfl, rfl⟩

theorem thm_277 (p₀ : str_001) (x : str_002) (t : ℝ) :
    def_042 (def_112 κ hκ p₀) (def_113 κ hκ x) t = def_042 p₀ x t := by
  have hk : κ ^ 2 ≠ 0 := pow_ne_zero 2 hκ
  have hk' : 0 < κ ^ 2 := by positivity
  have hs := x.s_pos
  have hb := p₀.beta_pos
  simp only [def_042, def_040, def_113, def_112]
  rw [show κ ^ 2 * x.s / (κ ^ 2 * p₀.beta) = x.s / p₀.beta by field_simp]
  congr 1
  field_simp

theorem thm_278 (p₀ : str_001) (x : str_002) :
    def_060 (def_112 κ hκ p₀) (def_113 κ hκ x) = def_060 p₀ x := by
  rw [def_060, def_060, thm_091, thm_091]
  simp only [def_050]
  rw [(thm_276 κ hκ p₀ x).1, thm_277 κ hκ]

theorem thm_279 (p : str_001) (hα : 1 < p.alpha) :
    def_079 (def_112 κ hκ p) = κ ^ 2 * def_079 p
      ∧ def_080 (def_112 κ hκ p) = κ ^ 2 * def_080 p
      ∧ def_081 (def_112 κ hκ p) = κ ^ 2 * def_081 p := by
  have hα' : 1 < (def_112 κ hκ p).alpha := hα
  rw [thm_166 _ hα', thm_166 _ hα, thm_168 _ hα', thm_168 _ hα, thm_171 _ hα',
    thm_171 _ hα]
  simp only [def_112, def_022]
  refine ⟨by ring, by ring, by ring⟩

end S10

section S25

variable (p₀ : str_001)

def def_114 (κ : ℝ) (hκ : κ ≠ 0) (x : str_002) : str_002 := def_113 κ hκ x

theorem thm_280 (κ : ℝ) (hκ : κ ≠ 0) (x : str_002) :
    def_084 p₀ (def_114 κ hκ x)
        = x.alpha * ((κ * x.gamma - p₀.gamma) ^ 2 + def_082 p₀) / (κ ^ 2 * x.s)
      ∧ def_084 p₀ (def_114 κ hκ x)
        = ((x.gamma - p₀.gamma / κ) ^ 2 + def_082 p₀ / κ ^ 2) / (x.s / x.alpha) := by
  refine ⟨rfl, ?_⟩
  have := x.s_pos
  have := x.alpha_pos
  simp only [def_084, def_114, def_113]
  field_simp

theorem thm_281 (hg : p₀.gamma = 0) (x : str_002) {κ κ' : ℝ} (hκ : 0 < κ)
    (hκκ : κ < κ') :
    def_084 p₀ (def_114 κ' (by linarith) x) < def_084 p₀ (def_114 κ hκ.ne' x)
      ∧ def_047 p₀ (def_114 κ hκ.ne' x) < def_047 p₀ (def_114 κ' (by linarith) x) := by
  have hb := thm_178 p₀
  have hs := x.s_pos
  have hα := x.alpha_pos
  have hQ : def_084 p₀ (def_114 κ' (by linarith) x) < def_084 p₀ (def_114 κ hκ.ne' x) := by
    rw [(thm_280 p₀ κ' _ x).2, (thm_280 p₀ κ _ x).2, hg]
    simp only [zero_div, sub_zero]
    apply div_lt_div_of_pos_right _ (by positivity)
    have : def_082 p₀ / κ' ^ 2 < def_082 p₀ / κ ^ 2 :=
      div_lt_div_of_pos_left hb (by positivity) (by nlinarith)
    linarith
  exact ⟨hQ, (thm_197 p₀ _ _).mpr hQ⟩

def def_115 (κ : ℝ) (hκ : κ ≠ 0) (x : str_002) : str_002 where
  gamma := p₀.gamma + κ * (x.gamma - p₀.gamma)
  alpha := x.alpha
  s := κ ^ 2 * x.s
  alpha_pos := x.alpha_pos
  s_pos := by have := x.s_pos; positivity

theorem thm_282 (x : str_002) {κ κ' : ℝ} (hκ : 0 < κ) (hκκ : κ < κ') :
    def_084 p₀ (def_115 p₀ κ hκ.ne' x)
        = ((x.gamma - p₀.gamma) ^ 2 + def_082 p₀ / κ ^ 2) / (x.s / x.alpha)
      ∧ def_084 p₀ (def_115 p₀ κ' (by linarith) x)
        < def_084 p₀ (def_115 p₀ κ hκ.ne' x)
      ∧ def_047 p₀ (def_115 p₀ κ hκ.ne' x)
        < def_047 p₀ (def_115 p₀ κ' (by linarith) x) := by
  have hb := thm_178 p₀
  have hs := x.s_pos
  have hα := x.alpha_pos
  have hform : ∀ (c : ℝ) (hc : c ≠ 0), def_084 p₀ (def_115 p₀ c hc x)
      = ((x.gamma - p₀.gamma) ^ 2 + def_082 p₀ / c ^ 2) / (x.s / x.alpha) := by
    intro c hc
    simp only [def_084, def_115]
    field_simp
    ring
  have hQ : def_084 p₀ (def_115 p₀ κ' (by linarith) x)
      < def_084 p₀ (def_115 p₀ κ hκ.ne' x) := by
    rw [hform, hform]
    apply div_lt_div_of_pos_right _ (by positivity)
    have : def_082 p₀ / κ' ^ 2 < def_082 p₀ / κ ^ 2 :=
      div_lt_div_of_pos_left hb (by positivity) (by nlinarith)
    linarith
  exact ⟨hform κ hκ.ne', hQ, (thm_197 p₀ _ _).mpr hQ⟩

theorem thm_283 (hg : p₀.gamma = 0) (x : str_002) :
    def_084 p₀ (def_114 2 two_ne_zero x) ≠ def_084 p₀ x := by
  have h := (thm_281 p₀ hg x (κ := 1) one_pos one_lt_two).1
  have e : def_084 p₀ (def_114 1 one_ne_zero x) = def_084 p₀ x := by
    simp [def_114, def_113]
  rw [e] at h
  exact h.ne

theorem thm_284 (hg : p₀.gamma = 0) :
    ∃ (x₁ x₂ : str_002) (κ κ' : ℝ) (hκ : κ ≠ 0) (hκ' : κ' ≠ 0),
      def_084 p₀ (def_114 κ hκ x₁) < def_084 p₀ (def_114 κ hκ x₂)
      ∧ def_084 p₀ (def_114 κ' hκ' x₂) < def_084 p₀ (def_114 κ' hκ' x₁)
      ∧ def_047 p₀ (def_114 κ hκ x₂) < def_047 p₀ (def_114 κ hκ x₁)
      ∧ def_047 p₀ (def_114 κ' hκ' x₁) < def_047 p₀ (def_114 κ' hκ' x₂) := by
  have hb := thm_178 p₀
  let x₁ : str_002 := ⟨1, 1, 1, one_pos, one_pos⟩
  let x₂ : str_002 := ⟨0, 1, 1 / 2, one_pos, by norm_num⟩
  have hκ : Real.sqrt (def_082 p₀ / 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hκ' : Real.sqrt (2 * def_082 p₀) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have e1 : Real.sqrt (def_082 p₀ / 2) ^ 2 = def_082 p₀ / 2 := Real.sq_sqrt (by positivity)
  have e2 : Real.sqrt (2 * def_082 p₀) ^ 2 = 2 * def_082 p₀ := Real.sq_sqrt (by positivity)
  have h1 : def_084 p₀ (def_114 _ hκ x₁) < def_084 p₀ (def_114 _ hκ x₂) := by
    rw [(thm_280 p₀ _ hκ x₁).1, (thm_280 p₀ _ hκ x₂).1, hg, e1]
    simp only [x₁, x₂]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (Real.sqrt (def_082 p₀ / 2))]
  have h2 : def_084 p₀ (def_114 _ hκ' x₂) < def_084 p₀ (def_114 _ hκ' x₁) := by
    rw [(thm_280 p₀ _ hκ' x₁).1, (thm_280 p₀ _ hκ' x₂).1, hg, e2]
    simp only [x₁, x₂]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (Real.sqrt (2 * def_082 p₀))]
  exact ⟨x₁, x₂, _, _, hκ, hκ', h1, h2, (thm_197 p₀ _ _).mpr h1,
    (thm_197 p₀ _ _).mpr h2⟩

end S25

end NS1
