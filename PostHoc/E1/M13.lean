import Mathlib
import PostHoc.E1.M12

/-! -/

noncomputable section

namespace NS1

open Set

section S22

variable (x₀ : str_002)

def def_089 (n : ℝ) (hn : 0 < n) : str_001 where
  gamma := x₀.gamma
  nu := n
  alpha := x₀.alpha
  beta := x₀.s * n / (n + 1)
  nu_pos := hn
  alpha_pos := x₀.alpha_pos
  beta_pos := by have := x₀.s_pos; positivity

theorem thm_203 (n : ℝ) (hn : 0 < n) :
    def_024 (def_089 x₀ n hn) = x₀ := by
  apply str_002.ext
  · rfl
  · rfl
  · change x₀.s * n / (n + 1) * (1 + 1 / n) = x₀.s
    field_simp

theorem thm_204 (p₀ : str_001) :
    def_016 p₀ = def_035 x₀ ↔ ∃ (n : ℝ) (hn : 0 < n), p₀ = def_089 x₀ n hn := by
  rw [thm_068, thm_072.eq_iff]
  constructor
  · intro h
    refine ⟨p₀.nu, p₀.nu_pos, ?_⟩
    have hg : p₀.gamma = x₀.gamma := congrArg str_002.gamma h
    have ha : p₀.alpha = x₀.alpha := congrArg str_002.alpha h
    have hs : p₀.beta * (1 + 1 / p₀.nu) = x₀.s := congrArg str_002.s h
    have hn := p₀.nu_pos
    have hb : p₀.beta = x₀.s * p₀.nu / (p₀.nu + 1) := by
      rw [← hs]
      field_simp
    cases p₀
    simp only [def_089] at *
    subst hg ha hb
    rfl
  · rintro ⟨n, hn, rfl⟩
    exact thm_203 x₀ n hn

theorem thm_205 (n : ℝ) (hn : 0 < n) :
    (def_089 x₀ n hn).gamma = x₀.gamma ∧ (def_089 x₀ n hn).alpha = x₀.alpha
      ∧ (def_089 x₀ n hn).beta = x₀.s * n / (n + 1)
      ∧ def_082 (def_089 x₀ n hn) = 2 * x₀.s / (n + 1) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  simp only [def_082, def_089]
  field_simp

theorem thm_206 (n : ℝ) (hn : 0 < n) :
    0 < def_082 (def_089 x₀ n hn) ∧ def_082 (def_089 x₀ n hn) < 2 * x₀.s
      ∧ n = 2 * x₀.s / def_082 (def_089 x₀ n hn) - 1
      ∧ (def_089 x₀ n hn).beta = x₀.s - def_082 (def_089 x₀ n hn) / 2 := by
  have hs := x₀.s_pos
  rw [(thm_205 x₀ n hn).2.2.2]
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ (by linarith)]
    nlinarith
  · field_simp
    ring
  · simp only [def_089]
    field_simp
    ring

theorem thm_207 (b : ℝ) (hb : 0 < b) (hb2 : b < 2 * x₀.s) :
    ∃ (n : ℝ) (hn : 0 < n), n = 2 * x₀.s / b - 1 ∧ def_082 (def_089 x₀ n hn) = b := by
  have hn : 0 < 2 * x₀.s / b - 1 := by
    rw [sub_pos, one_lt_div hb]
    exact hb2
  refine ⟨_, hn, rfl, ?_⟩
  rw [(thm_205 x₀ _ hn).2.2.2]
  have hs := x₀.s_pos.ne'
  field_simp
  ring

end S22

section S13

variable (x₀ : str_002)

theorem thm_208 (n : ℝ) (hn : 0 < n) (x₁ x₂ : str_002) :
    def_084 (def_089 x₀ n hn) x₁ - def_084 (def_089 x₀ n hn) x₂
      = (1 / (x₁.s / x₁.alpha) * (x₁.gamma - x₀.gamma) ^ 2
          - 1 / (x₂.s / x₂.alpha) * (x₂.gamma - x₀.gamma) ^ 2)
        + def_082 (def_089 x₀ n hn) * (1 / (x₁.s / x₁.alpha) - 1 / (x₂.s / x₂.alpha)) := by
  rw [thm_181, thm_181]
  simp only [def_089]
  ring

theorem thm_209 (c₀ c₁ : ℝ) (h : ¬ (c₀ = 0 ∧ c₁ = 0)) :
    {b : ℝ | c₀ + b * c₁ = 0}.Subsingleton := by
  intro b hb b' hb'
  have hb : c₀ + b * c₁ = 0 := hb
  have hb' : c₀ + b' * c₁ = 0 := hb'
  by_cases hc : c₁ = 0
  · exfalso
    apply h
    rw [hc, mul_zero, add_zero] at hb
    exact ⟨hb, hc⟩
  · have : (b - b') * c₁ = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · exact absurd h' hc

theorem thm_210 (c₀ c₁ S : ℝ) :
    (∃ b ∈ Ioo 0 S, ∃ b' ∈ Ioo 0 S, (c₀ + b * c₁) * (c₀ + b' * c₁) < 0)
      ↔ (c₁ ≠ 0 ∧ ∃ b ∈ Ioo 0 S, c₀ + b * c₁ = 0) := by
  constructor
  · rintro ⟨b, hb, b', hb', hneg⟩
    have hc : c₁ ≠ 0 := by
      intro hc
      simp only [hc, mul_zero, add_zero] at hneg
      nlinarith [sq_nonneg c₀]
    refine ⟨hc, -c₀ / c₁, ?_, by field_simp; ring⟩
    have key : (b + c₀ / c₁) * (b' + c₀ / c₁) < 0 := by
      have e : (c₀ + b * c₁) * (c₀ + b' * c₁) = c₁ ^ 2 * ((b + c₀ / c₁) * (b' + c₀ / c₁)) := by
        field_simp
        ring
      rw [e] at hneg
      have : 0 < c₁ ^ 2 := by positivity
      by_contra hk
      push Not at hk
      nlinarith
    obtain ⟨hb0, hbS⟩ := hb
    obtain ⟨hb0', hbS'⟩ := hb'
    rw [neg_div]
    rcases lt_or_ge 0 (b + c₀ / c₁) with h1 | h1
    · have h2 : b' + c₀ / c₁ < 0 := by
        by_contra h2
        push Not at h2
        nlinarith
      constructor <;> linarith
    · have h2 : 0 < b' + c₀ / c₁ := by
        by_contra h2
        push Not at h2
        nlinarith
      rcases h1.lt_or_eq with h1 | h1
      · constructor <;> linarith
      · rw [h1, zero_mul] at key
        exact absurd key (lt_irrefl 0)
  · rintro ⟨hc, b, ⟨hb0, hbS⟩, hroot⟩
    set ε := min (b / 2) ((S - b) / 2) with hε
    have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
    have hε1 : ε ≤ b / 2 := min_le_left _ _
    have hε2 : ε ≤ (S - b) / 2 := min_le_right _ _
    refine ⟨b - ε, ⟨by linarith, by linarith⟩, b + ε, ⟨by linarith, by linarith⟩, ?_⟩
    have e1 : c₀ + (b - ε) * c₁ = -(ε * c₁) := by linarith
    have e2 : c₀ + (b + ε) * c₁ = ε * c₁ := by linarith
    rw [e1, e2]
    have : 0 < (ε * c₁) ^ 2 := by
      have : ε * c₁ ≠ 0 := mul_ne_zero hε0.ne' hc
      positivity
    nlinarith

end S13

section S20

def def_090 (A : ℝ) (hA : 0 < A) : str_002 := ⟨0, A, 1, hA, one_pos⟩

def def_091 : str_002 := ⟨1, 2, 2, two_pos, two_pos⟩

def def_092 : str_002 := ⟨0, 2, 1, two_pos, one_pos⟩

theorem thm_211 (A : ℝ) (hA : 0 < A) :
    let p₁ := def_089 (def_090 A hA) 3 (by norm_num)
    let p₂ := def_089 (def_090 A hA) (1 / 3) (by norm_num)
    def_082 p₁ = 1 / 2 ∧ def_082 p₂ = 3 / 2
      ∧ def_084 p₁ def_092 < def_084 p₁ def_091 ∧ def_084 p₂ def_091 < def_084 p₂ def_092
      ∧ def_047 p₁ def_091 < def_047 p₁ def_092 ∧ def_047 p₂ def_092 < def_047 p₂ def_091 := by
  intro p₁ p₂
  have hb1 : def_082 p₁ = 1 / 2 := by
    simp only [p₁, def_082, def_089, def_090]
    norm_num
  have hb2 : def_082 p₂ = 3 / 2 := by
    simp only [p₂, def_082, def_089, def_090]
    norm_num
  have hQ1 : def_084 p₁ def_092 < def_084 p₁ def_091 := by
    simp only [def_084, hb1]
    simp only [p₁, def_089, def_090, def_091, def_092]
    norm_num
  have hQ2 : def_084 p₂ def_091 < def_084 p₂ def_092 := by
    simp only [def_084, hb2]
    simp only [p₂, def_089, def_090, def_091, def_092]
    norm_num
  exact ⟨hb1, hb2, hQ1, hQ2, (thm_197 p₁ _ _).mpr hQ1,
    (thm_197 p₂ _ _).mpr hQ2⟩

end S20

end NS1
