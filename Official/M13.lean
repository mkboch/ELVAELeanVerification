import Mathlib
import Official.M12

/-!
# Complete priors with the same predictive marginal

The complete priors whose prior predictive law has quotient coordinates
`(γ₀, A, s₀)` are exactly `n > 0`, `β₀ = s₀n/(n+1)`, `b = 2s₀/(n+1)`; equivalently
`0 < b < 2s₀`, `n = 2s₀/b − 1`, `β₀ = s₀ − b/2`. Along this family the score difference of two
fixed states is the affine function `(h₁e₁ − h₂e₂) + b(h₁ − h₂)` of `b`, which changes sign at most
once unless it vanishes identically; a strict reversal occurs exactly when it has a zero with
nonzero slope in `(0, 2s₀)`; and such reversals occur.
-/

noncomputable section

namespace NIGBottleneck

open Set

section Family

variable (x₀ : QuotientState)

/-- The complete prior with calibration `n` in the family inducing the prior
predictive law with quotient coordinates `x₀ = (γ₀, A, s₀)`. -/
def priorFamily (n : ℝ) (hn : 0 < n) : Parameters where
  gamma := x₀.gamma
  nu := n
  alpha := x₀.alpha
  beta := x₀.s * n / (n + 1)
  nu_pos := hn
  alpha_pos := x₀.alpha_pos
  beta_pos := by have := x₀.s_pos; positivity

theorem quotientCoordinates_priorFamily (n : ℝ) (hn : 0 < n) :
    quotientCoordinates (priorFamily x₀ n hn) = x₀ := by
  apply QuotientState.ext
  · rfl
  · rfl
  · change x₀.s * n / (n + 1) * (1 + 1 / n) = x₀.s
    field_simp

/-- The complete priors inducing the prior predictive law `f_{x₀}` are exactly
the members of the family, parameterized by `n > 0`. -/
theorem predictiveLaw_eq_iff_priorFamily (p₀ : Parameters) :
    predictiveLaw p₀ = quotientLaw x₀ ↔ ∃ (n : ℝ) (hn : 0 < n), p₀ = priorFamily x₀ n hn := by
  rw [predictiveLaw_eq_quotientLaw, quotientLaw_injective.eq_iff]
  constructor
  · intro h
    refine ⟨p₀.nu, p₀.nu_pos, ?_⟩
    have hg : p₀.gamma = x₀.gamma := congrArg QuotientState.gamma h
    have ha : p₀.alpha = x₀.alpha := congrArg QuotientState.alpha h
    have hs : p₀.beta * (1 + 1 / p₀.nu) = x₀.s := congrArg QuotientState.s h
    have hn := p₀.nu_pos
    have hb : p₀.beta = x₀.s * p₀.nu / (p₀.nu + 1) := by
      rw [← hs]
      field_simp
    cases p₀
    simp only [priorFamily] at *
    subst hg ha hb
    rfl
  · rintro ⟨n, hn, rfl⟩
    exact quotientCoordinates_priorFamily x₀ n hn

/-- Along the family, `β₀ = s₀n/(n+1)` and `b = 2s₀/(n+1)`, and `γ₀, A, s₀`
stay fixed. -/
theorem priorFamily_coords (n : ℝ) (hn : 0 < n) :
    (priorFamily x₀ n hn).gamma = x₀.gamma ∧ (priorFamily x₀ n hn).alpha = x₀.alpha
      ∧ (priorFamily x₀ n hn).beta = x₀.s * n / (n + 1)
      ∧ bParam (priorFamily x₀ n hn) = 2 * x₀.s / (n + 1) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  simp only [bParam, priorFamily]
  field_simp

/-- Equivalently, `0 < b < 2s₀`, `n = 2s₀/b − 1` and `β₀ = s₀ − b/2`. -/
theorem priorFamily_b_form (n : ℝ) (hn : 0 < n) :
    0 < bParam (priorFamily x₀ n hn) ∧ bParam (priorFamily x₀ n hn) < 2 * x₀.s
      ∧ n = 2 * x₀.s / bParam (priorFamily x₀ n hn) - 1
      ∧ (priorFamily x₀ n hn).beta = x₀.s - bParam (priorFamily x₀ n hn) / 2 := by
  have hs := x₀.s_pos
  rw [(priorFamily_coords x₀ n hn).2.2.2]
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ (by linarith)]
    nlinarith
  · field_simp
    ring
  · simp only [priorFamily]
    field_simp
    ring

/-- Every `b ∈ (0, 2s₀)` occurs, for the calibration `n = 2s₀/b − 1`. -/
theorem priorFamily_of_b (b : ℝ) (hb : 0 < b) (hb2 : b < 2 * x₀.s) :
    ∃ (n : ℝ) (hn : 0 < n), n = 2 * x₀.s / b - 1 ∧ bParam (priorFamily x₀ n hn) = b := by
  have hn : 0 < 2 * x₀.s / b - 1 := by
    rw [sub_pos, one_lt_div hb]
    exact hb2
  refine ⟨_, hn, rfl, ?_⟩
  rw [(priorFamily_coords x₀ _ hn).2.2.2]
  have hs := x₀.s_pos.ne'
  field_simp
  ring

end Family

section Crossing

variable (x₀ : QuotientState)

/-- Along the family, `Q₁ − Q₂ = (h₁e₁ − h₂e₂) + b(h₁ − h₂)` with `h_i = 1/w_i`
and `e_i = (γ_i − γ₀)²`. -/
theorem score_difference (n : ℝ) (hn : 0 < n) (x₁ x₂ : QuotientState) :
    scoreQ (priorFamily x₀ n hn) x₁ - scoreQ (priorFamily x₀ n hn) x₂
      = (1 / (x₁.s / x₁.alpha) * (x₁.gamma - x₀.gamma) ^ 2
          - 1 / (x₂.s / x₂.alpha) * (x₂.gamma - x₀.gamma) ^ 2)
        + bParam (priorFamily x₀ n hn) * (1 / (x₁.s / x₁.alpha) - 1 / (x₂.s / x₂.alpha)) := by
  rw [scoreQ_eq_div_w, scoreQ_eq_div_w]
  simp only [priorFamily]
  ring

/-- A nonconstant affine function of `b` changes sign at most once: unless it
vanishes identically, it has at most one zero. -/
theorem affine_zero_subsingleton (c₀ c₁ : ℝ) (h : ¬ (c₀ = 0 ∧ c₁ = 0)) :
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

/-- A strict ordering reversal on `(0, 2s₀)` (a sign change of the affine
function) occurs exactly when it has a zero with nonzero slope in `(0, 2s₀)`. -/
theorem reversal_iff (c₀ c₁ S : ℝ) :
    (∃ b ∈ Ioo 0 S, ∃ b' ∈ Ioo 0 S, (c₀ + b * c₁) * (c₀ + b' * c₁) < 0)
      ↔ (c₁ ≠ 0 ∧ ∃ b ∈ Ioo 0 S, c₀ + b * c₁ = 0) := by
  constructor
  · rintro ⟨b, hb, b', hb', hneg⟩
    have hc : c₁ ≠ 0 := by
      intro hc
      simp only [hc, mul_zero, add_zero] at hneg
      nlinarith [sq_nonneg c₀]
    refine ⟨hc, -c₀ / c₁, ?_, by field_simp; ring⟩
    -- the root lies between `b` and `b'`
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

end Crossing

section Example

/-- The prior predictive quotient state `(γ₀, A, s₀) = (0, A, 1)` of the example. -/
def exampleX₀ (A : ℝ) (hA : 0 < A) : QuotientState := ⟨0, A, 1, hA, one_pos⟩

/-- The first state of the example, `α = 2`, `(γ, w) = (1, 1)`. -/
def exampleX₁ : QuotientState := ⟨1, 2, 2, two_pos, two_pos⟩

/-- The second state of the example, `α = 2`, `(γ, w) = (0, 1/2)`. -/
def exampleX₂ : QuotientState := ⟨0, 2, 1, two_pos, one_pos⟩

/-- Strict ordering reversals occur. For the prior predictive coordinates
`(0, A, 1)`, the priors with `b = 1/2` (`n = 3`) and `b = 3/2` (`n = 1/3`) order the two example
states' scores oppositely (`Q₁ = 1 + b`, `Q₂ = 2b`), and hence, by `Official.M12`, their selected
allocations oppositely. -/
theorem reversal_occurs (A : ℝ) (hA : 0 < A) :
    let p₁ := priorFamily (exampleX₀ A hA) 3 (by norm_num)
    let p₂ := priorFamily (exampleX₀ A hA) (1 / 3) (by norm_num)
    bParam p₁ = 1 / 2 ∧ bParam p₂ = 3 / 2
      ∧ scoreQ p₁ exampleX₂ < scoreQ p₁ exampleX₁ ∧ scoreQ p₂ exampleX₁ < scoreQ p₂ exampleX₂
      ∧ selT p₁ exampleX₁ < selT p₁ exampleX₂ ∧ selT p₂ exampleX₂ < selT p₂ exampleX₁ := by
  intro p₁ p₂
  have hb1 : bParam p₁ = 1 / 2 := by
    simp only [p₁, bParam, priorFamily, exampleX₀]
    norm_num
  have hb2 : bParam p₂ = 3 / 2 := by
    simp only [p₂, bParam, priorFamily, exampleX₀]
    norm_num
  have hQ1 : scoreQ p₁ exampleX₂ < scoreQ p₁ exampleX₁ := by
    simp only [scoreQ, hb1]
    simp only [p₁, priorFamily, exampleX₀, exampleX₁, exampleX₂]
    norm_num
  have hQ2 : scoreQ p₂ exampleX₁ < scoreQ p₂ exampleX₂ := by
    simp only [scoreQ, hb2]
    simp only [p₂, priorFamily, exampleX₀, exampleX₁, exampleX₂]
    norm_num
  exact ⟨hb1, hb2, hQ1, hQ2, (selT_lt_iff_score p₁ _ _).mpr hQ1,
    (selT_lt_iff_score p₂ _ _).mpr hQ2⟩

end Example

end NIGBottleneck
