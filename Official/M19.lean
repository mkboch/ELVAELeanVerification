import Mathlib
import Official.M02
import Official.M08
import Official.M11
import Official.M12

/-!
# Consistent changes of units versus fixed-prior rescaling

Let `κ ≠ 0`. (1) Under the consistent change of latent units
`z' = κz, μ' = κμ, X' = κ²X`, i.e. `γ' = κγ, β' = κ²β, γ₀' = κγ₀, β₀' = κ²β₀` with `ν, α, n, A`
unchanged, the quantities `Q, t_*, ν_sel, R` are invariant, while `s, w, b, u_var, u_epi, V_z` are
multiplied by `κ²`. (2) If only the state is rescaled against a fixed prior, `Q_κ` is given by the
displayed formula; there is no general invariance; for `γ₀ = 0`, `κ > 0`, `Q_κ` decreases strictly
with `κ` and `t_*` increases; the same holds for rescaling about the prior center; and pairwise
orderings can change under a common rescaling.
-/

noncomputable section

namespace NIGBottleneck

open Set

section Consistent

variable (κ : ℝ) (hκ : κ ≠ 0)

/-- The parameters in the new units, `γ' = κγ`, `β' = κ²β`. -/
def scaleParams (p : Parameters) : Parameters where
  gamma := κ * p.gamma
  nu := p.nu
  alpha := p.alpha
  beta := κ ^ 2 * p.beta
  nu_pos := p.nu_pos
  alpha_pos := p.alpha_pos
  beta_pos := by have := p.beta_pos; positivity

/-- The quotient state in the new units, `(κγ, α, κ²s)`. -/
def scaleState (x : QuotientState) : QuotientState where
  gamma := κ * x.gamma
  alpha := x.alpha
  s := κ ^ 2 * x.s
  alpha_pos := x.alpha_pos
  s_pos := by have := x.s_pos; positivity

include hκ

theorem quotientCoordinates_scaleParams (p : Parameters) :
    quotientCoordinates (scaleParams κ hκ p) = scaleState κ hκ (quotientCoordinates p) := by
  apply QuotientState.ext
  · rfl
  · rfl
  · change κ ^ 2 * p.beta * (1 + 1 / p.nu) = κ ^ 2 * (p.beta * (1 + 1 / p.nu))
    ring

/-- `s`, `w` and `b` are multiplied by `κ²`. -/
theorem scale_s_w_b (p₀ : Parameters) (x : QuotientState) :
    (scaleState κ hκ x).s = κ ^ 2 * x.s
      ∧ (scaleState κ hκ x).s / (scaleState κ hκ x).alpha = κ ^ 2 * (x.s / x.alpha)
      ∧ bParam (scaleParams κ hκ p₀) = κ ^ 2 * bParam p₀ := by
  refine ⟨rfl, ?_, ?_⟩
  · simp only [scaleState]
    ring
  · simp only [bParam, scaleParams]
    ring

/-- The score is invariant. -/
theorem scoreQ_scale (p₀ : Parameters) (x : QuotientState) :
    scoreQ (scaleParams κ hκ p₀) (scaleState κ hκ x) = scoreQ p₀ x := by
  have hk : κ ^ 2 ≠ 0 := pow_ne_zero 2 hκ
  have := x.s_pos
  simp only [scoreQ, scaleState, scaleParams, bParam]
  field_simp

/-- `t_*` and `ν_sel` are invariant. -/
theorem selT_selNu_scale (p₀ : Parameters) (x : QuotientState) :
    selT (scaleParams κ hκ p₀) (scaleState κ hκ x) = selT p₀ x
      ∧ selNu (scaleParams κ hκ p₀) (scaleState κ hκ x) = selNu p₀ x := by
  rw [(selT_selNu_eq_score _ _).1, (selT_selNu_eq_score _ _).2, (selT_selNu_eq_score p₀ x).1,
    (selT_selNu_eq_score p₀ x).2, scoreQ_scale κ hκ]
  exact ⟨rfl, rfl⟩

theorem fiberKLFormula_scale (p₀ : Parameters) (x : QuotientState) (t : ℝ) :
    fiberKLFormula (scaleParams κ hκ p₀) (scaleState κ hκ x) t = fiberKLFormula p₀ x t := by
  have hk : κ ^ 2 ≠ 0 := pow_ne_zero 2 hκ
  have hk' : 0 < κ ^ 2 := by positivity
  have hs := x.s_pos
  have hb := p₀.beta_pos
  simp only [fiberKLFormula, priorB, scaleState, scaleParams]
  rw [show κ ^ 2 * x.s / (κ ^ 2 * p₀.beta) = x.s / p₀.beta by field_simp]
  congr 1
  field_simp

/-- The reduced regularizer `R` is invariant. -/
theorem regularizerR_scale (p₀ : Parameters) (x : QuotientState) :
    regularizerR (scaleParams κ hκ p₀) (scaleState κ hκ x) = regularizerR p₀ x := by
  rw [regularizerR, regularizerR, fiberKL_eq, fiberKL_eq]
  simp only [selTPos]
  rw [(selT_selNu_scale κ hκ p₀ x).1, fiberKLFormula_scale κ hκ]

/-- For `α > 1`, `u_var`, `u_epi` and `V_z` are multiplied by `κ²`. -/
theorem uncertainty_scale (p : Parameters) (hα : 1 < p.alpha) :
    uVar (scaleParams κ hκ p) = κ ^ 2 * uVar p
      ∧ uEpi (scaleParams κ hκ p) = κ ^ 2 * uEpi p
      ∧ totalVar (scaleParams κ hκ p) = κ ^ 2 * totalVar p := by
  have hα' : 1 < (scaleParams κ hκ p).alpha := hα
  rw [uVar_eq _ hα', uVar_eq _ hα, uEpi_eq _ hα', uEpi_eq _ hα, totalVar_eq _ hα',
    totalVar_eq _ hα]
  simp only [scaleParams, quotientScale]
  refine ⟨by ring, by ring, by ring⟩

end Consistent

section FixedPrior

variable (p₀ : Parameters)

/-- The state rescaled against a fixed prior: `(κγ, α, κ²s)`. -/
def rescaleState (κ : ℝ) (hκ : κ ≠ 0) (x : QuotientState) : QuotientState := scaleState κ hκ x

/-- With the prior held fixed,
`Q_κ = α((κγ−γ₀)² + b)/(κ²s) = ((γ − γ₀/κ)² + b/κ²)/w`. -/
theorem scoreQ_rescale (κ : ℝ) (hκ : κ ≠ 0) (x : QuotientState) :
    scoreQ p₀ (rescaleState κ hκ x)
        = x.alpha * ((κ * x.gamma - p₀.gamma) ^ 2 + bParam p₀) / (κ ^ 2 * x.s)
      ∧ scoreQ p₀ (rescaleState κ hκ x)
        = ((x.gamma - p₀.gamma / κ) ^ 2 + bParam p₀ / κ ^ 2) / (x.s / x.alpha) := by
  refine ⟨rfl, ?_⟩
  have := x.s_pos
  have := x.alpha_pos
  simp only [scoreQ, rescaleState, scaleState]
  field_simp

/-- For `γ₀ = 0` and `κ > 0`, `Q_κ` decreases strictly with `κ`, so `t_*`
increases. -/
theorem rescale_monotone (hg : p₀.gamma = 0) (x : QuotientState) {κ κ' : ℝ} (hκ : 0 < κ)
    (hκκ : κ < κ') :
    scoreQ p₀ (rescaleState κ' (by linarith) x) < scoreQ p₀ (rescaleState κ hκ.ne' x)
      ∧ selT p₀ (rescaleState κ hκ.ne' x) < selT p₀ (rescaleState κ' (by linarith) x) := by
  have hb := bParam_pos p₀
  have hs := x.s_pos
  have hα := x.alpha_pos
  have hQ : scoreQ p₀ (rescaleState κ' (by linarith) x) < scoreQ p₀ (rescaleState κ hκ.ne' x) := by
    rw [(scoreQ_rescale p₀ κ' _ x).2, (scoreQ_rescale p₀ κ _ x).2, hg]
    simp only [zero_div, sub_zero]
    apply div_lt_div_of_pos_right _ (by positivity)
    have : bParam p₀ / κ' ^ 2 < bParam p₀ / κ ^ 2 :=
      div_lt_div_of_pos_left hb (by positivity) (by nlinarith)
    linarith
  exact ⟨hQ, (selT_lt_iff_score p₀ _ _).mpr hQ⟩

/-- Rescaling about the prior center: `γ' = γ₀ + κ(γ − γ₀)`, `s' = κ²s`. -/
def rescaleAboutCenter (κ : ℝ) (hκ : κ ≠ 0) (x : QuotientState) : QuotientState where
  gamma := p₀.gamma + κ * (x.gamma - p₀.gamma)
  alpha := x.alpha
  s := κ ^ 2 * x.s
  alpha_pos := x.alpha_pos
  s_pos := by have := x.s_pos; positivity

/-- The same conclusion for rescaling about the prior center:
`Q_κ = (δ² + b/κ²)/w` decreases strictly in `κ > 0`, so `t_*` increases. -/
theorem rescaleAboutCenter_monotone (x : QuotientState) {κ κ' : ℝ} (hκ : 0 < κ) (hκκ : κ < κ') :
    scoreQ p₀ (rescaleAboutCenter p₀ κ hκ.ne' x)
        = ((x.gamma - p₀.gamma) ^ 2 + bParam p₀ / κ ^ 2) / (x.s / x.alpha)
      ∧ scoreQ p₀ (rescaleAboutCenter p₀ κ' (by linarith) x)
        < scoreQ p₀ (rescaleAboutCenter p₀ κ hκ.ne' x)
      ∧ selT p₀ (rescaleAboutCenter p₀ κ hκ.ne' x)
        < selT p₀ (rescaleAboutCenter p₀ κ' (by linarith) x) := by
  have hb := bParam_pos p₀
  have hs := x.s_pos
  have hα := x.alpha_pos
  have hform : ∀ (c : ℝ) (hc : c ≠ 0), scoreQ p₀ (rescaleAboutCenter p₀ c hc x)
      = ((x.gamma - p₀.gamma) ^ 2 + bParam p₀ / c ^ 2) / (x.s / x.alpha) := by
    intro c hc
    simp only [scoreQ, rescaleAboutCenter]
    field_simp
    ring
  have hQ : scoreQ p₀ (rescaleAboutCenter p₀ κ' (by linarith) x)
      < scoreQ p₀ (rescaleAboutCenter p₀ κ hκ.ne' x) := by
    rw [hform, hform]
    apply div_lt_div_of_pos_right _ (by positivity)
    have : bParam p₀ / κ' ^ 2 < bParam p₀ / κ ^ 2 :=
      div_lt_div_of_pos_left hb (by positivity) (by nlinarith)
    linarith
  exact ⟨hform κ hκ.ne', hQ, (selT_lt_iff_score p₀ _ _).mpr hQ⟩

/-- There is no general invariance under rescaling against a fixed
prior. -/
theorem no_general_invariance (hg : p₀.gamma = 0) (x : QuotientState) :
    scoreQ p₀ (rescaleState 2 two_ne_zero x) ≠ scoreQ p₀ x := by
  have h := (rescale_monotone p₀ hg x (κ := 1) one_pos one_lt_two).1
  have e : scoreQ p₀ (rescaleState 1 one_ne_zero x) = scoreQ p₀ x := by
    simp [rescaleState, scaleState]
  rw [e] at h
  exact h.ne

/-- Pairwise orderings can change under a common rescaling of states
with the prior fixed: with `γ₀ = 0`, the states `(γ, w) = (1, 1)` and `(0, 1/2)` (with `α = 1`) have
`Q_{1,κ} = 1 + b/κ²` and `Q_{2,κ} = 2b/κ²`, which cross at `κ² = b`. -/
theorem rescale_reverses_order (hg : p₀.gamma = 0) :
    ∃ (x₁ x₂ : QuotientState) (κ κ' : ℝ) (hκ : κ ≠ 0) (hκ' : κ' ≠ 0),
      scoreQ p₀ (rescaleState κ hκ x₁) < scoreQ p₀ (rescaleState κ hκ x₂)
      ∧ scoreQ p₀ (rescaleState κ' hκ' x₂) < scoreQ p₀ (rescaleState κ' hκ' x₁)
      ∧ selT p₀ (rescaleState κ hκ x₂) < selT p₀ (rescaleState κ hκ x₁)
      ∧ selT p₀ (rescaleState κ' hκ' x₁) < selT p₀ (rescaleState κ' hκ' x₂) := by
  have hb := bParam_pos p₀
  let x₁ : QuotientState := ⟨1, 1, 1, one_pos, one_pos⟩
  let x₂ : QuotientState := ⟨0, 1, 1 / 2, one_pos, by norm_num⟩
  have hκ : Real.sqrt (bParam p₀ / 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hκ' : Real.sqrt (2 * bParam p₀) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have e1 : Real.sqrt (bParam p₀ / 2) ^ 2 = bParam p₀ / 2 := Real.sq_sqrt (by positivity)
  have e2 : Real.sqrt (2 * bParam p₀) ^ 2 = 2 * bParam p₀ := Real.sq_sqrt (by positivity)
  have h1 : scoreQ p₀ (rescaleState _ hκ x₁) < scoreQ p₀ (rescaleState _ hκ x₂) := by
    rw [(scoreQ_rescale p₀ _ hκ x₁).1, (scoreQ_rescale p₀ _ hκ x₂).1, hg, e1]
    simp only [x₁, x₂]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (Real.sqrt (bParam p₀ / 2))]
  have h2 : scoreQ p₀ (rescaleState _ hκ' x₂) < scoreQ p₀ (rescaleState _ hκ' x₁) := by
    rw [(scoreQ_rescale p₀ _ hκ' x₁).1, (scoreQ_rescale p₀ _ hκ' x₂).1, hg, e2]
    simp only [x₁, x₂]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (Real.sqrt (2 * bParam p₀))]
  exact ⟨x₁, x₂, _, _, hκ, hκ', h1, h2, (selT_lt_iff_score p₀ _ _).mpr h1,
    (selT_lt_iff_score p₀ _ _).mpr h2⟩

end FixedPrior

end NIGBottleneck
