import Mathlib
import Official.M05
import Official.M07
import Official.M08
import Official.M13

/-!
# Dependence on the complete prior

The selected representative is not determined by the prior marginal law of
`z`, and neither, in general, is the reduced regularizer `R`. Along the family of complete priors
inducing a fixed prior predictive law `(γ₀, A, s₀)` (`Official.M13`): (1) at `x₀ = (γ₀, A, s₀)` the
selected point is the varying complete prior itself; (2) at every fixed state `x = (γ, α, s)`,
`R(x) ≥ nα(γ−γ₀)²/(2s)`, which diverges as `n → ∞` when `γ ≠ γ₀`, although every fixed prior gives a
finite value.
-/

noncomputable section

namespace NIGBottleneck

open Filter

section LowerBound

variable (p₀ : Parameters)

/-- The complete hierarchical divergence is at least the conditional
mean term, `K(γ,ν,α,β) ≥ nαδ²/(2β)`. -/
theorem hierarchicalKL_ge_mean_term (p : Parameters) :
    p₀.nu * p.alpha * (p.gamma - p₀.gamma) ^ 2 / (2 * p.beta) ≤ hierarchicalKL p p₀ := by
  -- compare with `p₁ = (γ₀, n, α, β)`, for which both normal terms vanish
  let p₁ : Parameters := ⟨p₀.gamma, p₀.nu, p.alpha, p.beta, p₀.nu_pos, p.alpha_pos, p.beta_pos⟩
  have h1 := hierarchicalKL_nonneg p₁ p₀
  rw [hierarchicalKL_eq_closedForm] at h1 ⊢
  have hn := p₀.nu_pos
  have hν := p.nu_pos
  have hb := p.beta_pos
  have hlog : 0 ≤ p₀.nu / p.nu - 1 - Real.log (p₀.nu / p.nu) :=
    sub_one_sub_log_nonneg (div_pos hn hν)
  have hlog' : Real.log (p.nu / p₀.nu) = -Real.log (p₀.nu / p.nu) := by
    rw [← Real.log_inv, inv_div]
  simp only [nigKLClosedForm, p₁, sub_self, div_self hn.ne', Real.log_one] at h1 ⊢
  rw [hlog']
  have e : p₀.nu * p.alpha * (p.gamma - p₀.gamma) ^ 2 / (2 * p.beta)
      = (1 / 2) * (p₀.nu * p.alpha * (p.gamma - p₀.gamma) ^ 2 / p.beta) := by
    field_simp
  rw [e]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    add_zero] at h1
  linarith

/-- `R(x) ≥ nα(γ−γ₀)²/(2s)`. -/
theorem regularizerR_ge (x : QuotientState) :
    p₀.nu * x.alpha * (x.gamma - p₀.gamma) ^ 2 / (2 * x.s) ≤ regularizerR p₀ x := by
  have h := hierarchicalKL_ge_mean_term p₀ (fiberParameters x (selTPos p₀ x))
  have ht := (selTPos p₀ x).property
  have hs := x.s_pos
  have hb : x.s / (1 + (selTPos p₀ x : ℝ)) ≤ x.s := div_le_self hs.le (by linarith)
  have hb0 : 0 < x.s / (1 + (selTPos p₀ x : ℝ)) := by positivity
  rw [regularizerR, fiberKL]
  refine le_trans ?_ h
  simp only [fiberParameters]
  apply div_le_div_of_nonneg_left (by have := p₀.nu_pos; have := x.alpha_pos; positivity)
    (by positivity) (by linarith)

end LowerBound

section Family

variable (x₀ : QuotientState)

/-- At `x₀ = (γ₀, A, s₀)` the selected point is the varying complete
prior itself. -/
theorem selected_at_x₀ (n : ℝ) (hn : 0 < n) :
    priorQuotient (priorFamily x₀ n hn) = x₀
      ∧ fiberParameters x₀ (selTPos (priorFamily x₀ n hn) x₀) = priorFamily x₀ n hn := by
  have h := quotientCoordinates_priorFamily x₀ n hn
  refine ⟨h, ?_⟩
  have := selected_priorQuotient (priorFamily x₀ n hn)
  rwa [priorQuotient, h] at this

/-- The selected representative is not determined by the prior marginal
law of `z`: the priors with `n = 1` and `n = 2` induce the same prior predictive law but have
different selected points at `x₀`. -/
theorem selected_not_determined_by_prior_law :
    predictiveLaw (priorFamily x₀ 1 one_pos) = predictiveLaw (priorFamily x₀ 2 two_pos)
      ∧ fiberParameters x₀ (selTPos (priorFamily x₀ 1 one_pos) x₀)
        ≠ fiberParameters x₀ (selTPos (priorFamily x₀ 2 two_pos) x₀) := by
  constructor
  · rw [predictiveLaw_eq_iff, quotientCoordinates_priorFamily, quotientCoordinates_priorFamily]
  · rw [(selected_at_x₀ x₀ 1 one_pos).2, (selected_at_x₀ x₀ 2 two_pos).2]
    intro h
    have := congrArg Parameters.nu h
    simp only [priorFamily] at this
    norm_num at this

/-- At a fixed state with `γ ≠ γ₀`, the reduced regularizer diverges
as `n → ∞` along the family, despite the unchanged prior predictive law. -/
theorem regularizerR_diverges (x : QuotientState) (hγ : x.gamma ≠ x₀.gamma) (K : ℝ) :
    ∃ N, ∀ (n : ℝ) (hn : 0 < n), N ≤ n → K < regularizerR (priorFamily x₀ n hn) x := by
  have hs := x.s_pos
  have hα := x.alpha_pos
  have hδ : 0 < (x.gamma - x₀.gamma) ^ 2 := by
    have : x.gamma - x₀.gamma ≠ 0 := sub_ne_zero.mpr hγ
    positivity
  set c := x.alpha * (x.gamma - x₀.gamma) ^ 2 / (2 * x.s) with hc
  have hc0 : 0 < c := by positivity
  refine ⟨(|K| + 1) / c, fun n hn hN => ?_⟩
  have h := regularizerR_ge (priorFamily x₀ n hn) x
  have e : (priorFamily x₀ n hn).nu * x.alpha * (x.gamma - (priorFamily x₀ n hn).gamma) ^ 2
      / (2 * x.s) = n * c := by
    simp only [priorFamily, hc]
    ring
  rw [e] at h
  have : |K| + 1 ≤ n * c := by rwa [div_le_iff₀ hc0] at hN
  have := le_abs_self K
  linarith

/-- Every fixed admissible prior gives a finite (real) value of `R`, yet `R`
is not a function of the prior predictive law: two priors of the family have the same prior
predictive law and different `R(x)` at any state with `γ ≠ γ₀`. -/
theorem regularizerR_not_determined_by_prior_law (x : QuotientState) (hγ : x.gamma ≠ x₀.gamma) :
    ∃ (n n' : ℝ) (hn : 0 < n) (hn' : 0 < n'),
      predictiveLaw (priorFamily x₀ n hn) = predictiveLaw (priorFamily x₀ n' hn')
        ∧ regularizerR (priorFamily x₀ n hn) x ≠ regularizerR (priorFamily x₀ n' hn') x := by
  obtain ⟨N, hN⟩ := regularizerR_diverges x₀ x hγ (regularizerR (priorFamily x₀ 1 one_pos) x)
  refine ⟨1, max N 1, one_pos, lt_of_lt_of_le one_pos (le_max_right _ _), ?_, ?_⟩
  · rw [predictiveLaw_eq_iff, quotientCoordinates_priorFamily, quotientCoordinates_priorFamily]
  · exact (hN _ _ (le_max_left _ _)).ne

end Family

end NIGBottleneck
