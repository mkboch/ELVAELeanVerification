import Mathlib
import Official.M11
import Official.M12

/-!
# Moment form of the score

For `α > 1`, `Q = α/(α−1) · ((γ−γ₀)² + b)/Var(z | y)`, where `Var(z | y)` is
the variance of the marginal law of `z` of any hierarchy with quotient state `x`. The score is not
determined by `Var(z | y)` alone: with `γ` fixed, equal predictive variances but different `α > 1`
give different scores and different allocations.
-/

noncomputable section

namespace NIGBottleneck

variable (p₀ : Parameters)

/-- For `α > 1`, `Q = α/(α−1) · ((γ−γ₀)² + b)/Var(z | y)`, for every hierarchy
`p` with quotient state `x`. -/
theorem scoreQ_moment_form (p : Parameters) (hα : 1 < p.alpha) :
    scoreQ p₀ (quotientCoordinates p)
      = p.alpha / (p.alpha - 1) * (((p.gamma - p₀.gamma) ^ 2 + bParam p₀) / totalVar p) := by
  have hs := quotientScale_pos p
  have ha : p.alpha - 1 ≠ 0 := by linarith
  rw [totalVar_eq p hα, scoreQ]
  change p.alpha * ((p.gamma - p₀.gamma) ^ 2 + bParam p₀) / quotientScale p = _
  field_simp

/-- At fixed `γ` and fixed predictive variance `V > 0`, the score is the
strictly decreasing function `α ↦ α/(α−1) · ((γ−γ₀)² + b)/V` of `α > 1`. -/
theorem scoreQ_strictAnti_alpha (γ V α α' : ℝ) (hV : 0 < V) (hα : 1 < α) (hαα : α < α') :
    α' / (α' - 1) * (((γ - p₀.gamma) ^ 2 + bParam p₀) / V)
      < α / (α - 1) * (((γ - p₀.gamma) ^ 2 + bParam p₀) / V) := by
  have hb := bParam_pos p₀
  have hk : 0 < ((γ - p₀.gamma) ^ 2 + bParam p₀) / V := by positivity
  have h : α' / (α' - 1) < α / (α - 1) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  exact mul_lt_mul_of_pos_right h hk

/-- The score, and hence the allocation, is not determined by `Var(z | y)`
alone: states `(γ, α = 2, s = V)` and `(γ, α = 3, s = 2V)` have the same predictive variance `V` but
different scores and different selected allocations. -/
theorem variance_does_not_determine_allocation (γ V : ℝ) (hV : 0 < V) :
    ∃ p p' : Parameters, p.gamma = γ ∧ p'.gamma = γ ∧ 1 < p.alpha ∧ 1 < p'.alpha
      ∧ p.alpha ≠ p'.alpha ∧ totalVar p = V ∧ totalVar p' = V
      ∧ scoreQ p₀ (quotientCoordinates p') < scoreQ p₀ (quotientCoordinates p)
      ∧ selT p₀ (quotientCoordinates p) < selT p₀ (quotientCoordinates p') := by
  -- hierarchies with quotient states `(γ, 2, V)` and `(γ, 3, 2V)` (at `t = 1`)
  let p := fiberParameters ⟨γ, 2, V, two_pos, hV⟩ ⟨1, one_pos⟩
  let p' := fiberParameters ⟨γ, 3, 2 * V, by norm_num, by positivity⟩ ⟨1, one_pos⟩
  have hV1 : totalVar p = V := by
    rw [(totalVar_fiber _ (by norm_num : (1 : ℝ) < 2) _).2]
    norm_num
  have hV2 : totalVar p' = V := by
    rw [(totalVar_fiber _ (by norm_num : (1 : ℝ) < 3) _).2]
    ring
  have hQ : scoreQ p₀ (quotientCoordinates p') < scoreQ p₀ (quotientCoordinates p) := by
    rw [scoreQ_moment_form p₀ p' (show (1 : ℝ) < 3 by norm_num),
      scoreQ_moment_form p₀ p (show (1 : ℝ) < 2 by norm_num), hV1, hV2]
    exact scoreQ_strictAnti_alpha p₀ γ V 2 3 hV (by norm_num) (by norm_num)
  refine ⟨p, p', rfl, rfl, (show (1 : ℝ) < 2 by norm_num), (show (1 : ℝ) < 3 by norm_num),
    (show (2 : ℝ) ≠ 3 by norm_num), hV1, hV2, hQ, (selT_lt_iff_score p₀ _ _).mpr hQ⟩

end NIGBottleneck
