import PostHoc.PaperAudit.Selector
import Official.M11
import Official.M12

/-!
# Paper audit: uncertainty allocation and ordinal transfer (Eqs. (14)–(17), Section 3.3)

Post-arXiv paper-wide verification. `u_var = E[V | y]` is B2's `uVar` (the mean of the variance
coordinate under the NIG law) and `u_epi = Var(μ | y)` is B2's `uEpi` (the variance of the mean
coordinate); both are evaluated at the selected representative.
-/

noncomputable section

open MeasureTheory ProbabilityTheory NIGBottleneck Set

namespace PaperAudit

variable (p₀ : Parameters) (q : QuotientState)

/-- The selected hierarchy `(γ, ν_can, α, β_can)` of the paper. -/
def paperSelected : Parameters :=
  paperFiberParams q (paperNuCan p₀ q) (paper_eq12_pos p₀ q)

/-- Eqs. (14)–(16): for `α > 1`, at the selected hierarchy, `u_var = E[V|y] = c/(α−1) ·
ν_can/(1+ν_can)`, `u_epi = Var(μ|y) = c/(α−1) · 1/(1+ν_can)`, `u_epi/u_var = 1/ν_can`, and `Var(z|y)
= u_var + u_epi`. -/
theorem paper_eq14_16_allocation (hα : 1 < q.alpha) :
    uVar (paperSelected p₀ q) = q.s / (q.alpha - 1) * (paperNuCan p₀ q / (1 + paperNuCan p₀ q))
      ∧ uEpi (paperSelected p₀ q) = q.s / (q.alpha - 1) * (1 / (1 + paperNuCan p₀ q))
      ∧ uEpi (paperSelected p₀ q) / uVar (paperSelected p₀ q) = 1 / paperNuCan p₀ q
      ∧ totalVar (paperSelected p₀ q) = uVar (paperSelected p₀ q) + uEpi (paperSelected p₀ q) := by
  have hν := paper_eq12_pos p₀ q
  have hs := q.s_pos
  have ha : 1 < (paperSelected p₀ q).alpha := hα
  have hv := uVar_eq (paperSelected p₀ q) ha
  have he := uEpi_eq (paperSelected p₀ q) ha
  simp only [paperSelected, paperFiberParams] at hv he ⊢
  have h1 : 1 + paperNuCan p₀ q ≠ 0 := by linarith
  have h2 : q.alpha - 1 ≠ 0 := by linarith
  have h3 : paperNuCan p₀ q ≠ 0 := hν.ne'
  refine ⟨?_, ?_, ?_, totalVar_eq_add _ ha⟩
  · rw [hv]; field_simp
  · rw [he]; field_simp
  · rw [he, hv]
    field_simp

/-- Paper Eq. (17): `ρ₀ = 2β₀/ν₀`. -/
def paperRho0 : ℝ := 2 * p₀.beta / p₀.nu

/-- Paper Eq. (17): `T = c / (α[(γ−γ₀)² + ρ₀])`. -/
def paperT : ℝ := q.s / (q.alpha * ((q.gamma - p₀.gamma) ^ 2 + paperRho0 p₀))

/-- The transfer function `g_{ν₀,α₀}(T) = T_{α₀}(ν₀(1 + 1/T))`, which depends on the prior only
through `(ν₀, α₀)`. -/
def paperG (ν₀ α₀ T : ℝ) : ℝ := TA α₀ (ν₀ * (1 + 1 / T))

theorem paperRho0_pos : 0 < paperRho0 p₀ := by
  have := p₀.beta_pos; have := p₀.nu_pos; unfold paperRho0; positivity

theorem paperT_pos : 0 < paperT p₀ q := by
  have := q.s_pos; have := q.alpha_pos; have := paperRho0_pos p₀
  unfold paperT; positivity

/-- `ρ₀` is B2's ordinal prior parameter `b`, and `1/T` is B2's score `Q`. -/
theorem paperT_inv_eq_score : 1 / paperT p₀ q = scoreQ p₀ q := by
  have := q.s_pos
  rw [paperT, scoreQ, paperRho0, bParam, one_div_div]

/-- Section 3.3: `1/ν_can = g_{ν₀,α₀}(T)`. -/
theorem paper_transfer_identity : 1 / paperNuCan p₀ q = paperG p₀.nu p₀.alpha (paperT p₀ q) := by
  rw [paper_eq12_nuCan, selNu_eq_inv_selT, one_div_one_div, paperG, paperT_inv_eq_score,
    (selT_eq_tOfScore p₀ q).1, tOfScore]

/-- Section 3.3: for every `ν₀ > 0` and every `α₀ ≥ 0` (in particular every admissible `α₀ > 0`),
`g_{ν₀,α₀}` is strictly increasing on `T > 0`.
-/
theorem paper_transfer_strictMono {ν₀ α₀ : ℝ} (hν₀ : 0 < ν₀) (hα₀ : 0 ≤ α₀) :
    StrictMonoOn (paperG ν₀ α₀) (Ioi 0) := by
  intro T hT T' hT' hlt
  simp only [mem_Ioi] at hT hT'
  have hd : ν₀ * (1 + 1 / T') ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi]; positivity
  have hd' : ν₀ * (1 + 1 / T) ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi]; positivity
  have hlt' : ν₀ * (1 + 1 / T') < ν₀ * (1 + 1 / T) := by
    have : 1 / T' < 1 / T := one_div_lt_one_div_of_lt hT hlt
    nlinarith
  exact TA_strictAntiOn hα₀ hd hd' hlt'

/-- Section 3.3: on the selected section the inverse allocation is a strictly increasing function of
`T`, determined by the quotient state and the prior: two states compare in `1/ν_can` exactly as they
compare in `T`. -/
theorem paper_inverse_allocation_order (q q' : QuotientState) :
    1 / paperNuCan p₀ q < 1 / paperNuCan p₀ q' ↔ paperT p₀ q < paperT p₀ q' := by
  rw [paper_transfer_identity, paper_transfer_identity]
  exact (paper_transfer_strictMono p₀.nu_pos p₀.alpha_pos.le).lt_iff_lt (paperT_pos p₀ q)
    (paperT_pos p₀ q')

end PaperAudit
