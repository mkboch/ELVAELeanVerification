import Mathlib
import ELVAELeanVerification.NIGKLDivergence
import ELVAELeanVerification.BoundaryLimits

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Partial minimization, the canonical selector and boundary behaviour for the measure-theoretic KL

Combining the Level-B identity `klDiv_nigMeasure` with the Level-A analysis, the
main variational statements hold for mathlib's Kullback–Leibler divergence
between NIG laws, not just for the closed-form expression:

* `klDiv_nig_fiber_eq`: on the fiber `β = cν/(1+ν)` the KL divergence equals
  `(α₀+½) log ν − α₀ log(1+ν) + B/ν + C(γ, α, c)`;
* `klDiv_nig_fiber_strict_min`: `ν_can` is the unique minimizer of the KL
  divergence along each fiber;
* `klDiv_nig_fiber_boundary`: boundary behaviour of the KL divergence on the fiber;
* `theorem2_klDiv_sInf_eq`, `theorem2_klDiv_strict_penalty`: exact partial minimization with
  `J₄ = L_rec + λ · KL(NIG(γ,ν,α,β) ‖ NIG(γ₀,ν₀,α₀,β₀))`.

Here `α₀ > 0` is required as well, so that the prior is a genuine NIG law.
-/

namespace ELVAE

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Set

/-- Real-valued KL divergence `KL(NIG(γ,ν,α,β) ‖ NIG(γ₀,ν₀,α₀,β₀))`. -/
noncomputable def nigKL (gamma nu alpha beta gamma0 nu0 alpha0 beta0 : ℝ) : ℝ :=
  (klDiv (nigMeasure gamma nu alpha beta) (nigMeasure gamma0 nu0 alpha0 beta0)).toReal

variable {gamma0 nu0 alpha0 beta0 : ℝ}

lemma nigKL_eq_closedForm {gamma nu alpha beta : ℝ}
    (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0) :
    nigKL gamma nu alpha beta gamma0 nu0 alpha0 beta0
      = nigKLClosedForm gamma nu alpha beta gamma0 nu0 alpha0 beta0 :=
  toReal_klDiv_nigMeasure hnu halpha hbeta hnu0 halpha0 hbeta0

/-- The KL divergence along the fiber of an admissible quotient state. -/
noncomputable def fiberKL (gamma0 nu0 alpha0 beta0 : ℝ) (θ : QuotientState) (nu : ℝ) : ℝ :=
  nigKL θ.gamma nu θ.alpha (θ.c * nu / (1 + nu)) gamma0 nu0 alpha0 beta0

lemma fiberKL_eq_restrictedNIGKL (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0)
    {θ : QuotientState} (hθ : θ ∈ admissibleQuotients) {nu : ℝ} (hnu : 0 < nu) :
    fiberKL gamma0 nu0 alpha0 beta0 θ nu = restrictedNIGKL gamma0 nu0 alpha0 beta0 θ nu :=
  nigKL_eq_closedForm hnu hθ.1 (beta_positive _ _ hθ.2 hnu) hnu0 halpha0 hbeta0

/--
On the fiber, the measure-theoretic KL divergence is the fiber objective plus a
`ν`-independent constant.
-/
theorem klDiv_nig_fiber_eq (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0)
    {θ : QuotientState} (hθ : θ ∈ admissibleQuotients) {nu : ℝ} (hnu : 0 < nu) :
    fiberKL gamma0 nu0 alpha0 beta0 θ nu
      = fiberObjective alpha0 (θ.B gamma0 nu0 beta0) nu
        + restrictedKLConstant θ.gamma θ.alpha θ.c gamma0 nu0 alpha0 beta0 := by
  rw [fiberKL_eq_restrictedNIGKL hnu0 halpha0 hbeta0 hθ hnu]
  exact nigKL_on_fiber _ _ _ _ _ _ _ _ hθ.2 hnu0 hnu

/-- `ν_can` is the unique minimizer of the KL divergence along each fiber. -/
theorem klDiv_nig_fiber_strict_min (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0)
    {θ : QuotientState} (hθ : θ ∈ admissibleQuotients) {nu : ℝ} (hnu : 0 < nu)
    (hne : nu ≠ θ.nuCan gamma0 nu0 alpha0 beta0) :
    fiberKL gamma0 nu0 alpha0 beta0 θ (θ.nuCan gamma0 nu0 alpha0 beta0)
      < fiberKL gamma0 nu0 alpha0 beta0 θ nu := by
  have hcan := QuotientState.nuCan_mem gamma0 nu0 alpha0 beta0 hnu0 hbeta0 θ hθ
  rw [fiberKL_eq_restrictedNIGKL hnu0 halpha0 hbeta0 hθ hcan,
    fiberKL_eq_restrictedNIGKL hnu0 halpha0 hbeta0 hθ hnu]
  exact restrictedNIGKL_strict_min gamma0 nu0 alpha0 beta0 hnu0 hbeta0 hθ hnu hne

lemma klDiv_nig_fiber_min (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0) :
    ∀ θ ∈ admissibleQuotients, ∀ nu ∈ Ioi (0 : ℝ),
      fiberKL gamma0 nu0 alpha0 beta0 θ (θ.nuCan gamma0 nu0 alpha0 beta0)
        ≤ fiberKL gamma0 nu0 alpha0 beta0 θ nu := by
  intro θ hθ nu hnu
  by_cases hne : nu = θ.nuCan gamma0 nu0 alpha0 beta0
  · rw [hne]
  · exact (klDiv_nig_fiber_strict_min hnu0 halpha0 hbeta0 hθ hnu hne).le

/-- **Boundary behaviour of the fiber KL divergence.** -/
theorem klDiv_nig_fiber_boundary (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0)
    {θ : QuotientState} (hθ : θ ∈ admissibleQuotients) :
    Tendsto (fiberKL gamma0 nu0 alpha0 beta0 θ) (𝓝[>] 0) atTop
      ∧ Tendsto (fiberKL gamma0 nu0 alpha0 beta0 θ) atTop atTop := by
  obtain ⟨h0, hinf⟩ := restrictedNIGKL_boundary gamma0 nu0 alpha0 beta0 hnu0 hbeta0 hθ
  refine ⟨h0.congr' ?_, hinf.congr' ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact (fiberKL_eq_restrictedNIGKL hnu0 halpha0 hbeta0 hθ hx).symm
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact (fiberKL_eq_restrictedNIGKL hnu0 halpha0 hbeta0 hθ hx).symm

/--
Value set of `J₄ = L_rec(γ, α, β(1+1/ν)) + λ · KL(NIG(γ,ν,α,β) ‖ NIG₀)` over the natural
NIG domain `ν, α, β > 0`.
-/
def klJ4Values (gamma0 nu0 alpha0 beta0 lam : ℝ) (L : QuotientState → ℝ) : Set ℝ :=
  {y | ∃ gamma nu alpha beta : ℝ, 0 < nu ∧ 0 < alpha ∧ 0 < beta ∧
      L ⟨gamma, alpha, beta * (1 + 1 / nu)⟩
        + lam * nigKL gamma nu alpha beta gamma0 nu0 alpha0 beta0 = y}

lemma klJ4Values_eq (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0)
    (lam : ℝ) (L : QuotientState → ℝ) :
    klJ4Values gamma0 nu0 alpha0 beta0 lam L = nigJ4Values gamma0 nu0 alpha0 beta0 lam L := by
  ext y
  constructor
  · rintro ⟨g, n, a, b, hn, ha, hb, rfl⟩
    exact ⟨g, n, a, b, hn, ha, hb, by rw [nigKL_eq_closedForm hn ha hb hnu0 halpha0 hbeta0]⟩
  · rintro ⟨g, n, a, b, hn, ha, hb, rfl⟩
    exact ⟨g, n, a, b, hn, ha, hb, by rw [nigKL_eq_closedForm hn ha hb hnu0 halpha0 hbeta0]⟩

/--
**Exact partial minimization for the measure-theoretic KL divergence.** For a valid NIG prior
(`ν₀, α₀, β₀ > 0`), any reconstruction term and `λ ≥ 0`,

  inf_{γ, ν>0, α>0, β>0} [L_rec(γ, α, β(1+1/ν)) + λ KL(NIG(γ,ν,α,β) ‖ NIG₀)]
    = inf_{γ, α>0, c>0} [L_rec(γ, α, c) + λ KL(NIG(γ, ν_can, α, cν_can/(1+ν_can)) ‖ NIG₀)].
-/
theorem theorem2_klDiv_sInf_eq (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0)
    {lam : ℝ} (hlam : 0 ≤ lam) (L : QuotientState → ℝ) :
    sInf (klJ4Values gamma0 nu0 alpha0 beta0 lam L)
      = sInf (J3Values admissibleQuotients L (fiberKL gamma0 nu0 alpha0 beta0)
          (QuotientState.nuCan gamma0 nu0 alpha0 beta0) lam) := by
  have hJ3 : J3Values admissibleQuotients L (fiberKL gamma0 nu0 alpha0 beta0)
        (QuotientState.nuCan gamma0 nu0 alpha0 beta0) lam
      = J3Values admissibleQuotients L (restrictedNIGKL gamma0 nu0 alpha0 beta0)
        (QuotientState.nuCan gamma0 nu0 alpha0 beta0) lam := by
    refine Set.image_congr fun θ hθ => ?_
    simp only [partialJ3]
    rw [fiberKL_eq_restrictedNIGKL hnu0 halpha0 hbeta0 hθ
      (QuotientState.nuCan_mem gamma0 nu0 alpha0 beta0 hnu0 hbeta0 θ hθ)]
  rw [klJ4Values_eq hnu0 halpha0 hbeta0, hJ3]
  exact theorem2_nigKL_sInf_eq gamma0 nu0 alpha0 beta0 lam L hnu0 hbeta0 hlam

/--
**Strict penalty for the measure-theoretic KL divergence.** For `λ > 0`,
every non-canonical representative of an admissible quotient state has strictly
larger objective.
-/
theorem theorem2_klDiv_strict_penalty (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0)
    (hbeta0 : 0 < beta0) {lam : ℝ} (hlam : 0 < lam) (L : QuotientState → ℝ)
    {θ : QuotientState} (hθ : θ ∈ admissibleQuotients) {nu : ℝ} (hnu : 0 < nu)
    (hne : nu ≠ θ.nuCan gamma0 nu0 alpha0 beta0) :
    partialJ3 L (fiberKL gamma0 nu0 alpha0 beta0)
        (QuotientState.nuCan gamma0 nu0 alpha0 beta0) lam θ
      < partialJ4 L (fiberKL gamma0 nu0 alpha0 beta0) lam θ nu :=
  partialJ3_lt_partialJ4 L _ _ hlam
    (fun _ hν' hne' => klDiv_nig_fiber_strict_min hnu0 halpha0 hbeta0 hθ hν' hne') hnu hne

/--
**Minimizers for the measure-theoretic KL divergence.** For `λ > 0`,
`(θ, ν)` minimizes `J₄` iff `θ` minimizes `J₃` and `ν = ν_can(θ)`.
-/
theorem theorem2_klDiv_minimizer_iff (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0)
    (hbeta0 : 0 < beta0) {lam : ℝ} (hlam : 0 < lam) (L : QuotientState → ℝ)
    {θ : QuotientState} (hθ : θ ∈ admissibleQuotients) {nu : ℝ} (hnu : 0 < nu) :
    (∀ θ' ∈ admissibleQuotients, ∀ ν' ∈ Ioi (0 : ℝ),
        partialJ4 L (fiberKL gamma0 nu0 alpha0 beta0) lam θ nu
          ≤ partialJ4 L (fiberKL gamma0 nu0 alpha0 beta0) lam θ' ν')
      ↔
    (nu = θ.nuCan gamma0 nu0 alpha0 beta0
      ∧ ∀ θ' ∈ admissibleQuotients,
        partialJ3 L (fiberKL gamma0 nu0 alpha0 beta0)
            (QuotientState.nuCan gamma0 nu0 alpha0 beta0) lam θ
          ≤ partialJ3 L (fiberKL gamma0 nu0 alpha0 beta0)
            (QuotientState.nuCan gamma0 nu0 alpha0 beta0) lam θ') :=
  partial_minimization_minimizer_iff L _ _ hlam
    (QuotientState.nuCan_mem gamma0 nu0 alpha0 beta0 hnu0 hbeta0)
    (klDiv_nig_fiber_min hnu0 halpha0 hbeta0)
    (fun _ hθ' _ hν' hne => klDiv_nig_fiber_strict_min hnu0 halpha0 hbeta0 hθ' hν' hne)
    hθ hnu

end ELVAE
