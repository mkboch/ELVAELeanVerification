import Mathlib
import ELVAELeanVerification.ExactPartialMinimization

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Closed-form NIG KL divergence and its fiber restriction (Level A)

For `NIG(γ, ν, α, β)`, i.e. `σ² ~ InvGamma(α, β)` and
`z | σ² ~ Normal(γ, σ²/ν)`, and the prior `NIG(γ₀, ν₀, α₀, β₀)`, the closed-form
KL divergence is

  KL = 1/2 · ν₀/ν − 1/2 + 1/2 · log(ν/ν₀)                  (conditional normal part)
     + ν₀/2 · (γ − γ₀)² · α/β                               (mean shift, E[σ⁻²] = α/β)
     + (α − α₀) ψ(α) − log Γ(α) + log Γ(α₀)
     + α₀ (log β − log β₀) + α (β₀ − β)/β.                  (inverse-gamma part)

This module takes that expression as a *mathematical definition*
(`nigKLClosedForm`); it does NOT prove that it equals the measure-theoretic
KL divergence of the two NIG laws (that is the Level-B statement, which is
not formalized here). What is proved is the exact Level-A algebra:

  KL(γ, ν, α, c ν/(1+ν)) = fiberObjective α₀ B ν + C(γ, α, c)

for `ν > 0`, with `B = BFromParams` and an explicit `C` independent of `ν`.

With this, exact partial minimization is proved for the literal closed-form KL, with the
four-coordinate infimum taken over the natural NIG domain
`γ ∈ ℝ, ν > 0, α > 0, β > 0`.

`ψ` is the real digamma function, defined here as the logarithmic derivative
of `Real.Gamma` (mathlib currently provides only `Complex.digamma`). Its value
does not affect any `ν`-dependence.
-/

namespace ELVAE

/-- Real digamma function `ψ = Γ'/Γ`. -/
noncomputable def realDigamma (x : ℝ) : ℝ :=
  logDeriv Real.Gamma x

/-- Closed-form `KL(NIG(γ,ν,α,β) ‖ NIG(γ₀,ν₀,α₀,β₀))` (as an explicit expression). -/
noncomputable def nigKLClosedForm
    (gamma nu alpha beta gamma0 nu0 alpha0 beta0 : ℝ) : ℝ :=
  (1 / 2) * (nu0 / nu) - 1 / 2 + (1 / 2) * Real.log (nu / nu0)
    + (nu0 / 2) * (gamma - gamma0) ^ 2 * (alpha / beta)
    + (alpha - alpha0) * realDigamma alpha
    - Real.log (Real.Gamma alpha) + Real.log (Real.Gamma alpha0)
    + alpha0 * (Real.log beta - Real.log beta0)
    + alpha * (beta0 - beta) / beta

/-- The `ν`-independent part `C(γ, α, c)` of the fiber-restricted KL. -/
noncomputable def restrictedKLConstant
    (gamma alpha c gamma0 nu0 alpha0 beta0 : ℝ) : ℝ :=
  (alpha - alpha0) * realDigamma alpha
    - Real.log (Real.Gamma alpha) + Real.log (Real.Gamma alpha0)
    + alpha0 * (Real.log c - Real.log beta0)
    - alpha - 1 / 2 - (1 / 2) * Real.log nu0
    + (alpha / c) * (beta0 + (nu0 / 2) * (gamma - gamma0) ^ 2)

/--
**Level-A fiber reduction.** On the fiber `β = c ν/(1+ν)`, the closed-form
NIG KL equals the verified fiber objective plus a `ν`-independent constant:

  KL = (α₀ + 1/2) log ν − α₀ log(1+ν) + B/ν + C(γ, α, c).
-/
theorem nigKL_on_fiber
    (gamma alpha c gamma0 nu0 alpha0 beta0 nu : ℝ)
    (hc : 0 < c) (hnu0 : 0 < nu0) (hnu : 0 < nu) :
    nigKLClosedForm gamma nu alpha (c * nu / (1 + nu)) gamma0 nu0 alpha0 beta0
      =
    fiberObjective alpha0 (BFromParams gamma alpha c gamma0 nu0 beta0) nu
      + restrictedKLConstant gamma alpha c gamma0 nu0 alpha0 beta0 := by
  have hc0 : c ≠ 0 := hc.ne'
  have hnu0' : nu0 ≠ 0 := hnu0.ne'
  have hnu' : nu ≠ 0 := hnu.ne'
  have h1nu : 1 + nu ≠ 0 := by linarith
  have hlogbeta :
      Real.log (c * nu / (1 + nu))
        = Real.log c + Real.log nu - Real.log (1 + nu) := by
    rw [Real.log_div (mul_ne_zero hc0 hnu') h1nu, Real.log_mul hc0 hnu']
  have hlognu : Real.log (nu / nu0) = Real.log nu - Real.log nu0 :=
    Real.log_div hnu' hnu0'
  unfold nigKLClosedForm restrictedKLConstant fiberObjective BFromParams
  rw [hlogbeta, hlognu]
  field_simp
  ring

/--
Consequently the fiber-restricted closed-form KL is exactly a
`restrictedRegularizer` with constant `C = restrictedKLConstant`,
on the admissible domain.
-/
theorem nigKL_on_fiber_eq_restrictedRegularizer
    (gamma0 nu0 alpha0 beta0 : ℝ) (hnu0 : 0 < nu0)
    {θ : QuotientState} (hθ : θ ∈ admissibleQuotients) {nu : ℝ} (hnu : 0 < nu) :
    nigKLClosedForm θ.gamma nu θ.alpha (θ.c * nu / (1 + nu)) gamma0 nu0 alpha0 beta0
      =
    restrictedRegularizer gamma0 nu0 alpha0 beta0
      (fun θ' => restrictedKLConstant θ'.gamma θ'.alpha θ'.c gamma0 nu0 alpha0 beta0)
      θ nu :=
  nigKL_on_fiber _ _ _ _ _ _ _ _ hθ.2 hnu0 hnu

/-- The fiber-restricted closed-form KL as a function of `(θ, ν)`. -/
noncomputable def restrictedNIGKL
    (gamma0 nu0 alpha0 beta0 : ℝ) (θ : QuotientState) (nu : ℝ) : ℝ :=
  nigKLClosedForm θ.gamma nu θ.alpha (θ.c * nu / (1 + nu)) gamma0 nu0 alpha0 beta0

/--
The canonical representative is the unique minimizer of the fiber-restricted
closed-form KL over `ν > 0`.
-/
theorem restrictedNIGKL_strict_min
    (gamma0 nu0 alpha0 beta0 : ℝ) (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0)
    {θ : QuotientState} (hθ : θ ∈ admissibleQuotients)
    {nu : ℝ} (hnu : 0 < nu) (hne : nu ≠ θ.nuCan gamma0 nu0 alpha0 beta0) :
    restrictedNIGKL gamma0 nu0 alpha0 beta0 θ (θ.nuCan gamma0 nu0 alpha0 beta0)
      < restrictedNIGKL gamma0 nu0 alpha0 beta0 θ nu := by
  have hcan := QuotientState.nuCan_mem gamma0 nu0 alpha0 beta0 hnu0 hbeta0 θ hθ
  unfold restrictedNIGKL
  rw [nigKL_on_fiber_eq_restrictedRegularizer gamma0 nu0 alpha0 beta0 hnu0 hθ hcan,
    nigKL_on_fiber_eq_restrictedRegularizer gamma0 nu0 alpha0 beta0 hnu0 hθ hnu]
  exact restrictedRegularizer_strict_min gamma0 nu0 alpha0 beta0 _ hnu0 hbeta0 hθ hnu hne

theorem restrictedNIGKL_min
    (gamma0 nu0 alpha0 beta0 : ℝ) (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0) :
    ∀ θ ∈ admissibleQuotients, ∀ nu ∈ Set.Ioi (0 : ℝ),
      restrictedNIGKL gamma0 nu0 alpha0 beta0 θ (θ.nuCan gamma0 nu0 alpha0 beta0)
        ≤ restrictedNIGKL gamma0 nu0 alpha0 beta0 θ nu := by
  intro θ hθ nu hnu
  by_cases hne : nu = θ.nuCan gamma0 nu0 alpha0 beta0
  · rw [hne]
  · exact (restrictedNIGKL_strict_min gamma0 nu0 alpha0 beta0 hnu0 hbeta0 hθ hnu hne).le

/-! ## Exact partial minimization for the literal closed-form KL over natural NIG coordinates -/

/--
Value set of the literal four-coordinate objective

  J₄(γ, ν, α, β) = L_rec(γ, α, c) + λ · KL(NIG(γ,ν,α,β) ‖ p₀),  c = β(1 + 1/ν),

over the natural NIG domain.
-/
def nigJ4Values
    (gamma0 nu0 alpha0 beta0 lam : ℝ) (L : QuotientState → ℝ) : Set ℝ :=
  {y | ∃ gamma nu alpha beta : ℝ, 0 < nu ∧ 0 < alpha ∧ 0 < beta ∧
      L ⟨gamma, alpha, beta * (1 + 1 / nu)⟩
        + lam * nigKLClosedForm gamma nu alpha beta gamma0 nu0 alpha0 beta0 = y}

/--
Reparameterization: the literal NIG-coordinate value set equals the
`(θ, ν)` value set with the fiber-restricted KL.
-/
theorem nigJ4Values_eq_J4Values
    (gamma0 nu0 alpha0 beta0 lam : ℝ) (L : QuotientState → ℝ) :
    nigJ4Values gamma0 nu0 alpha0 beta0 lam L
      = J4Values admissibleQuotients (Set.Ioi 0) L
          (restrictedNIGKL gamma0 nu0 alpha0 beta0) lam := by
  ext y
  constructor
  · rintro ⟨gamma, nu, alpha, beta, hnu, halpha, hbeta, rfl⟩
    have hc : 0 < beta * (1 + 1 / nu) := by positivity
    refine ⟨⟨gamma, alpha, beta * (1 + 1 / nu)⟩, ⟨halpha, hc⟩, nu, hnu, ?_⟩
    have hback : beta * (1 + 1 / nu) * nu / (1 + nu) = beta := by
      have : 1 + nu ≠ 0 := by linarith
      field_simp
      ring
    simp only [partialJ4, restrictedNIGKL, hback]
  · rintro ⟨θ, hθ, nu, hnu, rfl⟩
    have hnu' : 0 < nu := hnu
    refine ⟨θ.gamma, nu, θ.alpha, θ.c * nu / (1 + nu), hnu', hθ.1,
      beta_positive θ.c nu hθ.2 hnu', ?_⟩
    rw [fiber_parameterization θ.c nu hnu']
    rfl

/--
**Literal closed-form KL, infimum equality.**

  inf_{γ, ν>0, α>0, β>0} [L_rec(γ,α,β(1+1/ν)) + λ KL(NIG(γ,ν,α,β) ‖ p₀)]
    = inf_{γ, α>0, c>0} [L_rec(γ,α,c) + λ R_can(γ,α,c)],

where `R_can(θ) = KL` at the canonical representative
`β = c ν_can/(1+ν_can)`, which is the fiber infimum.
Holds for an arbitrary reconstruction term `L_rec` and any `λ ≥ 0`.
-/
theorem theorem2_nigKL_sInf_eq
    (gamma0 nu0 alpha0 beta0 lam : ℝ) (L : QuotientState → ℝ)
    (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0) (hlam : 0 ≤ lam) :
    sInf (nigJ4Values gamma0 nu0 alpha0 beta0 lam L)
      =
    sInf (J3Values admissibleQuotients L
        (restrictedNIGKL gamma0 nu0 alpha0 beta0)
        (QuotientState.nuCan gamma0 nu0 alpha0 beta0) lam) := by
  rw [nigJ4Values_eq_J4Values]
  exact partial_minimization_sInf_eq L _ _ hlam
    (QuotientState.nuCan_mem gamma0 nu0 alpha0 beta0 hnu0 hbeta0)
    (restrictedNIGKL_min gamma0 nu0 alpha0 beta0 hnu0 hbeta0)

/--
**Literal closed-form KL, strict penalty.** For a fixed admissible
quotient state and `λ > 0`, every non-canonical NIG representative on the same
fiber has the same reconstruction term but a strictly larger objective.
-/
theorem theorem2_nigKL_strict_penalty
    (gamma0 nu0 alpha0 beta0 lam : ℝ) (L : QuotientState → ℝ)
    (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0) (hlam : 0 < lam)
    {θ : QuotientState} (hθ : θ ∈ admissibleQuotients)
    {nu : ℝ} (hnu : 0 < nu) (hne : nu ≠ θ.nuCan gamma0 nu0 alpha0 beta0) :
    partialJ3 L (restrictedNIGKL gamma0 nu0 alpha0 beta0)
        (QuotientState.nuCan gamma0 nu0 alpha0 beta0) lam θ
      < partialJ4 L (restrictedNIGKL gamma0 nu0 alpha0 beta0) lam θ nu :=
  partialJ3_lt_partialJ4 L _ _ hlam
    (fun _ hν' hne' => restrictedNIGKL_strict_min gamma0 nu0 alpha0 beta0 hnu0 hbeta0 hθ
      hν' hne') hnu hne

/-- `R_can(θ)` is the infimum of the closed-form KL over the fiber. -/
theorem Rcan_nigKL_eq_fiber_sInf
    (gamma0 nu0 alpha0 beta0 : ℝ) (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0)
    {θ : QuotientState} (hθ : θ ∈ admissibleQuotients) :
    sInf (restrictedNIGKL gamma0 nu0 alpha0 beta0 θ '' Set.Ioi 0)
      = restrictedNIGKL gamma0 nu0 alpha0 beta0 θ (θ.nuCan gamma0 nu0 alpha0 beta0) :=
  selector_eq_sInf _ _
    (QuotientState.nuCan_mem gamma0 nu0 alpha0 beta0 hnu0 hbeta0 θ hθ)
    (restrictedNIGKL_min gamma0 nu0 alpha0 beta0 hnu0 hbeta0 θ hθ)

end ELVAE
