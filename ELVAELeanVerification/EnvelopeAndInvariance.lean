import Mathlib
import ELVAELeanVerification.GeometricTransfer
import ELVAELeanVerification.SelectorSensitivity

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Envelope identity and scale/translation covariance

**Envelope identity.** Let `R̃_can(B) = R̃(ν_can(B); B)` be the minimized fiber
objective, where `R̃(ν; B) = (α₀ + 1/2) log ν − α₀ log(1+ν) + B/ν`. Because
`∂R̃/∂ν = 0` at `ν_can`, only the explicit `B`-dependence survives:

  d R̃_can / dB = ∂R̃/∂B |_{ν = ν_can} = 1/ν_can(B)      (B > 0).

Consequently the canonical regularizer is strictly increasing in `B`.

**Covariance.** Under the data rescaling/translation
`γ ↦ λγ + t`, `γ₀ ↦ λγ₀ + t`, `c ↦ λ²c`, `β₀ ↦ λ²β₀` (`λ ≠ 0`),
the scalar `B`, the selector `ν_can`, the geometric score `T` and the inverse
allocation are invariant, while `β_can ↦ λ² β_can` and `ρ₀ ↦ λ² ρ₀`.
-/

namespace ELVAE

/-- Minimized fiber objective as a function of `B`. -/
noncomputable def fiberObjectiveMin (alpha0 B : ℝ) : ℝ :=
  fiberObjective alpha0 B (nuCan alpha0 B)

/--
**Envelope identity.** For `B > 0`,

  d/dB [R̃(ν_can(B); B)] = 1/ν_can(B).
-/
theorem fiberObjectiveMin_hasDerivAt
    (alpha0 B : ℝ) (hB : 0 < B) :
    HasDerivAt (fun x : ℝ => fiberObjectiveMin alpha0 x) (1 / nuCan alpha0 B) B := by
  set s := nuCan alpha0 B with hs
  have hspos : 0 < s := nuCan_positive alpha0 B hB
  have hs' := nuCan_hasDerivAt_B alpha0 B hB
  set s' := selectorDerivative alpha0 B
  -- g(ν) = (α₀+1/2) log ν − α₀ log(1+ν)
  have hlog : HasDerivAt (fun x : ℝ => Real.log (nuCan alpha0 x)) (s' / s) B :=
    hs'.log hspos.ne'
  have hlog1 : HasDerivAt (fun x : ℝ => Real.log (1 + nuCan alpha0 x)) (s' / (1 + s)) B := by
    have h := (hs'.const_add 1).log (by linarith)
    simpa using h
  have hdiv : HasDerivAt (fun x : ℝ => x / nuCan alpha0 x)
      ((1 * s - B * s') / s ^ 2) B :=
    (hasDerivAt_id B).div hs' hspos.ne'
  have htotal := ((hlog.const_mul (alpha0 + 1 / 2)).sub (hlog1.const_mul alpha0)).add hdiv
  have hstat : stationaryDerivative alpha0 B s = 0 :=
    (stationaryDerivative_zero_iff_nuCan alpha0 B s hB hspos).mpr rfl
  unfold stationaryDerivative at hstat
  have hs0 : s ≠ 0 := hspos.ne'
  have h1s : 1 + s ≠ 0 := by linarith
  -- the coefficient of `s'` is exactly the stationarity expression
  have key : (alpha0 + 1 / 2) * (s' / s) - alpha0 * (s' / (1 + s)) + (1 * s - B * s') / s ^ 2
      = s' * ((alpha0 + 1 / 2) / s - alpha0 / (1 + s) - B / s ^ 2) + 1 / s := by
    field_simp
    ring
  rw [key, hstat, mul_zero, zero_add] at htotal
  convert htotal using 1
  funext x
  simp [fiberObjectiveMin, fiberObjective]

/-- The minimized regularizer is strictly increasing in `B` on `B > 0`. -/
theorem fiberObjectiveMin_strictMonoOn
    (alpha0 : ℝ) :
    StrictMonoOn (fun x : ℝ => fiberObjectiveMin alpha0 x) (Set.Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · intro x hx
    exact (fiberObjectiveMin_hasDerivAt alpha0 x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(fiberObjectiveMin_hasDerivAt alpha0 x hx).deriv]
    exact one_div_pos.mpr (nuCan_positive alpha0 x hx)

/-! ## Scale and translation covariance -/

/-- `B` is invariant under `γ, γ₀ ↦ λγ + t, λγ₀ + t`, `c ↦ λ²c`, `β₀ ↦ λ²β₀`. -/
theorem BFromParams_scale_translate
    (gamma alpha c gamma0 nu0 beta0 lam t : ℝ) (hlam : lam ≠ 0) (hc : c ≠ 0) :
    BFromParams (lam * gamma + t) alpha (lam ^ 2 * c) (lam * gamma0 + t) nu0 (lam ^ 2 * beta0)
      = BFromParams gamma alpha c gamma0 nu0 beta0 := by
  unfold BFromParams
  field_simp
  ring

/-- The canonical selector is invariant under the same transformation. -/
theorem nuCanFromParams_scale_translate
    (gamma alpha c gamma0 nu0 alpha0 beta0 lam t : ℝ) (hlam : lam ≠ 0) (hc : c ≠ 0) :
    nuCanFromParams (lam * gamma + t) alpha (lam ^ 2 * c) (lam * gamma0 + t) nu0 alpha0
        (lam ^ 2 * beta0)
      = nuCanFromParams gamma alpha c gamma0 nu0 alpha0 beta0 := by
  unfold nuCanFromParams
  rw [BFromParams_scale_translate gamma alpha c gamma0 nu0 beta0 lam t hlam hc]

/-- The canonical `β` scales as `λ²`. -/
theorem betaCanFromParams_scale_translate
    (gamma alpha c gamma0 nu0 alpha0 beta0 lam t : ℝ) (hlam : lam ≠ 0) (hc : c ≠ 0) :
    betaCanFromParams (lam * gamma + t) alpha (lam ^ 2 * c) (lam * gamma0 + t) nu0 alpha0
        (lam ^ 2 * beta0)
      = lam ^ 2 * betaCanFromParams gamma alpha c gamma0 nu0 alpha0 beta0 := by
  unfold betaCanFromParams
  rw [nuCanFromParams_scale_translate gamma alpha c gamma0 nu0 alpha0 beta0 lam t hlam hc]
  ring

/-- The prior radius scales as `λ²`. -/
theorem rho0FromPrior_scale (nu0 beta0 lam : ℝ) :
    rho0FromPrior nu0 (lam ^ 2 * beta0) = lam ^ 2 * rho0FromPrior nu0 beta0 := by
  unfold rho0FromPrior
  ring

/-- The geometric score `T` is invariant. -/
theorem TFromParams_scale_translate
    (gamma alpha c gamma0 nu0 beta0 lam t : ℝ) (hlam : lam ≠ 0) :
    TFromParams (lam * gamma + t) alpha (lam ^ 2 * c) (lam * gamma0 + t) nu0 (lam ^ 2 * beta0)
      = TFromParams gamma alpha c gamma0 nu0 beta0 := by
  unfold TFromParams
  rw [rho0FromPrior_scale]
  have hsq : (lam * gamma + t - (lam * gamma0 + t)) ^ 2 = lam ^ 2 * (gamma - gamma0) ^ 2 := by
    ring
  rw [hsq, ← mul_add, mul_left_comm, mul_div_mul_left _ _ (pow_ne_zero 2 hlam)]

end ELVAE
