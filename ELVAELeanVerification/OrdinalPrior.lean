import Mathlib
import ELVAELeanVerification.LatentVariance
import ELVAELeanVerification.M0Dependence
import ELVAELeanVerification.Analyticity

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Ordinal dependence on the prior and limiting regimes

* `ν ↦ cν/(1+ν)` is a bijection `(0, ∞) → (0, c)` with inverse
  `β ↦ β/(c − β)` (`fiber_bijection`).
* On the canonical section, `u_epi/u_var = g_{ν₀,α₀}(T)` and the
  epistemic fraction is `g/(1+g)` (`corollary1_ratio_fraction`).
* Under `β₀ = ρ₀ν₀/2`, `T` depends on the prior only through
  `(γ₀, ρ₀)` (`TFromParams_rho_form`); two complete priors with the same
  `(γ₀, ρ₀)` induce the same ordering of quotient states by `1/ν_can`
  (`corollary2_same_ordering`), while the numerical values can differ
  (`corollary2_values_can_differ`). Without a common calibration map,
  cross-dimensional ranks can reverse even with equal `(γ₀, ρ₀)`
  (`cross_dimension_rank_reversal`).
* The `ρ₀`-interpolation limits of `T`.
* Limiting regimes in `c`: `c ↓ 0 ⇒ ν_can → ∞`, `1/ν_can → 0`; `c → ∞ ⇒ 1/ν_can → M₀`.
* `1/ν₀` is the infimum of the ceiling `M₀` over `α₀ > 0`.
-/

namespace ELVAE

open Filter Topology Set

/-! ## The fiber as `(0, c)` -/

/-- For `c > 0`, every `β ∈ (0, c)` corresponds to exactly one
`ν > 0` on the fiber, namely `ν = β/(c − β)`. -/
theorem fiber_bijection {c beta : ℝ} (hβ : 0 < beta) (hβc : beta < c) :
    ∃! nu : ℝ, 0 < nu ∧ c * nu / (1 + nu) = beta := by
  have hcb : 0 < c - beta := by linarith
  refine ⟨beta / (c - beta), ⟨div_pos hβ hcb, ?_⟩, ?_⟩
  · field_simp
    ring
  · rintro nu ⟨hnu, h⟩
    have h1 : 1 + nu ≠ 0 := by linarith
    field_simp at h ⊢
    linarith

/-- The fiber map takes values in `(0, c)`. -/
theorem fiber_mem_Ioo {c nu : ℝ} (hc : 0 < c) (hnu : 0 < nu) :
    c * nu / (1 + nu) ∈ Ioo 0 c := by
  refine ⟨by positivity, ?_⟩
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-! ## Uncertainty ratio on the canonical section -/

/--
For `α > 1` and a fixed complete prior, on the canonical section
`u_epi/u_var = g_{ν₀,α₀}(T)` and `u_epi/(u_epi + u_var) = g/(1 + g)`.
-/
theorem corollary1_ratio_fraction (gamma alpha c gamma0 nu0 alpha0 beta0 : ℝ)
    (halpha : 1 < alpha) (hc : 0 < c) (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0) :
    let nu := nuCanFromParams gamma alpha c gamma0 nu0 alpha0 beta0
    let g := canonicalTransfer nu0 alpha0 (TFromParams gamma alpha c gamma0 nu0 beta0)
    uEpi c alpha nu / uVar c alpha nu = g
      ∧ uEpi c alpha nu / (uEpi c alpha nu + uVar c alpha nu) = g / (1 + g) := by
  intro nu g
  have halpha0 : 0 < alpha := by linarith
  have hnu : 0 < nu := nuCanFromParams_positive _ _ _ _ _ _ _ halpha0 hc hnu0 hbeta0
  have hg : g = 1 / nu := by
    simp only [g, nu, nuCanFromParams]
    rw [← actual_invNuCan_eq_transfer _ _ _ _ _ _ _ halpha0 hc hnu0 hbeta0, invNuCan]
  refine ⟨?_, ?_⟩
  · rw [hg]; exact variance_allocation_ratio c alpha nu hc halpha hnu
  · rw [hg, add_comm, variance_budget c alpha nu halpha hnu]
    have ha1 : alpha - 1 ≠ 0 := by linarith
    unfold uEpi
    field_simp
    ring

/-! ## Ordinal dependence on the prior -/

/-- The prior reparameterization `(γ₀, ν₀, α₀, β₀) ↔ (γ₀, ρ₀, ν₀, α₀)` is bijective
on positive parameters: `ρ₀ = 2β₀/ν₀` and `β₀ = ρ₀ν₀/2` are mutually inverse. -/
theorem prior_reparam_inverse {nu0 beta0 rho0 : ℝ} (hnu0 : 0 < nu0) :
    rho0FromPrior nu0 (rho0 * nu0 / 2) = rho0
      ∧ rho0FromPrior nu0 beta0 * nu0 / 2 = beta0 := by
  have h : nu0 ≠ 0 := hnu0.ne'
  refine ⟨?_, ?_⟩ <;> unfold rho0FromPrior <;> field_simp

/-- In the `(γ₀, ρ₀, ν₀, α₀)` coordinates, `T` depends on the prior only through
`(γ₀, ρ₀)`. -/
theorem TFromParams_rho_form (gamma alpha c gamma0 nu0 rho0 : ℝ) (hnu0 : 0 < nu0) :
    TFromParams gamma alpha c gamma0 nu0 (rho0 * nu0 / 2)
      = c / (alpha * ((gamma - gamma0) ^ 2 + rho0)) := by
  rw [TFromParams, (prior_reparam_inverse (beta0 := 0) hnu0).1]

/-- Two complete priors with equal `ρ₀` (and equal `γ₀`) assign the same `T` to every
quotient state. -/
theorem TFromParams_eq_of_same_rho (gamma alpha c gamma0 nu01 beta01 nu02 beta02 : ℝ)
    (hrho : rho0FromPrior nu01 beta01 = rho0FromPrior nu02 beta02) :
    TFromParams gamma alpha c gamma0 nu01 beta01
      = TFromParams gamma alpha c gamma0 nu02 beta02 := by
  unfold TFromParams; rw [hrho]

/--
Let two complete priors share `(γ₀, ρ₀)`, i.e.
`2β₀₁/ν₀₁ = 2β₀₂/ν₀₂`. Then for any two admissible quotient states, the ordering by
inverse canonical allocation is the same under both priors (each with its own
transfer function), even though `(ν₀, α₀)` differ.
-/
theorem corollary2_same_ordering
    (gamma1 alpha1 c1 gamma2 alpha2 c2 gamma0 nu01 alpha01 beta01 nu02 alpha02 beta02 : ℝ)
    (ha1 : 0 < alpha1) (hc1 : 0 < c1) (ha2 : 0 < alpha2) (hc2 : 0 < c2)
    (hnu01 : 0 < nu01) (halpha01 : 0 < alpha01) (hbeta01 : 0 < beta01)
    (hnu02 : 0 < nu02) (halpha02 : 0 < alpha02) (hbeta02 : 0 < beta02)
    (hrho : rho0FromPrior nu01 beta01 = rho0FromPrior nu02 beta02) :
    (invNuCan alpha01 (BFromParams gamma1 alpha1 c1 gamma0 nu01 beta01)
        < invNuCan alpha01 (BFromParams gamma2 alpha2 c2 gamma0 nu01 beta01))
      ↔
    (invNuCan alpha02 (BFromParams gamma1 alpha1 c1 gamma0 nu02 beta02)
        < invNuCan alpha02 (BFromParams gamma2 alpha2 c2 gamma0 nu02 beta02)) := by
  rw [actual_inverse_allocation_order_iff_T _ _ _ _ _ _ _ _ _ _ ha1 hc1 ha2 hc2 hnu01
      halpha01 hbeta01,
    actual_inverse_allocation_order_iff_T _ _ _ _ _ _ _ _ _ _ ha1 hc1 ha2 hc2 hnu02
      halpha02 hbeta02,
    TFromParams_eq_of_same_rho _ _ _ _ _ _ _ _ hrho,
    TFromParams_eq_of_same_rho gamma2 alpha2 c2 _ _ _ _ _ hrho]

lemma sqrt_eq_of_sq {x y : ℝ} (hy : 0 ≤ y) (h : x = y ^ 2) : Real.sqrt x = y := by
  rw [h, Real.sqrt_sq hy]

/-- `1/ν_can` for the prior `(0, 2, 3/2, 1)` at `θ = (0, 1, 1)` is `1/2`. -/
lemma witness_P1 : invNuCan (3 / 2) (BFromParams 0 1 1 0 2 1) = 1 / 2 := by
  have hB : BFromParams 0 1 1 0 2 1 = 2 := by unfold BFromParams; norm_num
  rw [hB, invNuCan, nuCan, sqrt_eq_of_sq (y := 2) (by norm_num) (by norm_num)]
  norm_num

/-- `1/ν_can` for the prior `(0, 8, 15/2, 4)` at `θ = (0, 1, 1)` is `1/4`. -/
lemma witness_P2 : invNuCan (15 / 2) (BFromParams 0 1 1 0 8 4) = 1 / 4 := by
  have hB : BFromParams 0 1 1 0 8 4 = 8 := by unfold BFromParams; norm_num
  rw [hB, invNuCan, nuCan, sqrt_eq_of_sq (y := 4) (by norm_num) (by norm_num)]
  norm_num

/-- `1/ν_can` for the prior `(0, 8, 5, 4)` at `θ = (0, 1, 2)` is `1/4`. -/
lemma witness_P3 : invNuCan 5 (BFromParams 0 1 2 0 8 4) = 1 / 4 := by
  have hB : BFromParams 0 1 2 0 8 4 = 6 := by unfold BFromParams; norm_num
  rw [hB, invNuCan, nuCan, sqrt_eq_of_sq (y := 7 / 2) (by norm_num) (by norm_num)]
  norm_num

/--
**Numerical values can differ.** There are two complete priors with the
same `(γ₀, ρ₀)` and an admissible quotient state at which `1/ν_can` differs.
-/
theorem corollary2_values_can_differ :
    ∃ gamma alpha c gamma0 nu01 alpha01 beta01 nu02 alpha02 beta02 : ℝ,
      0 < alpha ∧ 0 < c ∧ 0 < nu01 ∧ 0 < alpha01 ∧ 0 < beta01
      ∧ 0 < nu02 ∧ 0 < alpha02 ∧ 0 < beta02
      ∧ rho0FromPrior nu01 beta01 = rho0FromPrior nu02 beta02
      ∧ invNuCan alpha01 (BFromParams gamma alpha c gamma0 nu01 beta01)
        ≠ invNuCan alpha02 (BFromParams gamma alpha c gamma0 nu02 beta02) := by
  refine ⟨0, 1, 1, 0, 2, 3 / 2, 1, 8, 15 / 2, 4, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by unfold rho0FromPrior; norm_num, ?_⟩
  rw [witness_P1, witness_P2]
  norm_num

/--
**Cross-dimensional caveat.** Two latent dimensions with priors sharing `(γ₀, ρ₀)` but
with different calibration pairs `(ν₀, α₀)` can reverse ranks: `T(θ₁) < T(θ₂)` while
`1/ν_can` of dimension 1 at `θ₁` exceeds `1/ν_can` of dimension 2 at `θ₂`.
-/
theorem cross_dimension_rank_reversal :
    ∃ gamma1 alpha1 c1 gamma2 alpha2 c2 gamma0 nu01 alpha01 beta01 nu02 alpha02 beta02 : ℝ,
      0 < alpha1 ∧ 0 < c1 ∧ 0 < alpha2 ∧ 0 < c2
      ∧ 0 < nu01 ∧ 0 < alpha01 ∧ 0 < beta01 ∧ 0 < nu02 ∧ 0 < alpha02 ∧ 0 < beta02
      ∧ rho0FromPrior nu01 beta01 = rho0FromPrior nu02 beta02
      ∧ TFromParams gamma1 alpha1 c1 gamma0 nu01 beta01
        < TFromParams gamma2 alpha2 c2 gamma0 nu02 beta02
      ∧ invNuCan alpha02 (BFromParams gamma2 alpha2 c2 gamma0 nu02 beta02)
        < invNuCan alpha01 (BFromParams gamma1 alpha1 c1 gamma0 nu01 beta01) := by
  refine ⟨0, 1, 1, 0, 1, 2, 0, 2, 3 / 2, 1, 8, 5, 4, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by unfold rho0FromPrior; norm_num, by unfold TFromParams rho0FromPrior; norm_num, ?_⟩
  rw [witness_P1, witness_P3]
  norm_num

/-! ## The radius floor as an interpolation parameter -/

/-- `T` as a function of the radius floor `ρ₀`. -/
noncomputable def TOfRho (gamma alpha c gamma0 rho0 : ℝ) : ℝ :=
  c / (alpha * ((gamma - gamma0) ^ 2 + rho0))

/-- **Small-`ρ₀` endpoint.** For `γ ≠ γ₀`,
`T → c/(α(γ − γ₀)²)` as `ρ₀ ↓ 0`. -/
theorem TOfRho_tendsto_zero (gamma alpha c gamma0 : ℝ) (halpha : 0 < alpha)
    (hγ : gamma ≠ gamma0) :
    Tendsto (TOfRho gamma alpha c gamma0) (𝓝[>] 0)
      (𝓝 (c / (alpha * (gamma - gamma0) ^ 2))) := by
  have hd : 0 < (gamma - gamma0) ^ 2 := by
    have : gamma - gamma0 ≠ 0 := sub_ne_zero.mpr hγ
    positivity
  have hc : ContinuousAt (TOfRho gamma alpha c gamma0) 0 := by
    unfold TOfRho
    exact continuousAt_const.div (continuousAt_const.mul (continuousAt_const.add continuousAt_id))
      (by rw [add_zero]; exact mul_ne_zero halpha.ne' hd.ne')
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa [TOfRho] using h

/-- **Large-`ρ₀` endpoint.** `ρ₀ T → c/α` as `ρ₀ → ∞`. -/
theorem rho_mul_TOfRho_tendsto_atTop (gamma alpha c gamma0 : ℝ) (halpha : 0 < alpha) :
    Tendsto (fun rho0 => rho0 * TOfRho gamma alpha c gamma0 rho0) atTop (𝓝 (c / alpha)) := by
  set d := (gamma - gamma0) ^ 2
  have h : ∀ᶠ rho0 : ℝ in atTop,
      rho0 * TOfRho gamma alpha c gamma0 rho0 = (c / alpha) / (1 + d * rho0⁻¹) := by
    filter_upwards [eventually_gt_atTop 0] with r hr
    have hd : 0 ≤ d := sq_nonneg _
    unfold TOfRho
    field_simp
    ring
  rw [tendsto_congr' h]
  have h2 : Tendsto (fun r : ℝ => 1 + d * r⁻¹) atTop (𝓝 (1 + d * 0)) :=
    tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul d)
  simp only [mul_zero, add_zero] at h2
  convert (tendsto_const_nhds (x := c / alpha)).div h2 one_ne_zero using 1
  simp

/-- Multiplying by a common `ρ₀ > 0` does not alter the ranking. -/
theorem rank_invariant_under_pos_scale {rho0 T1 T2 : ℝ} (hrho : 0 < rho0) :
    rho0 * T1 < rho0 * T2 ↔ T1 < T2 :=
  mul_lt_mul_iff_of_pos_left hrho

/-- Small-`ρ₀` endpoint in variance form (`α > 1`, `γ ≠ γ₀`). -/
theorem small_rho_endpoint_variance_form (gamma alpha c gamma0 nu : ℝ)
    (halpha : 1 < alpha) (hc : 0 < c) (hnu : 0 < nu) (hγ : gamma ≠ gamma0) :
    c / (alpha * (gamma - gamma0) ^ 2)
      = (alpha - 1) / alpha
        * ProbabilityTheory.variance (fun z => z)
            (nigZMarginal gamma nu alpha (c * nu / (1 + nu)))
        / (gamma - gamma0) ^ 2 := by
  obtain ⟨_, _, hvar, _⟩ := nig_variance_decomposition_on_fiber gamma alpha c nu halpha hc hnu
  rw [hvar]
  have hd : (gamma - gamma0) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hγ)
  have ha1 : alpha - 1 ≠ 0 := by linarith
  have ha : alpha ≠ 0 := by linarith
  field_simp

/-! ## Limiting regimes in `c` -/

lemma nuCan_ge_two_mul (alpha0 : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    2 * (B - alpha0 - 1 / 2) ≤ nuCan alpha0 B := by
  unfold nuCan
  have h : B - alpha0 - 1 / 2 ≤ Real.sqrt ((B - alpha0 - 1 / 2) ^ 2 + 2 * B) := by
    refine le_trans (le_abs_self _) ?_
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  linarith

/-- `B` as a function of `c` for fixed `(γ, α)` and prior. -/
lemma BFromParams_tendsto_atTop_c (gamma alpha gamma0 nu0 beta0 : ℝ) (halpha : 0 < alpha)
    (hbeta0 : 0 < beta0) (hnu0 : 0 < nu0) :
    Tendsto (fun c => BFromParams gamma alpha c gamma0 nu0 beta0) (𝓝[>] 0) atTop := by
  set K := beta0 + nu0 / 2 * (gamma - gamma0) ^ 2
  have hK : 0 < K := by positivity
  have h : Tendsto (fun c : ℝ => alpha * K * c⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop (by positivity)
  refine (h.atTop_add (tendsto_const_nhds (x := nu0 / 2))).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  unfold BFromParams
  field_simp
  ring

/--
**Small-`c` regime.** For fixed `(γ, α)` and prior, as `c ↓ 0`: `ν_can → ∞` and
`1/ν_can → 0`; hence (for `α > 1`) `u_epi/u_var → 0`.
-/
theorem nuCan_tendsto_atTop_c (gamma alpha gamma0 nu0 alpha0 beta0 : ℝ) (halpha : 0 < alpha)
    (hbeta0 : 0 < beta0) (hnu0 : 0 < nu0) :
    Tendsto (fun c => nuCanFromParams gamma alpha c gamma0 nu0 alpha0 beta0) (𝓝[>] 0) atTop
      ∧ Tendsto (fun c => 1 / nuCanFromParams gamma alpha c gamma0 nu0 alpha0 beta0)
          (𝓝[>] 0) (𝓝 0) := by
  have hB := BFromParams_tendsto_atTop_c gamma alpha gamma0 nu0 beta0 halpha hbeta0 hnu0
  have hlin : Tendsto (fun c => 2 * (BFromParams gamma alpha c gamma0 nu0 beta0 - alpha0 - 1 / 2))
      (𝓝[>] 0) atTop := by
    have := (hB.atTop_add (tendsto_const_nhds (x := -alpha0 - 1 / 2))).const_mul_atTop two_pos
    refine this.congr' (Eventually.of_forall fun c => ?_)
    ring
  have hnu : Tendsto (fun c => nuCanFromParams gamma alpha c gamma0 nu0 alpha0 beta0)
      (𝓝[>] 0) atTop := by
    refine tendsto_atTop_mono' _ ?_ hlin
    filter_upwards [self_mem_nhdsWithin] with c (hc : 0 < c)
    exact nuCan_ge_two_mul alpha0
      (BFromParams_positive gamma alpha c gamma0 nu0 beta0 halpha hc hnu0 hbeta0).le
  refine ⟨hnu, ?_⟩
  exact hnu.inv_tendsto_atTop.congr fun c => by simp [one_div]

/--
**Large-`c` regime.** For fixed `(γ, α)` and prior, as `c → ∞`: `B → ν₀/2` and
`1/ν_can → M₀`; together with `actual_inverse_allocation_lt_M0` the approach is from
below.
-/
theorem invNuCan_tendsto_M0_c (gamma alpha gamma0 nu0 alpha0 beta0 : ℝ) (hnu0 : 0 < nu0) :
    Tendsto (fun c => invNuCan alpha0 (BFromParams gamma alpha c gamma0 nu0 beta0))
      atTop (𝓝 (M0 nu0 alpha0)) := by
  have hB : Tendsto (fun c => BFromParams gamma alpha c gamma0 nu0 beta0) atTop
      (𝓝 (nu0 / 2)) := by
    have h : Tendsto (fun c : ℝ => nu0 / 2 + alpha * c⁻¹
        * (beta0 + nu0 / 2 * (gamma - gamma0) ^ 2)) atTop
        (𝓝 (nu0 / 2 + alpha * 0 * (beta0 + nu0 / 2 * (gamma - gamma0) ^ 2))) :=
      tendsto_const_nhds.add ((tendsto_inv_atTop_zero.const_mul alpha).mul_const _)
    simp only [mul_zero, zero_mul, add_zero] at h
    refine h.congr' (Eventually.of_forall fun c => ?_)
    unfold BFromParams
    ring
  have hhalf : 0 < nu0 / 2 := by linarith
  have hcont : ContinuousAt (fun B => invNuCan alpha0 B) (nu0 / 2) := by
    unfold invNuCan
    exact continuousAt_const.div (nuCan_analyticAt_B alpha0 hhalf).continuousAt
      (nuCan_positive alpha0 _ hhalf).ne'
  exact hcont.tendsto.comp hB

/-- The geometric score `T` tends to `0` as `c ↓ 0` and to `∞` as `c → ∞`. -/
theorem TFromParams_limits_c (gamma alpha gamma0 nu0 beta0 : ℝ) (halpha : 0 < alpha)
    (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0) :
    Tendsto (fun c => TFromParams gamma alpha c gamma0 nu0 beta0) (𝓝[>] 0) (𝓝 0)
      ∧ Tendsto (fun c => TFromParams gamma alpha c gamma0 nu0 beta0) atTop atTop := by
  set D := alpha * ((gamma - gamma0) ^ 2 + rho0FromPrior nu0 beta0)
  have hD : 0 < D := by
    have := rho0FromPrior_positive nu0 beta0 hnu0 hbeta0
    positivity
  have hT : (fun c => TFromParams gamma alpha c gamma0 nu0 beta0) = fun c => c / D := rfl
  rw [hT]
  refine ⟨?_, tendsto_id.atTop_div_const hD⟩
  have h := ((continuous_id.div_const D).tendsto 0).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa using h

/-! ## `1/ν₀` is the infimum of the ceiling -/

/-- For fixed `ν₀ > 0`, `1/ν₀` is the greatest lower bound of
`{M₀(ν₀, α₀) : α₀ > 0}` and is not attained. -/
theorem M0_isGLB_alpha0 (nu0 : ℝ) (hnu0 : 0 < nu0) :
    IsGLB ((fun a => M0 nu0 a) '' Ioi 0) (1 / nu0)
      ∧ 1 / nu0 ∉ (fun a => M0 nu0 a) '' Ioi 0 := by
  have hmono := M0_strictMono_alpha0 nu0 hnu0
  have h0 : M0 nu0 0 = 1 / nu0 := by
    rw [M0_eq_closedForm nu0 0 hnu0, M0ClosedForm_at_zero nu0 hnu0]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨a, (ha : 0 < a), rfl⟩
    rw [← h0]
    exact (hmono ha).le
  · intro b hb
    have hlim := M0_tendsto_alpha0_zero nu0 hnu0
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
    exact hb ⟨a, ha, rfl⟩
  · rintro ⟨a, (ha : 0 < a), hEq⟩
    have := hmono ha
    simp only at this hEq
    rw [h0, ← hEq] at this
    exact lt_irrefl _ this

end ELVAE
