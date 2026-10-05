import Mathlib
import ELVAELeanVerification.KLTheorem2
import ELVAELeanVerification.Analyticity

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# The envelope identity for the measure-theoretic KL

With `θ = (γ, α, c)` and `F(θ, ν) = D_KL(NIG(γ, ν, α, cν/(1+ν)) ‖ p₀)` (mathlib's
`klDiv`), `R_can(θ) = F(θ, ν_can(θ))`. This module proves, on the admissible domain
`ℝ × (0, ∞) × (0, ∞)` and for a valid prior (`ν₀, α₀, β₀ > 0`):

  ∇_θ R_can(θ) = ∂_θ F(θ, ν)|_{ν = ν_can(θ)},

where the partial derivative holds `ν` fixed (`envelope_identity_klDiv`); `F` is
Fréchet differentiable at `(θ, ν_can(θ))`, so both sides are genuine derivatives.

Ingredients: an abstract envelope theorem (`hasFDerivAt_envelope`); real
analyticity of `Γ`, `log Γ` and `ψ = Γ'/Γ` on `(0, ∞)`, derived here from complex
analyticity of `Γ` on `Re z > 0` (mathlib has no real version).
-/

namespace ELVAE

open Filter Topology Set ContinuousLinearMap

/-- Complex `Γ` is analytic on the right half-plane. -/
lemma analyticAt_complex_Gamma' {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ Complex.Gamma z := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticAt (s := {w : ℂ | 0 < w.re}) ?_ (hopen.mem_nhds hz)
  intro w hw
  refine (Complex.differentiableAt_Gamma w fun m hm => ?_).differentiableWithinAt
  have : (0 : ℝ) < w.re := hw
  rw [hm] at this
  simp at this
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- Real `Γ` is analytic on `(0, ∞)`. -/
lemma analyticAt_real_Gamma {x : ℝ} (hx : 0 < x) : AnalyticAt ℝ Real.Gamma x := by
  have h := (analyticAt_complex_Gamma' (z := (x : ℂ)) (by simpa using hx)).re_ofReal
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp [Complex.Gamma_ofReal]

/-- The real digamma function `ψ = Γ'/Γ` is analytic on `(0, ∞)`. -/
lemma analyticAt_logDeriv_Gamma {x : ℝ} (hx : 0 < x) :
    AnalyticAt ℝ (logDeriv Real.Gamma) x := by
  have hG := analyticAt_real_Gamma hx
  have : logDeriv Real.Gamma = fun y => deriv Real.Gamma y / Real.Gamma y := by
    funext y; rfl
  rw [this]
  exact hG.deriv.div hG (Real.Gamma_pos_of_pos hx).ne'

/-- **Abstract envelope theorem.** If `F` is differentiable at `(θ, s θ)`, `s` is
differentiable at `θ`, and the partial derivative of `F` in the second variable
vanishes there, then `θ ↦ F(θ, s θ)` has derivative `∂_θ F(θ, s θ)`. -/
theorem hasFDerivAt_envelope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E × ℝ → ℝ} {s : E → ℝ} {θ : E} {F' : E × ℝ →L[ℝ] ℝ} {s' : E →L[ℝ] ℝ}
    (hF : HasFDerivAt F F' (θ, s θ)) (hs : HasFDerivAt s s' θ)
    (hstat : F'.comp (inr ℝ E ℝ) = 0) :
    HasFDerivAt (fun x => F (x, s x)) (F'.comp (inl ℝ E ℝ)) θ := by
  have h := hF.comp θ ((hasFDerivAt_id θ).prodMk hs)
  have key : F'.comp (inl ℝ E ℝ) = F'.comp ((ContinuousLinearMap.id ℝ E).prod s') := by
    ext v
    have hv : F' (0, s' v) = 0 := by
      have := congrArg (fun L : ℝ →L[ℝ] ℝ => L (s' v)) hstat
      simpa using this
    change F' (v, 0) = F' (v, s' v)
    rw [show ((v, s' v) : E × ℝ) = (v, 0) + (0, s' v) by simp, map_add, hv, add_zero]
  rw [key]
  exact h

/-! ## The explicit fiber-restricted KL and its analyticity -/

/-- `F(θ, ν) = R̃(ν; B(θ)) + C(θ)`: the fiber-restricted KL in closed form. -/
noncomputable def fiberKLExplicit (gamma0 nu0 alpha0 beta0 : ℝ) (q : (ℝ × ℝ × ℝ) × ℝ) : ℝ :=
  fiberObjective alpha0 (BSection gamma0 nu0 beta0 q.1) q.2
    + restrictedKLConstant q.1.1 q.1.2.1 q.1.2.2 gamma0 nu0 alpha0 beta0

/-- `F` with the genuine KL divergence. -/
noncomputable def fiberKLJoint (gamma0 nu0 alpha0 beta0 : ℝ) (q : (ℝ × ℝ × ℝ) × ℝ) : ℝ :=
  fiberKL gamma0 nu0 alpha0 beta0 ⟨q.1.1, q.1.2.1, q.1.2.2⟩ q.2

variable {gamma0 nu0 alpha0 beta0 : ℝ}

lemma analyticAt_fiberKLExplicit
    {p : ℝ × ℝ × ℝ} (hp : p ∈ quotientDomain) {nu : ℝ} (hnu : 0 < nu) :
    AnalyticAt ℝ (fiberKLExplicit gamma0 nu0 alpha0 beta0) (p, nu) := by
  set X := (ℝ × ℝ × ℝ) × ℝ
  have hfst : AnalyticAt ℝ (fun q : X => q.1) (p, nu) := analyticAt_fst
  have hsnd : AnalyticAt ℝ (fun q : X => q.2) (p, nu) := analyticAt_snd
  have hg : AnalyticAt ℝ (fun q : X => q.1.1) (p, nu) := analyticAt_fst.comp hfst
  have ha : AnalyticAt ℝ (fun q : X => q.1.2.1) (p, nu) :=
    analyticAt_fst.comp (analyticAt_snd.comp hfst)
  have hc : AnalyticAt ℝ (fun q : X => q.1.2.2) (p, nu) :=
    analyticAt_snd.comp (analyticAt_snd.comp hfst)
  have hB := AnalyticAt.comp (f := fun q : X => q.1) (g := BSection gamma0 nu0 beta0)
    (BSection_analyticAt gamma0 nu0 beta0 hp.2.ne') hfst
  have hlogν := AnalyticAt.comp (f := fun q : X => q.2) (g := Real.log) (analyticAt_log hnu) hsnd
  have hlog1ν := AnalyticAt.comp (f := fun q : X => 1 + q.2) (g := Real.log)
    (analyticAt_log (show (0 : ℝ) < 1 + nu by linarith)) (analyticAt_const.add hsnd)
  have hGam := AnalyticAt.comp (f := fun q : X => q.1.2.1) (g := Real.Gamma)
    (analyticAt_real_Gamma hp.1) ha
  have hΓ := AnalyticAt.comp (f := fun q : X => Real.Gamma q.1.2.1) (g := Real.log)
    (analyticAt_log (Real.Gamma_pos_of_pos hp.1)) hGam
  have hψ := AnalyticAt.comp (f := fun q : X => q.1.2.1) (g := logDeriv Real.Gamma)
    (analyticAt_logDeriv_Gamma hp.1) ha
  have hlogc := AnalyticAt.comp (f := fun q : X => q.1.2.2) (g := Real.log)
    (analyticAt_log hp.2) hc
  have cst : ∀ a : ℝ, AnalyticAt ℝ (fun _ : X => a) (p, nu) := fun a => analyticAt_const
  have hobj := (((cst (alpha0 + 1 / 2)).mul hlogν).sub ((cst alpha0).mul hlog1ν)).add
    (hB.div hsnd hnu.ne')
  have hC := ((((((((ha.sub (cst alpha0)).mul hψ).sub hΓ).add
    (cst (Real.log (Real.Gamma alpha0)))).add
    ((cst alpha0).mul (hlogc.sub (cst (Real.log beta0))))).sub ha).sub (cst (1 / 2))).sub
    ((cst (1 / 2)).mul (cst (Real.log nu0)))).add ((ha.div hc hp.2.ne').mul
      ((cst beta0).add ((cst (nu0 / 2)).mul ((hg.sub (cst gamma0)).pow 2))))
  unfold fiberKLExplicit fiberObjective restrictedKLConstant
  exact (hobj.add hC : _)

/-- On the admissible domain the genuine KL agrees with the closed form near `(p, ν)`. -/
lemma fiberKLJoint_eventuallyEq (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0)
    {p : ℝ × ℝ × ℝ} (hp : p ∈ quotientDomain) {nu : ℝ} (hnu : 0 < nu) :
    fiberKLJoint gamma0 nu0 alpha0 beta0 =ᶠ[𝓝 (p, nu)]
      fiberKLExplicit gamma0 nu0 alpha0 beta0 := by
  have hopen : IsOpen {q : (ℝ × ℝ × ℝ) × ℝ | q.1 ∈ quotientDomain ∧ 0 < q.2} :=
    (isOpen_quotientDomain.preimage continuous_fst).inter
      (isOpen_lt continuous_const continuous_snd)
  filter_upwards [hopen.mem_nhds ⟨hp, hnu⟩] with q hq
  exact klDiv_nig_fiber_eq hnu0 halpha0 hbeta0 (θ := ⟨q.1.1, q.1.2.1, q.1.2.2⟩) hq.1 hq.2

/-! ## The envelope identity -/

/--
**Envelope identity.** For a valid prior and every admissible
`θ = (γ, α, c)`, with `F(θ, ν) = D_KL(NIG(γ, ν, α, cν/(1+ν)) ‖ p₀)`:

1. `F` is differentiable at `(θ, ν_can(θ))`, and
2. `R_can = θ ↦ F(θ, ν_can(θ))` is differentiable at `θ` with
   `∇_θ R_can(θ) = ∂_θ F(θ, ν)|_{ν=ν_can(θ)}` (partial derivative with `ν` fixed).
-/
theorem envelope_identity_klDiv (hnu0 : 0 < nu0) (halpha0 : 0 < alpha0) (hbeta0 : 0 < beta0)
    {p : ℝ × ℝ × ℝ} (hp : p ∈ quotientDomain) :
    HasFDerivAt (fiberKLJoint gamma0 nu0 alpha0 beta0)
        (fderiv ℝ (fiberKLJoint gamma0 nu0 alpha0 beta0)
          (p, nuCanSection gamma0 nu0 alpha0 beta0 p))
        (p, nuCanSection gamma0 nu0 alpha0 beta0 p)
      ∧ HasFDerivAt
          (fun x => fiberKLJoint gamma0 nu0 alpha0 beta0
            (x, nuCanSection gamma0 nu0 alpha0 beta0 x))
          ((fderiv ℝ (fiberKLJoint gamma0 nu0 alpha0 beta0)
              (p, nuCanSection gamma0 nu0 alpha0 beta0 p)).comp (inl ℝ (ℝ × ℝ × ℝ) ℝ)) p := by
  set s := nuCanSection gamma0 nu0 alpha0 beta0
  set F := fiberKLJoint gamma0 nu0 alpha0 beta0
  have hsp : 0 < s p := nuCanFromParams_positive _ _ _ _ _ _ _ hp.1 hp.2 hnu0 hbeta0
  set G := fiberKLExplicit gamma0 nu0 alpha0 beta0
  have hGan := analyticAt_fiberKLExplicit (gamma0 := gamma0) (nu0 := nu0) (alpha0 := alpha0)
    (beta0 := beta0) hp hsp
  have hEq : F =ᶠ[𝓝 (p, s p)] G := fiberKLJoint_eventuallyEq hnu0 halpha0 hbeta0 hp hsp
  have hderivEq : fderiv ℝ F (p, s p) = fderiv ℝ G (p, s p) := hEq.fderiv_eq
  have hG : HasFDerivAt G (fderiv ℝ G (p, s p)) (p, s p) :=
    hGan.differentiableAt.hasFDerivAt
  have hF : HasFDerivAt F (fderiv ℝ F (p, s p)) (p, s p) := by
    rw [hderivEq]; exact hG.congr_of_eventuallyEq hEq
  refine ⟨hF, ?_⟩
  -- stationarity in `ν`
  have hstat : (fderiv ℝ G (p, s p)).comp (inr ℝ (ℝ × ℝ × ℝ) ℝ) = 0 := by
    have h1 : HasFDerivAt (fun ν => G (p, ν)) ((fderiv ℝ G (p, s p)).comp
        (inr ℝ (ℝ × ℝ × ℝ) ℝ)) (s p) :=
      hG.comp (s p) (hasFDerivAt_prodMk_right p (s p))
    have hB : 0 < BSection gamma0 nu0 beta0 p :=
      BFromParams_positive _ _ _ _ _ _ hp.1 hp.2 hnu0 hbeta0
    have h2 : HasDerivAt (fun ν => G (p, ν))
        (stationaryDerivative alpha0 (BSection gamma0 nu0 beta0 p) (s p)) (s p) :=
      (fiberObjective_hasDerivAt alpha0 (BSection gamma0 nu0 beta0 p) (s p) hsp).add_const
        (restrictedKLConstant p.1 p.2.1 p.2.2 gamma0 nu0 alpha0 beta0)
    have hzero : stationaryDerivative alpha0 (BSection gamma0 nu0 beta0 p) (s p) = 0 :=
      (stationaryDerivative_zero_iff_nuCan alpha0 _ _ hB hsp).mpr rfl
    rw [hzero] at h2
    rw [h1.unique h2.hasFDerivAt]
    ext
    simp
  have hs : HasFDerivAt s (fderiv ℝ s p) p :=
    (nuCanSection_analyticOnNhd gamma0 nu0 alpha0 beta0 hnu0 hbeta0 p hp).differentiableAt
      |>.hasFDerivAt
  have hGenv := hasFDerivAt_envelope hG hs hstat
  rw [hderivEq]
  refine hGenv.congr_of_eventuallyEq ?_
  have hcont : ContinuousAt (fun x => (x, s x)) p :=
    continuousAt_id.prodMk hs.continuousAt
  exact (hcont.eventually hEq).mono fun x hx => hx

end ELVAE
