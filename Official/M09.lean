import Mathlib
import Official.M08

/-!
# Analytic regularizer, envelope derivatives, and stationarity

The regularizer `R` is real analytic on `Q`; in coordinates `(γ, α, s)` its
partial derivatives are `R_γ = nαδ(1+t_*)/s`, `R_α = (α−A)ψ₁(α) − 1 + B(1+t_*)/s`,
`R_s = A/s − αB(1+t_*)/s²`; `DR(x) = D_xF(x, t_*(x))` with the fiber coordinate held fixed; every
interior local minimizer of `J₃ = ℓ + λR` with differentiable `ℓ` satisfies `Dℓ + λ DR = 0`; and the
`λ`-independence of the fiber minimizer does not imply `λ`-independence of the optimal quotient
state.
-/

noncomputable section

namespace NIGBottleneck

open Filter Topology Set ContinuousLinearMap

section GammaFunctions

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

lemma hasDerivAt_logGamma {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun b => Real.log (Real.Gamma b)) (deriv Real.Gamma a / Real.Gamma a) a := by
  have hG := (analyticAt_real_Gamma ha).differentiableAt.hasDerivAt
  exact hG.log (Real.Gamma_pos_of_pos ha).ne'

/-- On `(0, ∞)` the model's digamma function is `Γ'/Γ`. -/
lemma digamma_eq {a : ℝ} (ha : 0 < a) : digamma a = deriv Real.Gamma a / Real.Gamma a :=
  (hasDerivAt_logGamma ha).deriv

/-- `d/da log Γ(a) = ψ(a)` for `a > 0`. -/
lemma hasDerivAt_logGamma' {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun b => Real.log (Real.Gamma b)) (digamma a) a := by
  rw [digamma_eq ha]
  exact hasDerivAt_logGamma ha

/-- `ψ` is real analytic on `(0, ∞)`. -/
lemma analyticAt_digamma {a : ℝ} (ha : 0 < a) : AnalyticAt ℝ digamma a := by
  have hG := analyticAt_real_Gamma ha
  have h : AnalyticAt ℝ (fun b => deriv Real.Gamma b / Real.Gamma b) a :=
    hG.deriv.div hG (Real.Gamma_pos_of_pos ha).ne'
  refine h.congr ?_
  filter_upwards [Ioi_mem_nhds ha] with b hb
  exact (digamma_eq hb).symm

/-- The trigamma function `ψ₁ = ψ'`. -/
def trigamma (a : ℝ) : ℝ := deriv digamma a

lemma hasDerivAt_digamma {a : ℝ} (ha : 0 < a) : HasDerivAt digamma (trigamma a) a :=
  (analyticAt_digamma ha).differentiableAt.hasDerivAt

end GammaFunctions

section Coordinates

variable (p₀ : Parameters)

/-- Quotient coordinates `(γ, α, s)`. -/
abbrev QCoord : Type := ℝ × ℝ × ℝ

/-- The domain `Q = ℝ × (0,∞) × (0,∞)` in coordinates. -/
def qDomain : Set QCoord := {x | 0 < x.2.1 ∧ 0 < x.2.2}

theorem isOpen_qDomain : IsOpen qDomain :=
  (isOpen_lt continuous_const (by fun_prop : Continuous fun x : QCoord => x.2.1)).inter
    (isOpen_lt continuous_const (by fun_prop : Continuous fun x : QCoord => x.2.2))

/-- `B` in coordinates. -/
def BCoord (x : QCoord) : ℝ := p₀.beta + p₀.nu / 2 * (x.1 - p₀.gamma) ^ 2

/-- `F(x, t)` in coordinates (the fiber formula of `Official.M05`). -/
def FCoord (x : QCoord) (t : ℝ) : ℝ :=
  p₀.alpha * Real.log (x.2.2 / p₀.beta) + (Real.log (Real.Gamma p₀.alpha)
    - Real.log (Real.Gamma x.2.1)) + (x.2.1 - p₀.alpha) * digamma x.2.1 - x.2.1
    - p₀.alpha * Real.log (1 + t) + x.2.1 * BCoord p₀ x / x.2.2 * (1 + t)
    + (1 / 2) * (p₀.nu * t - 1 - Real.log (p₀.nu * t))

/-- `d` in coordinates. -/
def dCoord (x : QCoord) : ℝ := p₀.nu + 2 * x.2.1 * BCoord p₀ x / x.2.2

/-- `t_*` in coordinates. -/
def tStarCoord (x : QCoord) : ℝ := TA p₀.alpha (dCoord p₀ x)

/-- The regularizer `R(x) = F(x, t_*(x))` in coordinates. -/
def RCoord (x : QCoord) : ℝ := FCoord p₀ x (tStarCoord p₀ x)

theorem FCoord_eq (x : QuotientState) (t : ℝ) :
    FCoord p₀ (x.gamma, x.alpha, x.s) t = fiberKLFormula p₀ x t := by
  rw [FCoord, fiberKLFormula, BCoord, priorB,
    Real.log_div (Real.Gamma_pos_of_pos p₀.alpha_pos).ne' (Real.Gamma_pos_of_pos x.alpha_pos).ne']

theorem tStarCoord_eq (x : QuotientState) : tStarCoord p₀ (x.gamma, x.alpha, x.s) = selT p₀ x := rfl

/-- The coordinate `R` is the regularizer of `Official.M08`. -/
theorem RCoord_eq (x : QuotientState) : RCoord p₀ (x.gamma, x.alpha, x.s) = regularizerR p₀ x := by
  rw [RCoord, tStarCoord_eq, FCoord_eq, regularizerR, fiberKL_eq]
  rfl

lemma dCoord_pos {x : QCoord} (hx : x ∈ qDomain) : 0 < dCoord p₀ x := by
  have := p₀.nu_pos
  have := p₀.beta_pos
  obtain ⟨ha, hs⟩ := hx
  unfold dCoord BCoord
  positivity

lemma tStarCoord_pos {x : QCoord} (hx : x ∈ qDomain) : 0 < tStarCoord p₀ x :=
  TA_pos (dCoord_pos p₀ hx)

end Coordinates

section Analytic

variable (p₀ : Parameters)

lemma analyticAt_dCoord {x : QCoord} (hx : x ∈ qDomain) : AnalyticAt ℝ (dCoord p₀) x := by
  have hg : AnalyticAt ℝ (fun y : QCoord => y.1) x := analyticAt_fst
  have ha : AnalyticAt ℝ (fun y : QCoord => y.2.1) x := analyticAt_fst.comp analyticAt_snd
  have hs : AnalyticAt ℝ (fun y : QCoord => y.2.2) x := analyticAt_snd.comp analyticAt_snd
  have hB : AnalyticAt ℝ (BCoord p₀) x :=
    analyticAt_const.add (analyticAt_const.mul ((hg.sub analyticAt_const).pow 2))
  exact analyticAt_const.add (((analyticAt_const.mul ha).mul hB).div hs hx.2.ne')

lemma analyticAt_tStarCoord {x : QCoord} (hx : x ∈ qDomain) :
    AnalyticAt ℝ (tStarCoord p₀) x := by
  have hd := analyticAt_dCoord p₀ hx
  have hD : 0 < selDisc p₀.alpha (dCoord p₀ x) := selDisc_pos (dCoord_pos p₀ hx)
  have hdisc : AnalyticAt ℝ (fun y : QCoord => selDisc p₀.alpha (dCoord p₀ y)) x :=
    (((hd.sub analyticAt_const).sub analyticAt_const).pow 2).add (analyticAt_const.mul hd)
  have hsq := AnalyticAt.comp (g := Real.sqrt)
    (f := fun y : QCoord => selDisc p₀.alpha (dCoord p₀ y)) (analyticAt_real_sqrt hD) hdisc
  have hd0 : 2 * dCoord p₀ x ≠ 0 := by have := dCoord_pos p₀ hx; positivity
  exact (((analyticAt_const.add analyticAt_const).sub hd).add hsq).div
    (analyticAt_const.mul hd) hd0

/-- `F` is jointly real analytic in `(x, t)` for `x ∈ Q`, `t > 0`. -/
lemma analyticAt_FJoint {x : QCoord} (hx : x ∈ qDomain) {t : ℝ} (ht : 0 < t) :
    AnalyticAt ℝ (fun q : QCoord × ℝ => FCoord p₀ q.1 q.2) (x, t) := by
  set X := QCoord × ℝ
  have hfst : AnalyticAt ℝ (fun q : X => q.1) (x, t) := analyticAt_fst
  have hsnd : AnalyticAt ℝ (fun q : X => q.2) (x, t) := analyticAt_snd
  have hg : AnalyticAt ℝ (fun q : X => q.1.1) (x, t) := analyticAt_fst.comp hfst
  have ha : AnalyticAt ℝ (fun q : X => q.1.2.1) (x, t) :=
    analyticAt_fst.comp (analyticAt_snd.comp hfst)
  have hs : AnalyticAt ℝ (fun q : X => q.1.2.2) (x, t) :=
    analyticAt_snd.comp (analyticAt_snd.comp hfst)
  have hlogs := AnalyticAt.comp (g := Real.log) (f := fun q : X => q.1.2.2 / p₀.beta)
    (analyticAt_log (div_pos hx.2 p₀.beta_pos)) (hs.div analyticAt_const p₀.beta_pos.ne')
  have hGam := AnalyticAt.comp (g := Real.Gamma) (f := fun q : X => q.1.2.1)
    (analyticAt_real_Gamma hx.1) ha
  have hlogG := AnalyticAt.comp (g := Real.log) (f := fun q : X => Real.Gamma q.1.2.1)
    (analyticAt_log (Real.Gamma_pos_of_pos hx.1)) hGam
  have hpsi := AnalyticAt.comp (g := digamma) (f := fun q : X => q.1.2.1)
    (analyticAt_digamma hx.1) ha
  have hlog1 := AnalyticAt.comp (g := Real.log) (f := fun q : X => 1 + q.2)
    (analyticAt_log (by linarith : (0 : ℝ) < 1 + t)) (analyticAt_const.add hsnd)
  have hlognt := AnalyticAt.comp (g := Real.log) (f := fun q : X => p₀.nu * q.2)
    (analyticAt_log (mul_pos p₀.nu_pos ht)) (analyticAt_const.mul hsnd)
  have hB : AnalyticAt ℝ (fun q : X => BCoord p₀ q.1) (x, t) :=
    analyticAt_const.add (analyticAt_const.mul ((hg.sub analyticAt_const).pow 2))
  unfold FCoord
  exact ((((((analyticAt_const.mul hlogs).add (analyticAt_const.sub hlogG)).add
    ((ha.sub analyticAt_const).mul hpsi)).sub ha).sub (analyticAt_const.mul hlog1)).add
    (((ha.mul hB).div hs hx.2.ne').mul (analyticAt_const.add hsnd))).add
    (analyticAt_const.mul (((analyticAt_const.mul hsnd).sub analyticAt_const).sub hlognt))

/-- The regularizer `R` is real analytic on `Q`. -/
theorem RCoord_analyticOnNhd : AnalyticOnNhd ℝ (RCoord p₀) qDomain := by
  intro x hx
  have ht := analyticAt_tStarCoord p₀ hx
  have hF := analyticAt_FJoint p₀ hx (tStarCoord_pos p₀ hx)
  exact AnalyticAt.comp (g := fun q : QCoord × ℝ => FCoord p₀ q.1 q.2)
    (f := fun y : QCoord => (y, tStarCoord p₀ y)) hF (analyticAt_id.prod ht)

end Analytic

section Envelope

variable (p₀ : Parameters)

/-- Abstract envelope theorem. -/
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

/-- `∂F/∂t (x,t) = ½ (d − 2A/(1+t) − 1/t)`. -/
lemma hasDerivAt_FCoord_t (x : QCoord) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => FCoord p₀ x u)
      ((1 / 2) * (dCoord p₀ x - 2 * p₀.alpha / (1 + t) - 1 / t)) t := by
  have h1t : 1 + t ≠ 0 := by linarith
  have hn := p₀.nu_pos
  have hlog1 : HasDerivAt (fun u => Real.log (1 + u)) (1 / (1 + t)) t :=
    ((hasDerivAt_id' t).const_add 1).log h1t
  have hlognt : HasDerivAt (fun u => Real.log (p₀.nu * u)) (1 / t) t :=
    (((hasDerivAt_id' t).const_mul p₀.nu).log (mul_pos hn ht).ne').congr_deriv (by field_simp)
  have h := ((((hasDerivAt_const t (p₀.alpha * Real.log (x.2.2 / p₀.beta)
      + (Real.log (Real.Gamma p₀.alpha) - Real.log (Real.Gamma x.2.1))
      + (x.2.1 - p₀.alpha) * digamma x.2.1 - x.2.1)).sub (hlog1.const_mul p₀.alpha)).add
    (((hasDerivAt_id' t).const_add 1).const_mul (x.2.1 * BCoord p₀ x / x.2.2))).add
    ((((hasDerivAt_id' t).const_mul p₀.nu).sub_const 1).sub hlognt |>.const_mul (1 / 2)))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)).congr_deriv ?_
  · simp only [FCoord, Pi.add_apply, Pi.sub_apply]
  · rw [dCoord]
    ring

/-- At `t = t_*(x)` the partial derivative of `F` in `t` vanishes. -/
lemma hasDerivAt_FCoord_t_star {x : QCoord} (hx : x ∈ qDomain) :
    HasDerivAt (fun u => FCoord p₀ x u) 0 (tStarCoord p₀ x) := by
  have h := hasDerivAt_FCoord_t p₀ x (tStarCoord_pos p₀ hx)
  have hsel := TA_selection_eq (A := p₀.alpha) (dCoord_pos p₀ hx)
  refine h.congr_deriv ?_
  unfold tStarCoord
  linarith

/-- Envelope identity: `DR(x) = D_xF(x, t_*(x))`, where the derivative on
the right holds the fiber coordinate fixed. -/
theorem hasFDerivAt_RCoord {x : QCoord} (hx : x ∈ qDomain) :
    HasFDerivAt (RCoord p₀)
      ((fderiv ℝ (fun q : QCoord × ℝ => FCoord p₀ q.1 q.2) (x, tStarCoord p₀ x)).comp
        (inl ℝ QCoord ℝ)) x := by
  set G := fun q : QCoord × ℝ => FCoord p₀ q.1 q.2
  have hGan := analyticAt_FJoint p₀ hx (tStarCoord_pos p₀ hx)
  have hG : HasFDerivAt G (fderiv ℝ G (x, tStarCoord p₀ x)) (x, tStarCoord p₀ x) :=
    hGan.differentiableAt.hasFDerivAt
  have hs : HasFDerivAt (tStarCoord p₀) (fderiv ℝ (tStarCoord p₀) x) x :=
    (analyticAt_tStarCoord p₀ hx).differentiableAt.hasFDerivAt
  have hstat : (fderiv ℝ G (x, tStarCoord p₀ x)).comp (inr ℝ QCoord ℝ) = 0 := by
    have h1 : HasFDerivAt (fun u => G (x, u)) ((fderiv ℝ G (x, tStarCoord p₀ x)).comp
        (inr ℝ QCoord ℝ)) (tStarCoord p₀ x) :=
      hG.comp (tStarCoord p₀ x) (hasFDerivAt_prodMk_right x (tStarCoord p₀ x))
    have h2 := hasDerivAt_FCoord_t_star p₀ hx
    rw [h1.unique h2.hasFDerivAt]
    ext
    simp
  exact hasFDerivAt_envelope hG hs hstat

/-- The partial derivative of `R` in a direction `v` is the partial derivative of `F(·, t)` at
`t = t_*(x)`: if `u ↦ F(x + u v, t_*(x))` has derivative `c` at `0`, then so does
`u ↦ R(x + u v)`. -/
lemma hasDerivAt_RCoord_line {x : QCoord} (hx : x ∈ qDomain) (v : QCoord) {c : ℝ}
    (hc : HasDerivAt (fun u : ℝ => FCoord p₀ (x + u • v) (tStarCoord p₀ x)) c 0) :
    HasDerivAt (fun u : ℝ => RCoord p₀ (x + u • v)) c 0 := by
  set G := fun q : QCoord × ℝ => FCoord p₀ q.1 q.2
  have hGan := analyticAt_FJoint p₀ hx (tStarCoord_pos p₀ hx)
  have hG : HasFDerivAt G (fderiv ℝ G (x, tStarCoord p₀ x)) (x, tStarCoord p₀ x) :=
    hGan.differentiableAt.hasFDerivAt
  have hline : HasDerivAt (fun u : ℝ => x + u • v) v 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add x
    rwa [one_smul] at this
  have hR := hasFDerivAt_RCoord p₀ hx
  have hR' : HasDerivAt (fun u : ℝ => RCoord p₀ (x + u • v))
      ((fderiv ℝ G (x, tStarCoord p₀ x)) (v, 0)) 0 := by
    have := hR.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] at this
    exact this
  have hF' : HasDerivAt (fun u : ℝ => FCoord p₀ (x + u • v) (tStarCoord p₀ x))
      ((fderiv ℝ G (x, tStarCoord p₀ x)) (v, 0)) 0 := by
    have hl : HasDerivAt (fun u : ℝ => (x + u • v, tStarCoord p₀ x)) (v, (0 : ℝ)) 0 :=
      hline.prodMk (hasDerivAt_const _ _)
    have := hG.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
    exact this
  rw [hF'.unique hc] at hR'
  exact hR'

/-- `R_γ = nαδ(1+t_*)/s`. -/
theorem hasDerivAt_RCoord_gamma {x : QCoord} (hx : x ∈ qDomain) :
    HasDerivAt (fun u : ℝ => RCoord p₀ (x + u • ((1 : ℝ), (0 : ℝ), (0 : ℝ))))
      (p₀.nu * x.2.1 * (x.1 - p₀.gamma) * (1 + tStarCoord p₀ x) / x.2.2) 0 := by
  apply hasDerivAt_RCoord_line p₀ hx
  set t := tStarCoord p₀ x
  have hd : HasDerivAt (fun u : ℝ => x.1 + u - p₀.gamma) 1 0 :=
    ((hasDerivAt_id' (0 : ℝ)).const_add x.1).sub_const p₀.gamma
  have hB : HasDerivAt (fun u : ℝ => p₀.beta + p₀.nu / 2 * ((x.1 + u - p₀.gamma)
      * (x.1 + u - p₀.gamma))) (p₀.nu * (x.1 - p₀.gamma)) 0 :=
    (((hd.mul hd).const_mul (p₀.nu / 2)).const_add p₀.beta).congr_deriv (by ring)
  have h := ((((hB.const_mul (x.2.1)).div_const x.2.2).mul_const (1 + t)).const_add
    (p₀.alpha * Real.log (x.2.2 / p₀.beta) + (Real.log (Real.Gamma p₀.alpha)
      - Real.log (Real.Gamma x.2.1)) + (x.2.1 - p₀.alpha) * digamma x.2.1 - x.2.1
      - p₀.alpha * Real.log (1 + t))).add_const
    ((1 / 2) * (p₀.nu * t - 1 - Real.log (p₀.nu * t)))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)).congr_deriv ?_
  · simp only [FCoord, BCoord, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul, mul_one,
      mul_zero, add_zero]
    ring
  · ring

/-- `R_α = (α − A)ψ₁(α) − 1 + B(1+t_*)/s`. -/
theorem hasDerivAt_RCoord_alpha {x : QCoord} (hx : x ∈ qDomain) :
    HasDerivAt (fun u : ℝ => RCoord p₀ (x + u • ((0 : ℝ), (1 : ℝ), (0 : ℝ))))
      ((x.2.1 - p₀.alpha) * trigamma x.2.1 - 1
        + BCoord p₀ x * (1 + tStarCoord p₀ x) / x.2.2) 0 := by
  apply hasDerivAt_RCoord_line p₀ hx
  set t := tStarCoord p₀ x
  have hlin : HasDerivAt (fun u : ℝ => x.2.1 + u) 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add x.2.1
  have hlogG : HasDerivAt (fun u : ℝ => Real.log (Real.Gamma (x.2.1 + u))) (digamma x.2.1) 0 := by
    have := (hasDerivAt_logGamma' hx.1).comp_of_eq (0 : ℝ) hlin (by simp)
    rw [mul_one] at this
    exact this
  have hpsi : HasDerivAt (fun u : ℝ => digamma (x.2.1 + u)) (trigamma x.2.1) 0 := by
    have := (hasDerivAt_digamma hx.1).comp_of_eq (0 : ℝ) hlin (by simp)
    rw [mul_one] at this
    exact this
  have h := ((((((hasDerivAt_const (0 : ℝ) (p₀.alpha * Real.log (x.2.2 / p₀.beta)
      + Real.log (Real.Gamma p₀.alpha))).sub hlogG).add ((hlin.sub_const p₀.alpha).mul hpsi)).sub
      hlin).sub (hasDerivAt_const (0 : ℝ) (p₀.alpha * Real.log (1 + t)))).add
      ((hlin.mul_const (BCoord p₀ x / x.2.2 * (1 + t))))).add
    (hasDerivAt_const (0 : ℝ) ((1 / 2) * (p₀.nu * t - 1 - Real.log (p₀.nu * t))))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)).congr_deriv ?_
  · simp only [FCoord, BCoord, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul, mul_one,
      mul_zero, add_zero, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  · simp only [add_zero]
    ring

/-- `R_s = A/s − αB(1+t_*)/s²`. -/
theorem hasDerivAt_RCoord_s {x : QCoord} (hx : x ∈ qDomain) :
    HasDerivAt (fun u : ℝ => RCoord p₀ (x + u • ((0 : ℝ), (0 : ℝ), (1 : ℝ))))
      (p₀.alpha / x.2.2 - x.2.1 * BCoord p₀ x * (1 + tStarCoord p₀ x) / x.2.2 ^ 2) 0 := by
  apply hasDerivAt_RCoord_line p₀ hx
  set t := tStarCoord p₀ x
  have hlin : HasDerivAt (fun u : ℝ => x.2.2 + u) 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add x.2.2
  have hlogs : HasDerivAt (fun u : ℝ => Real.log ((x.2.2 + u) / p₀.beta)) (1 / x.2.2) 0 :=
    ((hlin.div_const p₀.beta).log (by simpa using (div_pos hx.2 p₀.beta_pos).ne')).congr_deriv
      (by have := p₀.beta_pos; have := hx.2; rw [add_zero]; field_simp)
  have hinv : HasDerivAt (fun u : ℝ => (x.2.1 * BCoord p₀ x) / (x.2.2 + u))
      (-(x.2.1 * BCoord p₀ x) / x.2.2 ^ 2) 0 :=
    ((hasDerivAt_const (0 : ℝ) (x.2.1 * BCoord p₀ x)).div hlin
      (by simpa using hx.2.ne')).congr_deriv (by rw [add_zero]; ring)
  have h := ((((hasDerivAt_const (0 : ℝ) (Real.log (Real.Gamma p₀.alpha)
      - Real.log (Real.Gamma x.2.1) + (x.2.1 - p₀.alpha) * digamma x.2.1 - x.2.1
      - p₀.alpha * Real.log (1 + t))).add (hlogs.const_mul p₀.alpha)).add
      (hinv.mul_const (1 + t))).add
    (hasDerivAt_const (0 : ℝ) ((1 / 2) * (p₀.nu * t - 1 - Real.log (p₀.nu * t)))))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)).congr_deriv ?_
  · simp only [FCoord, BCoord, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul, mul_one,
      mul_zero, add_zero, Pi.add_apply]
    ring
  · ring

/-- Every interior local minimizer of `J₃ = ℓ + λR` with `ℓ` differentiable
satisfies `Dℓ(x;y) + λ DR(x) = 0`. -/
theorem stationarity {ℓ : QCoord → ℝ} {ℓ' : QCoord →L[ℝ] ℝ} (w : PositiveReal) {x : QCoord}
    (hx : x ∈ qDomain) (hℓ : HasFDerivAt ℓ ℓ' x)
    (hmin : IsLocalMin (fun y => ℓ y + w.val * RCoord p₀ y) x) :
    ℓ' + w.val • fderiv ℝ (RCoord p₀) x = 0 := by
  have hR := (hasFDerivAt_RCoord p₀ hx).differentiableAt.hasFDerivAt
  have hJ : HasFDerivAt (fun y => ℓ y + w.val * RCoord p₀ y)
      (ℓ' + w.val • fderiv ℝ (RCoord p₀) x) x := hℓ.add (hR.const_mul w.val)
  exact hmin.hasFDerivAt_eq_zero hJ

end Envelope

section WeightDependence

variable (p₀ : Parameters)

open Classical in
/-- The three-level loss of the weight-dependence witness. -/
def weightWitnessLoss (x₁ : QuotientState) : ReconstructionLoss Unit :=
  fun μ _ => if μ = quotientLaw x₁ then 0 else if μ = quotientLaw (priorQuotient p₀) then 1 else 2

/-- Independence of the fiber minimizer from `λ` does not imply
independence of the optimal quotient state from `λ`: there are a finite nonnegative reconstruction
loss and two weights whose (unique) optimal quotient states differ, although the fiber minimizer is
the same for every weight. -/
theorem optimal_state_depends_on_weight :
    ∃ (L : ReconstructionLoss Unit) (w₁ w₂ : PositiveReal) (x₁ x₂ : QuotientState),
      x₁ ≠ x₂ ∧ (∀ μ, 0 ≤ L μ () ∧ L μ () ≠ ⊤) ∧
      (∀ x, x ≠ x₁ → reducedObjective L p₀ w₁ x₁ () < reducedObjective L p₀ w₁ x ()) ∧
      (∀ x, x ≠ x₂ → reducedObjective L p₀ w₂ x₂ () < reducedObjective L p₀ w₂ x ()) ∧
      (∀ w : PositiveReal, ∀ x : QuotientState, ∀ t : PositiveReal,
        (∀ t' : PositiveReal, w.val * fiberKL p₀ x t ≤ w.val * fiberKL p₀ x t') ↔
          t = selTPos p₀ x) := by
  classical
  obtain ⟨x₁, hx₁, -⟩ := exists_regularizerR_lt p₀ 1 one_pos
  set R₁ := regularizerR p₀ x₁ with hR₁
  have hR₁pos : 0 < R₁ := by
    rcases (regularizerR_nonneg p₀ x₁).lt_or_eq with h | h
    · exact h
    · exact absurd ((minimizedKL_eq_zero_iff p₀ x₁).mp h.symm) hx₁
  let w₁ : PositiveReal := ⟨1 / (2 * R₁), by positivity⟩
  let w₂ : PositiveReal := ⟨2 / R₁, by positivity⟩
  have hloss : ∀ x, quotientLoss (weightWitnessLoss p₀ x₁) x () =
      if x = x₁ then 0 else if x = priorQuotient p₀ then 1 else 2 := by
    intro x
    simp only [quotientLoss, weightWitnessLoss, quotientLaw_injective.eq_iff]
  have hR0 : regularizerR p₀ (priorQuotient p₀) = 0 := minimizedKL_priorQuotient p₀
  have hRnn := regularizerR_nonneg p₀
  refine ⟨weightWitnessLoss p₀ x₁, w₁, w₂, x₁, priorQuotient p₀, hx₁, fun μ => ?_, ?_, ?_,
    fun w x t => fiber_minimizer_independent_of_weight p₀ w x t⟩
  · unfold weightWitnessLoss
    split_ifs
    · exact ⟨le_rfl, EReal.zero_ne_top⟩
    · exact ⟨zero_le_one, ne_of_lt (EReal.coe_lt_top 1)⟩
    · exact ⟨by norm_num, ne_of_lt (EReal.coe_lt_top 2)⟩
  · intro x hx
    have hv1 : reducedObjective (weightWitnessLoss p₀ x₁) p₀ w₁ x₁ () = ((1 / 2 : ℝ) : EReal) := by
      rw [reducedObjective, hloss]
      simp only [↓reduceIte, zero_add]
      congr 1
      change 1 / (2 * R₁) * R₁ = 1 / 2
      field_simp
    rw [hv1, reducedObjective, hloss]
    simp only [hx, ↓reduceIte]
    by_cases h0 : x = priorQuotient p₀
    · simp only [h0, ↓reduceIte]
      have : (1 : EReal) ≤ 1 + ((w₁.val * regularizerR p₀ (priorQuotient p₀) : ℝ) : EReal) :=
        le_add_of_nonneg_right (EReal.coe_nonneg.mpr (mul_nonneg (by positivity) (hRnn _)))
      exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : (1 / 2 : ℝ) < 1)) this
    · simp only [h0, ↓reduceIte]
      have : (2 : EReal) ≤ 2 + ((w₁.val * regularizerR p₀ x : ℝ) : EReal) :=
        le_add_of_nonneg_right (EReal.coe_nonneg.mpr (mul_nonneg (by positivity) (hRnn _)))
      have h2 : ((2 : ℝ) : EReal) = 2 := by norm_cast
      exact lt_of_lt_of_le (h2 ▸ EReal.coe_lt_coe_iff.mpr (by norm_num)) this
  · intro x hx
    have hv0 : reducedObjective (weightWitnessLoss p₀ x₁) p₀ w₂ (priorQuotient p₀) () = 1 := by
      rw [reducedObjective, hloss]
      simp only [Ne.symm hx₁, ↓reduceIte, hR0, mul_zero, EReal.coe_zero, add_zero]
    rw [hv0, reducedObjective, hloss]
    by_cases h1 : x = x₁
    · simp only [h1, ↓reduceIte, zero_add]
      have : w₂.val * R₁ = 2 := by simp only [w₂]; field_simp
      rw [← hR₁, this]
      exact_mod_cast (by norm_num : (1 : ℝ) < 2)
    · simp only [h1, hx, ↓reduceIte]
      have : (2 : EReal) ≤ 2 + ((w₂.val * regularizerR p₀ x : ℝ) : EReal) :=
        le_add_of_nonneg_right (EReal.coe_nonneg.mpr (mul_nonneg (by positivity) (hRnn _)))
      exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : (1 : ℝ) < 2)) this

end WeightDependence

end NIGBottleneck
