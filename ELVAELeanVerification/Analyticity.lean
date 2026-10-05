import Mathlib
import ELVAELeanVerification.ParameterBridge

set_option linter.style.header false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false

/-!
# Real analyticity of the canonical section

Coordinates `p = (γ, α, c) ∈ ℝ × ℝ × ℝ`; the admissible domain is the open set

  U = ℝ × (0, ∞) × (0, ∞).

For a valid prior (`ν₀ > 0`, `β₀ > 0`, any `γ₀`, `α₀`) this module proves that
the following are real analytic on `U` (`AnalyticOnNhd ℝ`, i.e. analytic at
every point of `U`, with convergent power series in a neighbourhood):

* the scalar `B(γ, α, c)`;
* the canonical selector `ν_can(γ, α, c)`;
* the canonical `β_can(γ, α, c) = c ν_can/(1 + ν_can)`;
* the full canonical section `(γ, α, c) ↦ (γ, ν_can, α, β_can)`.

Mathlib provides real analyticity of `log` on `(0, ∞)` and of `exp`; real
analyticity of `√` at positive points is derived here from
`√x = exp(½ log x)` on the neighbourhood `(0, ∞)`.
-/

namespace ELVAE

open Topology

/-- `√` is real analytic at every positive point. -/
theorem analyticAt_real_sqrt {x : ℝ} (hx : 0 < x) :
    AnalyticAt ℝ Real.sqrt x := by
  have hexp : AnalyticAt ℝ (fun y : ℝ => Real.exp (Real.log y * (1 / 2 : ℝ))) x :=
    ((analyticAt_log hx).mul analyticAt_const).rexp'
  refine hexp.congr ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy]

/-- Composition form: `√ ∘ f` is analytic where `f` is analytic and positive. -/
theorem analyticAt_real_sqrt_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : AnalyticAt ℝ f x) (hpos : 0 < f x) :
    AnalyticAt ℝ (fun z => Real.sqrt (f z)) x :=
  (analyticAt_real_sqrt hpos).comp hf

/-- The admissible quotient domain `ℝ × (0, ∞) × (0, ∞)`. -/
def quotientDomain : Set (ℝ × ℝ × ℝ) :=
  {p | 0 < p.2.1 ∧ 0 < p.2.2}

theorem isOpen_quotientDomain : IsOpen quotientDomain := by
  have h1 : IsOpen {p : ℝ × ℝ × ℝ | 0 < p.2.1} :=
    isOpen_lt continuous_const (continuous_fst.comp continuous_snd)
  have h2 : IsOpen {p : ℝ × ℝ × ℝ | 0 < p.2.2} :=
    isOpen_lt continuous_const (continuous_snd.comp continuous_snd)
  exact h1.inter h2

/-- `B` as a function of the quotient coordinates. -/
noncomputable def BSection (gamma0 nu0 beta0 : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  BFromParams p.1 p.2.1 p.2.2 gamma0 nu0 beta0

/-- `ν_can` as a function of the quotient coordinates. -/
noncomputable def nuCanSection (gamma0 nu0 alpha0 beta0 : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  nuCanFromParams p.1 p.2.1 p.2.2 gamma0 nu0 alpha0 beta0

/-- `β_can` as a function of the quotient coordinates. -/
noncomputable def betaCanSection (gamma0 nu0 alpha0 beta0 : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  betaCanFromParams p.1 p.2.1 p.2.2 gamma0 nu0 alpha0 beta0

/-- The canonical section `(γ, α, c) ↦ (γ, ν_can, α, β_can)` into NIG coordinates. -/
noncomputable def canonicalSection (gamma0 nu0 alpha0 beta0 : ℝ) (p : ℝ × ℝ × ℝ) :
    ℝ × ℝ × ℝ × ℝ :=
  (p.1, nuCanSection gamma0 nu0 alpha0 beta0 p, p.2.1,
    betaCanSection gamma0 nu0 alpha0 beta0 p)

/-- `B` is real analytic wherever `c ≠ 0` (in particular on `U`). -/
theorem BSection_analyticAt
    (gamma0 nu0 beta0 : ℝ) {p : ℝ × ℝ × ℝ} (hc : p.2.2 ≠ 0) :
    AnalyticAt ℝ (BSection gamma0 nu0 beta0) p := by
  have hg : AnalyticAt ℝ (fun q : ℝ × ℝ × ℝ => q.1) p := analyticAt_fst
  have ha : AnalyticAt ℝ (fun q : ℝ × ℝ × ℝ => q.2.1) p :=
    analyticAt_fst.comp analyticAt_snd
  have hcc : AnalyticAt ℝ (fun q : ℝ × ℝ × ℝ => q.2.2) p :=
    analyticAt_snd.comp analyticAt_snd
  have hdiv : AnalyticAt ℝ (fun q : ℝ × ℝ × ℝ => q.2.1 / q.2.2) p := ha.div hcc hc
  have hsq : AnalyticAt ℝ (fun q : ℝ × ℝ × ℝ => (q.1 - gamma0) ^ 2) p :=
    (hg.sub analyticAt_const).pow 2
  have hin : AnalyticAt ℝ
      (fun q : ℝ × ℝ × ℝ => beta0 + (nu0 / 2) * (q.1 - gamma0) ^ 2) p :=
    analyticAt_const.add (analyticAt_const.mul hsq)
  exact analyticAt_const.add (hdiv.mul hin)

theorem BSection_analyticOnNhd (gamma0 nu0 beta0 : ℝ) :
    AnalyticOnNhd ℝ (BSection gamma0 nu0 beta0) quotientDomain :=
  fun _ hp => BSection_analyticAt gamma0 nu0 beta0 hp.2.ne'

/-- The canonical selector is real analytic in `B` on `B > 0` (for every `α₀`). -/
theorem nuCan_analyticAt_B (alpha0 : ℝ) {B : ℝ} (hB : 0 < B) :
    AnalyticAt ℝ (fun x : ℝ => nuCan alpha0 x) B := by
  have hd : AnalyticAt ℝ (fun x : ℝ => x - alpha0 - (1 / 2 : ℝ)) B :=
    (analyticAt_id.sub analyticAt_const).sub analyticAt_const
  have hD : AnalyticAt ℝ (fun x : ℝ => (x - alpha0 - (1 / 2 : ℝ)) ^ 2 + 2 * x) B :=
    (hd.pow 2).add (analyticAt_const.mul analyticAt_id)
  have hDpos : 0 < (B - alpha0 - (1 / 2 : ℝ)) ^ 2 + 2 * B := by positivity
  exact hd.add (analyticAt_real_sqrt_comp hD hDpos)

/-- **Selector.** `ν_can(γ, α, c)` is real analytic on `U`. -/
theorem nuCanSection_analyticOnNhd
    (gamma0 nu0 alpha0 beta0 : ℝ) (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0) :
    AnalyticOnNhd ℝ (nuCanSection gamma0 nu0 alpha0 beta0) quotientDomain := by
  intro p hp
  have hB : 0 < BSection gamma0 nu0 beta0 p :=
    BFromParams_positive _ _ _ _ _ _ hp.1 hp.2 hnu0 hbeta0
  exact (nuCan_analyticAt_B alpha0 hB).comp (BSection_analyticAt gamma0 nu0 beta0 hp.2.ne')

/-- **Fiber coordinate.** `β_can(γ, α, c)` is real analytic on `U`. -/
theorem betaCanSection_analyticOnNhd
    (gamma0 nu0 alpha0 beta0 : ℝ) (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0) :
    AnalyticOnNhd ℝ (betaCanSection gamma0 nu0 alpha0 beta0) quotientDomain := by
  intro p hp
  have hnu := nuCanSection_analyticOnNhd gamma0 nu0 alpha0 beta0 hnu0 hbeta0 p hp
  have hpos : 0 < nuCanSection gamma0 nu0 alpha0 beta0 p :=
    nuCanFromParams_positive _ _ _ _ _ _ _ hp.1 hp.2 hnu0 hbeta0
  have hcc : AnalyticAt ℝ (fun q : ℝ × ℝ × ℝ => q.2.2) p :=
    analyticAt_snd.comp analyticAt_snd
  have hden : (1 + nuCanSection gamma0 nu0 alpha0 beta0 p) ≠ 0 := by linarith
  exact (hcc.mul hnu).div (analyticAt_const.add hnu) hden

/--
**Canonical section.** The canonical section
`(γ, α, c) ↦ (γ, ν_can, α, β_can)` is real analytic on
`ℝ × (0, ∞) × (0, ∞)`.
-/
theorem canonicalSection_analyticOnNhd
    (gamma0 nu0 alpha0 beta0 : ℝ) (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0) :
    AnalyticOnNhd ℝ (canonicalSection gamma0 nu0 alpha0 beta0) quotientDomain := by
  intro p hp
  have hg : AnalyticAt ℝ (fun q : ℝ × ℝ × ℝ => q.1) p := analyticAt_fst
  have ha : AnalyticAt ℝ (fun q : ℝ × ℝ × ℝ => q.2.1) p :=
    analyticAt_fst.comp analyticAt_snd
  exact hg.prod ((nuCanSection_analyticOnNhd gamma0 nu0 alpha0 beta0 hnu0 hbeta0 p hp).prod
    (ha.prod (betaCanSection_analyticOnNhd gamma0 nu0 alpha0 beta0 hnu0 hbeta0 p hp)))

/-- The canonical section lands in the admissible NIG domain and on the correct fiber. -/
theorem canonicalSection_admissible
    (gamma0 nu0 alpha0 beta0 : ℝ) (hnu0 : 0 < nu0) (hbeta0 : 0 < beta0)
    {p : ℝ × ℝ × ℝ} (hp : p ∈ quotientDomain) :
    0 < nuCanSection gamma0 nu0 alpha0 beta0 p
      ∧ 0 < betaCanSection gamma0 nu0 alpha0 beta0 p
      ∧ betaCanSection gamma0 nu0 alpha0 beta0 p
          * (1 + 1 / nuCanSection gamma0 nu0 alpha0 beta0 p) = p.2.2 :=
  ⟨nuCanFromParams_positive _ _ _ _ _ _ _ hp.1 hp.2 hnu0 hbeta0,
    betaCanFromParams_positive _ _ _ _ _ _ _ hp.1 hp.2 hnu0 hbeta0,
    betaCanFromParams_fiber _ _ _ _ _ _ _ hp.1 hp.2 hnu0 hbeta0⟩

end ELVAE
