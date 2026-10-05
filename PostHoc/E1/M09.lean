import Mathlib
import PostHoc.E1.M08

/-! -/

noncomputable section

namespace NS1

open Filter Topology Set ContinuousLinearMap

section S27

lemma lem_078 {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ Complex.Gamma z := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticAt (s := {w : ℂ | 0 < w.re}) ?_ (hopen.mem_nhds hz)
  intro w hw
  refine (Complex.differentiableAt_Gamma w fun m hm => ?_).differentiableWithinAt
  have : (0 : ℝ) < w.re := hw
  rw [hm] at this
  simp at this
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

lemma lem_079 {x : ℝ} (hx : 0 < x) : AnalyticAt ℝ Real.Gamma x := by
  have h := (lem_078 (z := (x : ℂ)) (by simpa using hx)).re_ofReal
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp [Complex.Gamma_ofReal]

lemma lem_080 {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun b => Real.log (Real.Gamma b)) (deriv Real.Gamma a / Real.Gamma a) a := by
  have hG := (lem_079 ha).differentiableAt.hasDerivAt
  exact hG.log (Real.Gamma_pos_of_pos ha).ne'

lemma lem_081 {a : ℝ} (ha : 0 < a) : def_019 a = deriv Real.Gamma a / Real.Gamma a :=
  (lem_080 ha).deriv

lemma lem_082 {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun b => Real.log (Real.Gamma b)) (def_019 a) a := by
  rw [lem_081 ha]
  exact lem_080 ha

lemma lem_083 {a : ℝ} (ha : 0 < a) : AnalyticAt ℝ def_019 a := by
  have hG := lem_079 ha
  have h : AnalyticAt ℝ (fun b => deriv Real.Gamma b / Real.Gamma b) a :=
    hG.deriv.div hG (Real.Gamma_pos_of_pos ha).ne'
  refine h.congr ?_
  filter_upwards [Ioi_mem_nhds ha] with b hb
  exact (lem_081 hb).symm

def def_064 (a : ℝ) : ℝ := deriv def_019 a

lemma lem_084 {a : ℝ} (ha : 0 < a) : HasDerivAt def_019 (def_064 a) a :=
  (lem_083 ha).differentiableAt.hasDerivAt

end S27

section S12

variable (p₀ : str_001)

abbrev abb_005 : Type := ℝ × ℝ × ℝ

def def_065 : Set abb_005 := {x | 0 < x.2.1 ∧ 0 < x.2.2}

theorem thm_148 : IsOpen def_065 :=
  (isOpen_lt continuous_const (by fun_prop : Continuous fun x : abb_005 => x.2.1)).inter
    (isOpen_lt continuous_const (by fun_prop : Continuous fun x : abb_005 => x.2.2))

def def_066 (x : abb_005) : ℝ := p₀.beta + p₀.nu / 2 * (x.1 - p₀.gamma) ^ 2

def def_067 (x : abb_005) (t : ℝ) : ℝ :=
  p₀.alpha * Real.log (x.2.2 / p₀.beta) + (Real.log (Real.Gamma p₀.alpha)
    - Real.log (Real.Gamma x.2.1)) + (x.2.1 - p₀.alpha) * def_019 x.2.1 - x.2.1
    - p₀.alpha * Real.log (1 + t) + x.2.1 * def_066 p₀ x / x.2.2 * (1 + t)
    + (1 / 2) * (p₀.nu * t - 1 - Real.log (p₀.nu * t))

def def_068 (x : abb_005) : ℝ := p₀.nu + 2 * x.2.1 * def_066 p₀ x / x.2.2

def def_069 (x : abb_005) : ℝ := def_044 p₀.alpha (def_068 p₀ x)

def def_070 (x : abb_005) : ℝ := def_067 p₀ x (def_069 p₀ x)

theorem thm_149 (x : str_002) (t : ℝ) :
    def_067 p₀ (x.gamma, x.alpha, x.s) t = def_042 p₀ x t := by
  rw [def_067, def_042, def_066, def_040,
    Real.log_div (Real.Gamma_pos_of_pos p₀.alpha_pos).ne' (Real.Gamma_pos_of_pos x.alpha_pos).ne']

theorem thm_150 (x : str_002) : def_069 p₀ (x.gamma, x.alpha, x.s) = def_047 p₀ x := rfl

theorem thm_151 (x : str_002) : def_070 p₀ (x.gamma, x.alpha, x.s) = def_060 p₀ x := by
  rw [def_070, thm_150, thm_149, def_060, thm_091]
  rfl

lemma lem_085 {x : abb_005} (hx : x ∈ def_065) : 0 < def_068 p₀ x := by
  have := p₀.nu_pos
  have := p₀.beta_pos
  obtain ⟨ha, hs⟩ := hx
  unfold def_068 def_066
  positivity

lemma lem_086 {x : abb_005} (hx : x ∈ def_065) : 0 < def_069 p₀ x :=
  thm_092 (lem_085 p₀ hx)

end S12

section S03

variable (p₀ : str_001)

lemma lem_087 {x : abb_005} (hx : x ∈ def_065) : AnalyticAt ℝ (def_068 p₀) x := by
  have hg : AnalyticAt ℝ (fun y : abb_005 => y.1) x := analyticAt_fst
  have ha : AnalyticAt ℝ (fun y : abb_005 => y.2.1) x := analyticAt_fst.comp analyticAt_snd
  have hs : AnalyticAt ℝ (fun y : abb_005 => y.2.2) x := analyticAt_snd.comp analyticAt_snd
  have hB : AnalyticAt ℝ (def_066 p₀) x :=
    analyticAt_const.add (analyticAt_const.mul ((hg.sub analyticAt_const).pow 2))
  exact analyticAt_const.add (((analyticAt_const.mul ha).mul hB).div hs hx.2.ne')

lemma lem_088 {x : abb_005} (hx : x ∈ def_065) :
    AnalyticAt ℝ (def_069 p₀) x := by
  have hd := lem_087 p₀ hx
  have hD : 0 < def_043 p₀.alpha (def_068 p₀ x) := lem_054 (lem_085 p₀ hx)
  have hdisc : AnalyticAt ℝ (fun y : abb_005 => def_043 p₀.alpha (def_068 p₀ y)) x :=
    (((hd.sub analyticAt_const).sub analyticAt_const).pow 2).add (analyticAt_const.mul hd)
  have hsq := AnalyticAt.comp (g := Real.sqrt)
    (f := fun y : abb_005 => def_043 p₀.alpha (def_068 p₀ y)) (thm_110 hD) hdisc
  have hd0 : 2 * def_068 p₀ x ≠ 0 := by have := lem_085 p₀ hx; positivity
  exact (((analyticAt_const.add analyticAt_const).sub hd).add hsq).div
    (analyticAt_const.mul hd) hd0

lemma lem_089 {x : abb_005} (hx : x ∈ def_065) {t : ℝ} (ht : 0 < t) :
    AnalyticAt ℝ (fun q : abb_005 × ℝ => def_067 p₀ q.1 q.2) (x, t) := by
  set X := abb_005 × ℝ
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
    (lem_079 hx.1) ha
  have hlogG := AnalyticAt.comp (g := Real.log) (f := fun q : X => Real.Gamma q.1.2.1)
    (analyticAt_log (Real.Gamma_pos_of_pos hx.1)) hGam
  have hpsi := AnalyticAt.comp (g := def_019) (f := fun q : X => q.1.2.1)
    (lem_083 hx.1) ha
  have hlog1 := AnalyticAt.comp (g := Real.log) (f := fun q : X => 1 + q.2)
    (analyticAt_log (by linarith : (0 : ℝ) < 1 + t)) (analyticAt_const.add hsnd)
  have hlognt := AnalyticAt.comp (g := Real.log) (f := fun q : X => p₀.nu * q.2)
    (analyticAt_log (mul_pos p₀.nu_pos ht)) (analyticAt_const.mul hsnd)
  have hB : AnalyticAt ℝ (fun q : X => def_066 p₀ q.1) (x, t) :=
    analyticAt_const.add (analyticAt_const.mul ((hg.sub analyticAt_const).pow 2))
  unfold def_067
  exact ((((((analyticAt_const.mul hlogs).add (analyticAt_const.sub hlogG)).add
    ((ha.sub analyticAt_const).mul hpsi)).sub ha).sub (analyticAt_const.mul hlog1)).add
    (((ha.mul hB).div hs hx.2.ne').mul (analyticAt_const.add hsnd))).add
    (analyticAt_const.mul (((analyticAt_const.mul hsnd).sub analyticAt_const).sub hlognt))

theorem thm_152 : AnalyticOnNhd ℝ (def_070 p₀) def_065 := by
  intro x hx
  have ht := lem_088 p₀ hx
  have hF := lem_089 p₀ hx (lem_086 p₀ hx)
  exact AnalyticAt.comp (g := fun q : abb_005 × ℝ => def_067 p₀ q.1 q.2)
    (f := fun y : abb_005 => (y, def_069 p₀ y)) hF (analyticAt_id.prod ht)

end S03

section S18

variable (p₀ : str_001)

theorem thm_153 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

lemma lem_090 (x : abb_005) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => def_067 p₀ x u)
      ((1 / 2) * (def_068 p₀ x - 2 * p₀.alpha / (1 + t) - 1 / t)) t := by
  have h1t : 1 + t ≠ 0 := by linarith
  have hn := p₀.nu_pos
  have hlog1 : HasDerivAt (fun u => Real.log (1 + u)) (1 / (1 + t)) t :=
    ((hasDerivAt_id' t).const_add 1).log h1t
  have hlognt : HasDerivAt (fun u => Real.log (p₀.nu * u)) (1 / t) t :=
    (((hasDerivAt_id' t).const_mul p₀.nu).log (mul_pos hn ht).ne').congr_deriv (by field_simp)
  have h := ((((hasDerivAt_const t (p₀.alpha * Real.log (x.2.2 / p₀.beta)
      + (Real.log (Real.Gamma p₀.alpha) - Real.log (Real.Gamma x.2.1))
      + (x.2.1 - p₀.alpha) * def_019 x.2.1 - x.2.1)).sub (hlog1.const_mul p₀.alpha)).add
    (((hasDerivAt_id' t).const_add 1).const_mul (x.2.1 * def_066 p₀ x / x.2.2))).add
    ((((hasDerivAt_id' t).const_mul p₀.nu).sub_const 1).sub hlognt |>.const_mul (1 / 2)))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)).congr_deriv ?_
  · simp only [def_067, Pi.add_apply, Pi.sub_apply]
  · rw [def_068]
    ring

lemma lem_091 {x : abb_005} (hx : x ∈ def_065) :
    HasDerivAt (fun u => def_067 p₀ x u) 0 (def_069 p₀ x) := by
  have h := lem_090 p₀ x (lem_086 p₀ hx)
  have hsel := thm_098 (A := p₀.alpha) (lem_085 p₀ hx)
  refine h.congr_deriv ?_
  unfold def_069
  linarith

theorem thm_154 {x : abb_005} (hx : x ∈ def_065) :
    HasFDerivAt (def_070 p₀)
      ((fderiv ℝ (fun q : abb_005 × ℝ => def_067 p₀ q.1 q.2) (x, def_069 p₀ x)).comp
        (inl ℝ abb_005 ℝ)) x := by
  set G := fun q : abb_005 × ℝ => def_067 p₀ q.1 q.2
  have hGan := lem_089 p₀ hx (lem_086 p₀ hx)
  have hG : HasFDerivAt G (fderiv ℝ G (x, def_069 p₀ x)) (x, def_069 p₀ x) :=
    hGan.differentiableAt.hasFDerivAt
  have hs : HasFDerivAt (def_069 p₀) (fderiv ℝ (def_069 p₀) x) x :=
    (lem_088 p₀ hx).differentiableAt.hasFDerivAt
  have hstat : (fderiv ℝ G (x, def_069 p₀ x)).comp (inr ℝ abb_005 ℝ) = 0 := by
    have h1 : HasFDerivAt (fun u => G (x, u)) ((fderiv ℝ G (x, def_069 p₀ x)).comp
        (inr ℝ abb_005 ℝ)) (def_069 p₀ x) :=
      hG.comp (def_069 p₀ x) (hasFDerivAt_prodMk_right x (def_069 p₀ x))
    have h2 := lem_091 p₀ hx
    rw [h1.unique h2.hasFDerivAt]
    ext
    simp
  exact thm_153 hG hs hstat

lemma lem_092 {x : abb_005} (hx : x ∈ def_065) (v : abb_005) {c : ℝ}
    (hc : HasDerivAt (fun u : ℝ => def_067 p₀ (x + u • v) (def_069 p₀ x)) c 0) :
    HasDerivAt (fun u : ℝ => def_070 p₀ (x + u • v)) c 0 := by
  set G := fun q : abb_005 × ℝ => def_067 p₀ q.1 q.2
  have hGan := lem_089 p₀ hx (lem_086 p₀ hx)
  have hG : HasFDerivAt G (fderiv ℝ G (x, def_069 p₀ x)) (x, def_069 p₀ x) :=
    hGan.differentiableAt.hasFDerivAt
  have hline : HasDerivAt (fun u : ℝ => x + u • v) v 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add x
    rwa [one_smul] at this
  have hR := thm_154 p₀ hx
  have hR' : HasDerivAt (fun u : ℝ => def_070 p₀ (x + u • v))
      ((fderiv ℝ G (x, def_069 p₀ x)) (v, 0)) 0 := by
    have := hR.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] at this
    exact this
  have hF' : HasDerivAt (fun u : ℝ => def_067 p₀ (x + u • v) (def_069 p₀ x))
      ((fderiv ℝ G (x, def_069 p₀ x)) (v, 0)) 0 := by
    have hl : HasDerivAt (fun u : ℝ => (x + u • v, def_069 p₀ x)) (v, (0 : ℝ)) 0 :=
      hline.prodMk (hasDerivAt_const _ _)
    have := hG.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
    exact this
  rw [hF'.unique hc] at hR'
  exact hR'

theorem thm_155 {x : abb_005} (hx : x ∈ def_065) :
    HasDerivAt (fun u : ℝ => def_070 p₀ (x + u • ((1 : ℝ), (0 : ℝ), (0 : ℝ))))
      (p₀.nu * x.2.1 * (x.1 - p₀.gamma) * (1 + def_069 p₀ x) / x.2.2) 0 := by
  apply lem_092 p₀ hx
  set t := def_069 p₀ x
  have hd : HasDerivAt (fun u : ℝ => x.1 + u - p₀.gamma) 1 0 :=
    ((hasDerivAt_id' (0 : ℝ)).const_add x.1).sub_const p₀.gamma
  have hB : HasDerivAt (fun u : ℝ => p₀.beta + p₀.nu / 2 * ((x.1 + u - p₀.gamma)
      * (x.1 + u - p₀.gamma))) (p₀.nu * (x.1 - p₀.gamma)) 0 :=
    (((hd.mul hd).const_mul (p₀.nu / 2)).const_add p₀.beta).congr_deriv (by ring)
  have h := ((((hB.const_mul (x.2.1)).div_const x.2.2).mul_const (1 + t)).const_add
    (p₀.alpha * Real.log (x.2.2 / p₀.beta) + (Real.log (Real.Gamma p₀.alpha)
      - Real.log (Real.Gamma x.2.1)) + (x.2.1 - p₀.alpha) * def_019 x.2.1 - x.2.1
      - p₀.alpha * Real.log (1 + t))).add_const
    ((1 / 2) * (p₀.nu * t - 1 - Real.log (p₀.nu * t)))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)).congr_deriv ?_
  · simp only [def_067, def_066, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul, mul_one,
      mul_zero, add_zero]
    ring
  · ring

theorem thm_156 {x : abb_005} (hx : x ∈ def_065) :
    HasDerivAt (fun u : ℝ => def_070 p₀ (x + u • ((0 : ℝ), (1 : ℝ), (0 : ℝ))))
      ((x.2.1 - p₀.alpha) * def_064 x.2.1 - 1
        + def_066 p₀ x * (1 + def_069 p₀ x) / x.2.2) 0 := by
  apply lem_092 p₀ hx
  set t := def_069 p₀ x
  have hlin : HasDerivAt (fun u : ℝ => x.2.1 + u) 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add x.2.1
  have hlogG : HasDerivAt (fun u : ℝ => Real.log (Real.Gamma (x.2.1 + u))) (def_019 x.2.1) 0 := by
    have := (lem_082 hx.1).comp_of_eq (0 : ℝ) hlin (by simp)
    rw [mul_one] at this
    exact this
  have hpsi : HasDerivAt (fun u : ℝ => def_019 (x.2.1 + u)) (def_064 x.2.1) 0 := by
    have := (lem_084 hx.1).comp_of_eq (0 : ℝ) hlin (by simp)
    rw [mul_one] at this
    exact this
  have h := ((((((hasDerivAt_const (0 : ℝ) (p₀.alpha * Real.log (x.2.2 / p₀.beta)
      + Real.log (Real.Gamma p₀.alpha))).sub hlogG).add ((hlin.sub_const p₀.alpha).mul hpsi)).sub
      hlin).sub (hasDerivAt_const (0 : ℝ) (p₀.alpha * Real.log (1 + t)))).add
      ((hlin.mul_const (def_066 p₀ x / x.2.2 * (1 + t))))).add
    (hasDerivAt_const (0 : ℝ) ((1 / 2) * (p₀.nu * t - 1 - Real.log (p₀.nu * t))))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)).congr_deriv ?_
  · simp only [def_067, def_066, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul, mul_one,
      mul_zero, add_zero, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  · simp only [add_zero]
    ring

theorem thm_157 {x : abb_005} (hx : x ∈ def_065) :
    HasDerivAt (fun u : ℝ => def_070 p₀ (x + u • ((0 : ℝ), (0 : ℝ), (1 : ℝ))))
      (p₀.alpha / x.2.2 - x.2.1 * def_066 p₀ x * (1 + def_069 p₀ x) / x.2.2 ^ 2) 0 := by
  apply lem_092 p₀ hx
  set t := def_069 p₀ x
  have hlin : HasDerivAt (fun u : ℝ => x.2.2 + u) 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add x.2.2
  have hlogs : HasDerivAt (fun u : ℝ => Real.log ((x.2.2 + u) / p₀.beta)) (1 / x.2.2) 0 :=
    ((hlin.div_const p₀.beta).log (by simpa using (div_pos hx.2 p₀.beta_pos).ne')).congr_deriv
      (by have := p₀.beta_pos; have := hx.2; rw [add_zero]; field_simp)
  have hinv : HasDerivAt (fun u : ℝ => (x.2.1 * def_066 p₀ x) / (x.2.2 + u))
      (-(x.2.1 * def_066 p₀ x) / x.2.2 ^ 2) 0 :=
    ((hasDerivAt_const (0 : ℝ) (x.2.1 * def_066 p₀ x)).div hlin
      (by simpa using hx.2.ne')).congr_deriv (by rw [add_zero]; ring)
  have h := ((((hasDerivAt_const (0 : ℝ) (Real.log (Real.Gamma p₀.alpha)
      - Real.log (Real.Gamma x.2.1) + (x.2.1 - p₀.alpha) * def_019 x.2.1 - x.2.1
      - p₀.alpha * Real.log (1 + t))).add (hlogs.const_mul p₀.alpha)).add
      (hinv.mul_const (1 + t))).add
    (hasDerivAt_const (0 : ℝ) ((1 / 2) * (p₀.nu * t - 1 - Real.log (p₀.nu * t)))))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)).congr_deriv ?_
  · simp only [def_067, def_066, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul, mul_one,
      mul_zero, add_zero, Pi.add_apply]
    ring
  · ring

theorem thm_158 {ℓ : abb_005 → ℝ} {ℓ' : abb_005 →L[ℝ] ℝ} (w : abb_001) {x : abb_005}
    (hx : x ∈ def_065) (hℓ : HasFDerivAt ℓ ℓ' x)
    (hmin : IsLocalMin (fun y => ℓ y + w.val * def_070 p₀ y) x) :
    ℓ' + w.val • fderiv ℝ (def_070 p₀) x = 0 := by
  have hR := (thm_154 p₀ hx).differentiableAt.hasFDerivAt
  have hJ : HasFDerivAt (fun y => ℓ y + w.val * def_070 p₀ y)
      (ℓ' + w.val • fderiv ℝ (def_070 p₀) x) x := hℓ.add (hR.const_mul w.val)
  exact hmin.hasFDerivAt_eq_zero hJ

end S18

section S59

variable (p₀ : str_001)

open Classical in
def def_071 (x₁ : str_002) : abb_003 Unit :=
  fun μ _ => if μ = def_035 x₁ then 0 else if μ = def_035 (def_057 p₀) then 1 else 2

theorem thm_159 :
    ∃ (L : abb_003 Unit) (w₁ w₂ : abb_001) (x₁ x₂ : str_002),
      x₁ ≠ x₂ ∧ (∀ μ, 0 ≤ L μ () ∧ L μ () ≠ ⊤) ∧
      (∀ x, x ≠ x₁ → def_061 L p₀ w₁ x₁ () < def_061 L p₀ w₁ x ()) ∧
      (∀ x, x ≠ x₂ → def_061 L p₀ w₂ x₂ () < def_061 L p₀ w₂ x ()) ∧
      (∀ w : abb_001, ∀ x : str_002, ∀ t : abb_001,
        (∀ t' : abb_001, w.val * def_041 p₀ x t ≤ w.val * def_041 p₀ x t') ↔
          t = def_050 p₀ x) := by
  classical
  obtain ⟨x₁, hx₁, -⟩ := thm_146 p₀ 1 one_pos
  set R₁ := def_060 p₀ x₁ with hR₁
  have hR₁pos : 0 < R₁ := by
    rcases (thm_133 p₀ x₁).lt_or_eq with h | h
    · exact h
    · exact absurd ((thm_131 p₀ x₁).mp h.symm) hx₁
  let w₁ : abb_001 := ⟨1 / (2 * R₁), by positivity⟩
  let w₂ : abb_001 := ⟨2 / R₁, by positivity⟩
  have hloss : ∀ x, def_059 (def_071 p₀ x₁) x () =
      if x = x₁ then 0 else if x = def_057 p₀ then 1 else 2 := by
    intro x
    simp only [def_059, def_071, thm_072.eq_iff]
  have hR0 : def_060 p₀ (def_057 p₀) = 0 := thm_130 p₀
  have hRnn := thm_133 p₀
  refine ⟨def_071 p₀ x₁, w₁, w₂, x₁, def_057 p₀, hx₁, fun μ => ?_, ?_, ?_,
    fun w x t => thm_142 p₀ w x t⟩
  · unfold def_071
    split_ifs
    · exact ⟨le_rfl, EReal.zero_ne_top⟩
    · exact ⟨zero_le_one, ne_of_lt (EReal.coe_lt_top 1)⟩
    · exact ⟨by norm_num, ne_of_lt (EReal.coe_lt_top 2)⟩
  · intro x hx
    have hv1 : def_061 (def_071 p₀ x₁) p₀ w₁ x₁ () = ((1 / 2 : ℝ) : EReal) := by
      rw [def_061, hloss]
      simp only [↓reduceIte, zero_add]
      congr 1
      change 1 / (2 * R₁) * R₁ = 1 / 2
      field_simp
    rw [hv1, def_061, hloss]
    simp only [hx, ↓reduceIte]
    by_cases h0 : x = def_057 p₀
    · simp only [h0, ↓reduceIte]
      have : (1 : EReal) ≤ 1 + ((w₁.val * def_060 p₀ (def_057 p₀) : ℝ) : EReal) :=
        le_add_of_nonneg_right (EReal.coe_nonneg.mpr (mul_nonneg (by positivity) (hRnn _)))
      exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : (1 / 2 : ℝ) < 1)) this
    · simp only [h0, ↓reduceIte]
      have : (2 : EReal) ≤ 2 + ((w₁.val * def_060 p₀ x : ℝ) : EReal) :=
        le_add_of_nonneg_right (EReal.coe_nonneg.mpr (mul_nonneg (by positivity) (hRnn _)))
      have h2 : ((2 : ℝ) : EReal) = 2 := by norm_cast
      exact lt_of_lt_of_le (h2 ▸ EReal.coe_lt_coe_iff.mpr (by norm_num)) this
  · intro x hx
    have hv0 : def_061 (def_071 p₀ x₁) p₀ w₂ (def_057 p₀) () = 1 := by
      rw [def_061, hloss]
      simp only [Ne.symm hx₁, ↓reduceIte, hR0, mul_zero, EReal.coe_zero, add_zero]
    rw [hv0, def_061, hloss]
    by_cases h1 : x = x₁
    · simp only [h1, ↓reduceIte, zero_add]
      have : w₂.val * R₁ = 2 := by simp only [w₂]; field_simp
      rw [← hR₁, this]
      exact_mod_cast (by norm_num : (1 : ℝ) < 2)
    · simp only [h1, hx, ↓reduceIte]
      have : (2 : EReal) ≤ 2 + ((w₂.val * def_060 p₀ x : ℝ) : EReal) :=
        le_add_of_nonneg_right (EReal.coe_nonneg.mpr (mul_nonneg (by positivity) (hRnn _)))
      exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : (1 : ℝ) < 2)) this

end S59

end NS1
