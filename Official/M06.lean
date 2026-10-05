import Mathlib
import Official.M05

/-!
# Unique analytic fiber selection and exact positive gap

For every quotient state `x`, the fiber divergence `F(x, ·)` has a unique
minimizer `t_*(x) > 0`, the unique positive solution of `d = 2A/(1+t) + 1/t` with
`d = n + 2αB/s`; explicitly `t_* = T_A(d)`, `ν_sel = Φ_A(d) = 1/t_*`, `β_sel = s/(1+t_*)`; these
are real analytic in `x` and in the complete prior parameters; and the exact gap formula holds.
-/

noncomputable section

namespace NIGBottleneck

section Scalar

/-- The discriminant `(d − 2A − 1)² + 4d`. -/
def selDisc (A d : ℝ) : ℝ := (d - 2 * A - 1) ^ 2 + 4 * d

/-- `T_A(d) = (2A + 1 − d + √((d − 2A − 1)² + 4d)) / (2d)`. -/
def TA (A d : ℝ) : ℝ := (2 * A + 1 - d + Real.sqrt (selDisc A d)) / (2 * d)

/-- `Φ_A(d) = (d − 2A − 1 + √((d − 2A − 1)² + 4d)) / 2`. -/
def PhiA (A d : ℝ) : ℝ := (d - 2 * A - 1 + Real.sqrt (selDisc A d)) / 2

variable {A d : ℝ}

lemma selDisc_pos (hd : 0 < d) : 0 < selDisc A d := by
  unfold selDisc; positivity

lemma abs_lt_sqrt_selDisc (hd : 0 < d) : |d - 2 * A - 1| < Real.sqrt (selDisc A d) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) (by unfold selDisc; linarith)

lemma TA_num_pos (hd : 0 < d) : 0 < 2 * A + 1 - d + Real.sqrt (selDisc A d) := by
  have h := abs_lt_sqrt_selDisc (A := A) hd
  have := le_abs_self (d - 2 * A - 1)
  linarith

lemma PhiA_num_pos (hd : 0 < d) : 0 < d - 2 * A - 1 + Real.sqrt (selDisc A d) := by
  have h := abs_lt_sqrt_selDisc (A := A) hd
  have := neg_abs_le (d - 2 * A - 1)
  linarith

/-- `T_A(d) > 0` for `d > 0`. -/
theorem TA_pos (hd : 0 < d) : 0 < TA A d :=
  div_pos (TA_num_pos hd) (by positivity)

/-- `Φ_A(d) > 0` for `d > 0`. -/
theorem PhiA_pos (hd : 0 < d) : 0 < PhiA A d :=
  div_pos (PhiA_num_pos hd) two_pos

/-- `T_A(d) Φ_A(d) = 1`, i.e. `Φ_A(d) = 1 / T_A(d)`. -/
theorem TA_mul_PhiA (hd : 0 < d) : TA A d * PhiA A d = 1 := by
  have hD := (selDisc_pos (A := A) hd).le
  unfold TA PhiA
  rw [div_mul_div_comm]
  have hsq : (2 * A + 1 - d + Real.sqrt (selDisc A d)) * (d - 2 * A - 1 + Real.sqrt (selDisc A d))
      = Real.sqrt (selDisc A d) ^ 2 - (d - 2 * A - 1) ^ 2 := by ring
  rw [hsq, Real.sq_sqrt hD, selDisc]
  field_simp
  ring

theorem PhiA_eq_inv_TA (hd : 0 < d) : PhiA A d = 1 / TA A d := by
  rw [eq_div_iff (TA_pos hd).ne', mul_comm, TA_mul_PhiA hd]

/-- `T_A(d)` is the positive root of `d t² + (d − 2A − 1) t − 1 = 0`. -/
theorem TA_quadratic (hd : 0 < d) : d * TA A d ^ 2 + (d - 2 * A - 1) * TA A d - 1 = 0 := by
  have hD := (selDisc_pos (A := A) hd).le
  unfold TA
  field_simp
  have hs := Real.sq_sqrt hD
  unfold selDisc at hs ⊢
  nlinarith [hs]

/-- For `t > 0`, the selection equation `d = 2A/(1+t) + 1/t` is the quadratic. -/
lemma selection_eq_iff_quadratic {t : ℝ} (ht : 0 < t) :
    d = 2 * A / (1 + t) + 1 / t ↔ d * t ^ 2 + (d - 2 * A - 1) * t - 1 = 0 := by
  have h1t : (1 + t) ≠ 0 := by linarith
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    field_simp
    linarith

/-- For `d > 0`, `T_A(d)` is the unique positive solution of
`d = 2A/(1+t) + 1/t`. -/
theorem selection_eq_iff (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    d = 2 * A / (1 + t) + 1 / t ↔ t = TA A d := by
  rw [selection_eq_iff_quadratic ht]
  constructor
  · intro h
    have hq := TA_quadratic (A := A) hd
    have hfac : (t - TA A d) * (d * t + d * TA A d + (d - 2 * A - 1)) = 0 := by
      linear_combination h - hq
    have hpos : 0 < d * t + d * TA A d + (d - 2 * A - 1) := by
      have h2 : d * TA A d + (d - 2 * A - 1) = (d - 2 * A - 1 + Real.sqrt (selDisc A d)) / 2 := by
        unfold TA; field_simp; ring
      have := PhiA_num_pos (A := A) hd
      nlinarith [mul_pos hd ht]
    rcases mul_eq_zero.mp hfac with h0 | h0
    · linarith
    · linarith
  · rintro rfl
    exact TA_quadratic hd

theorem TA_selection_eq (hd : 0 < d) : d = 2 * A / (1 + TA A d) + 1 / TA A d :=
  (selection_eq_iff hd (TA_pos hd)).mpr rfl

/-- `u − 1 − log u ≥ 0` for `u > 0`. -/
lemma sub_one_sub_log_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ u - 1 - Real.log u := by
  have := Real.log_le_sub_one_of_pos hu
  linarith

/-- `u − 1 − log u > 0` for `u > 0`, `u ≠ 1`. -/
lemma sub_one_sub_log_pos {u : ℝ} (hu : 0 < u) (h1 : u ≠ 1) : 0 < u - 1 - Real.log u := by
  have := Real.log_lt_sub_one_of_pos hu h1
  linarith

end Scalar

section Selection

variable (p₀ : Parameters) (x : QuotientState)

/-- `d = n + 2αB/s`. -/
def selD : ℝ := p₀.nu + 2 * x.alpha * priorB p₀ x / x.s

/-- `d > 0`. -/
theorem selD_pos : 0 < selD p₀ x := by
  have := priorB_pos p₀ x
  have := x.alpha_pos
  have := x.s_pos
  have := p₀.nu_pos
  unfold selD
  positivity

/-- The selected fiber coordinate `t_*(x) = T_A(d)`. -/
def selT : ℝ := TA p₀.alpha (selD p₀ x)

/-- The selected `ν_sel = Φ_A(d)`. -/
def selNu : ℝ := PhiA p₀.alpha (selD p₀ x)

/-- The selected `β_sel = s/(1 + t_*)`. -/
def selBeta : ℝ := x.s / (1 + selT p₀ x)

/-- The minimizer is interior, `t_* > 0`. -/
theorem selT_pos : 0 < selT p₀ x := TA_pos (selD_pos p₀ x)

/-- The selected fiber coordinate as a positive real. -/
def selTPos : PositiveReal := ⟨selT p₀ x, selT_pos p₀ x⟩

/-- `ν_sel = Φ_A(d) = 1/t_*`. -/
theorem selNu_eq_inv_selT : selNu p₀ x = 1 / selT p₀ x :=
  PhiA_eq_inv_TA (selD_pos p₀ x)

/-- The selected representative of the fiber is
`(γ, ν_sel, α, β_sel) = (γ, Φ_A(d), α, s/(1 + t_*))`. -/
theorem selectedParameters_eq :
    (fiberParameters x (selTPos p₀ x)).gamma = x.gamma ∧
      (fiberParameters x (selTPos p₀ x)).nu = selNu p₀ x ∧
      (fiberParameters x (selTPos p₀ x)).alpha = x.alpha ∧
      (fiberParameters x (selTPos p₀ x)).beta = selBeta p₀ x := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  simp only [fiberParameters, selTPos]
  rw [selNu_eq_inv_selT]

/-- `t_*` is the unique positive solution of the selection equation. -/
theorem selT_unique_solution (t : ℝ) (ht : 0 < t) :
    selD p₀ x = 2 * p₀.alpha / (1 + t) + 1 / t ↔ t = selT p₀ x :=
  selection_eq_iff (selD_pos p₀ x) ht

/-- The gap function `A(η − 1 − log η) + ½(ζ − 1 − log ζ)` with
`η = (1+t)/(1+t_*)`, `ζ = t/t_*`. -/
def fiberGap (t : ℝ) : ℝ :=
  p₀.alpha * ((1 + t) / (1 + selT p₀ x) - 1 - Real.log ((1 + t) / (1 + selT p₀ x)))
    + (1 / 2) * (t / selT p₀ x - 1 - Real.log (t / selT p₀ x))

/-- The exact gap formula `F(x,t) − F(x,t_*) = A(η−1−log η) + ½(ζ−1−log ζ)`
for `t > 0`. -/
theorem fiberKLFormula_sub_min (t : ℝ) (ht : 0 < t) :
    fiberKLFormula p₀ x t - fiberKLFormula p₀ x (selT p₀ x) = fiberGap p₀ x t := by
  have hts := selT_pos p₀ x
  have h1t : 0 < 1 + t := by linarith
  have h1ts : 0 < 1 + selT p₀ x := by linarith
  have hn := p₀.nu_pos
  have hs := x.s_pos
  have hsel := TA_selection_eq (A := p₀.alpha) (selD_pos p₀ x)
  have key : x.alpha * priorB p₀ x / x.s * (t - selT p₀ x) + p₀.nu / 2 * (t - selT p₀ x)
      = p₀.alpha * ((1 + t) / (1 + selT p₀ x) - 1) + 1 / 2 * (t / selT p₀ x - 1) := by
    have hd : x.alpha * priorB p₀ x / x.s = (selD p₀ x - p₀.nu) / 2 := by
      unfold selD; ring
    rw [hd]
    change (selD p₀ x - p₀.nu) / 2 * (t - selT p₀ x) + p₀.nu / 2 * (t - selT p₀ x) = _
    have hd2 : selD p₀ x = 2 * p₀.alpha / (1 + selT p₀ x) + 1 / selT p₀ x := hsel
    rw [hd2]
    field_simp
    ring
  unfold fiberKLFormula fiberGap
  rw [Real.log_div h1t.ne' h1ts.ne', Real.log_div ht.ne' hts.ne',
    Real.log_mul hn.ne' ht.ne', Real.log_mul hn.ne' hts.ne']
  linear_combination key

/-- The gap is nonnegative, and strictly positive unless `t = t_*`. -/
theorem fiberGap_pos (t : ℝ) (ht : 0 < t) (hne : t ≠ selT p₀ x) : 0 < fiberGap p₀ x t := by
  have hts := selT_pos p₀ x
  have h1 := sub_one_sub_log_nonneg (div_pos (by linarith : (0 : ℝ) < 1 + t)
    (by linarith : (0 : ℝ) < 1 + selT p₀ x))
  have h2 := sub_one_sub_log_pos (div_pos ht hts) (by
    intro h
    exact hne ((div_eq_one_iff_eq hts.ne').mp h))
  have hA := p₀.alpha_pos
  unfold fiberGap
  nlinarith [mul_nonneg hA.le h1]

theorem fiberGap_self : fiberGap p₀ x (selT p₀ x) = 0 := by
  have hts := selT_pos p₀ x
  unfold fiberGap
  rw [div_self (by linarith), div_self hts.ne']
  simp

/-- Gap on the fiber: for every `t > 0`,
`F(x,t) − F(x,t_*) = A(η − 1 − log η) + ½(ζ − 1 − log ζ)`. -/
theorem fiberKL_sub_selected (t : PositiveReal) :
    fiberKL p₀ x t - fiberKL p₀ x (selTPos p₀ x) = fiberGap p₀ x t := by
  rw [fiberKL_eq, fiberKL_eq]
  exact fiberKLFormula_sub_min p₀ x t t.property

/-- `t_*` minimizes `F(x, ·)` on `t > 0`, strictly: every other `t > 0` has a
strictly larger divergence. -/
theorem fiberKL_selected_lt (t : PositiveReal) (hne : (t : ℝ) ≠ selT p₀ x) :
    fiberKL p₀ x (selTPos p₀ x) < fiberKL p₀ x t := by
  have h := fiberKL_sub_selected p₀ x t
  have hg := fiberGap_pos p₀ x t t.property hne
  linarith

/-- `F(x, ·)` has a unique minimizer on `t > 0`, namely `t_*(x)`. -/
theorem fiberKL_unique_minimizer :
    ∃! t : PositiveReal, ∀ t' : PositiveReal, fiberKL p₀ x t ≤ fiberKL p₀ x t' := by
  refine ⟨selTPos p₀ x, fun t' => ?_, fun t ht => ?_⟩
  · by_cases h : (t' : ℝ) = selT p₀ x
    · have : t' = selTPos p₀ x := Subtype.ext h
      rw [this]
    · exact (fiberKL_selected_lt p₀ x t' h).le
  · by_contra hne
    have hne' : (t : ℝ) ≠ selT p₀ x := fun h => hne (Subtype.ext h)
    have := fiberKL_selected_lt p₀ x t hne'
    have := ht (selTPos p₀ x)
    linarith

end Selection

section Analyticity

open Topology

/-- `√` is real analytic at every positive point. -/
theorem analyticAt_real_sqrt {y : ℝ} (hy : 0 < y) : AnalyticAt ℝ Real.sqrt y := by
  have hexp : AnalyticAt ℝ (fun z : ℝ => Real.exp (Real.log z * (1 / 2 : ℝ))) y :=
    ((analyticAt_log hy).mul analyticAt_const).rexp'
  refine hexp.congr ?_
  filter_upwards [Ioi_mem_nhds hy] with z hz
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hz]

/-- Coordinates `(γ, α, s, γ₀, n, A, β₀)` of a quotient state and a complete prior. -/
abbrev StatePrior : Type := ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ

/-- The admissible open domain: `α, s > 0` and `n, A, β₀ > 0`. -/
def statePriorDomain : Set StatePrior :=
  {v | 0 < v.2.1 ∧ 0 < v.2.2.1 ∧ 0 < v.2.2.2.2.1 ∧ 0 < v.2.2.2.2.2.1 ∧ 0 < v.2.2.2.2.2.2}

theorem isOpen_statePriorDomain : IsOpen statePriorDomain := by
  have c1 : Continuous (fun v : StatePrior => v.2.1) := by fun_prop
  have c2 : Continuous (fun v : StatePrior => v.2.2.1) := by fun_prop
  have c3 : Continuous (fun v : StatePrior => v.2.2.2.2.1) := by fun_prop
  have c4 : Continuous (fun v : StatePrior => v.2.2.2.2.2.1) := by fun_prop
  have c5 : Continuous (fun v : StatePrior => v.2.2.2.2.2.2) := by fun_prop
  exact (isOpen_lt continuous_const c1).inter ((isOpen_lt continuous_const c2).inter
    ((isOpen_lt continuous_const c3).inter ((isOpen_lt continuous_const c4).inter
    (isOpen_lt continuous_const c5))))

/-- `d` in the coordinates `(γ, α, s, γ₀, n, A, β₀)`. -/
def selDCoord (v : StatePrior) : ℝ :=
  v.2.2.2.2.1 + 2 * v.2.1 * (v.2.2.2.2.2.2 + v.2.2.2.2.1 / 2 * (v.1 - v.2.2.2.1) ^ 2) / v.2.2.1

/-- `t_*` in the coordinates `(γ, α, s, γ₀, n, A, β₀)`. -/
def selTCoord (v : StatePrior) : ℝ := TA v.2.2.2.2.2.1 (selDCoord v)

/-- `ν_sel` in the coordinates `(γ, α, s, γ₀, n, A, β₀)`. -/
def selNuCoord (v : StatePrior) : ℝ := PhiA v.2.2.2.2.2.1 (selDCoord v)

/-- `β_sel` in the coordinates `(γ, α, s, γ₀, n, A, β₀)`. -/
def selBetaCoord (v : StatePrior) : ℝ := v.2.2.1 / (1 + selTCoord v)

/-- The coordinate functions agree with the selection of a quotient state and a complete prior. -/
theorem selTCoord_eq (p₀ : Parameters) (x : QuotientState) :
    selTCoord (x.gamma, x.alpha, x.s, p₀.gamma, p₀.nu, p₀.alpha, p₀.beta) = selT p₀ x := rfl

theorem selNuCoord_eq (p₀ : Parameters) (x : QuotientState) :
    selNuCoord (x.gamma, x.alpha, x.s, p₀.gamma, p₀.nu, p₀.alpha, p₀.beta) = selNu p₀ x := rfl

theorem selBetaCoord_eq (p₀ : Parameters) (x : QuotientState) :
    selBetaCoord (x.gamma, x.alpha, x.s, p₀.gamma, p₀.nu, p₀.alpha, p₀.beta) = selBeta p₀ x := rfl

lemma selDCoord_pos {v : StatePrior} (hv : v ∈ statePriorDomain) : 0 < selDCoord v := by
  obtain ⟨ha, hs, hn, _, hb⟩ := hv
  unfold selDCoord
  positivity

section Coord
variable (v : StatePrior)
lemma an_g : AnalyticAt ℝ (fun w : StatePrior => w.1) v := analyticAt_fst
lemma an_a : AnalyticAt ℝ (fun w : StatePrior => w.2.1) v := analyticAt_fst.comp analyticAt_snd
lemma an_s : AnalyticAt ℝ (fun w : StatePrior => w.2.2.1) v :=
  analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd)
lemma an_g0 : AnalyticAt ℝ (fun w : StatePrior => w.2.2.2.1) v :=
  analyticAt_fst.comp (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd))
lemma an_n : AnalyticAt ℝ (fun w : StatePrior => w.2.2.2.2.1) v :=
  analyticAt_fst.comp (analyticAt_snd.comp (analyticAt_snd.comp (analyticAt_snd.comp
    analyticAt_snd)))
lemma an_A : AnalyticAt ℝ (fun w : StatePrior => w.2.2.2.2.2.1) v :=
  analyticAt_fst.comp (analyticAt_snd.comp (analyticAt_snd.comp (analyticAt_snd.comp
    (analyticAt_snd.comp analyticAt_snd))))
lemma an_b0 : AnalyticAt ℝ (fun w : StatePrior => w.2.2.2.2.2.2) v :=
  analyticAt_snd.comp (analyticAt_snd.comp (analyticAt_snd.comp (analyticAt_snd.comp
    (analyticAt_snd.comp analyticAt_snd))))
end Coord

lemma selDCoord_analyticAt {v : StatePrior} (hv : v ∈ statePriorDomain) :
    AnalyticAt ℝ selDCoord v := by
  have hs : v.2.2.1 ≠ 0 := hv.2.1.ne'
  have hin : AnalyticAt ℝ (fun w : StatePrior =>
      w.2.2.2.2.2.2 + w.2.2.2.2.1 / 2 * (w.1 - w.2.2.2.1) ^ 2) v :=
    (an_b0 v).add (((an_n v).div analyticAt_const (by norm_num)).mul
      (((an_g v).sub (an_g0 v)).pow 2))
  exact (an_n v).add (((analyticAt_const.mul (an_a v)).mul hin).div (an_s v) hs)

lemma selDisc_analyticAt {v : StatePrior} (hv : v ∈ statePriorDomain) :
    AnalyticAt ℝ (fun w : StatePrior => Real.sqrt (selDisc w.2.2.2.2.2.1 (selDCoord w))) v := by
  have hD : 0 < selDisc v.2.2.2.2.2.1 (selDCoord v) := selDisc_pos (selDCoord_pos hv)
  have hd := selDCoord_analyticAt hv
  have hdisc : AnalyticAt ℝ (fun w : StatePrior => selDisc w.2.2.2.2.2.1 (selDCoord w)) v :=
    (((hd.sub (analyticAt_const.mul (an_A v))).sub analyticAt_const).pow 2).add
      (analyticAt_const.mul hd)
  exact AnalyticAt.comp (g := Real.sqrt)
    (f := fun w : StatePrior => selDisc w.2.2.2.2.2.1 (selDCoord w)) (analyticAt_real_sqrt hD) hdisc

/-- `t_*` is real analytic in the quotient state and in the admissible
complete prior parameters. -/
theorem selTCoord_analyticOnNhd : AnalyticOnNhd ℝ selTCoord statePriorDomain := by
  intro v hv
  have hd := selDCoord_analyticAt hv
  have hq := selDisc_analyticAt hv
  have hd0 : 2 * selDCoord v ≠ 0 := by have := selDCoord_pos hv; positivity
  exact ((((analyticAt_const.mul (an_A v)).add analyticAt_const).sub hd).add hq).div
    (analyticAt_const.mul hd) hd0

/-- `ν_sel` is real analytic in the quotient state and in the admissible
complete prior parameters. -/
theorem selNuCoord_analyticOnNhd : AnalyticOnNhd ℝ selNuCoord statePriorDomain := by
  intro v hv
  have hd := selDCoord_analyticAt hv
  have hq := selDisc_analyticAt hv
  exact (((hd.sub (analyticAt_const.mul (an_A v))).sub analyticAt_const).add hq).div
    analyticAt_const (by norm_num)

/-- `β_sel` is real analytic in the quotient state and in the admissible
complete prior parameters. -/
theorem selBetaCoord_analyticOnNhd : AnalyticOnNhd ℝ selBetaCoord statePriorDomain := by
  intro v hv
  have ht := selTCoord_analyticOnNhd v hv
  have hpos : 0 < selTCoord v := TA_pos (selDCoord_pos hv)
  exact (an_s v).div (analyticAt_const.add ht) (by linarith)

end Analyticity

end NIGBottleneck
