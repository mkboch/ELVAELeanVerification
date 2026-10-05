import Mathlib
import PostHoc.E1.M05

/-! -/

noncomputable section

namespace NS1

section S49

def def_043 (A d : ℝ) : ℝ := (d - 2 * A - 1) ^ 2 + 4 * d

def def_044 (A d : ℝ) : ℝ := (2 * A + 1 - d + Real.sqrt (def_043 A d)) / (2 * d)

def def_045 (A d : ℝ) : ℝ := (d - 2 * A - 1 + Real.sqrt (def_043 A d)) / 2

variable {A d : ℝ}

lemma lem_054 (hd : 0 < d) : 0 < def_043 A d := by
  unfold def_043; positivity

lemma lem_055 (hd : 0 < d) : |d - 2 * A - 1| < Real.sqrt (def_043 A d) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) (by unfold def_043; linarith)

lemma lem_056 (hd : 0 < d) : 0 < 2 * A + 1 - d + Real.sqrt (def_043 A d) := by
  have h := lem_055 (A := A) hd
  have := le_abs_self (d - 2 * A - 1)
  linarith

lemma lem_057 (hd : 0 < d) : 0 < d - 2 * A - 1 + Real.sqrt (def_043 A d) := by
  have h := lem_055 (A := A) hd
  have := neg_abs_le (d - 2 * A - 1)
  linarith

theorem thm_092 (hd : 0 < d) : 0 < def_044 A d :=
  div_pos (lem_056 hd) (by positivity)

theorem thm_093 (hd : 0 < d) : 0 < def_045 A d :=
  div_pos (lem_057 hd) two_pos

theorem thm_094 (hd : 0 < d) : def_044 A d * def_045 A d = 1 := by
  have hD := (lem_054 (A := A) hd).le
  unfold def_044 def_045
  rw [div_mul_div_comm]
  have hsq : (2 * A + 1 - d + Real.sqrt (def_043 A d)) * (d - 2 * A - 1 + Real.sqrt (def_043 A d))
      = Real.sqrt (def_043 A d) ^ 2 - (d - 2 * A - 1) ^ 2 := by ring
  rw [hsq, Real.sq_sqrt hD, def_043]
  field_simp
  ring

theorem thm_095 (hd : 0 < d) : def_045 A d = 1 / def_044 A d := by
  rw [eq_div_iff (thm_092 hd).ne', mul_comm, thm_094 hd]

theorem thm_096 (hd : 0 < d) : d * def_044 A d ^ 2 + (d - 2 * A - 1) * def_044 A d - 1 = 0 := by
  have hD := (lem_054 (A := A) hd).le
  unfold def_044
  field_simp
  have hs := Real.sq_sqrt hD
  unfold def_043 at hs ⊢
  nlinarith [hs]

lemma lem_058 {t : ℝ} (ht : 0 < t) :
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

theorem thm_097 (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    d = 2 * A / (1 + t) + 1 / t ↔ t = def_044 A d := by
  rw [lem_058 ht]
  constructor
  · intro h
    have hq := thm_096 (A := A) hd
    have hfac : (t - def_044 A d) * (d * t + d * def_044 A d + (d - 2 * A - 1)) = 0 := by
      linear_combination h - hq
    have hpos : 0 < d * t + d * def_044 A d + (d - 2 * A - 1) := by
      have h2 : d * def_044 A d + (d - 2 * A - 1) = (d - 2 * A - 1 + Real.sqrt (def_043 A d)) / 2 := by
        unfold def_044; field_simp; ring
      have := lem_057 (A := A) hd
      nlinarith [mul_pos hd ht]
    rcases mul_eq_zero.mp hfac with h0 | h0
    · linarith
    · linarith
  · rintro rfl
    exact thm_096 hd

theorem thm_098 (hd : 0 < d) : d = 2 * A / (1 + def_044 A d) + 1 / def_044 A d :=
  (thm_097 hd (thm_092 hd)).mpr rfl

lemma lem_059 {u : ℝ} (hu : 0 < u) : 0 ≤ u - 1 - Real.log u := by
  have := Real.log_le_sub_one_of_pos hu
  linarith

lemma lem_060 {u : ℝ} (hu : 0 < u) (h1 : u ≠ 1) : 0 < u - 1 - Real.log u := by
  have := Real.log_lt_sub_one_of_pos hu h1
  linarith

end S49

section S52

variable (p₀ : str_001) (x : str_002)

def def_046 : ℝ := p₀.nu + 2 * x.alpha * def_040 p₀ x / x.s

theorem thm_099 : 0 < def_046 p₀ x := by
  have := thm_090 p₀ x
  have := x.alpha_pos
  have := x.s_pos
  have := p₀.nu_pos
  unfold def_046
  positivity

def def_047 : ℝ := def_044 p₀.alpha (def_046 p₀ x)

def def_048 : ℝ := def_045 p₀.alpha (def_046 p₀ x)

def def_049 : ℝ := x.s / (1 + def_047 p₀ x)

theorem thm_100 : 0 < def_047 p₀ x := thm_092 (thm_099 p₀ x)

def def_050 : abb_001 := ⟨def_047 p₀ x, thm_100 p₀ x⟩

theorem thm_101 : def_048 p₀ x = 1 / def_047 p₀ x :=
  thm_095 (thm_099 p₀ x)

theorem thm_102 :
    (def_026 x (def_050 p₀ x)).gamma = x.gamma ∧
      (def_026 x (def_050 p₀ x)).nu = def_048 p₀ x ∧
      (def_026 x (def_050 p₀ x)).alpha = x.alpha ∧
      (def_026 x (def_050 p₀ x)).beta = def_049 p₀ x := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  simp only [def_026, def_050]
  rw [thm_101]

theorem thm_103 (t : ℝ) (ht : 0 < t) :
    def_046 p₀ x = 2 * p₀.alpha / (1 + t) + 1 / t ↔ t = def_047 p₀ x :=
  thm_097 (thm_099 p₀ x) ht

def def_051 (t : ℝ) : ℝ :=
  p₀.alpha * ((1 + t) / (1 + def_047 p₀ x) - 1 - Real.log ((1 + t) / (1 + def_047 p₀ x)))
    + (1 / 2) * (t / def_047 p₀ x - 1 - Real.log (t / def_047 p₀ x))

theorem thm_104 (t : ℝ) (ht : 0 < t) :
    def_042 p₀ x t - def_042 p₀ x (def_047 p₀ x) = def_051 p₀ x t := by
  have hts := thm_100 p₀ x
  have h1t : 0 < 1 + t := by linarith
  have h1ts : 0 < 1 + def_047 p₀ x := by linarith
  have hn := p₀.nu_pos
  have hs := x.s_pos
  have hsel := thm_098 (A := p₀.alpha) (thm_099 p₀ x)
  have key : x.alpha * def_040 p₀ x / x.s * (t - def_047 p₀ x) + p₀.nu / 2 * (t - def_047 p₀ x)
      = p₀.alpha * ((1 + t) / (1 + def_047 p₀ x) - 1) + 1 / 2 * (t / def_047 p₀ x - 1) := by
    have hd : x.alpha * def_040 p₀ x / x.s = (def_046 p₀ x - p₀.nu) / 2 := by
      unfold def_046; ring
    rw [hd]
    change (def_046 p₀ x - p₀.nu) / 2 * (t - def_047 p₀ x) + p₀.nu / 2 * (t - def_047 p₀ x) = _
    have hd2 : def_046 p₀ x = 2 * p₀.alpha / (1 + def_047 p₀ x) + 1 / def_047 p₀ x := hsel
    rw [hd2]
    field_simp
    ring
  unfold def_042 def_051
  rw [Real.log_div h1t.ne' h1ts.ne', Real.log_div ht.ne' hts.ne',
    Real.log_mul hn.ne' ht.ne', Real.log_mul hn.ne' hts.ne']
  linear_combination key

theorem thm_105 (t : ℝ) (ht : 0 < t) (hne : t ≠ def_047 p₀ x) : 0 < def_051 p₀ x t := by
  have hts := thm_100 p₀ x
  have h1 := lem_059 (div_pos (by linarith : (0 : ℝ) < 1 + t)
    (by linarith : (0 : ℝ) < 1 + def_047 p₀ x))
  have h2 := lem_060 (div_pos ht hts) (by
    intro h
    exact hne ((div_eq_one_iff_eq hts.ne').mp h))
  have hA := p₀.alpha_pos
  unfold def_051
  nlinarith [mul_nonneg hA.le h1]

theorem thm_106 : def_051 p₀ x (def_047 p₀ x) = 0 := by
  have hts := thm_100 p₀ x
  unfold def_051
  rw [div_self (by linarith), div_self hts.ne']
  simp

theorem thm_107 (t : abb_001) :
    def_041 p₀ x t - def_041 p₀ x (def_050 p₀ x) = def_051 p₀ x t := by
  rw [thm_091, thm_091]
  exact thm_104 p₀ x t t.property

theorem thm_108 (t : abb_001) (hne : (t : ℝ) ≠ def_047 p₀ x) :
    def_041 p₀ x (def_050 p₀ x) < def_041 p₀ x t := by
  have h := thm_107 p₀ x t
  have hg := thm_105 p₀ x t t.property hne
  linarith

theorem thm_109 :
    ∃! t : abb_001, ∀ t' : abb_001, def_041 p₀ x t ≤ def_041 p₀ x t' := by
  refine ⟨def_050 p₀ x, fun t' => ?_, fun t ht => ?_⟩
  · by_cases h : (t' : ℝ) = def_047 p₀ x
    · have : t' = def_050 p₀ x := Subtype.ext h
      rw [this]
    · exact (thm_108 p₀ x t' h).le
  · by_contra hne
    have hne' : (t : ℝ) ≠ def_047 p₀ x := fun h => hne (Subtype.ext h)
    have := thm_108 p₀ x t hne'
    have := ht (def_050 p₀ x)
    linarith

end S52

section S04

open Topology

theorem thm_110 {y : ℝ} (hy : 0 < y) : AnalyticAt ℝ Real.sqrt y := by
  have hexp : AnalyticAt ℝ (fun z : ℝ => Real.exp (Real.log z * (1 / 2 : ℝ))) y :=
    ((analyticAt_log hy).mul analyticAt_const).rexp'
  refine hexp.congr ?_
  filter_upwards [Ioi_mem_nhds hy] with z hz
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hz]

abbrev abb_004 : Type := ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ

def def_052 : Set abb_004 :=
  {v | 0 < v.2.1 ∧ 0 < v.2.2.1 ∧ 0 < v.2.2.2.2.1 ∧ 0 < v.2.2.2.2.2.1 ∧ 0 < v.2.2.2.2.2.2}

theorem thm_111 : IsOpen def_052 := by
  have c1 : Continuous (fun v : abb_004 => v.2.1) := by fun_prop
  have c2 : Continuous (fun v : abb_004 => v.2.2.1) := by fun_prop
  have c3 : Continuous (fun v : abb_004 => v.2.2.2.2.1) := by fun_prop
  have c4 : Continuous (fun v : abb_004 => v.2.2.2.2.2.1) := by fun_prop
  have c5 : Continuous (fun v : abb_004 => v.2.2.2.2.2.2) := by fun_prop
  exact (isOpen_lt continuous_const c1).inter ((isOpen_lt continuous_const c2).inter
    ((isOpen_lt continuous_const c3).inter ((isOpen_lt continuous_const c4).inter
    (isOpen_lt continuous_const c5))))

def def_053 (v : abb_004) : ℝ :=
  v.2.2.2.2.1 + 2 * v.2.1 * (v.2.2.2.2.2.2 + v.2.2.2.2.1 / 2 * (v.1 - v.2.2.2.1) ^ 2) / v.2.2.1

def def_054 (v : abb_004) : ℝ := def_044 v.2.2.2.2.2.1 (def_053 v)

def def_055 (v : abb_004) : ℝ := def_045 v.2.2.2.2.2.1 (def_053 v)

def def_056 (v : abb_004) : ℝ := v.2.2.1 / (1 + def_054 v)

theorem thm_112 (p₀ : str_001) (x : str_002) :
    def_054 (x.gamma, x.alpha, x.s, p₀.gamma, p₀.nu, p₀.alpha, p₀.beta) = def_047 p₀ x := rfl

theorem thm_113 (p₀ : str_001) (x : str_002) :
    def_055 (x.gamma, x.alpha, x.s, p₀.gamma, p₀.nu, p₀.alpha, p₀.beta) = def_048 p₀ x := rfl

theorem thm_114 (p₀ : str_001) (x : str_002) :
    def_056 (x.gamma, x.alpha, x.s, p₀.gamma, p₀.nu, p₀.alpha, p₀.beta) = def_049 p₀ x := rfl

lemma lem_061 {v : abb_004} (hv : v ∈ def_052) : 0 < def_053 v := by
  obtain ⟨ha, hs, hn, _, hb⟩ := hv
  unfold def_053
  positivity

section S11
variable (v : abb_004)
lemma lem_062 : AnalyticAt ℝ (fun w : abb_004 => w.1) v := analyticAt_fst
lemma lem_063 : AnalyticAt ℝ (fun w : abb_004 => w.2.1) v := analyticAt_fst.comp analyticAt_snd
lemma lem_064 : AnalyticAt ℝ (fun w : abb_004 => w.2.2.1) v :=
  analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd)
lemma lem_065 : AnalyticAt ℝ (fun w : abb_004 => w.2.2.2.1) v :=
  analyticAt_fst.comp (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd))
lemma lem_066 : AnalyticAt ℝ (fun w : abb_004 => w.2.2.2.2.1) v :=
  analyticAt_fst.comp (analyticAt_snd.comp (analyticAt_snd.comp (analyticAt_snd.comp
    analyticAt_snd)))
lemma lem_067 : AnalyticAt ℝ (fun w : abb_004 => w.2.2.2.2.2.1) v :=
  analyticAt_fst.comp (analyticAt_snd.comp (analyticAt_snd.comp (analyticAt_snd.comp
    (analyticAt_snd.comp analyticAt_snd))))
lemma lem_068 : AnalyticAt ℝ (fun w : abb_004 => w.2.2.2.2.2.2) v :=
  analyticAt_snd.comp (analyticAt_snd.comp (analyticAt_snd.comp (analyticAt_snd.comp
    (analyticAt_snd.comp analyticAt_snd))))
end S11

lemma lem_069 {v : abb_004} (hv : v ∈ def_052) :
    AnalyticAt ℝ def_053 v := by
  have hs : v.2.2.1 ≠ 0 := hv.2.1.ne'
  have hin : AnalyticAt ℝ (fun w : abb_004 =>
      w.2.2.2.2.2.2 + w.2.2.2.2.1 / 2 * (w.1 - w.2.2.2.1) ^ 2) v :=
    (lem_068 v).add (((lem_066 v).div analyticAt_const (by norm_num)).mul
      (((lem_062 v).sub (lem_065 v)).pow 2))
  exact (lem_066 v).add (((analyticAt_const.mul (lem_063 v)).mul hin).div (lem_064 v) hs)

lemma lem_070 {v : abb_004} (hv : v ∈ def_052) :
    AnalyticAt ℝ (fun w : abb_004 => Real.sqrt (def_043 w.2.2.2.2.2.1 (def_053 w))) v := by
  have hD : 0 < def_043 v.2.2.2.2.2.1 (def_053 v) := lem_054 (lem_061 hv)
  have hd := lem_069 hv
  have hdisc : AnalyticAt ℝ (fun w : abb_004 => def_043 w.2.2.2.2.2.1 (def_053 w)) v :=
    (((hd.sub (analyticAt_const.mul (lem_067 v))).sub analyticAt_const).pow 2).add
      (analyticAt_const.mul hd)
  exact AnalyticAt.comp (g := Real.sqrt)
    (f := fun w : abb_004 => def_043 w.2.2.2.2.2.1 (def_053 w)) (thm_110 hD) hdisc

theorem thm_115 : AnalyticOnNhd ℝ def_054 def_052 := by
  intro v hv
  have hd := lem_069 hv
  have hq := lem_070 hv
  have hd0 : 2 * def_053 v ≠ 0 := by have := lem_061 hv; positivity
  exact ((((analyticAt_const.mul (lem_067 v)).add analyticAt_const).sub hd).add hq).div
    (analyticAt_const.mul hd) hd0

theorem thm_116 : AnalyticOnNhd ℝ def_055 def_052 := by
  intro v hv
  have hd := lem_069 hv
  have hq := lem_070 hv
  exact (((hd.sub (analyticAt_const.mul (lem_067 v))).sub analyticAt_const).add hq).div
    analyticAt_const (by norm_num)

theorem thm_117 : AnalyticOnNhd ℝ def_056 def_052 := by
  intro v hv
  have ht := thm_115 v hv
  have hpos : 0 < def_054 v := thm_092 (lem_061 hv)
  exact (lem_064 v).div (analyticAt_const.add ht) (by linarith)

end S04

end NS1
