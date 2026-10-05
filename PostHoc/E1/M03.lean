import Mathlib
import PostHoc.E1.M02

/-! -/

noncomputable section

namespace NS1

def def_022 (p : str_001) : ℝ :=
  p.beta * (1 + 1 / p.nu)

def def_023 (p : str_001) : ℝ :=
  def_022 p / p.alpha

theorem thm_031 (p : str_001) :
    0 < 1 + 1 / p.nu :=
  add_pos zero_lt_one (one_div_pos.mpr p.nu_pos)

theorem thm_032 (p : str_001) :
    0 < def_022 p :=
  mul_pos p.beta_pos (thm_031 p)

theorem thm_033 (p : str_001) :
    0 < def_023 p :=
  div_pos (thm_032 p) p.alpha_pos

@[ext]
structure str_002 where
  gamma : ℝ
  alpha : ℝ
  s : ℝ
  alpha_pos : 0 < alpha
  s_pos : 0 < s

def def_024 (p : str_001) : str_002 where
  gamma := p.gamma
  alpha := p.alpha
  s := def_022 p
  alpha_pos := p.alpha_pos
  s_pos := thm_032 p

def def_025 (p : str_001) : abb_001 :=
  ⟨1 / p.nu, one_div_pos.mpr p.nu_pos⟩

def def_026 (x : str_002) (t : abb_001) : str_001 where
  gamma := x.gamma
  nu := 1 / (t : ℝ)
  alpha := x.alpha
  beta := x.s / (1 + (t : ℝ))
  nu_pos := one_div_pos.mpr t.property
  alpha_pos := x.alpha_pos
  beta_pos := div_pos x.s_pos (add_pos zero_lt_one t.property)

def def_027 (x : str_002) : Set str_001 :=
  {p | def_024 p = x}

private theorem thm_034 {p q : str_001}
    (hgamma : p.gamma = q.gamma) (hnu : p.nu = q.nu)
    (halpha : p.alpha = q.alpha) (hbeta : p.beta = q.beta) :
    p = q := by
  cases p
  cases q
  cases hgamma
  cases hnu
  cases halpha
  cases hbeta
  rfl

theorem thm_035 (p q : str_001) :
    def_024 p = def_024 q ↔
      p.gamma = q.gamma ∧
      p.alpha = q.alpha ∧
      p.beta * (1 + 1 / p.nu) = q.beta * (1 + 1 / q.nu) := by
  constructor
  · intro h
    exact ⟨congrArg str_002.gamma h,
      congrArg str_002.alpha h, congrArg str_002.s h⟩
  · rintro ⟨hgamma, halpha, hs⟩
    exact str_002.ext hgamma halpha hs

theorem thm_036
    (x : str_002) (t : abb_001) :
    def_024 (def_026 x t) = x := by
  apply str_002.ext
  · rfl
  · rfl
  · change
      (x.s / (1 + (t : ℝ))) * (1 + 1 / (1 / (t : ℝ))) = x.s
    have hden : 1 + (t : ℝ) ≠ 0 :=
      ne_of_gt (add_pos zero_lt_one t.property)
    simp only [one_div, inv_inv]
    exact div_mul_cancel₀ x.s hden

theorem thm_037
    (x : str_002) (t : abb_001) :
    def_025 (def_026 x t) = t := by
  apply Subtype.ext
  change 1 / (1 / (t : ℝ)) = (t : ℝ)
  simp only [one_div, inv_inv]

theorem thm_038 (p : str_001) :
    def_026 (def_024 p) (def_025 p) = p := by
  apply thm_034
  · rfl
  · change 1 / (1 / p.nu) = p.nu
    simp only [one_div, inv_inv]
  · rfl
  · change
      (p.beta * (1 + 1 / p.nu)) / (1 + 1 / p.nu) = p.beta
    exact mul_div_cancel_right₀ p.beta (ne_of_gt (thm_031 p))

theorem thm_039 :
    Function.Surjective def_024 := by
  intro x
  refine ⟨def_026 x ⟨1, zero_lt_one⟩, ?_⟩
  exact thm_036 x ⟨1, zero_lt_one⟩

theorem thm_040 (x : str_002) (p : str_001) :
    p ∈ def_027 x ↔
      ∃ t : abb_001, def_026 x t = p := by
  constructor
  · intro hp
    have hx : def_024 p = x := hp
    refine ⟨def_025 p, ?_⟩
    rw [← hx]
    exact thm_038 p
  · rintro ⟨t, rfl⟩
    exact thm_036 x t

theorem thm_041 (x : str_002) :
    def_027 x = Set.range (def_026 x) := by
  apply Set.ext
  intro p
  exact thm_040 x p

theorem thm_042 (x : str_002) :
    Function.Injective (def_026 x) := by
  intro t u h
  have hc := congrArg def_025 h
  simpa only [thm_037] using hc

theorem thm_043 (x : str_002) (p : str_001)
    (hp : p ∈ def_027 x) :
    ∃! t : abb_001, def_026 x t = p := by
  have hx : def_024 p = x := hp
  refine ⟨def_025 p, ?_, ?_⟩
  · rw [← hx]
    exact thm_038 p
  · intro t ht
    have hc := congrArg def_025 ht
    simpa only [thm_037] using hc

theorem thm_044 (p q : str_001) :
    p = q ↔
      def_024 p = def_024 q ∧
      def_025 p = def_025 q := by
  constructor
  · intro h
    subst q
    exact ⟨rfl, rfl⟩
  · rintro ⟨hx, ht⟩
    calc
      p = def_026 (def_024 p) (def_025 p) :=
        (thm_038 p).symm
      _ = def_026 (def_024 q) (def_025 q) := by
        rw [hx, ht]
      _ = q := thm_038 q

def def_028 : str_001 ≃ str_002 × abb_001 where
  toFun p := (def_024 p, def_025 p)
  invFun u := def_026 u.1 u.2
  left_inv := thm_038
  right_inv u := by
    rcases u with ⟨x, t⟩
    change
      (def_024 (def_026 x t),
        def_025 (def_026 x t)) = (x, t)
    rw [thm_036, thm_037]

theorem thm_045
    (x : str_002) (t : abb_001) :
    def_023 (def_026 x t) = x.s / x.alpha := by
  have hs := congrArg str_002.s (thm_036 x t)
  change def_022 (def_026 x t) = x.s at hs
  change def_022 (def_026 x t) / x.alpha = x.s / x.alpha
  rw [hs]

theorem thm_046 (p : str_001) :
    MeasureTheory.Measure.map
        (fun v : ℝ => (1 + 1 / p.nu) * v) (def_005 p) =
      def_002 ⟨p.alpha, p.alpha_pos⟩
        ⟨def_022 p, thm_032 p⟩ := by
  have h :=
    thm_030
      (⟨p.alpha, p.alpha_pos⟩ : abb_001)
      (⟨p.beta, p.beta_pos⟩ : abb_001)
      (⟨1 + 1 / p.nu, thm_031 p⟩ : abb_001)
  simpa only [def_005, def_022, mul_comm] using h

private def def_029 (x : str_002) : ℝ :=
  Real.Gamma (x.alpha + 1 / 2) /
    (Real.Gamma x.alpha * Real.sqrt (2 * Real.pi * x.s))

private theorem thm_047 (x : str_002) :
    0 < def_029 x := by
  have hs := x.s_pos
  unfold def_029
  apply div_pos
  · exact Real.Gamma_pos_of_pos (by linarith [x.alpha_pos])
  · exact mul_pos (Real.Gamma_pos_of_pos x.alpha_pos)
      (Real.sqrt_pos.mpr (by positivity))

private theorem thm_048 (x : str_002) (z : ℝ) :
    0 < 1 + (z - x.gamma) ^ 2 / (2 * x.s) := by
  have hs := x.s_pos
  positivity

def def_030 (x : str_002) (z : ℝ) : ℝ :=
  def_029 x *
    (1 + (z - x.gamma) ^ 2 / (2 * x.s)) ^ (-x.alpha - 1 / 2)

theorem thm_049 (x : str_002) (z : ℝ) :
    0 < def_030 x z :=
  mul_pos (thm_047 x)
    (Real.rpow_pos_of_pos (thm_048 x z) _)

theorem thm_050 (x : str_002) (z : ℝ)
    (hz : z ≠ x.gamma) :
    def_030 x z <
      def_030 x x.gamma := by
  have hsq : 0 < (z - x.gamma) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hz)
  have hdiv : 0 < (z - x.gamma) ^ 2 / (2 * x.s) :=
    div_pos hsq (mul_pos (by norm_num) x.s_pos)
  have hbase : 1 < 1 + (z - x.gamma) ^ 2 / (2 * x.s) := by
    linarith
  have hexponent : -x.alpha - (1 / 2 : ℝ) < 0 := by
    linarith [x.alpha_pos]
  have hpow :
      (1 + (z - x.gamma) ^ 2 / (2 * x.s)) ^ (-x.alpha - 1 / 2) < 1 := by
    rw [Real.rpow_def_of_pos (thm_048 x z)]
    exact Real.exp_lt_one_iff.mpr
      (mul_neg_of_pos_of_neg (Real.log_pos hbase) hexponent)
  calc
    def_030 x z =
        def_029 x *
          (1 + (z - x.gamma) ^ 2 / (2 * x.s)) ^ (-x.alpha - 1 / 2) := rfl
    _ < def_029 x * 1 :=
      mul_lt_mul_of_pos_left hpow (thm_047 x)
    _ = def_030 x x.gamma := by
      simp [def_030]

theorem thm_051 (x : str_002) (z : ℝ) :
    def_030 x z = def_030 x x.gamma ↔
      z = x.gamma := by
  constructor
  · intro h
    by_contra hz
    exact (ne_of_lt (thm_050 x z hz)) h
  · intro h
    subst z
    rfl

private theorem thm_052 (x : str_002) (z : ℝ) :
    Real.log (def_030 x z) =
      Real.log (def_029 x) +
        (-x.alpha - 1 / 2) *
          Real.log (1 + (z - x.gamma) ^ 2 / (2 * x.s)) := by
  unfold def_030
  rw [Real.log_mul (ne_of_gt (thm_047 x))
    (ne_of_gt (Real.rpow_pos_of_pos (thm_048 x z) _)),
    Real.log_rpow (thm_048 x z)]

private theorem thm_053
    (x : str_002) (z : ℝ) :
    HasDerivAt (fun u : ℝ => Real.log (def_030 x u))
      (-((2 * x.alpha + 1) * (z - x.gamma)) /
        (2 * x.s + (z - x.gamma) ^ 2)) z := by
  have hbase :
      HasDerivAt (fun u : ℝ => 1 + (u - x.gamma) ^ 2 / (2 * x.s))
        ((2 * (z - x.gamma)) / (2 * x.s)) z := by
    convert ((((hasDerivAt_id z).sub_const x.gamma).pow 2).div_const
      (2 * x.s)).const_add 1 using 1 <;> (dsimp; try ring)
  have haux :=
    ((hbase.log (ne_of_gt (thm_048 x z))).const_mul
      (-x.alpha - 1 / 2)).const_add (Real.log (def_029 x))
  have hfun :
      (fun u : ℝ => Real.log (def_030 x u)) =
        (fun u : ℝ => Real.log (def_029 x) +
          (-x.alpha - 1 / 2) *
            Real.log (1 + (u - x.gamma) ^ 2 / (2 * x.s))) :=
    funext (thm_052 x)
  have hs0 : x.s ≠ 0 := ne_of_gt x.s_pos
  have hd0 : 2 * x.s + (z - x.gamma) ^ 2 ≠ 0 :=
    ne_of_gt (by nlinarith [x.s_pos, sq_nonneg (z - x.gamma)])
  have hb0 : 1 + (z - x.gamma) ^ 2 / (2 * x.s) ≠ 0 :=
    ne_of_gt (thm_048 x z)
  rw [hfun]
  convert haux using 1
  field_simp [hs0, hd0, hb0]
  ring

theorem thm_054 :
    Function.Injective def_030 := by
  intro x y h
  have hgamma : x.gamma = y.gamma := by
    by_contra hne
    have hxy := thm_050 y x.gamma hne
    have hyx := thm_050 x y.gamma (Ne.symm hne)
    rw [h] at hyx
    exact lt_asymm hxy hyx
  have hderiv (z : ℝ) :
      -((2 * x.alpha + 1) * (z - x.gamma)) /
          (2 * x.s + (z - x.gamma) ^ 2) =
        -((2 * y.alpha + 1) * (z - y.gamma)) /
          (2 * y.s + (z - y.gamma) ^ 2) := by
    have hy := thm_053 y z
    rw [← h] at hy
    exact (thm_053 x z).unique hy
  have h1 := hderiv (x.gamma + 1)
  have h2 := hderiv (x.gamma + 2)
  simp only [← hgamma] at h1 h2
  have hshift1 : x.gamma + 1 - x.gamma = (1 : ℝ) := by ring
  have hshift2 : x.gamma + 2 - x.gamma = (2 : ℝ) := by ring
  simp only [hshift1, one_pow, mul_one] at h1
  simp only [hshift2, show (2 : ℝ) ^ 2 = 4 by norm_num] at h2
  have hsx1 : 2 * x.s + 1 ≠ 0 :=
    ne_of_gt (by linarith [x.s_pos])
  have hsy1 : 2 * y.s + 1 ≠ 0 :=
    ne_of_gt (by linarith [y.s_pos])
  have hsx4 : 2 * x.s + 4 ≠ 0 :=
    ne_of_gt (by linarith [x.s_pos])
  have hsy4 : 2 * y.s + 4 ≠ 0 :=
    ne_of_gt (by linarith [y.s_pos])
  have hc1 :
      (2 * x.alpha + 1) * (2 * y.s + 1) =
        (2 * y.alpha + 1) * (2 * x.s + 1) := by
    have hc := (div_eq_div_iff hsx1 hsy1).mp h1
    nlinarith [hc]
  have hc2 :
      (2 * x.alpha + 1) * (2 * y.s + 4) =
        (2 * y.alpha + 1) * (2 * x.s + 4) := by
    have hc := (div_eq_div_iff hsx4 hsy4).mp h2
    nlinarith [hc]
  have halpha : x.alpha = y.alpha := by
    nlinarith [hc1, hc2]
  have hc1' :
      (2 * x.alpha + 1) * (2 * y.s + 1) =
        (2 * x.alpha + 1) * (2 * x.s + 1) := by
    simpa only [← halpha] using hc1
  have ha0 : 2 * x.alpha + 1 ≠ 0 :=
    ne_of_gt (by linarith [x.alpha_pos])
  have he := mul_left_cancel₀ ha0 hc1'
  have hs : x.s = y.s := by
    linarith
  exact str_002.ext hgamma halpha hs

theorem thm_055 (x y : str_002) :
    (∀ z : ℝ, def_030 x z =
      def_030 y z) ↔ x = y := by
  constructor
  · intro h
    exact thm_054 (funext h)
  · rintro rfl
    intro z
    rfl

theorem thm_056 (p q : str_001) :
    (∀ z : ℝ, def_030 (def_024 p) z =
      def_030 (def_024 q) z) ↔
      p.gamma = q.gamma ∧
      p.alpha = q.alpha ∧
      p.beta * (1 + 1 / p.nu) = q.beta * (1 + 1 / q.nu) :=
  (thm_055
    (def_024 p) (def_024 q)).trans
      (thm_035 p q)

section S55

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

def def_031 (n m s2 y : ℝ) : ℝ :=
  Real.Gamma ((n + 1) / 2) / (Real.Gamma (n / 2) * Real.sqrt (n * π * s2))
    * (1 + (y - m) ^ 2 / (n * s2)) ^ (-((n + 1) / 2))

lemma lem_001 (a b k m y t : ℝ) (ha : 0 < a) (hk : 0 < k) (ht : 0 < t) :
    gammaPDFReal a b t * gaussianPDFReal m (k / t).toNNReal y
      = (b ^ a / (Real.Gamma a * Real.sqrt (2 * π * k)))
          * (t ^ ((a + 1 / 2) - 1) * Real.exp (-((b + (y - m) ^ 2 / (2 * k)) * t))) := by
  have hkt : 0 ≤ k / t := by positivity
  simp only [gammaPDFReal, ht.le, ↓reduceIte]
  rw [gaussianPDFReal, Real.coe_toNNReal _ hkt]
  have hsq : Real.sqrt (2 * π * (k / t)) = Real.sqrt (2 * π * k) / Real.sqrt t := by
    rw [← Real.sqrt_div' _ ht.le]; congr 1; ring
  have hpow : t ^ ((a + 1 / 2) - 1) = t ^ (a - 1) * Real.sqrt t := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]; congr 1; ring
  have hexp : Real.exp (-(b * t)) * Real.exp (-(y - m) ^ 2 / (2 * (k / t)))
      = Real.exp (-((b + (y - m) ^ 2 / (2 * k)) * t)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [hsq, hpow, ← hexp]
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs2 : 0 < Real.sqrt (2 * π * k) := Real.sqrt_pos.mpr (by positivity)
  have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  field_simp

theorem thm_057 (a b k m y : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    ∫ t in Ioi 0, gammaPDFReal a b t * gaussianPDFReal m (k / t).toNNReal y
      = def_031 (2 * a) m (k * b / a) y := by
  set u : ℝ := (y - m) ^ 2 / (2 * k * b) with hu
  have hu0 : 0 ≤ u := by positivity
  have hr : b + (y - m) ^ 2 / (2 * k) = b * (1 + u) := by
    rw [hu]; field_simp
  have hrpos : 0 < b + (y - m) ^ 2 / (2 * k) := by positivity
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => lem_001 a b k m y t ha hk ht),
    integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hrpos, hr]
  have h1u : 0 < 1 + u := by linarith
  unfold def_031
  have e1 : (2 * a + 1) / 2 = a + 1 / 2 := by ring
  have e2 : 2 * a / 2 = a := by ring
  have e3 : 2 * a * π * (k * b / a) = (2 * π * k) * b := by field_simp
  have e4 : (y - m) ^ 2 / (2 * a * (k * b / a)) = u := by rw [hu]; field_simp
  rw [e1, e2, e3, e4, Real.sqrt_mul (by positivity), one_div, Real.inv_rpow (by positivity),
    Real.mul_rpow hb.le h1u.le, Real.rpow_neg h1u.le]
  have hbp : b ^ (a + 1 / 2) = b ^ a * Real.sqrt b := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hb]
  rw [hbp]
  have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hs2 : 0 < Real.sqrt (2 * π * k) := Real.sqrt_pos.mpr (by positivity)
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hba : 0 < b ^ a := Real.rpow_pos_of_pos hb a
  have hup : 0 < (1 + u) ^ (a + 1 / 2) := Real.rpow_pos_of_pos h1u _
  field_simp
  rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * π * k),
    Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * π)]

lemma lem_002 (n m s2 y : ℝ) (hn : 0 < n) (hs : 0 < s2) :
    0 < def_031 n m s2 y := by
  unfold def_031
  have h1 : 0 < Real.Gamma ((n + 1) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have h2 : 0 < Real.Gamma (n / 2) := Real.Gamma_pos_of_pos (by positivity)
  have h3 : 0 < Real.sqrt (n * π * s2) := Real.sqrt_pos.mpr (by positivity)
  have h4 : 0 < (1 + (y - m) ^ 2 / (n * s2)) ^ (-((n + 1) / 2)) :=
    Real.rpow_pos_of_pos (by positivity) _
  positivity

lemma lem_003 (a b k m y : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    ∫⁻ t, gammaPDF a b t * gaussianPDF m (k / t).toNNReal y
      = ENNReal.ofReal (def_031 (2 * a) m (k * b / a) y) := by
  have hf : (fun t => gammaPDF a b t * gaussianPDF m (k / t).toNNReal y)
      = fun t => ENNReal.ofReal (gammaPDFReal a b t * gaussianPDFReal m (k / t).toNNReal y) := by
    funext t
    rw [gammaPDF, gaussianPDF, ENNReal.ofReal_mul (gammaPDFReal_nonneg ha hb t)]
  rw [hf, ← lintegral_add_compl _ (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ))),
    Set.compl_Ioi]
  have hzero : ∫⁻ t in Iic 0,
      ENNReal.ofReal (gammaPDFReal a b t * gaussianPDFReal m (k / t).toNNReal y) = 0 := by
    rw [← setLIntegral_congr Iio_ae_eq_Iic]
    rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0)
      (fun t (ht : t < 0) => by simp [gammaPDFReal, not_le.mpr ht])]
    simp
  rw [hzero, add_zero]
  have hint_val := thm_057 a b k m y ha hb hk
  have hpos := lem_002 (2 * a) m (k * b / a) y (by positivity) (by positivity)
  have hint : Integrable
      (fun t => gammaPDFReal a b t * gaussianPDFReal m (k / t).toNNReal y)
      (volume.restrict (Ioi 0)) :=
    Integrable.of_integral_ne_zero (by rw [hint_val]; exact hpos.ne')
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun t => mul_nonneg (gammaPDFReal_nonneg ha hb t)
      (gaussianPDFReal_nonneg _ _ _)), hint_val]

def def_032 (n m s2 : ℝ) : Measure ℝ :=
  volume.withDensity (fun y => ENNReal.ofReal (def_031 n m s2 y))

lemma lem_004 (m k : ℝ) :
    Measurable (fun t : ℝ => gaussianReal m (k / t).toNNReal) :=
  measurable_gaussianReal.comp
    (measurable_const.prodMk ((measurable_const.div measurable_id).real_toNNReal))

theorem thm_058 (a b k m : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    (gammaMeasure a b).bind (fun t => gaussianReal m (k / t).toNNReal)
      = def_032 (2 * a) m (k * b / a) := by
  ext s hs
  have hmeasG : Measurable (gammaPDF a b) := (measurable_gammaPDFReal a b).ennreal_ofReal
  have hmk : Measurable (fun t : ℝ => gaussianReal m (k / t).toNNReal s) :=
    (Measure.measurable_coe hs).comp (lem_004 m k)
  rw [Measure.bind_apply hs (lem_004 m k).aemeasurable, def_032,
    withDensity_apply _ hs, gammaMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hmeasG hmk]
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
    have : (volume : Measure ℝ) {0} = 0 := measure_singleton 0
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp this] with t ht
    simpa using ht
  have hstep : ∀ᵐ t ∂(volume : Measure ℝ),
      (gammaPDF a b * fun t => gaussianReal m (k / t).toNNReal s) t
        = ∫⁻ y in s, gammaPDF a b t * gaussianPDF m (k / t).toNNReal y := by
    filter_upwards [hae] with t ht
    rcases lt_or_gt_of_ne ht with hneg | hpos
    · have h0 : gammaPDF a b t = 0 := gammaPDF_of_neg hneg
      simp [h0]
    · have hv : (k / t).toNNReal ≠ 0 := by
        rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
      simp only [Pi.mul_apply]
      rw [gaussianReal_apply _ hv, lintegral_const_mul _ (measurable_gaussianPDF _ _)]
  rw [lintegral_congr_ae hstep]
  have hmeas2 : Measurable (Function.uncurry
      (fun (t y : ℝ) => gammaPDF a b t * gaussianPDF m (k / t).toNNReal y)) := by
    refine (hmeasG.comp measurable_fst).mul ?_
    exact measurable_uncurry_gaussianPDF.comp (measurable_const.prodMk
      (((measurable_const.div measurable_fst).real_toNNReal).prodMk measurable_snd))
  rw [lintegral_lintegral_swap hmeas2.aemeasurable]
  refine lintegral_congr fun y => ?_
  exact lem_003 a b k m y ha hb hk

lemma lem_005 (μ ν : Measure ℝ) [SFinite ν]
    (hf : AEMeasurable (fun x : ℝ => ν.map (x + ·)) μ) :
    μ.bind (fun x => ν.map (x + ·)) = μ ∗ ν := by
  ext s hs
  rw [Measure.bind_apply hs hf, ← lintegral_indicator_one hs,
    Measure.lintegral_conv (measurable_one.indicator hs)]
  refine lintegral_congr fun x => ?_
  rw [Measure.map_apply (measurable_const_add x) hs,
    ← lintegral_indicator_one (measurable_const_add x hs)]
  rfl

theorem thm_059 (m : ℝ) (v1 v2 : ℝ≥0) :
    (gaussianReal m v1).bind (fun z => gaussianReal z v2) = gaussianReal m (v1 + v2) := by
  have hk : (fun z : ℝ => gaussianReal z v2) = fun z => (gaussianReal 0 v2).map (z + ·) := by
    funext z
    rw [gaussianReal_map_const_add, zero_add]
  have hmeas : Measurable (fun z : ℝ => gaussianReal z v2) :=
    measurable_gaussianReal.comp (measurable_id.prodMk measurable_const)
  rw [hk, lem_005 _ _ (hk ▸ hmeas.aemeasurable),
    gaussianReal_conv_gaussianReal, add_zero]

def def_033 (a b : ℝ) : Measure ℝ :=
  (gammaMeasure a b).map (fun t => t⁻¹)

def def_034 (gamma nu alpha beta : ℝ) : Measure ℝ :=
  (def_033 alpha beta).bind
    (fun s => (gaussianReal gamma (s / nu).toNNReal).bind
      (fun m => gaussianReal m s.toNNReal))

lemma lem_006 {μ : Measure ℝ} {f : ℝ → ℝ} {g : ℝ → Measure ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    (μ.map f).bind g = μ.bind (g ∘ f) := by
  ext s hs
  rw [Measure.bind_apply hs hg.aemeasurable, Measure.bind_apply hs (hg.comp hf).aemeasurable,
    lintegral_map (f := fun a => g a s) ((Measure.measurable_coe hs).comp hg) hf]
  rfl

lemma lem_007 (a b : ℝ) : ∀ᵐ t ∂(gammaMeasure a b), 0 < t := by
  rw [ae_iff]
  have hset : {t : ℝ | ¬ 0 < t} = Iic 0 := by ext t; simp
  rw [hset, gammaMeasure, withDensity_apply _ measurableSet_Iic,
    ← setLIntegral_congr Iio_ae_eq_Iic]
  exact lintegral_gammaPDF_of_nonpos le_rfl

theorem thm_060 (gamma nu alpha beta : ℝ)
    (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta) :
    def_034 gamma nu alpha beta
      = def_032 (2 * alpha) gamma (beta * (1 + 1 / nu) / alpha) := by
  have hinner : (fun s : ℝ => (gaussianReal gamma (s / nu).toNNReal).bind
        (fun m => gaussianReal m s.toNNReal))
      = fun s => gaussianReal gamma ((s / nu).toNNReal + s.toNNReal) := by
    funext s
    exact thm_059 gamma _ _
  have hg : Measurable (fun s : ℝ => gaussianReal gamma ((s / nu).toNNReal + s.toNNReal)) :=
    measurable_gaussianReal.comp (measurable_const.prodMk
      (((measurable_id.div_const nu).real_toNNReal).add measurable_id.real_toNNReal))
  rw [def_034, hinner, def_033, lem_006 measurable_inv hg]
  have hae : (fun s : ℝ => gaussianReal gamma ((s / nu).toNNReal + s.toNNReal)) ∘ (fun t => t⁻¹)
      =ᵐ[gammaMeasure alpha beta]
        fun t => gaussianReal gamma ((1 + 1 / nu) / t).toNNReal := by
    filter_upwards [lem_007 alpha beta] with t ht
    have h1 : 0 ≤ t⁻¹ / nu := by positivity
    have h2 : 0 ≤ t⁻¹ := by positivity
    simp only [Function.comp_apply]
    rw [← Real.toNNReal_add h1 h2]
    congr 2
    field_simp
    ring
  rw [Measure.bind_congr_right hae,
    thm_058 _ _ _ _ halpha hbeta (by positivity)]
  congr 1
  ring

theorem thm_061 (n m s2 : ℝ) (hn : 0 < n) (hs2 : 0 < s2) :
    IsProbabilityMeasure (def_032 n m s2) := by
  have hn2 : 2 * (n / 2) = n := by ring
  have hmix2 := thm_058 (n / 2) (n / 2) s2 m
    (by positivity) (by positivity) hs2
  rw [hn2, show s2 * (n / 2) / (n / 2) = s2 by field_simp] at hmix2
  rw [← hmix2]
  have : IsProbabilityMeasure (gammaMeasure (n / 2) (n / 2)) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by positivity)
  constructor
  rw [Measure.bind_apply MeasurableSet.univ (lem_004 m s2).aemeasurable]
  have h1 : ∀ t : ℝ, (gaussianReal m (s2 / t).toNNReal) Set.univ = 1 := fun t => by
    have := instIsProbabilityMeasureGaussianReal m (s2 / t).toNNReal
    exact measure_univ
  simp [h1]

lemma lem_008 (a b : ℝ) (A : Set ℝ) :
    ∫⁻ t in A, gammaPDF a b t = ∫⁻ t in A ∩ Ioi 0, gammaPDF a b t := by
  rw [← lintegral_inter_add_sdiff _ A (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
  have hzero : ∫⁻ t in A \ Ioi 0, gammaPDF a b t = 0 := by
    refine le_antisymm ?_ bot_le
    calc ∫⁻ t in A \ Ioi 0, gammaPDF a b t ≤ ∫⁻ t in Iic 0, gammaPDF a b t :=
          lintegral_mono_set fun t ht => by
            simpa using ht.2
      _ = 0 := by
          rw [← setLIntegral_congr Iio_ae_eq_Iic]
          exact lintegral_gammaPDF_of_nonpos le_rfl
  rw [hzero, add_zero]

lemma lem_009 (a b : ℝ) : Measurable (def_001 a b) := by
  unfold def_001
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  simp only [Real.rpow_eq_pow]
  fun_prop

theorem thm_062 (a b : abb_001) :
    def_002 a b = def_033 a b := by
  have ha : 0 < (a : ℝ) := a.property
  have hmeasIG : Measurable fun x => ENNReal.ofReal (def_001 a b x) :=
    (lem_009 _ _).ennreal_ofReal
  ext s hs
  rw [def_002, def_033, Measure.map_apply measurable_inv hs, gammaMeasure,
    withDensity_apply _ (measurable_inv hs), withDensity_apply _ hs,
    lem_008 _ _ _]
  have hRHS : ∫⁻ x in s, ENNReal.ofReal (def_001 a b x)
      = ∫⁻ x in s ∩ Ioi 0, ENNReal.ofReal (def_001 a b x) := by
    rw [← lintegral_inter_add_sdiff _ s (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    have hzero : ∫⁻ x in s \ Ioi 0, ENNReal.ofReal (def_001 a b x) = 0 := by
      rw [setLIntegral_congr_fun (hs.diff measurableSet_Ioi) (g := fun _ => 0)
        (fun x hx => by
          have hx2 : ¬ 0 < x := hx.2
          simp [def_001, hx2])]
      simp
    rw [hzero, add_zero]
  rw [hRHS]
  set S := (fun t : ℝ => t⁻¹) ⁻¹' s ∩ Ioi 0 with hS
  have hSmeas : MeasurableSet S := (measurable_inv hs).inter measurableSet_Ioi
  have himage : (fun t : ℝ => t⁻¹) '' S = s ∩ Ioi 0 := by
    ext x
    constructor
    · rintro ⟨t, ⟨ht, (htpos : 0 < t)⟩, rfl⟩
      exact ⟨ht, inv_pos.mpr htpos⟩
    · rintro ⟨hx, (hxpos : 0 < x)⟩
      exact ⟨x⁻¹, ⟨by simpa using hx, inv_pos.mpr hxpos⟩, inv_inv x⟩
  have hderiv : ∀ t ∈ S, HasDerivWithinAt (fun t : ℝ => t⁻¹) (-(t ^ 2)⁻¹) S t :=
    fun t ht => (hasDerivAt_inv (ne_of_gt ht.2)).hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => t⁻¹) S := fun a _ b _ h => inv_injective h
  rw [← himage, lintegral_image_eq_lintegral_abs_deriv_mul hSmeas hderiv hinj]
  refine setLIntegral_congr_fun hSmeas fun t ht => ?_
  have htpos : 0 < t := ht.2
  have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hgam : gammaPDFReal a b t = (b : ℝ) ^ (a : ℝ) / Real.Gamma a
      * (t ^ ((a : ℝ) - 1) * Real.exp (-((b : ℝ) * t))) := by
    simp only [gammaPDFReal, htpos.le, ↓reduceIte]
    ring
  rw [gammaPDF, hgam, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  simp only [def_001, inv_pos.mpr htpos, ↓reduceIte, abs_neg,
    abs_of_pos (inv_pos.mpr (pow_pos htpos 2)), Real.rpow_eq_pow, div_inv_eq_mul]
  rw [Real.inv_rpow htpos.le, ← Real.rpow_neg htpos.le, neg_sub, sub_neg_eq_add]
  have hpow : t ^ ((a : ℝ) - 1) = (t ^ 2)⁻¹ * t ^ (1 + (a : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg htpos.le, ← Real.rpow_add htpos]
    congr 1
    push_cast
    ring
  rw [hpow]
  ring

end S55

section S46

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

lemma thm_013 (a b x : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    0 ≤ def_001 a b x := by
  unfold def_001
  split_ifs with hx
  · have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
    exact mul_nonneg (mul_nonneg (div_nonneg (Real.rpow_nonneg hb a) hG.le)
      (Real.rpow_nonneg hx.le _)) (Real.exp_pos _).le
  · exact le_rfl

lemma lem_010 (a b x : ℝ) (hx : ¬ 0 < x) :
    def_001 a b x = 0 := by
  simp [def_001, hx]

lemma lem_011 (m v z : ℝ) : 0 ≤ def_003 m v z :=
  mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.exp_pos _).le

lemma lem_012 (m v z : ℝ) (hv : 0 ≤ v) :
    def_003 m v z = gaussianPDFReal m v.toNNReal z := by
  simp only [def_003, gaussianPDFReal, Real.coe_toNNReal _ hv]

lemma lem_013 (p : str_001) (q : ℝ × ℝ) : 0 ≤ def_008 p q :=
  mul_nonneg (thm_013 _ _ _ p.alpha_pos p.beta_pos.le)
    (lem_011 _ _ _)

lemma lem_014 (p : str_001) (q : ℝ × ℝ) (hq : ¬ 0 < q.2) : def_008 p q = 0 := by
  simp [def_008, lem_010 _ _ _ hq]

lemma lem_015 (p : str_001) : Measurable (def_008 p) := by
  have hIG := lem_009 p.alpha p.beta
  unfold def_008 def_003
  fun_prop

lemma lem_016 (p : str_001) : Measurable (def_014 p) := by
  have hN := lem_015 p
  unfold def_014 def_003 def_012 def_011 def_013
  fun_prop

lemma lem_017 (p : str_001) {s : Set ℝ} (hs : MeasurableSet s) (q : ℝ × ℝ) :
    ∫⁻ z, s.indicator (fun z => ENNReal.ofReal (def_014 p (q, z))) z
      = ENNReal.ofReal (def_008 p q) * gaussianReal q.1 q.2.toNNReal s := by
  by_cases hq : 0 < q.2
  · have hv : q.2.toNNReal ≠ 0 := by
      rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hq
    have hfun : (fun z => ENNReal.ofReal (def_014 p (q, z)))
        = fun z => ENNReal.ofReal (def_008 p q) * gaussianPDF q.1 q.2.toNNReal z := by
      funext z
      rw [gaussianPDF, ← ENNReal.ofReal_mul (lem_013 p q)]
      congr 1
      simp only [def_014, def_012, def_011, def_013]
      rw [lem_012 _ _ _ hq.le]
    rw [hfun, lintegral_indicator hs, lintegral_const_mul _ (measurable_gaussianPDF _ _),
      gaussianReal_apply _ hv]
  · have h0 : def_008 p q = 0 := lem_014 p q hq
    have hfun : (fun z => ENNReal.ofReal (def_014 p (q, z))) = fun _ => 0 := by
      funext z
      simp [def_014, h0]
    simp [hfun, h0]

lemma lem_018 (p : str_001) {s : Set ℝ} (hs : MeasurableSet s) (x : ℝ) :
    ∫⁻ m, ENNReal.ofReal (def_008 p (m, x)) * gaussianReal m x.toNNReal s
      = ENNReal.ofReal (def_001 p.alpha p.beta x)
          * gaussianReal p.gamma ((x / p.nu).toNNReal + x.toNNReal) s := by
  by_cases hx : 0 < x
  · have hv : (x / p.nu).toNNReal ≠ 0 := by
      rw [Ne, Real.toNNReal_eq_zero, not_le]; exact div_pos hx p.nu_pos
    have hker : Measurable (fun m : ℝ => gaussianReal m x.toNNReal) :=
      measurable_gaussianReal.comp (measurable_id.prodMk measurable_const)
    have hmk : Measurable (fun m : ℝ => gaussianReal m x.toNNReal s) :=
      (Measure.measurable_coe hs).comp hker
    have hfun : (fun m => ENNReal.ofReal (def_008 p (m, x)) * gaussianReal m x.toNNReal s)
        = fun m => ENNReal.ofReal (def_001 p.alpha p.beta x)
            * (gaussianPDF p.gamma (x / p.nu).toNNReal m * gaussianReal m x.toNNReal s) := by
      funext m
      rw [← mul_assoc, gaussianPDF,
        ← ENNReal.ofReal_mul (thm_013 _ _ _ p.alpha_pos p.beta_pos.le)]
      congr 2
      simp only [def_008]
      rw [lem_012 _ _ _ (div_pos hx p.nu_pos).le]
    rw [hfun, lintegral_const_mul _
        (f := fun m => gaussianPDF p.gamma (x / p.nu).toNNReal m * gaussianReal m x.toNNReal s)
        ((measurable_gaussianPDF _ _).mul hmk),
      ← thm_059, Measure.bind_apply hs hker.aemeasurable,
      gaussianReal_of_var_ne_zero _ hv,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hmk]
    rfl
  · have h0 : def_001 p.alpha p.beta x = 0 := lem_010 _ _ _ hx
    have hfun : (fun m => ENNReal.ofReal (def_008 p (m, x)) * gaussianReal m x.toNNReal s)
        = fun _ => 0 := by
      funext m
      simp [def_008, h0]
    simp [hfun, h0]

theorem thm_063 (p : str_001) :
    def_016 p = (def_002 ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩).bind
      (fun x => gaussianReal p.gamma ((x / p.nu).toNNReal + x.toNNReal)) := by
  have hK : Measurable (fun x : ℝ => gaussianReal p.gamma ((x / p.nu).toNNReal + x.toNNReal)) :=
    measurable_gaussianReal.comp (measurable_const.prodMk
      (((measurable_id.div_const _).real_toNNReal).add measurable_id.real_toNNReal))
  have hH := lem_016 p
  have hlat : Measurable def_013 := measurable_snd
  ext s hs
  rw [Measure.bind_apply hs hK.aemeasurable, def_002,
    lintegral_withDensity_eq_lintegral_mul _ (lem_009 _ _).ennreal_ofReal
      (g := fun x => gaussianReal p.gamma ((x / p.nu).toNNReal + x.toNNReal) s)
      ((Measure.measurable_coe hs).comp hK),
    def_016, Measure.map_apply hlat hs, def_015, withDensity_apply _ (hlat hs),
    ← lintegral_indicator (hlat hs), Measure.volume_eq_prod,
    lintegral_prod _ ((hH.ennreal_ofReal.indicator (hlat hs)).aemeasurable)]
  have hin : ∀ q : ℝ × ℝ,
      ∫⁻ z, (def_013 ⁻¹' s).indicator
          (fun h => ENNReal.ofReal (def_014 p h)) (q, z)
        = ENNReal.ofReal (def_008 p q) * gaussianReal q.1 q.2.toNNReal s := fun q =>
    lem_017 p hs q
  simp_rw [hin]
  have hmeas : Measurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal (def_008 p q) * gaussianReal q.1 q.2.toNNReal s) :=
    (lem_015 p).ennreal_ofReal.mul ((Measure.measurable_coe hs).comp
      (measurable_gaussianReal.comp (measurable_fst.prodMk measurable_snd.real_toNNReal)))
  rw [Measure.volume_eq_prod, lintegral_prod_symm _ hmeas.aemeasurable]
  refine lintegral_congr fun x => ?_
  exact lem_018 p hs x

theorem thm_064 (p : str_001) :
    def_016 p = def_034 p.gamma p.nu p.alpha p.beta := by
  rw [thm_063, thm_062, def_034]
  congr 1
  funext x
  exact (thm_059 _ _ _).symm

theorem thm_065 (p : str_001) :
    def_016 p = def_032 (2 * p.alpha) p.gamma (def_023 p) := by
  rw [thm_064,
    thm_060 _ _ _ _ p.nu_pos p.alpha_pos p.beta_pos]
  rfl

theorem thm_066 (x : str_002) (z : ℝ) :
    def_031 (2 * x.alpha) x.gamma (x.s / x.alpha) z = def_030 x z := by
  have ha := x.alpha_pos
  unfold def_031 def_030 def_029
  have e1 : (2 * x.alpha + 1) / 2 = x.alpha + 1 / 2 := by ring
  have e2 : 2 * x.alpha / 2 = x.alpha := by ring
  have e3 : 2 * x.alpha * Real.pi * (x.s / x.alpha) = 2 * Real.pi * x.s := by
    field_simp
  have e4 : 2 * x.alpha * (x.s / x.alpha) = 2 * x.s := by
    field_simp
  rw [e1, e2, e3, e4, neg_add']

theorem thm_067 (x : str_002) (z : ℝ) :
    def_030 x z =
      Real.Gamma (x.alpha + 1 / 2) / (Real.Gamma x.alpha * Real.sqrt (2 * Real.pi * x.s))
        * (1 + (z - x.gamma) ^ 2 / (2 * x.s)) ^ (-x.alpha - 1 / 2) := rfl

def def_035 (x : str_002) : Measure ℝ :=
  volume.withDensity (fun z => ENNReal.ofReal (def_030 x z))

theorem thm_068 (p : str_001) :
    def_016 p = def_035 (def_024 p) := by
  rw [thm_065, def_032, def_035]
  congr 1
  funext z
  congr 1
  exact thm_066 (def_024 p) z

theorem thm_069 (p : str_001) :
    def_016 p = volume.withDensity (fun z => ENNReal.ofReal
      (Real.Gamma (p.alpha + 1 / 2)
          / (Real.Gamma p.alpha * Real.sqrt (2 * Real.pi * def_022 p))
        * (1 + (z - p.gamma) ^ 2 / (2 * def_022 p)) ^ (-p.alpha - 1 / 2))) :=
  thm_068 p

theorem thm_070 (p : str_001) :
    IsProbabilityMeasure (def_016 p) := by
  rw [thm_065]
  exact thm_061 _ _ _ (by linarith [p.alpha_pos])
    (thm_033 p)

theorem thm_071 (x : str_002) :
    Continuous (def_030 x) := by
  unfold def_030
  refine continuous_const.mul ?_
  exact (by fun_prop : Continuous fun z : ℝ => 1 + (z - x.gamma) ^ 2 / (2 * x.s)).rpow_const
    (fun z => Or.inl (thm_048 x z).ne')

theorem thm_072 : Function.Injective def_035 := by
  intro x y h
  have hcx : Continuous (fun z => ENNReal.ofReal (def_030 x z)) :=
    ENNReal.continuous_ofReal.comp (thm_071 x)
  have hcy : Continuous (fun z => ENNReal.ofReal (def_030 y z)) :=
    ENNReal.continuous_ofReal.comp (thm_071 y)
  have hae := (withDensity_eq_iff_of_sigmaFinite hcx.measurable.aemeasurable
    hcy.measurable.aemeasurable).mp h
  have hfun := (Continuous.ae_eq_iff_eq volume hcx hcy).mp hae
  apply thm_054
  funext z
  exact (ENNReal.ofReal_eq_ofReal_iff (thm_049 x z).le
    (thm_049 y z).le).mp (congrFun hfun z)

theorem thm_073 (p q : str_001) :
    def_016 p = def_016 q ↔ def_024 p = def_024 q := by
  rw [thm_068, thm_068]
  exact thm_072.eq_iff

theorem thm_074 (p q : str_001) :
    def_016 p = def_016 q ↔
      p.gamma = q.gamma ∧ p.alpha = q.alpha ∧ def_022 p = def_022 q :=
  (thm_073 p q).trans (thm_035 p q)

theorem thm_075 {x : str_002} {p q : str_001}
    (hp : p ∈ def_027 x) (hq : q ∈ def_027 x) :
    def_016 p = def_016 q :=
  (thm_073 p q).mpr (hp.trans hq.symm)

theorem thm_076 (x : str_002) (t : abb_001) :
    def_016 (def_026 x t) = def_035 x := by
  rw [thm_068, thm_036]

theorem thm_077 {Y : Type*} (L : abb_003 Y) (y : Y)
    {x : str_002} {p q : str_001} (hp : p ∈ def_027 x)
    (hq : q ∈ def_027 x) :
    L (def_016 p) y = L (def_016 q) y := by
  rw [thm_075 hp hq]

theorem thm_078 {Y : Type*} (L : abb_003 Y) (y : Y)
    (x : str_002) (t t' : abb_001) :
    L (def_016 (def_026 x t)) y = L (def_016 (def_026 x t')) y := by
  rw [thm_076, thm_076]

theorem thm_079 {Y : Type*} (L : abb_003 Y) (y : Y)
    (p : str_001) : L (def_016 p) y = L (def_035 (def_024 p)) y := by
  rw [thm_068]

theorem thm_080 :
    ∃ (L : abb_003 Unit), ¬ Function.Injective
      (fun x : str_002 => L (def_035 x) ()) := by
  refine ⟨fun _ _ => 0, fun h => ?_⟩
  let x₁ : str_002 := ⟨0, 1, 1, one_pos, one_pos⟩
  let x₂ : str_002 := ⟨1, 1, 1, one_pos, one_pos⟩
  have h12 : x₁ = x₂ := h rfl
  have : (0 : ℝ) = 1 := congrArg str_002.gamma h12
  exact zero_ne_one this

end S46

end NS1
