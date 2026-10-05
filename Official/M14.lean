import Mathlib
import Official.M11
import Official.M13

/-!
# Geometric and fixed-marginal limiting regimes

Asymptotic equivalence `f ∼ g` is Mathlib's `Asymptotics.IsEquivalent`.
The leading behaviour `T_A(d) ∼ (2A+1)/d` (`d ↓ 0`) and `T_A(d) ∼ 1/d` (`d → ∞`) is proved from the
closed form, and transferred to the geometric family (`γ₀, A, n` fixed, `b` varying) and to the
fixed-prior-marginal family of `Official.M13` (`n` varying). The allocations along a family are the
explicit functions `b ↦ T_A(n(1+Q(b)))` and `n ↦ T_A(n(1+Q(n)))`, which are shown to be the selected
allocations for every admissible member of the family.
-/

noncomputable section

namespace NIGBottleneck

open Filter Topology Set Asymptotics

section Leading

variable {A : ℝ}

lemma continuousAt_TA {d : ℝ} (hd : 0 < d) : ContinuousAt (TA A) d := by
  unfold TA selDisc
  have h2 : (2 : ℝ) * d ≠ 0 := by positivity
  exact ((continuous_const.sub continuous_id).add (Real.continuous_sqrt.comp
    (by fun_prop))).continuousAt.div (by fun_prop) h2

/-- `d T_A(d) = (2A + 1 − d + √((d−2A−1)² + 4d))/2` for `d > 0`. -/
lemma mul_TA_eq {d : ℝ} (hd : 0 < d) :
    d * TA A d = (2 * A + 1 - d + Real.sqrt (selDisc A d)) / 2 := by
  unfold TA
  field_simp

/-- `d T_A(d) = 2 / (√((1 − (2A+1)/d)² + 4/d) + 1 − (2A+1)/d)` for `d > 0`. -/
lemma mul_TA_eq' {d : ℝ} (hd : 0 < d) :
    d * TA A d
      = 2 / (Real.sqrt ((1 - (2 * A + 1) * d⁻¹) ^ 2 + 4 * d⁻¹) + 1 - (2 * A + 1) * d⁻¹) := by
  have hD := selDisc_pos (A := A) hd
  set r := Real.sqrt (selDisc A d) with hr
  have hr2 : r ^ 2 = selDisc A d := Real.sq_sqrt hD.le
  have habs := abs_lt_sqrt_selDisc (A := A) hd
  have hpos : 0 < r + d - (2 * A + 1) := by
    have := neg_abs_le (d - 2 * A - 1)
    rw [← hr] at habs
    linarith
  have hsq : Real.sqrt ((1 - (2 * A + 1) * d⁻¹) ^ 2 + 4 * d⁻¹) = r / d := by
    have e : (1 - (2 * A + 1) * d⁻¹) ^ 2 + 4 * d⁻¹ = (r / d) ^ 2 := by
      rw [div_pow, hr2]
      unfold selDisc
      field_simp
      ring
    rw [e, Real.sqrt_sq (div_nonneg (Real.sqrt_nonneg _) hd.le)]
  rw [hsq, mul_TA_eq hd, ← hr]
  have hden : r / d + 1 - (2 * A + 1) * d⁻¹ = (r + d - (2 * A + 1)) / d := by
    field_simp
  rw [hden, div_div_eq_mul_div]
  rw [eq_div_iff hpos.ne']
  have hr2' : r ^ 2 = (d - 2 * A - 1) ^ 2 + 4 * d := hr2
  linear_combination (1 / 2) * hr2'

/-- `d T_A(d) → 2A + 1` as `d ↓ 0`. -/
theorem tendsto_mul_TA_zero (hA : 0 < A) :
    Tendsto (fun d => d * TA A d) (𝓝[>] 0) (𝓝 (2 * A + 1)) := by
  have hc : Continuous fun d : ℝ => (2 * A + 1 - d + Real.sqrt (selDisc A d)) / 2 := by
    unfold selDisc
    fun_prop
  have h0 : (2 * A + 1 - 0 + Real.sqrt (selDisc A 0)) / 2 = 2 * A + 1 := by
    unfold selDisc
    rw [show ((0 : ℝ) - 2 * A - 1) ^ 2 + 4 * 0 = (2 * A + 1) ^ 2 by ring,
      Real.sqrt_sq (by linarith)]
    ring
  have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  rw [h0] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with d hd
  exact (mul_TA_eq hd).symm

/-- `d T_A(d) → 1` as `d → ∞`. -/
theorem tendsto_mul_TA_atTop :
    Tendsto (fun d => d * TA A d) atTop (𝓝 1) := by
  set G : ℝ → ℝ := fun ε =>
    2 / (Real.sqrt ((1 - (2 * A + 1) * ε) ^ 2 + 4 * ε) + 1 - (2 * A + 1) * ε)
  have hG0 : G 0 = 1 := by
    simp only [G]
    norm_num
  have hGc : ContinuousAt G 0 := by
    simp only [G]
    refine ContinuousAt.div continuousAt_const (by fun_prop) ?_
    norm_num
  have h := hGc.tendsto.comp tendsto_inv_atTop_zero
  rw [hG0] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  exact (mul_TA_eq' hd).symm

/-- `T_A(d) ∼ (2A+1)/d` as `d ↓ 0`. -/
theorem TA_isEquivalent_zero (hA : 0 < A) :
    TA A ~[𝓝[>] 0] fun d => (2 * A + 1) / d := by
  refine isEquivalent_of_tendsto_one ?_
  have h := (tendsto_mul_TA_zero hA).div_const (2 * A + 1)
  rw [div_self (by linarith)] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with d (hd : 0 < d)
  simp only [Pi.div_apply]
  field_simp

/-- `T_A(d) ∼ 1/d` as `d → ∞`. -/
theorem TA_isEquivalent_atTop : TA A ~[atTop] fun d => 1 / d := by
  refine isEquivalent_of_tendsto_one ?_
  refine (tendsto_mul_TA_atTop (A := A)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  simp only [Pi.div_apply]
  field_simp

end Leading

section Transfer

/-- If `d(u) → ℓ`-regime with `d(u) T_A(d(u)) → L ≠ 0` and `c(u)/d(u) → 1`, then
`T_A(d(u)) ∼ L / c(u)` and `1/T_A(d(u)) ∼ c(u) / L`. -/
lemma transfer_equiv {l : Filter ℝ} {A L : ℝ} (hL : L ≠ 0) {d c : ℝ → ℝ}
    (hdT : Tendsto (fun u => d u * TA A (d u)) l (𝓝 L)) (hcd : Tendsto (fun u => c u / d u) l (𝓝 1))
    (hpos : ∀ᶠ u in l, 0 < d u ∧ 0 < c u) :
    (fun u => TA A (d u)) ~[l] (fun u => L / c u)
      ∧ (fun u => 1 / TA A (d u)) ~[l] (fun u => c u / L) := by
  have h1 : Tendsto (fun u => (d u * TA A (d u)) / L * (c u / d u)) l (𝓝 1) := by
    have := (hdT.div_const L).mul hcd
    rwa [div_self hL, one_mul] at this
  have e1 : ∀ᶠ u in l, (d u * TA A (d u)) / L * (c u / d u) = TA A (d u) / (L / c u) := by
    filter_upwards [hpos] with u ⟨hd, hc⟩
    field_simp
  have h2 : Tendsto (fun u => TA A (d u) / (L / c u)) l (𝓝 1) := h1.congr' e1
  refine ⟨isEquivalent_of_tendsto_one h2, isEquivalent_of_tendsto_one ?_⟩
  have h3 := h2.inv₀ one_ne_zero
  rw [inv_one] at h3
  refine h3.congr' ?_
  filter_upwards [hpos] with u ⟨hd, hc⟩
  simp only [Pi.div_apply]
  field_simp

end Transfer

section GeometricFamily

variable (A n e w : ℝ)

/-- The score along the geometric family: `Q(b) = (δ² + b)/w`, with `e = δ²`. -/
def scoreB (b : ℝ) : ℝ := (e + b) / w

/-- The selected inverse allocation along the geometric family, `b ↦ T_A(n(1+Q(b)))`. -/
def tB (b : ℝ) : ℝ := TA A (n * (1 + scoreB e w b))

/-- The members of the geometric family are the priors `(γ₀, b, A, n)`; along it the selected
allocation is `tB`. -/
theorem selT_geometric_family (g₀ b : ℝ) (hb : 0 < b) (hA : 0 < A) (hn : 0 < n)
    (x : QuotientState) :
    selT (priorOfCoords g₀ b A n hb hA hn) x
      = tB A n ((x.gamma - g₀) ^ 2) (x.s / x.alpha) b := by
  rw [(selT_eq_tOfScore _ x).1, scoreQ_eq_div_w]
  have hbp : bParam (priorOfCoords g₀ b A n hb hA hn) = b := by
    simp only [bParam, priorOfCoords]
    field_simp
  rw [hbp]
  rfl

/-- `Q → δ²/w` as `b ↓ 0`. -/
theorem scoreB_tendsto_zero : Tendsto (scoreB e w) (𝓝[>] 0) (𝓝 (e / w)) := by
  have h : Continuous (scoreB e w) := by unfold scoreB; fun_prop
  have := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simpa [scoreB] using this

/-- `Q/b → 1/w` as `b → ∞`. -/
theorem scoreB_div_tendsto_atTop (hw : 0 < w) :
    Tendsto (fun b => scoreB e w b / b) atTop (𝓝 (1 / w)) := by
  have h : Tendsto (fun b : ℝ => e / w * b⁻¹ + 1 / w) atTop (𝓝 (e / w * 0 + 1 / w)) :=
    (tendsto_inv_atTop_zero.const_mul _).add_const _
  rw [mul_zero, zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with b hb
  unfold scoreB
  field_simp

/-- If `δ = 0`, the selected inverse allocation tends, as `b ↓ 0`, to
`T_A(n)`, which is its maximal possible value (a strict upper bound over all scores `Q > 0`). -/
theorem tB_tendsto_max (hA : 0 < A) (hn : 0 < n) :
    Tendsto (tB A n 0 w) (𝓝[>] 0) (𝓝 (TA A n))
      ∧ ∀ Q : ℝ, 0 < Q → tOfScore A n Q < TA A n := by
  constructor
  · have hc : ContinuousAt (fun b => n * (1 + scoreB 0 w b)) 0 := by
      unfold scoreB; fun_prop
    have hf : Tendsto (fun b => n * (1 + scoreB 0 w b)) (𝓝 0) (𝓝 n) := by
      simpa [scoreB] using hc.tendsto
    exact ((continuousAt_TA (A := A) hn).tendsto.comp hf).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
  · intro Q hQ
    have hd : n < n * (1 + Q) := by nlinarith
    exact TA_strictAntiOn hA.le (show (0 : ℝ) < n from hn) (show 0 < n * (1 + Q) by linarith) hd

/-- As `b → ∞`, comparisons with distinct `w`'s are eventually ordered
by inverse squared Student scale: `w₁ < w₂` makes eventually `Q₁ > Q₂` and `t₁ < t₂`. -/
theorem eventually_ordered_by_w (hA : 0 < A) (hn : 0 < n) (e₁ e₂ w₁ w₂ : ℝ)
    (he₂ : 0 ≤ e₂) (hw₁ : 0 < w₁) (hw : w₁ < w₂) :
    ∀ᶠ b in atTop, scoreB e₂ w₂ b < scoreB e₁ w₁ b ∧ tB A n e₁ w₁ b < tB A n e₂ w₂ b := by
  have hw₂ : 0 < w₂ := by linarith
  have hk : 0 < 1 / w₁ - 1 / w₂ := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt hw₁ hw
  have hlin : Tendsto (fun b => (1 / w₁ - 1 / w₂) * b + (e₁ / w₁ - e₂ / w₂)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop hk)
  filter_upwards [hlin.eventually_gt_atTop 0, eventually_gt_atTop 0] with b hb hb0
  have hQ : scoreB e₂ w₂ b < scoreB e₁ w₁ b := by
    unfold scoreB
    have : (e₁ + b) / w₁ - (e₂ + b) / w₂ = (1 / w₁ - 1 / w₂) * b + (e₁ / w₁ - e₂ / w₂) := by
      field_simp
      ring
    linarith
  refine ⟨hQ, ?_⟩
  have hQ2 : 0 < scoreB e₂ w₂ b := by unfold scoreB; positivity
  exact tOfScore_strictAntiOn hA hn hQ2 (hQ2.trans hQ) hQ

/-- As `b → ∞`, `t_* ∼ w/(nb)` and `ν_sel ∼ nb/w`. -/
theorem tB_isEquivalent_atTop (hn : 0 < n) (he : 0 ≤ e) (hw : 0 < w) :
    tB A n e w ~[atTop] (fun b => w / (n * b))
      ∧ (fun b => 1 / tB A n e w b) ~[atTop] (fun b => n * b / w) := by
  have hd : Tendsto (fun b => n * (1 + scoreB e w b)) atTop atTop := by
    unfold scoreB
    refine tendsto_atTop_mono' _ ?_ (tendsto_id.const_mul_atTop (div_pos hn hw))
    filter_upwards [eventually_gt_atTop 0] with b hb
    simp only [id]
    have : n / w * b ≤ n * (1 + (e + b) / w) := by
      rw [div_mul_eq_mul_div, mul_add, mul_one, mul_div_assoc']
      have : n * b / w ≤ n * (e + b) / w := by
        apply div_le_div_of_nonneg_right _ hw.le
        nlinarith
      linarith
    exact this
  have hdT := (tendsto_mul_TA_atTop (A := A)).comp hd
  have hcd : Tendsto (fun b => n * b / w / (n * (1 + scoreB e w b))) atTop (𝓝 1) := by
    -- `(nb/w)/(n(1 + (e+b)/w)) = 1/((w+e)/b + 1)`
    have h0 : Tendsto (fun b : ℝ => (w + e) * b⁻¹ + 1) atTop (𝓝 1) := by
      have := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (w + e)).add_const 1
      simpa using this
    have h := h0.inv₀ one_ne_zero
    rw [inv_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with b hb
    unfold scoreB
    field_simp
    ring
  have hpos : ∀ᶠ b in atTop, 0 < n * (1 + scoreB e w b) ∧ 0 < n * b / w := by
    filter_upwards [eventually_gt_atTop 0] with b hb
    unfold scoreB
    constructor <;> positivity
  obtain ⟨h1, h2⟩ := transfer_equiv one_ne_zero hdT hcd hpos
  refine ⟨h1.congr_right ?_, h2.congr_right ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with b hb
    field_simp
  · filter_upwards with b
    simp

end GeometricFamily

section FixedMarginalFamily

variable (A s₀ e w : ℝ)

/-- The score along the fixed-prior-marginal family, `Q(n) = (δ² + 2s₀/(n+1))/w`. -/
def scoreN (n : ℝ) : ℝ := (e + 2 * s₀ / (n + 1)) / w

/-- `Q_low = (δ² + 2s₀)/w`. -/
def scoreLow : ℝ := (e + 2 * s₀) / w

/-- `Q_high = δ²/w`. -/
def scoreHigh : ℝ := e / w

/-- The selected inverse allocation along the fixed-prior-marginal family,
`n ↦ T_A(n(1+Q(n)))`. -/
def tN (n : ℝ) : ℝ := TA A (n * (1 + scoreN s₀ e w n))

/-- Along the fixed-prior-marginal family of `Official.M13` the selected allocation is `tN`. -/
theorem selT_marginal_family (x₀ x : QuotientState) (n : ℝ) (hn : 0 < n) :
    selT (priorFamily x₀ n hn) x
      = tN x₀.alpha x₀.s ((x.gamma - x₀.gamma) ^ 2) (x.s / x.alpha) n := by
  rw [(selT_eq_tOfScore _ x).1, scoreQ_eq_div_w, (priorFamily_coords x₀ n hn).2.2.2]
  rfl

theorem scoreN_continuousAt (n : ℝ) (hn : 0 ≤ n) : ContinuousAt (scoreN s₀ e w) n := by
  unfold scoreN
  have : n + 1 ≠ 0 := by linarith
  fun_prop (disch := assumption)

/-- `Q → Q_low` as `n ↓ 0`. -/
theorem scoreN_tendsto_zero : Tendsto (scoreN s₀ e w) (𝓝[>] 0) (𝓝 (scoreLow s₀ e w)) := by
  have h := (scoreN_continuousAt s₀ e w 0 le_rfl).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi 0))
  have e0 : scoreN s₀ e w 0 = scoreLow s₀ e w := by
    simp [scoreN, scoreLow]
  rwa [e0] at h

/-- `Q → Q_high` as `n → ∞`. -/
theorem scoreN_tendsto_atTop : Tendsto (scoreN s₀ e w) atTop (𝓝 (scoreHigh e w)) := by
  have h : Tendsto (fun n : ℝ => (e + 2 * s₀ * (n + 1)⁻¹) / w) atTop (𝓝 ((e + 2 * s₀ * 0) / w)) :=
    ((tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)).const_mul _
      |>.const_add e).div_const w
  rw [mul_zero, add_zero] at h
  refine h.congr' (Eventually.of_forall fun n => ?_)
  simp [scoreN, div_eq_mul_inv]

variable {A s₀ e w} (hA : 0 < A) (hs : 0 < s₀) (he : 0 ≤ e) (hw : 0 < w)
include hA hs he hw

omit hA in
lemma scoreN_pos {n : ℝ} (hn : 0 < n) : 0 < scoreN s₀ e w n := by
  unfold scoreN
  positivity

/-- As `n ↓ 0`, `t_* ∼ (2A+1)/(n(1+Q_low))` and
`ν_sel ∼ n(1+Q_low)/(2A+1)`. -/
theorem tN_isEquivalent_zero :
    tN A s₀ e w ~[𝓝[>] 0] (fun n => (2 * A + 1) / (n * (1 + scoreLow s₀ e w)))
      ∧ (fun n => 1 / tN A s₀ e w n) ~[𝓝[>] 0]
          (fun n => n * (1 + scoreLow s₀ e w) / (2 * A + 1)) := by
  have hQl : 0 < scoreLow s₀ e w := by unfold scoreLow; positivity
  have hd : Tendsto (fun n => n * (1 + scoreN s₀ e w n)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun n => n * (1 + scoreN s₀ e w n)) 0 :=
        continuousAt_id.mul (continuousAt_const.add (scoreN_continuousAt s₀ e w 0 le_rfl))
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with n (hn : 0 < n)
      have := scoreN_pos hs he hw hn
      exact (mul_pos hn (by linarith) : 0 < n * (1 + scoreN s₀ e w n))
  have hdT := (tendsto_mul_TA_zero hA).comp hd
  have hcd : Tendsto (fun n => n * (1 + scoreLow s₀ e w) / (n * (1 + scoreN s₀ e w n)))
      (𝓝[>] 0) (𝓝 1) := by
    have h := ((scoreN_tendsto_zero s₀ e w).const_add 1).inv₀ (by linarith)
      |>.const_mul (1 + scoreLow s₀ e w)
    rw [mul_inv_cancel₀ (by linarith)] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with n (hn : 0 < n)
    have := scoreN_pos hs he hw hn
    field_simp
  have hpos : ∀ᶠ n in 𝓝[>] 0, 0 < n * (1 + scoreN s₀ e w n) ∧ 0 < n * (1 + scoreLow s₀ e w) := by
    filter_upwards [self_mem_nhdsWithin] with n (hn : 0 < n)
    have := scoreN_pos hs he hw hn
    constructor <;> positivity
  obtain ⟨h1, h2⟩ := transfer_equiv (by linarith) hdT hcd hpos
  exact ⟨h1, h2⟩

omit hA in
/-- As `n → ∞`, `t_* ∼ 1/(n(1+Q_high))` and `ν_sel ∼ n(1+Q_high)`. -/
theorem tN_isEquivalent_atTop :
    tN A s₀ e w ~[atTop] (fun n => 1 / (n * (1 + scoreHigh e w)))
      ∧ (fun n => 1 / tN A s₀ e w n) ~[atTop] (fun n => n * (1 + scoreHigh e w)) := by
  have hQh : 0 ≤ scoreHigh e w := by unfold scoreHigh; positivity
  have hd : Tendsto (fun n => n * (1 + scoreN s₀ e w n)) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ tendsto_id
    filter_upwards [eventually_gt_atTop 0] with n hn
    have := scoreN_pos hs he hw hn
    simp only [id]
    nlinarith
  have hdT := (tendsto_mul_TA_atTop (A := A)).comp hd
  have hcd : Tendsto (fun n => n * (1 + scoreHigh e w) / (n * (1 + scoreN s₀ e w n)))
      atTop (𝓝 1) := by
    have h := ((scoreN_tendsto_atTop s₀ e w).const_add 1).inv₀ (by linarith)
      |>.const_mul (1 + scoreHigh e w)
    rw [mul_inv_cancel₀ (by linarith)] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have := scoreN_pos hs he hw hn
    field_simp
  have hpos : ∀ᶠ n in atTop, 0 < n * (1 + scoreN s₀ e w n) ∧ 0 < n * (1 + scoreHigh e w) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have := scoreN_pos hs he hw hn
    constructor <;> positivity
  obtain ⟨h1, h2⟩ := transfer_equiv one_ne_zero hdT hcd hpos
  refine ⟨h1, h2.congr_right ?_⟩
  filter_upwards with n
  simp

omit hA hs he hw in
/-- The fraction `t/(1+t)`. -/
lemma tendsto_frac_atTop {l : Filter ℝ} {f : ℝ → ℝ} (hf : Tendsto f l atTop) :
    Tendsto (fun u => f u / (1 + f u)) l (𝓝 1) := by
  have h : Tendsto (fun u => 1 - 1 / (1 + f u)) l (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub ((tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ 1 hf)))
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [hf.eventually_gt_atTop 0] with u hu
  field_simp
  ring

/-- If `α > 1`, the selected epistemic fraction `u_epi/V_z = t_*/(1+t_*)`
tends to `1` as `n ↓ 0` and to `0` as `n → ∞`. -/
theorem epistemic_fraction_limits :
    Tendsto (fun n => tN A s₀ e w n / (1 + tN A s₀ e w n)) (𝓝[>] 0) (𝓝 1)
      ∧ Tendsto (fun n => tN A s₀ e w n / (1 + tN A s₀ e w n)) atTop (𝓝 0) := by
  have hQl : 0 < scoreLow s₀ e w := by unfold scoreLow; positivity
  have hQh : 0 ≤ scoreHigh e w := by unfold scoreHigh; positivity
  constructor
  · -- `t_* → ∞`: `t_* ∼ (2A+1)/(n(1+Q_low))` and the latter tends to `∞`
    have hg : Tendsto (fun n => (2 * A + 1) / (n * (1 + scoreLow s₀ e w))) (𝓝[>] 0) atTop := by
      have h := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop
        (show 0 < (2 * A + 1) / (1 + scoreLow s₀ e w) by positivity)
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with n (hn : 0 < n)
      field_simp
    exact tendsto_frac_atTop ((tN_isEquivalent_zero hA hs he hw).1.symm.tendsto_atTop hg)
  · have hg : Tendsto (fun n => 1 / (n * (1 + scoreHigh e w))) atTop (𝓝 0) := by
      have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).mul_const (1 / (1 + scoreHigh e w))
      rw [zero_mul] at h
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      field_simp
    have ht := (tN_isEquivalent_atTop (A := A) hs he hw).1.symm.tendsto_nhds hg
    have h := ht.div (tendsto_const_nhds.add ht) (show (1 : ℝ) + 0 ≠ 0 by norm_num)
    rwa [zero_div] at h

omit hA hs he hw in
/-- The selected epistemic fraction along the family is
`t_*/(1+t_*)` for every admissible member with `α > 1`. -/
theorem epistemic_fraction_marginal_family (x₀ x : QuotientState) (hα : 1 < x.alpha) (n : ℝ)
    (hn : 0 < n) :
    uEpi (fiberParameters x (selTPos (priorFamily x₀ n hn) x))
        / totalVar (fiberParameters x (selTPos (priorFamily x₀ n hn) x))
      = tN x₀.alpha x₀.s ((x.gamma - x₀.gamma) ^ 2) (x.s / x.alpha) n
        / (1 + tN x₀.alpha x₀.s ((x.gamma - x₀.gamma) ^ 2) (x.s / x.alpha) n) := by
  rw [(selected_ratios x hα (priorFamily x₀ n hn)).2.2.1, selT_marginal_family]

end FixedMarginalFamily

end NIGBottleneck
