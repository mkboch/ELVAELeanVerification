import Mathlib
import Official.M11
import Official.M12
import Official.M15

/-!
# Marginal-scale limits and absolute uncertainty amplitude

Fix `γ, α` and the complete prior; put `C = α(δ² + b) > 0` and
`D = 2αB = nC > 0`. Along the states `(γ, α, s)`, `d = n + D/s`, so the selected allocation is the
explicit function `s ↦ T_A(n + D/s)`. As `s ↓ 0`: `Q = C/s → ∞`, `t_* = s/D + O(s²)`,
`ν_sel = D/s + n − 2A + O(s)`; as `s → ∞`: `Q → 0`, `t_* → M(A,n)`, `ν_sel → 1/M(A,n)`. For
`α > 1` the uncertainty summands have the stated asymptotic equivalents, and neither has a finite
uniform upper bound.
-/

noncomputable section

namespace NIGBottleneck

open Filter Topology Set Asymptotics

section Explicit

variable {A : ℝ}

/-- `0 ≤ T_A(d) − 1/d ≤ 2A/(d(d−2A))` for `d > 2A ≥ 0`. -/
lemma TA_sub_inv_bounds (hA : 0 ≤ A) {d : ℝ} (hd : 0 < d) (hd2 : 2 * A < d) :
    0 ≤ TA A d - 1 / d ∧ TA A d - 1 / d ≤ 2 * A / (d * (d - 2 * A)) := by
  have hT := TA_pos (A := A) hd
  have hdef := boundM_defining (A := A) hd
  simp only [boundM] at hdef
  set T := TA A d
  -- `T − 1/d = 2AT/(d(1+T))`
  have e : T - 1 / d = 2 * A * T / (d * (1 + T)) := by
    field_simp
    linarith
  -- `T ≤ 1/(d − 2A)`, using `dT ≥ 1`
  have hkey : (d * T - 1) * (1 + T) = 2 * A * T := by linear_combination hdef
  have hdT : 0 ≤ d * T - 1 := by
    by_contra hc
    have : (d * T - 1) * (1 + T) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    nlinarith
  have hTup : T * (d - 2 * A) ≤ 1 := by nlinarith
  rw [e]
  constructor
  · positivity
  · rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
    have : 0 ≤ 2 * A * d := by positivity
    nlinarith

/-- `0 < Φ_A(d) − (d − 2A) ≤ 2A/(d − 2A)` for `d > 2A ≥ 0`. -/
lemma PhiA_sub_bounds (hA : 0 ≤ A) {d : ℝ} (hd : 0 < d) (hd2 : 2 * A < d) :
    0 ≤ PhiA A d - (d - 2 * A) ∧ PhiA A d - (d - 2 * A) ≤ 2 * A / (d - 2 * A) := by
  have h := gA_PhiA (A := A) hd
  have hr := PhiA_pos (A := A) hd
  set r := PhiA A d
  unfold gA at h
  -- `r − (d − 2A) = 2A/(1+r)`
  have e : r - (d - 2 * A) = 2 * A / (1 + r) := by
    rw [← h]
    field_simp
    ring
  have hr' : d - 2 * A ≤ r := by
    have : 0 ≤ 2 * A / (1 + r) := by positivity
    linarith
  rw [e]
  refine ⟨by positivity, div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)⟩

end Explicit

section ScaleFamily

variable (A n D : ℝ)

/-- The selected inverse allocation along the states `(γ, α, s)`: `s ↦ T_A(n + D/s)`. -/
def tScale (s : ℝ) : ℝ := TA A (n + D / s)

/-- The corresponding `ν_sel`: `s ↦ Φ_A(n + D/s)`. -/
def nuScale (s : ℝ) : ℝ := PhiA A (n + D / s)

/-- `C = α(δ² + b)`. -/
def scaleC (p₀ : Parameters) (γ α : ℝ) : ℝ := α * ((γ - p₀.gamma) ^ 2 + bParam p₀)

/-- Along the states `x = (γ, α, s)`, `Q = C/s`, `d = n + D/s` with
`D = nC = 2αB`, and `t_*`, `ν_sel` are `tScale`, `nuScale`. -/
theorem scale_family (p₀ : Parameters) (γ α s : ℝ) (hα : 0 < α) (hs : 0 < s) :
    scoreQ p₀ ⟨γ, α, s, hα, hs⟩ = scaleC p₀ γ α / s
      ∧ p₀.nu * scaleC p₀ γ α = 2 * α * priorB p₀ ⟨γ, α, s, hα, hs⟩
      ∧ selT p₀ ⟨γ, α, s, hα, hs⟩ = tScale p₀.alpha p₀.nu (p₀.nu * scaleC p₀ γ α) s
      ∧ selNu p₀ ⟨γ, α, s, hα, hs⟩ = nuScale p₀.alpha p₀.nu (p₀.nu * scaleC p₀ γ α) s := by
  have hQ : scoreQ p₀ ⟨γ, α, s, hα, hs⟩ = scaleC p₀ γ α / s := rfl
  have hd : p₀.nu * (1 + scaleC p₀ γ α / s) = p₀.nu + p₀.nu * scaleC p₀ γ α / s := by ring
  refine ⟨hQ, ?_, ?_, ?_⟩
  · simp only [scaleC, priorB, bParam]
    have := p₀.nu_pos
    field_simp
    ring
  · rw [(selT_selNu_eq_score p₀ _).1, hQ, hd]
    rfl
  · rw [(selT_selNu_eq_score p₀ _).2, hQ, hd]
    rfl

theorem scaleC_pos (p₀ : Parameters) (γ α : ℝ) (hα : 0 < α) : 0 < scaleC p₀ γ α := by
  have := bParam_pos p₀
  unfold scaleC
  positivity

variable {A n D} (hA : 0 < A) (hn : 0 < n) (hD : 0 < D)
include hA hn hD

omit hA hn hD in
/-- `Q = C/s → ∞` as `s ↓ 0`. -/
theorem score_tendsto_zero (C : ℝ) (hC : 0 < C) :
    Tendsto (fun s => C / s) (𝓝[>] 0) atTop :=
  (tendsto_inv_nhdsGT_zero).const_mul_atTop hC |>.congr fun s => (div_eq_mul_inv C s).symm

/-- `t_* = s/D + O(s²)` as `s ↓ 0`. -/
theorem tScale_isBigO_zero :
    (fun s => tScale A n D s - s / D) =O[𝓝[>] 0] (fun s => s ^ 2) := by
  refine IsBigO.of_bound ((4 * A + n) / D ^ 2) ?_
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < D / (4 * A) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
  filter_upwards [self_mem_nhdsWithin, hsmall] with s (hs : 0 < s) hsD
  set d := n + D / s with hd
  have hDs : D / s ≤ d := by rw [hd]; linarith
  have h4A : 4 * A < D / s := by
    rw [lt_div_iff₀ hs]
    rw [lt_div_iff₀ (by positivity)] at hsD
    linarith
  have hd0 : 0 < d := by linarith [div_pos hD hs]
  obtain ⟨h1, h2⟩ := TA_sub_inv_bounds hA.le hd0 (by linarith)
  -- `|T − 1/d| ≤ 4A/d² ≤ 4A s²/D²`
  have hb1 : 2 * A / (d * (d - 2 * A)) ≤ 4 * A * s ^ 2 / D ^ 2 := by
    have hdd : d / 2 ≤ d - 2 * A := by linarith
    have hds : D ≤ d * s := by rw [div_le_iff₀ hs] at hDs; linarith
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    have h5 : D ^ 2 ≤ (d * s) ^ 2 := by nlinarith
    have h6 : d ^ 2 / 2 ≤ d * (d - 2 * A) := by nlinarith
    have h7 := mul_le_mul_of_nonneg_left h6 (by positivity : (0 : ℝ) ≤ 4 * A * s ^ 2)
    have h8 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 2 * A)
    nlinarith
  -- `|1/d − s/D| = n s²/(D(ns + D)) ≤ n s²/D²`
  have e2 : 1 / d - s / D = -(n * s ^ 2 / (D * (n * s + D))) := by
    rw [hd]
    field_simp
    ring
  have hb2 : n * s ^ 2 / (D * (n * s + D)) ≤ n * s ^ 2 / D ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [mul_pos hD (mul_pos hn hs)]
  have hpos2 : 0 ≤ n * s ^ 2 / (D * (n * s + D)) := by positivity
  change ‖TA A d - s / D‖ ≤ (4 * A + n) / D ^ 2 * ‖s ^ 2‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg s), abs_le]
  have e3 : TA A d - s / D = (TA A d - 1 / d) + (1 / d - s / D) := by ring
  have e4 : (4 * A + n) / D ^ 2 * s ^ 2 = 4 * A * s ^ 2 / D ^ 2 + n * s ^ 2 / D ^ 2 := by ring
  rw [e3, e2, e4]
  constructor <;> linarith

/-- `ν_sel = D/s + n − 2A + O(s)` as `s ↓ 0`. -/
theorem nuScale_isBigO_zero :
    (fun s => nuScale A n D s - (D / s + n - 2 * A)) =O[𝓝[>] 0] (fun s => s) := by
  refine IsBigO.of_bound (4 * A / D) ?_
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < D / (4 * A) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
  filter_upwards [self_mem_nhdsWithin, hsmall] with s (hs : 0 < s) hsD
  set d := n + D / s with hd
  have hDs : D / s ≤ d := by rw [hd]; linarith
  have h4A : 4 * A < D / s := by
    rw [lt_div_iff₀ hs]
    rw [lt_div_iff₀ (by positivity)] at hsD
    linarith
  have hd0 : 0 < d := by linarith [div_pos hD hs]
  obtain ⟨h1, h2⟩ := PhiA_sub_bounds hA.le hd0 (by linarith)
  have hb : 2 * A / (d - 2 * A) ≤ 4 * A / D * s := by
    have hdd : d / 2 ≤ d - 2 * A := by linarith
    have hds : D ≤ d * s := by rw [div_le_iff₀ hs] at hDs; linarith
    rw [div_le_iff₀ (by linarith), show 4 * A / D * s * (d - 2 * A) = 4 * A * s * (d - 2 * A) / D
      by ring, le_div_iff₀ hD]
    have h7 := mul_le_mul_of_nonneg_left hdd (by positivity : (0 : ℝ) ≤ 4 * A * s)
    have h8 := mul_le_mul_of_nonneg_left hds (by positivity : (0 : ℝ) ≤ 2 * A)
    nlinarith
  change ‖PhiA A d - (D / s + n - 2 * A)‖ ≤ 4 * A / D * ‖s‖
  have e : D / s + n - 2 * A = d - 2 * A := by rw [hd]; ring
  rw [e, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hs, abs_of_nonneg h1]
  linarith

omit hA hn hD in
/-- `d(s) = n + D/s → n` as `s → ∞`. -/
lemma d_tendsto_atTop : Tendsto (fun s => n + D / s) atTop (𝓝 n) := by
  have := (tendsto_const_nhds (x := D)).div_atTop tendsto_id
  simpa using this.const_add n

omit hA in
/-- As `s → ∞`, `Q → 0`, `t_* → M(A,n)` and `ν_sel → 1/M(A,n)`. -/
theorem scale_limits_atTop (C : ℝ) :
    Tendsto (fun s => C / s) atTop (𝓝 0)
      ∧ Tendsto (tScale A n D) atTop (𝓝 (boundM A n))
      ∧ Tendsto (nuScale A n D) atTop (𝓝 (1 / boundM A n)) := by
  have hT : Tendsto (tScale A n D) atTop (𝓝 (boundM A n)) :=
    (continuousAt_TA hn).tendsto.comp (d_tendsto_atTop (n := n) (D := D))
  refine ⟨tendsto_const_nhds.div_atTop tendsto_id, hT, ?_⟩
  have hM : boundM A n ≠ 0 := (TA_pos hn).ne'
  have h := hT.inv₀ hM
  rw [← one_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  have hd : 0 < n + D / s := by positivity
  simp only [nuScale, tScale]
  rw [PhiA_eq_inv_TA hd, one_div]

end ScaleFamily

section Uncertainty

variable {A n D : ℝ} (hA : 0 < A) (hn : 0 < n) (hD : 0 < D) (a : ℝ) (ha : 0 < a)
include hA hn hD ha

/-- `u_var` along the scale family: `s/((α−1)(1+t))`, with `a = α − 1 > 0`. -/
def uVarScale (A n D a s : ℝ) : ℝ := s / (a * (1 + tScale A n D s))

/-- `u_epi` along the scale family: `s t/((α−1)(1+t))`. -/
def uEpiScale (A n D a s : ℝ) : ℝ := s * tScale A n D s / (a * (1 + tScale A n D s))

omit hA hn hD ha in
/-- Along the scale family, the uncertainty summands of `Official.M11` are `uVarScale`,
`uEpiScale`. -/
theorem uncertainty_scale_family (p₀ : Parameters) (γ α s : ℝ) (hα : 1 < α) (hs : 0 < s) :
    uVar (selParams p₀ ⟨γ, α, s, by linarith, hs⟩)
        = uVarScale p₀.alpha p₀.nu (p₀.nu * scaleC p₀ γ α) (α - 1) s
      ∧ uEpi (selParams p₀ ⟨γ, α, s, by linarith, hs⟩)
        = uEpiScale p₀.alpha p₀.nu (p₀.nu * scaleC p₀ γ α) (α - 1) s := by
  have ht := (scale_family p₀ γ α s (by linarith) hs).2.2.1
  constructor
  · rw [selParams, uVar_fiber _ hα, uVarScale]
    simp only [selTPos]
    rw [ht]
  · rw [selParams, uEpi_fiber _ hα, uEpiScale]
    simp only [selTPos]
    rw [ht]

omit ha in
lemma tScale_tendsto_zero : Tendsto (tScale A n D) (𝓝[>] 0) (𝓝 0) := by
  have h := (tScale_isBigO_zero hA hn hD).trans_tendsto
    ((continuous_pow 2).tendsto' 0 0 (by norm_num) |>.mono_left nhdsWithin_le_nhds)
  have h2 : Tendsto (fun s : ℝ => s / D) (𝓝[>] 0) (𝓝 0) := by
    have := ((continuous_id.div_const D).tendsto' 0 0 (by simp)).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    exact this
  have := h.add h2
  rw [zero_add] at this
  refine this.congr' (Eventually.of_forall fun s => ?_)
  simp

omit ha in
lemma tScale_mul_div_tendsto_zero : Tendsto (fun s => tScale A n D s * D / s) (𝓝[>] 0) (𝓝 1) := by
  -- `t D/s = 1 + D (t − s/D)/s` and `(t − s/D)/s = O(s)`
  have hO := (tScale_isBigO_zero hA hn hD)
  have hlim : Tendsto (fun s => (tScale A n D s - s / D) / s) (𝓝[>] 0) (𝓝 0) := by
    have h1 : (fun s => (tScale A n D s - s / D) / s) =O[𝓝[>] 0] (fun s => s) := by
      have := hO.mul (isBigO_refl (fun s : ℝ => s⁻¹) (𝓝[>] 0))
      refine (this.congr' ?_ ?_)
      · filter_upwards with s
        ring
      · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
        field_simp
    exact h1.trans_tendsto (tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto' 0 0 rfl))
  have := (hlim.const_mul D).const_add 1
  rw [mul_zero, add_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  field_simp
  ring

/-- For `α > 1`, as `s ↓ 0`, `u_var ∼ s/(α−1)` and
`u_epi ∼ s²/(D(α−1))`. -/
theorem uncertainty_isEquivalent_zero :
    uVarScale A n D a ~[𝓝[>] 0] (fun s => s / a)
      ∧ uEpiScale A n D a ~[𝓝[>] 0] (fun s => s ^ 2 / (D * a)) := by
  have ht := tScale_tendsto_zero hA hn hD
  have htD := tScale_mul_div_tendsto_zero hA hn hD
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ 0 < tScale A n D s := by
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    exact ⟨hs, TA_pos (by positivity)⟩
  constructor
  · refine isEquivalent_of_tendsto_one ?_
    have h := (ht.const_add 1).inv₀ (by norm_num)
    rw [add_zero, inv_one] at h
    refine h.congr' ?_
    filter_upwards [hpos] with s ⟨hs, hts⟩
    have ha' := ha.ne'
    simp only [Pi.div_apply, uVarScale]
    field_simp
  · refine isEquivalent_of_tendsto_one ?_
    have h := htD.div (ht.const_add 1) (by norm_num)
    rw [add_zero, div_one] at h
    refine h.congr' ?_
    filter_upwards [hpos] with s ⟨hs, hts⟩
    have ha' := ha.ne'
    simp only [Pi.div_apply, uEpiScale]
    field_simp

omit hA in
/-- For `α > 1`, as `s → ∞`, `u_var ∼ s/((α−1)(1+M))` and
`u_epi ∼ sM/((α−1)(1+M))`. -/
theorem uncertainty_isEquivalent_atTop :
    uVarScale A n D a ~[atTop] (fun s => s / (a * (1 + boundM A n)))
      ∧ uEpiScale A n D a ~[atTop] (fun s => s * boundM A n / (a * (1 + boundM A n))) := by
  have ht := (scale_limits_atTop (A := A) hn hD 0).2.1
  have hM := TA_pos (A := A) hn
  have hpos : ∀ᶠ s in atTop, 0 < s ∧ 0 < tScale A n D s := by
    filter_upwards [eventually_gt_atTop 0] with s hs
    exact ⟨hs, TA_pos (by positivity)⟩
  constructor
  · refine isEquivalent_of_tendsto_one ?_
    have h := (tendsto_const_nhds (x := 1 + boundM A n)).div (ht.const_add 1) (by positivity)
    rw [div_self (by positivity)] at h
    refine h.congr' ?_
    filter_upwards [hpos] with s ⟨hs, hts⟩
    simp only [Pi.div_apply, uVarScale]
    field_simp
  · refine isEquivalent_of_tendsto_one ?_
    have h := (ht.mul_const (1 + boundM A n)).div ((ht.const_add 1).const_mul (boundM A n))
      (by positivity)
    rw [show boundM A n * (1 + boundM A n) / (boundM A n * (1 + boundM A n)) = 1 from
      div_self (by positivity)] at h
    refine h.congr' ?_
    filter_upwards [hpos] with s ⟨hs, hts⟩
    simp only [Pi.div_apply, uEpiScale]
    field_simp

omit hA in
/-- The selected uncertainty ratio is uniformly bounded for a fixed prior
(`u_epi/u_var = t_* < M(A,n)`), but neither uncertainty summand has a finite uniform upper bound. -/
theorem summands_unbounded (K : ℝ) :
    ∃ s, 0 < s ∧ K < uVarScale A n D a s ∧ K < uEpiScale A n D a s := by
  obtain ⟨h1, h2⟩ := uncertainty_isEquivalent_atTop (A := A) hn hD a ha
  have hM := TA_pos (A := A) hn
  have g1 : Tendsto (fun s => s / (a * (1 + boundM A n))) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  have g2 : Tendsto (fun s => s * boundM A n / (a * (1 + boundM A n))) atTop atTop :=
    (tendsto_id.atTop_mul_const hM).atTop_div_const (by positivity)
  obtain ⟨s, hs1, hs2, hs0⟩ := ((h1.symm.tendsto_atTop g1).eventually_gt_atTop K).and
    (((h2.symm.tendsto_atTop g2).eventually_gt_atTop K).and (eventually_gt_atTop 0)) |>.exists
  exact ⟨s, hs0, hs1, hs2⟩

end Uncertainty

end NIGBottleneck
