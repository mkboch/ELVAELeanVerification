import Mathlib
import Official.M11
import Official.M12
import Official.M14

/-!
# The sharp inverse-allocation bound `M(A,n)`

`M(A,n) = T_A(n)`. Over all quotient states `0 < t_* < M(A,n)` and
`1/M(A,n) < ν_sel < ∞`, both exact ranges with unattained finite endpoints, also when the states are
restricted to `α > 1`; the uncertainty bounds; the dependence of `M` on `(A,n)` only and its strict
monotonicity; its boundary behaviour; and the sharp aggregate bound `< max_i M(A_i,n_i)`.
-/

noncomputable section

namespace NIGBottleneck

open Filter Topology Set Asymptotics

section Bound

/-- The bound `M(A,n) := T_A(n)`. -/
def boundM (A n : ℝ) : ℝ := TA A n

/-- `M(A,n) = (2A + 1 − n + √((n−2A−1)² + 4n))/(2n)`. -/
theorem boundM_eq (A n : ℝ) :
    boundM A n = (2 * A + 1 - n + Real.sqrt ((n - 2 * A - 1) ^ 2 + 4 * n)) / (2 * n) := rfl

/-- The bound depends only on `A = α₀` and `n = ν₀`, not on the prior center or
on `b`. -/
theorem boundM_prior (p₀ p₀' : Parameters) (hA : p₀.alpha = p₀'.alpha) (hn : p₀.nu = p₀'.nu) :
    boundM p₀.alpha p₀.nu = boundM p₀'.alpha p₀'.nu := by
  rw [hA, hn]

variable (p₀ : Parameters)

/-- `0 < t_* < M(A,n)` for every quotient state. -/
theorem selT_lt_boundM (x : QuotientState) :
    0 < selT p₀ x ∧ selT p₀ x < boundM p₀.alpha p₀.nu := by
  refine ⟨selT_pos p₀ x, ?_⟩
  have hQ := scoreQ_pos p₀ x
  have hn := p₀.nu_pos
  rw [(selT_selNu_eq_score p₀ x).1, boundM]
  exact TA_strictAntiOn p₀.alpha_pos.le (show (0 : ℝ) < p₀.nu from hn)
    (show 0 < p₀.nu * (1 + scoreQ p₀ x) by positivity) (by nlinarith)

/-- `1/M(A,n) < ν_sel < ∞`. -/
theorem inv_boundM_lt_selNu (x : QuotientState) : 1 / boundM p₀.alpha p₀.nu < selNu p₀ x := by
  obtain ⟨h0, h1⟩ := selT_lt_boundM p₀ x
  rw [selNu_eq_inv_selT]
  exact one_div_lt_one_div_of_lt h0 h1

/-- Every value in `(0, M(A,n))` is attained, at any prescribed `γ` and `α > 0`. -/
theorem exists_state_selT_eq (γ α : ℝ) (hα : 0 < α) (τ : ℝ) (hτ : 0 < τ)
    (hτM : τ < boundM p₀.alpha p₀.nu) :
    ∃ x : QuotientState, x.gamma = γ ∧ x.alpha = α ∧ selT p₀ x = τ := by
  have hA := p₀.alpha_pos
  have hn := p₀.nu_pos
  set d := selH p₀.alpha τ with hd
  have hnd : p₀.nu < d := by
    have h := selH_lt_of_lt hA.le hτ hτM
    rw [boundM, selH_TA hn] at h
    exact h
  have hd0 : 0 < d := by linarith
  set Q := d / p₀.nu - 1 with hQ
  have hQpos : 0 < Q := by
    rw [hQ, sub_pos, one_lt_div hn]
    exact hnd
  have hb := bParam_pos p₀
  have hs : 0 < α * ((γ - p₀.gamma) ^ 2 + bParam p₀) / Q := by positivity
  refine ⟨⟨γ, α, α * ((γ - p₀.gamma) ^ 2 + bParam p₀) / Q, hα, hs⟩, rfl, rfl, ?_⟩
  have hscore : scoreQ p₀ ⟨γ, α, α * ((γ - p₀.gamma) ^ 2 + bParam p₀) / Q, hα, hs⟩ = Q := by
    simp only [scoreQ]
    have : 0 < (γ - p₀.gamma) ^ 2 + bParam p₀ := by positivity
    field_simp
  rw [(selT_selNu_eq_score p₀ _).1, hscore]
  have hdn : p₀.nu * (1 + Q) = d := by
    rw [hQ]
    field_simp
    ring
  rw [hdn]
  exact ((selection_eq_iff hd0 hτ).mp rfl).symm

/-- The range of `t_*` over all quotient states is exactly `(0, M(A,n))`. -/
theorem range_selT : range (selT p₀) = Ioo 0 (boundM p₀.alpha p₀.nu) := by
  ext τ
  constructor
  · rintro ⟨x, rfl⟩
    exact selT_lt_boundM p₀ x
  · rintro ⟨h0, h1⟩
    obtain ⟨x, -, -, hx⟩ := exists_state_selT_eq p₀ 0 1 one_pos τ h0 h1
    exact ⟨x, hx⟩

/-- The same range holds for states restricted to `α > 1`. -/
theorem range_selT_alpha_gt_one :
    selT p₀ '' {x | 1 < x.alpha} = Ioo 0 (boundM p₀.alpha p₀.nu) := by
  ext τ
  constructor
  · rintro ⟨x, -, rfl⟩
    exact selT_lt_boundM p₀ x
  · rintro ⟨h0, h1⟩
    obtain ⟨x, -, hα, hx⟩ := exists_state_selT_eq p₀ 0 2 two_pos τ h0 h1
    exact ⟨x, by simp [hα], hx⟩

lemma selNu_image_eq (S : Set QuotientState)
    (hS : selT p₀ '' S = Ioo 0 (boundM p₀.alpha p₀.nu)) :
    selNu p₀ '' S = Ioi (1 / boundM p₀.alpha p₀.nu) := by
  have hM : 0 < boundM p₀.alpha p₀.nu := TA_pos p₀.nu_pos
  ext ν
  constructor
  · rintro ⟨x, -, rfl⟩
    exact inv_boundM_lt_selNu p₀ x
  · intro hν
    have hν' : 1 / boundM p₀.alpha p₀.nu < ν := hν
    have hν0 : 0 < ν := lt_trans (by positivity) hν'
    have h1 : 1 / ν < boundM p₀.alpha p₀.nu := by
      rw [div_lt_iff₀ hν0]
      rw [div_lt_iff₀ hM] at hν'
      linarith
    have hmem : 1 / ν ∈ selT p₀ '' S := by rw [hS]; exact ⟨by positivity, h1⟩
    obtain ⟨x, hxS, hx⟩ := hmem
    refine ⟨x, hxS, ?_⟩
    rw [selNu_eq_inv_selT, hx, one_div_one_div]

/-- The range of `ν_sel` is exactly `(1/M(A,n), ∞)`, also for `α > 1`. -/
theorem range_selNu :
    range (selNu p₀) = Ioi (1 / boundM p₀.alpha p₀.nu)
      ∧ selNu p₀ '' {x | 1 < x.alpha} = Ioi (1 / boundM p₀.alpha p₀.nu) := by
  refine ⟨?_, selNu_image_eq p₀ _ (range_selT_alpha_gt_one p₀)⟩
  rw [← image_univ]
  exact selNu_image_eq p₀ _ (by rw [image_univ]; exact range_selT p₀)

/-- The finite endpoints are not attained by admissible states. -/
theorem endpoints_not_attained (x : QuotientState) :
    selT p₀ x ≠ boundM p₀.alpha p₀.nu ∧ selNu p₀ x ≠ 1 / boundM p₀.alpha p₀.nu :=
  ⟨(selT_lt_boundM p₀ x).2.ne, (inv_boundM_lt_selNu p₀ x).ne'⟩

/-- For `α > 1`, `0 < u_epi/u_var < M(A,n)` and
`u_epi/V_z < M(A,n)/(1+M(A,n))` at the selected representative. -/
theorem uncertainty_bound (x : QuotientState) (hα : 1 < x.alpha) :
    0 < uEpi (fiberParameters x (selTPos p₀ x)) / uVar (fiberParameters x (selTPos p₀ x))
      ∧ uEpi (fiberParameters x (selTPos p₀ x)) / uVar (fiberParameters x (selTPos p₀ x))
        < boundM p₀.alpha p₀.nu
      ∧ uEpi (fiberParameters x (selTPos p₀ x)) / totalVar (fiberParameters x (selTPos p₀ x))
        < boundM p₀.alpha p₀.nu / (1 + boundM p₀.alpha p₀.nu) := by
  obtain ⟨h1, -, h3, -⟩ := selected_ratios x hα p₀
  obtain ⟨ht0, htM⟩ := selT_lt_boundM p₀ x
  rw [h1, h3]
  refine ⟨ht0, htM, ?_⟩
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

end Bound

section Monotone

/-- `M(A,n)` is strictly increasing in `A`. -/
theorem boundM_strictMono_A {A A' n : ℝ} (hA : 0 ≤ A) (hAA : A < A') (hn : 0 < n) :
    boundM A n < boundM A' n := by
  unfold boundM
  have h1 := selH_TA (A := A) hn
  have h2 := selH_TA (A := A') hn
  have ht := TA_pos (A := A) hn
  have ht' := TA_pos (A := A') hn
  by_contra hle
  rw [not_lt] at hle
  have hgt : n < selH A' (TA A n) := by
    have hlt : selH A (TA A n) < selH A' (TA A n) := by
      unfold selH
      have : 2 * A / (1 + TA A n) < 2 * A' / (1 + TA A n) :=
        div_lt_div_of_pos_right (by linarith) (by linarith)
      linarith
    linarith [h1]
  rcases hle.lt_or_eq with h | h
  · have := selH_lt_of_lt (A := A') (by linarith) ht' h
    linarith
  · rw [← h] at hgt
    linarith

/-- `M(A,n)` is strictly decreasing in `n`. -/
theorem boundM_strictAnti_n {A : ℝ} (hA : 0 ≤ A) : StrictAntiOn (boundM A) (Ioi 0) :=
  TA_strictAntiOn hA

end Monotone

section Boundary

/-- `M(A,n) → 1/n` as `A ↓ 0`. -/
theorem boundM_tendsto_A_zero {n : ℝ} (hn : 0 < n) :
    Tendsto (fun A => boundM A n) (𝓝[>] 0) (𝓝 (1 / n)) := by
  have hc : Continuous fun A : ℝ =>
      (2 * A + 1 - n + Real.sqrt ((n - 2 * A - 1) ^ 2 + 4 * n)) / (2 * n) := by fun_prop
  have h0 : (2 * 0 + 1 - n + Real.sqrt ((n - 2 * 0 - 1) ^ 2 + 4 * n)) / (2 * n) = 1 / n := by
    rw [show (n - 2 * 0 - 1) ^ 2 + 4 * n = (n + 1) ^ 2 by ring, Real.sqrt_sq (by linarith)]
    field_simp
    ring
  have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  rw [h0] at h
  exact h

/-- `M(A,n) = 2A/n + (1−n)/n + O(A⁻¹)` as `A → ∞`. -/
theorem boundM_isBigO_A_atTop {n : ℝ} (hn : 0 < n) :
    (fun A => boundM A n - (2 * A / n + (1 - n) / n)) =O[atTop] (fun A : ℝ => A⁻¹) := by
  refine IsBigO.of_bound' ?_
  filter_upwards [eventually_ge_atTop (max n 1)] with A hA
  have hA1 : 1 ≤ A := le_trans (le_max_right _ _) hA
  have hAn : n ≤ A := le_trans (le_max_left _ _) hA
  have hApos : 0 < A := by linarith
  set H := 2 * A + 1 - n with hH
  have hHA : A ≤ H := by rw [hH]; linarith
  set r := Real.sqrt (H ^ 2 + 4 * n) with hr
  have hr2 : r ^ 2 = H ^ 2 + 4 * n := Real.sq_sqrt (by positivity)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrH : H < r := by
    rw [hr, Real.lt_sqrt (by linarith)]
    linarith
  have hM : boundM A n = (H + r) / (2 * n) := by
    rw [boundM_eq, hr, hH]
    congr 2
    ring_nf
  have hrem : boundM A n - (2 * A / n + (1 - n) / n) = (r - H) / (2 * n) := by
    rw [hM, hH]
    field_simp
    ring
  rw [hrem, Real.norm_of_nonneg (div_nonneg (by linarith) (by linarith)),
    Real.norm_of_nonneg (inv_nonneg.mpr hApos.le), div_le_iff₀ (by linarith)]
  have hprod : (r - H) * (r + H) = 4 * n := by nlinarith [hr2]
  have : (r - H) * (2 * A) ≤ 4 * n := by nlinarith
  rw [inv_mul_eq_div, le_div_iff₀ hApos]
  nlinarith

/-- The defining equation `n M(1+M) = 1 + (2A+1) M` of `M = T_A(n)`. -/
lemma boundM_defining {A n : ℝ} (hn : 0 < n) :
    n * boundM A n * (1 + boundM A n) = 1 + (2 * A + 1) * boundM A n := by
  have h := TA_selection_eq (A := A) hn
  have hM := TA_pos (A := A) hn
  unfold boundM
  set M := TA A n
  rw [h]
  field_simp
  ring

/-- `M(A,n) = (2A+1)/n − 2A/(2A+1) + O(n)` as `n ↓ 0`. -/
theorem boundM_isBigO_n_zero {A : ℝ} (hA : 0 < A) :
    (fun n => boundM A n - ((2 * A + 1) / n - 2 * A / (2 * A + 1)))
      =O[𝓝[>] 0] (fun n : ℝ => n) := by
  have hC0 : 0 < 2 * A + 1 := by linarith
  refine IsBigO.of_bound (4 * A / (2 * A + 1) ^ 2 + 16 * A ^ 2 / (2 * A + 1) ^ 3) ?_
  have hsmall : ∀ᶠ n in 𝓝[>] (0 : ℝ), n < (2 * A + 1) / (4 * A) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
  filter_upwards [self_mem_nhdsWithin, hsmall] with n (hn : 0 < n) hnC
  set M := boundM A n with hMdef
  have hM : 0 < M := TA_pos hn
  have hdef := boundM_defining (A := A) hn
  rw [← hMdef] at hdef
  -- `n M = (2A+1) − 2A/(1+M)`
  have hnM : n * M = 2 * A + 1 - 2 * A / (1 + M) := by
    field_simp
    linarith
  have hfrac : 2 * A / (1 + M) ≤ 2 * A / M :=
    div_le_div_of_nonneg_left (by linarith) hM (by linarith)
  have hnM1 : 1 ≤ n * M := by
    have : 2 * A / (1 + M) ≤ 2 * A := div_le_self (by linarith) (by linarith)
    linarith
  have hinvM : 2 * A / M ≤ 2 * A * n := by
    rw [div_le_iff₀ hM]
    nlinarith
  have hnMlow : (2 * A + 1) / 2 ≤ n * M := by
    have h2 : 2 * A * n ≤ (2 * A + 1) / 2 := by
      rw [lt_div_iff₀ (by positivity)] at hnC
      linarith
    linarith
  set P := n * (1 + M) with hP
  have hPlow : (2 * A + 1) / 2 ≤ P := by rw [hP]; nlinarith
  have hPpos : 0 < P := by linarith
  have hid : (M - ((2 * A + 1) / n - 2 * A / (2 * A + 1))) * P
      = 2 * A / (2 * A + 1) * (P - (2 * A + 1)) := by
    rw [hP]
    field_simp
    linear_combination (2 * A + 1) * hdef
  have hPC : |P - (2 * A + 1)| ≤ n + 4 * A * n / (2 * A + 1) := by
    have e : P - (2 * A + 1) = n - 2 * A / (1 + M) := by rw [hP]; linarith
    have hM' : 2 * A / M ≤ 4 * A * n / (2 * A + 1) := by
      rw [div_le_div_iff₀ hM hC0]
      nlinarith
    rw [e, abs_le]
    have h0 : 0 ≤ 2 * A / (1 + M) := by positivity
    constructor <;> linarith
  have hrem : M - ((2 * A + 1) / n - 2 * A / (2 * A + 1))
      = 2 * A / (2 * A + 1) * (P - (2 * A + 1)) / P := by
    rw [← hid]
    field_simp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hn, hrem, abs_div, abs_mul,
    abs_of_pos hPpos, abs_of_pos (by positivity : (0 : ℝ) < 2 * A / (2 * A + 1)),
    div_le_iff₀ hPpos]
  have h1 : 2 * A / (2 * A + 1) * |P - (2 * A + 1)|
      ≤ 2 * A / (2 * A + 1) * (n + 4 * A * n / (2 * A + 1)) :=
    mul_le_mul_of_nonneg_left hPC (by positivity)
  have h2 : 2 * A / (2 * A + 1) * (n + 4 * A * n / (2 * A + 1))
      = (4 * A / (2 * A + 1) ^ 2 + 16 * A ^ 2 / (2 * A + 1) ^ 3) * n * ((2 * A + 1) / 2) := by
    field_simp
    ring
  have h3 : (4 * A / (2 * A + 1) ^ 2 + 16 * A ^ 2 / (2 * A + 1) ^ 3) * n * ((2 * A + 1) / 2)
      ≤ (4 * A / (2 * A + 1) ^ 2 + 16 * A ^ 2 / (2 * A + 1) ^ 3) * n * P :=
    mul_le_mul_of_nonneg_left hPlow (by positivity)
  linarith

/-- `M(A,n) = 1/n + 2A/n² + O(n⁻³)` as `n → ∞`. -/
theorem boundM_isBigO_n_atTop {A : ℝ} (hA : 0 < A) :
    (fun n => boundM A n - (1 / n + 2 * A / n ^ 2)) =O[atTop] (fun n : ℝ => (n ^ 3)⁻¹) := by
  refine IsBigO.of_bound (4 * A * (2 * A + 2)) ?_
  filter_upwards [eventually_ge_atTop (max (4 * A) 2)] with n hn
  have hn4 : 4 * A ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : 0 < n := by linarith
  set M := boundM A n with hMdef
  have hM : 0 < M := TA_pos hn0
  have hdef := boundM_defining (A := A) hn0
  rw [← hMdef] at hdef
  -- `M ≤ 2/n`
  have hMup : M ≤ 2 / n := by
    have h1 : n * M - 1 ≤ 2 * A * M := by
      have e : n * M - 1 = 2 * A * M / (1 + M) := by
        field_simp
        linarith
      rw [e]
      exact div_le_self (by positivity) (by linarith)
    rw [le_div_iff₀ hn0]
    nlinarith
  have hM1 : M ≤ 1 := le_trans hMup (by rw [div_le_one hn0]; exact hn2)
  have hid : (M - (1 / n + 2 * A / n ^ 2)) * (n ^ 2 * (1 + M) ^ 2)
      = 2 * A * M * (2 * A - 1 - M) := by
    field_simp
    linear_combination (n * (1 + M) + 2 * A) * hdef
  have hden : 0 < n ^ 2 * (1 + M) ^ 2 := by positivity
  have hrem : M - (1 / n + 2 * A / n ^ 2)
      = 2 * A * M * (2 * A - 1 - M) / (n ^ 2 * (1 + M) ^ 2) := by
    rw [← hid]
    field_simp
  rw [hrem, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_pos hden,
    abs_of_pos (by positivity : (0 : ℝ) < (n ^ 3)⁻¹), div_le_iff₀ hden]
  have habs : |2 * A * M * (2 * A - 1 - M)| ≤ 2 * A * M * (2 * A + 2) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * A * M)]
    have : |2 * A - 1 - M| ≤ 2 * A + 2 := by
      rw [abs_le]
      constructor <;> linarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hstep : 2 * A * M * (2 * A + 2) ≤ 4 * A * (2 * A + 2) / n := by
    have := mul_le_mul_of_nonneg_left hMup (by positivity : (0 : ℝ) ≤ 2 * A * (2 * A + 2))
    calc 2 * A * M * (2 * A + 2) = 2 * A * (2 * A + 2) * M := by ring
      _ ≤ 2 * A * (2 * A + 2) * (2 / n) := this
      _ = 4 * A * (2 * A + 2) / n := by ring
  have hfin : 4 * A * (2 * A + 2) / n
      ≤ 4 * A * (2 * A + 2) * (n ^ 3)⁻¹ * (n ^ 2 * (1 + M) ^ 2) := by
    have e : 4 * A * (2 * A + 2) * (n ^ 3)⁻¹ * (n ^ 2 * (1 + M) ^ 2)
        = 4 * A * (2 * A + 2) / n * (1 + M) ^ 2 := by
      field_simp
    rw [e]
    have : 1 ≤ (1 + M) ^ 2 := by nlinarith
    have hpos : 0 ≤ 4 * A * (2 * A + 2) / n := by positivity
    nlinarith
  linarith

end Boundary

section Aggregate

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The selected hierarchy `(γ, 1/t_*, α, s/(1+t_*))` of a state. -/
def selParams (p₀ : Parameters) (x : QuotientState) : Parameters :=
  fiberParameters x (selTPos p₀ x)

/-- The aggregate uncertainty ratio `Σ c_i u_epi,i / Σ c_i u_var,i` of finitely
many coordinates, each with its own prior and state, at their selected hierarchies. -/
def aggRatio (p₀ : ι → Parameters) (x : ι → QuotientState) (c : ι → ℝ) : ℝ :=
  (∑ i, c i * uEpi (selParams (p₀ i) (x i))) / (∑ i, c i * uVar (selParams (p₀ i) (x i)))

/-- `max_i M(A_i, n_i)`. -/
def maxBound (p₀ : ι → Parameters) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => boundM (p₀ i).alpha (p₀ i).nu

lemma uVar_selParams_pos (p₀ : Parameters) (x : QuotientState) (hα : 1 < x.alpha) :
    0 < uVar (selParams p₀ x) := by
  rw [selParams, uVar_fiber x hα]
  have := x.s_pos
  have : (0 : ℝ) < (selTPos p₀ x : ℝ) := (selTPos p₀ x).property
  have : 0 < x.alpha - 1 := by linarith
  positivity

lemma uEpi_selParams_eq (p₀ : Parameters) (x : QuotientState) (hα : 1 < x.alpha) :
    uEpi (selParams p₀ x) = uVar (selParams p₀ x) * selT p₀ x := by
  have h := (selected_ratios x hα p₀).1
  have hu := uVar_selParams_pos p₀ x hα
  rw [selParams] at hu ⊢
  rw [← h]
  field_simp

/-- For positive weights and `α_i > 1`, the aggregate ratio is strictly less
than `max_i M(A_i, n_i)`. -/
theorem aggRatio_lt_maxBound (p₀ : ι → Parameters) (x : ι → QuotientState) (c : ι → ℝ)
    (hα : ∀ i, 1 < (x i).alpha) (hc : ∀ i, 0 < c i) : aggRatio p₀ x c < maxBound p₀ := by
  unfold aggRatio
  have hD : 0 < ∑ i, c i * uVar (selParams (p₀ i) (x i)) :=
    Finset.sum_pos (fun i _ => mul_pos (hc i) (uVar_selParams_pos _ _ (hα i)))
      Finset.univ_nonempty
  rw [div_lt_iff₀ hD, Finset.mul_sum]
  refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => ?_
  rw [uEpi_selParams_eq _ _ (hα i)]
  have ht := (selT_lt_boundM (p₀ i) (x i)).2
  have hle : boundM (p₀ i).alpha (p₀ i).nu ≤ maxBound p₀ := by
    unfold maxBound
    exact Finset.le_sup' (fun k => boundM (p₀ k).alpha (p₀ k).nu) (Finset.mem_univ i)
  have hpos := mul_pos (hc i) (uVar_selParams_pos (p₀ i) _ (hα i))
  nlinarith

omit [Nonempty ι] in
lemma sum_update [DecidableEq ι] (f : ι → QuotientState → ℝ) (x : ι → QuotientState) (j : ι)
    (y : QuotientState) :
    ∑ i, f i (Function.update x j y i) = (∑ i ∈ Finset.univ.erase j, f i (x i)) + f j y := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- The state `(γ₀, α = 2, s = e^u)` used to approach the bound. -/
def approachState (p₀ : Parameters) (u : ℝ) : QuotientState :=
  ⟨p₀.gamma, 2, Real.exp u, two_pos, Real.exp_pos u⟩

lemma selT_approachState_tendsto (p₀ : Parameters) :
    Tendsto (fun u => selT p₀ (approachState p₀ u)) atTop (𝓝 (boundM p₀.alpha p₀.nu)) := by
  have hQ : Tendsto (fun u => scoreQ p₀ (approachState p₀ u)) atTop (𝓝 0) := by
    have h : Tendsto (fun u : ℝ => 2 * bParam p₀ * Real.exp (-u)) atTop (𝓝 (2 * bParam p₀ * 0)) :=
      (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul _
    rw [mul_zero] at h
    refine h.congr' (Eventually.of_forall fun u => ?_)
    simp only [scoreQ, approachState, sub_self]
    rw [Real.exp_neg]
    field_simp
    ring
  have hd : Tendsto (fun u => p₀.nu * (1 + scoreQ p₀ (approachState p₀ u))) atTop
      (𝓝 p₀.nu) := by
    have := (hQ.const_add 1).const_mul p₀.nu
    rwa [add_zero, mul_one] at this
  have h := (continuousAt_TA (A := p₀.alpha) p₀.nu_pos).tendsto.comp hd
  refine h.congr' (Eventually.of_forall fun u => ?_)
  exact ((selT_selNu_eq_score p₀ _).1).symm

/-- The aggregate bound is sharp over the joint state space: for every `ε > 0`
there are states with all `α_i > 1` whose aggregate ratio exceeds `max_i M(A_i,n_i) − ε`. -/
theorem aggRatio_sharp (p₀ : ι → Parameters) (x : ι → QuotientState) (c : ι → ℝ)
    (hα : ∀ i, 1 < (x i).alpha) (hc : ∀ i, 0 < c i) (ε : ℝ) (hε : 0 < ε) :
    ∃ x' : ι → QuotientState, (∀ i, 1 < (x' i).alpha) ∧ maxBound p₀ - ε < aggRatio p₀ x' c := by
  classical
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i => boundM (p₀ i).alpha (p₀ i).nu)
  set Mj := boundM (p₀ j).alpha (p₀ j).nu
  have hmax : maxBound p₀ = Mj := hj
  set N := ∑ i ∈ Finset.univ.erase j, c i * uEpi (selParams (p₀ i) (x i))
  set D := ∑ i ∈ Finset.univ.erase j, c i * uVar (selParams (p₀ i) (x i))
  set t := fun u => selT (p₀ j) (approachState (p₀ j) u)
  set U := fun u => uVar (selParams (p₀ j) (approachState (p₀ j) u))
  have hα2 : ∀ u, 1 < (approachState (p₀ j) u).alpha := fun u => by
    simp [approachState]
  have hU : ∀ u, U u = Real.exp u / (1 + t u) := by
    intro u
    simp only [U, t, selParams]
    rw [uVar_fiber _ (hα2 u)]
    norm_num [approachState, selTPos]
  have ht := selT_approachState_tendsto (p₀ j)
  have hM0 : 0 < Mj := TA_pos (p₀ j).nu_pos
  have hUtop : Tendsto U atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ (Real.tendsto_exp_atTop.atTop_div_const
      (show (0 : ℝ) < 1 + Mj by linarith))
    filter_upwards with u
    rw [hU u]
    have htu := selT_lt_boundM (p₀ j) (approachState (p₀ j) u)
    exact div_le_div_of_nonneg_left (Real.exp_pos u).le (by linarith [htu.1]) (by linarith [htu.2])
  have hratio : Tendsto (fun u => (N / U u + c j * t u) / (D / U u + c j)) atTop
      (𝓝 ((0 + c j * Mj) / (0 + c j))) :=
    ((tendsto_const_nhds.div_atTop hUtop).add (ht.const_mul (c j))).div
      ((tendsto_const_nhds.div_atTop hUtop).add tendsto_const_nhds) (by simp [(hc j).ne'])
  rw [zero_add, zero_add, mul_div_cancel_left₀ _ (hc j).ne'] at hratio
  obtain ⟨u, hu, hUpos⟩ :=
    ((tendsto_order.1 hratio).1 (Mj - ε) (by linarith)).and
      (hUtop.eventually_gt_atTop 0) |>.exists
  refine ⟨Function.update x j (approachState (p₀ j) u), fun i => ?_, ?_⟩
  · by_cases hi : i = j
    · subst hi; rw [Function.update_self]; exact hα2 u
    · rw [Function.update_of_ne hi]; exact hα i
  · rw [hmax]
    unfold aggRatio
    rw [sum_update (fun i y => c i * uEpi (selParams (p₀ i) y)),
      sum_update (fun i y => c i * uVar (selParams (p₀ i) y))]
    rw [uEpi_selParams_eq _ _ (hα2 u)]
    have e : (N + c j * (U u * t u)) / (D + c j * U u)
        = (N / U u + c j * t u) / (D / U u + c j) := by
      field_simp
    change Mj - ε < (N + c j * (U u * t u)) / (D + c j * U u)
    rw [e]
    exact hu

end Aggregate

end NIGBottleneck
