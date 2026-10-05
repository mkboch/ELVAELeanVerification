import Mathlib
import Official.M11
import Official.M12
import Official.M15

/-!
# Cross-coordinate comparisons and aggregation

For finitely many latent coordinates, each with its own admissible state and
complete prior: (1) equal calibrations `(A, n)` make score order, `ν` order and reversed `t` order
equivalent, even with different centers and `b`; (2) `Q_i ≤ Q_j`, `n_i ≤ n_j`, `A_i ≥ A_j` imply
`ν_i ≤ ν_j` and `t_i ≥ t_j`, while score ordering alone does not suffice without restrictions on the
calibrations; (3) componentwise score inequalities transfer to weighted sums under common
calibrations and common nonnegative weights, whereas ordering only mean scores is insufficient;
(4) the aggregate uncertainty ratio formula, its monotonicity at fixed variance weights, and the
failure of that monotonicity without control of the variance weights.
-/

noncomputable section

namespace NIGBottleneck

open Filter Topology Set

section Basic

/-- Every positive score is realized by a state, with any prescribed `γ` and `α > 0`. -/
theorem exists_state_score (p₀ : Parameters) (γ α : ℝ) (hα : 0 < α) (Q : ℝ) (hQ : 0 < Q) :
    ∃ x : QuotientState, x.gamma = γ ∧ x.alpha = α ∧ scoreQ p₀ x = Q := by
  have hb := bParam_pos p₀
  have hs : 0 < α * ((γ - p₀.gamma) ^ 2 + bParam p₀) / Q := by positivity
  refine ⟨⟨γ, α, α * ((γ - p₀.gamma) ^ 2 + bParam p₀) / Q, hα, hs⟩, rfl, rfl, ?_⟩
  simp only [scoreQ]
  have : 0 < (γ - p₀.gamma) ^ 2 + bParam p₀ := by positivity
  field_simp

/-- `T_A(d)` is strictly increasing in `A ≥ 0` (for fixed `d > 0`). -/
theorem TA_strictMono_A {A A' d : ℝ} (hA : 0 ≤ A) (hAA : A < A') (hd : 0 < d) :
    TA A d < TA A' d :=
  boundM_strictMono_A hA hAA hd

/-- `d − 2A < Φ_A(d) ≤ d` for `A ≥ 0`, `d > 0`. -/
theorem PhiA_bounds {A d : ℝ} (hA : 0 ≤ A) (hd : 0 < d) : d - 2 * A ≤ PhiA A d ∧ PhiA A d ≤ d := by
  have h := gA_PhiA (A := A) hd
  have hr := PhiA_pos (A := A) hd
  set r := PhiA A d
  have h1 : 2 * A * r / (1 + r) ≤ 2 * A := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h2 : 0 ≤ 2 * A * r / (1 + r) := by positivity
  unfold gA at h
  constructor <;> linarith

end Basic

section Pairwise

/-- With equal calibrations `A_i = A_j`, `n_i = n_j` (centers and
`b`-parameters may differ, each score computed with its own prior),
`Q_i < Q_j ↔ ν_i < ν_j ↔ t_i > t_j`. -/
theorem equal_calibration_order (p p' : Parameters) (hA : p.alpha = p'.alpha) (hn : p.nu = p'.nu)
    (x x' : QuotientState) :
    (scoreQ p x < scoreQ p' x' ↔ selNu p x < selNu p' x')
      ∧ (selNu p x < selNu p' x' ↔ selT p' x' < selT p x) := by
  have hA0 := p.alpha_pos
  have hn0 := p.nu_pos
  rw [(selT_eq_tOfScore p x).1, (selT_eq_tOfScore p' x').1, (selT_eq_tOfScore p x).2,
    (selT_eq_tOfScore p' x').2, ← hA, ← hn]
  have hQ := scoreQ_pos p x
  have hQ' := scoreQ_pos p' x'
  exact ⟨((nuOfScore_strictMonoOn hA0 hn0).lt_iff_lt hQ hQ').symm,
    ((nuOfScore_strictMonoOn hA0 hn0).lt_iff_lt hQ hQ').trans
      ((tOfScore_strictAntiOn hA0 hn0).lt_iff_gt hQ' hQ).symm⟩

/-- `Q_i ≤ Q_j`, `n_i ≤ n_j` and `A_i ≥ A_j` imply `ν_i ≤ ν_j` and
`t_i ≥ t_j`. -/
theorem sufficient_order (p p' : Parameters) (x x' : QuotientState)
    (hQ : scoreQ p x ≤ scoreQ p' x') (hn : p.nu ≤ p'.nu) (hA : p'.alpha ≤ p.alpha) :
    selNu p x ≤ selNu p' x' ∧ selT p' x' ≤ selT p x := by
  have hQ0 := scoreQ_pos p x
  have hd : p.nu * (1 + scoreQ p x) ≤ p'.nu * (1 + scoreQ p' x') := by
    have := p.nu_pos
    nlinarith
  have hd0 : 0 < p.nu * (1 + scoreQ p x) := by have := p.nu_pos; positivity
  have ht : selT p' x' ≤ selT p x := by
    rw [(selT_selNu_eq_score p x).1, (selT_selNu_eq_score p' x').1]
    calc TA p'.alpha (p'.nu * (1 + scoreQ p' x'))
        ≤ TA p.alpha (p'.nu * (1 + scoreQ p' x')) := by
          rcases hA.lt_or_eq with h | h
          · exact (TA_strictMono_A p'.alpha_pos.le h (by linarith)).le
          · rw [h]
      _ ≤ TA p.alpha (p.nu * (1 + scoreQ p x)) :=
          (TA_strictAntiOn p.alpha_pos.le).antitoneOn hd0 (show (0 : ℝ) < _ by linarith) hd
  refine ⟨?_, ht⟩
  rw [selNu_eq_inv_selT, selNu_eq_inv_selT]
  exact one_div_le_one_div_of_le (selT_pos p' x') ht

/-- Without restrictions on the calibrations, score ordering alone does
not imply allocation ordering: here `Q_i < Q_j` but `ν_i > ν_j` (common `A = 1`, `n_i = 3`,
`n_j = 1`). -/
theorem score_order_insufficient :
    ∃ (p p' : Parameters) (x x' : QuotientState), p.alpha = p'.alpha
      ∧ scoreQ p x < scoreQ p' x' ∧ selNu p' x' < selNu p x := by
  let p := priorOfCoords 0 1 1 3 one_pos one_pos (by norm_num)
  let p' := priorOfCoords 0 1 1 1 one_pos one_pos one_pos
  obtain ⟨x, -, -, hx⟩ := exists_state_score p 0 1 one_pos 1 one_pos
  obtain ⟨x', -, -, hx'⟩ := exists_state_score p' 0 1 one_pos 2 two_pos
  refine ⟨p, p', x, x', rfl, by rw [hx, hx']; norm_num, ?_⟩
  rw [(selT_selNu_eq_score p x).2, (selT_selNu_eq_score p' x').2, hx, hx']
  have h1 := (PhiA_bounds (A := 1) zero_le_one (show (0 : ℝ) < 1 * (1 + 2) by norm_num)).2
  have h2 := (PhiA_bounds (A := 1) zero_le_one (show (0 : ℝ) < 3 * (1 + 1) by norm_num)).1
  change PhiA 1 (1 * (1 + 2)) < PhiA 1 (3 * (1 + 1))
  linarith

end Pairwise

section Collections

variable {ι : Type*} [Fintype ι]

/-- With the same calibrations and the same nonnegative aggregation
weights, componentwise score inequalities imply the corresponding inequalities for weighted sums of
allocations and of inverse allocations. -/
theorem weighted_sums_order (A n Q Q' c : ι → ℝ) (hA : ∀ i, 0 < A i) (hn : ∀ i, 0 < n i)
    (hQ : ∀ i, 0 < Q i) (hQQ : ∀ i, Q i ≤ Q' i) (hc : ∀ i, 0 ≤ c i) :
    ∑ i, c i * tOfScore (A i) (n i) (Q' i) ≤ ∑ i, c i * tOfScore (A i) (n i) (Q i)
      ∧ ∑ i, c i * nuOfScore (A i) (n i) (Q i) ≤ ∑ i, c i * nuOfScore (A i) (n i) (Q' i) := by
  constructor
  · refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hc i)
    exact (tOfScore_strictAntiOn (hA i) (hn i)).antitoneOn (hQ i)
      (show (0 : ℝ) < Q' i from lt_of_lt_of_le (hQ i) (hQQ i)) (hQQ i)
  · refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hc i)
    exact (nuOfScore_strictMonoOn (hA i) (hn i)).monotoneOn (hQ i)
      (show (0 : ℝ) < Q' i from lt_of_lt_of_le (hQ i) (hQQ i)) (hQQ i)

omit [Fintype ι] in
/-- By strict convexity, `(H(1) + H(3))/2 > H(2)` for `H = t_*` and for
`H = ν_sel`, so the same mean score can produce different mean allocations. -/
theorem mean_score_same_mean_allocation_differs {A n : ℝ} (hA : 0 < A) (hn : 0 < n) :
    tOfScore A n 2 < (tOfScore A n 1 + tOfScore A n 3) / 2
      ∧ nuOfScore A n 2 < (nuOfScore A n 1 + nuOfScore A n 3) / 2 := by
  have h1 := (tOfScore_strictConvexOn hA hn).2 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show (3 : ℝ) ∈ Ioi 0 by norm_num) (by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num)
  have h2 := (nuOfScore_strictConvexOn hA hn).2 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show (3 : ℝ) ∈ Ioi 0 by norm_num) (by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at h1 h2
  norm_num at h1 h2
  constructor <;> linarith

omit [Fintype ι] in
lemma continuousAt_tOfScore {A n Q : ℝ} (hn : 0 < n) (hQ : 0 < Q) :
    ContinuousAt (tOfScore A n) Q := by
  have hd : 0 < n * (1 + Q) := by positivity
  unfold tOfScore
  exact (continuousAt_TA hd).comp (f := fun Q => n * (1 + Q)) (by fun_prop)

omit [Fintype ι] in
lemma continuousAt_nuOfScore {A n Q : ℝ} (hn : 0 < n) (hQ : 0 < Q) :
    ContinuousAt (nuOfScore A n) Q := by
  have hd : 0 < n * (1 + Q) := by positivity
  have hc : ContinuousAt (PhiA A) (n * (1 + Q)) := by
    have hT := continuousAt_TA (A := A) hd
    have hT0 := TA_pos (A := A) hd
    refine (hT.inv₀ hT0.ne').congr ?_
    filter_upwards [Ioi_mem_nhds hd] with d (hd' : 0 < d)
    rw [PhiA_eq_inv_TA hd', one_div]
    rfl
  unfold nuOfScore
  exact hc.comp (f := fun Q => n * (1 + Q)) (by fun_prop)

omit [Fintype ι] in
/-- Ordering only the mean scores is insufficient, even strictly: the
pair of scores `(1, 3)` has mean score `2 > 2 − ε` but a larger mean `t_*` than the balanced
collection `(2 − ε, 2 − ε)`; and mean score `2 < 2 + ε` but a larger mean `ν_sel` than
`(2 + ε, 2 + ε)`, for some `ε ∈ (0, 1)`. -/
theorem mean_score_reversal {A n : ℝ} (hA : 0 < A) (hn : 0 < n) :
    (∃ ε, 0 < ε ∧ ε < 1 ∧ tOfScore A n (2 - ε) < (tOfScore A n 1 + tOfScore A n 3) / 2)
      ∧ (∃ ε, 0 < ε ∧ ε < 1 ∧ nuOfScore A n (2 + ε) < (nuOfScore A n 1 + nuOfScore A n 3) / 2) := by
  obtain ⟨h1, h2⟩ := mean_score_same_mean_allocation_differs hA hn
  constructor
  · have hev := (continuousAt_tOfScore (A := A) hn two_pos).eventually (gt_mem_nhds h1)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨min (δ / 2) (1 / 2), lt_min (by linarith) (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num), hball ?_⟩
    rw [Real.dist_eq, show 2 - min (δ / 2) (1 / 2) - 2 = -min (δ / 2) (1 / 2) by ring, abs_neg,
      abs_of_pos (lt_min (by linarith) (by norm_num))]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  · have hev := (continuousAt_nuOfScore (A := A) hn two_pos).eventually (gt_mem_nhds h2)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨min (δ / 2) (1 / 2), lt_min (by linarith) (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num), hball ?_⟩
    rw [Real.dist_eq, show 2 + min (δ / 2) (1 / 2) - 2 = min (δ / 2) (1 / 2) by ring,
      abs_of_pos (lt_min (by linarith) (by norm_num))]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

end Collections

section AggregateFormula

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
/-- If every `α_i > 1`, with `V_i = s_i/(α_i − 1)`,
`Σ c_i u_epi,i / Σ c_i u_var,i = Σ c_i V_i t_i/(1+t_i) / Σ c_i V_i/(1+t_i)
 = Σ c_i u_var,i t_i / Σ c_i u_var,i`. -/
theorem aggregate_ratio_formula (p₀ : ι → Parameters) (x : ι → QuotientState) (c : ι → ℝ)
    (hα : ∀ i, 1 < (x i).alpha) :
    aggRatio p₀ x c
        = (∑ i, c i * ((x i).s / ((x i).alpha - 1)) * (selT (p₀ i) (x i) / (1 + selT (p₀ i) (x i))))
          / (∑ i, c i * ((x i).s / ((x i).alpha - 1)) * (1 / (1 + selT (p₀ i) (x i))))
      ∧ aggRatio p₀ x c
        = (∑ i, c i * uVar (selParams (p₀ i) (x i)) * selT (p₀ i) (x i))
          / (∑ i, c i * uVar (selParams (p₀ i) (x i))) := by
  have hV : ∀ i, uVar (selParams (p₀ i) (x i))
      = (x i).s / ((x i).alpha - 1) * (1 / (1 + selT (p₀ i) (x i))) := by
    intro i
    rw [selParams, uVar_fiber _ (hα i)]
    have : (x i).alpha - 1 ≠ 0 := by linarith [hα i]
    have : 1 + selT (p₀ i) (x i) ≠ 0 := by linarith [selT_pos (p₀ i) (x i)]
    simp only [selTPos]
    field_simp
  have hE : ∀ i, uEpi (selParams (p₀ i) (x i))
      = (x i).s / ((x i).alpha - 1) * (selT (p₀ i) (x i) / (1 + selT (p₀ i) (x i))) := by
    intro i
    rw [selParams, uEpi_fiber _ (hα i)]
    have : (x i).alpha - 1 ≠ 0 := by linarith [hα i]
    have : 1 + selT (p₀ i) (x i) ≠ 0 := by linarith [selT_pos (p₀ i) (x i)]
    simp only [selTPos]
    field_simp
  constructor
  · unfold aggRatio
    simp only [hV, hE, mul_assoc]
  · unfold aggRatio
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [uEpi_selParams_eq _ _ (hα i)]
    ring

/-- The aggregate ratio at variance weights `a_i = c_i V_i` and inverse allocations `t_i`. -/
def ratioOfT (a t : ι → ℝ) : ℝ :=
  (∑ i, a i * (t i / (1 + t i))) / (∑ i, a i * (1 / (1 + t i)))

/-- With the quantities `c_i V_i` held fixed, componentwise increases of
the `t_i` increase the aggregate ratio (strictly if one increase is strict). -/
theorem ratioOfT_mono (a t t' : ι → ℝ) (ha : ∀ i, 0 < a i) (ht : ∀ i, 0 < t i)
    (htt : ∀ i, t i ≤ t' i) : ratioOfT a t ≤ ratioOfT a t'
      ∧ ((∃ k, t k < t' k) → ratioOfT a t < ratioOfT a t') := by
  have ht' : ∀ i, 0 < t' i := fun i => lt_of_lt_of_le (ht i) (htt i)
  have hfrac : ∀ i, t i / (1 + t i) ≤ t' i / (1 + t' i) := fun i => by
    rw [div_le_div_iff₀ (by linarith [ht i]) (by linarith [ht' i])]
    nlinarith [htt i]
  have hinv : ∀ i, 1 / (1 + t' i) ≤ 1 / (1 + t i) := fun i =>
    one_div_le_one_div_of_le (by linarith [ht i]) (by linarith [htt i])
  have hN : ∑ i, a i * (t i / (1 + t i)) ≤ ∑ i, a i * (t' i / (1 + t' i)) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hfrac i) (ha i).le
  have hD : ∑ i, a i * (1 / (1 + t' i)) ≤ ∑ i, a i * (1 / (1 + t i)) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hinv i) (ha i).le
  have hD0 : 0 < ∑ i, a i * (1 / (1 + t' i)) :=
    Finset.sum_pos (fun i _ => mul_pos (ha i) (by have := ht' i; positivity)) Finset.univ_nonempty
  have hN0 : 0 ≤ ∑ i, a i * (t i / (1 + t i)) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (ha i).le (by have := ht i; positivity)
  unfold ratioOfT
  constructor
  · rw [div_le_div_iff₀ (lt_of_lt_of_le hD0 hD) hD0]
    nlinarith
  · rintro ⟨k, hk⟩
    have hDs : ∑ i, a i * (1 / (1 + t' i)) < ∑ i, a i * (1 / (1 + t i)) :=
      Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hinv i) (ha i).le)
        ⟨k, Finset.mem_univ k, mul_lt_mul_of_pos_left
          (one_div_lt_one_div_of_lt (by linarith [ht k]) (by linarith)) (ha k)⟩
    have hNs : ∑ i, a i * (t i / (1 + t i)) < ∑ i, a i * (t' i / (1 + t' i)) :=
      Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hfrac i) (ha i).le)
        ⟨k, Finset.mem_univ k, mul_lt_mul_of_pos_left (by
          rw [div_lt_div_iff₀ (by linarith [ht k]) (by linarith [ht' k])]
          nlinarith) (ha k)⟩
    rw [div_lt_div_iff₀ (lt_of_lt_of_le hD0 hD) hD0]
    nlinarith

end AggregateFormula

section WeightCounterexample

/-- The inverse allocations `(1,3)` and `(2,4)` of the counterexample, and the weights. -/
def pairT₁ : Fin 2 → ℝ := ![1, 3]
def pairT₂ : Fin 2 → ℝ := ![2, 4]

/-- Without control of the variance weights the monotonicity is not
universal. For the common prior `A = 3`, `n = 1` (where `M(A,n) > 4`), inverse allocations
`(1, 3)` and `(2, 4)` are realized by states with `α = 2`; the first pair is componentwise smaller,
yet suitable positive aggregation weights give it the strictly larger aggregate ratio. -/
theorem weight_control_needed :
    ∃ (p₀ : Parameters) (x₁ x₂ : Fin 2 → QuotientState) (c₁ c₂ : Fin 2 → ℝ),
      p₀.alpha = 3 ∧ p₀.nu = 1 ∧ 4 < boundM p₀.alpha p₀.nu
      ∧ (∀ i, (x₁ i).alpha = 2 ∧ (x₂ i).alpha = 2)
      ∧ (∀ i, selT p₀ (x₁ i) = pairT₁ i ∧ selT p₀ (x₂ i) = pairT₂ i)
      ∧ (∀ i, pairT₁ i < pairT₂ i) ∧ (∀ i, 0 < c₁ i ∧ 0 < c₂ i)
      ∧ aggRatio (fun _ => p₀) x₂ c₂ < aggRatio (fun _ => p₀) x₁ c₁ := by
  let p₀ := priorOfCoords 0 1 3 1 one_pos (by norm_num) one_pos
  have hM : 4 < boundM p₀.alpha p₀.nu := by
    change 4 < boundM 3 1
    rw [boundM_eq]
    have h : (6 : ℝ) < Real.sqrt ((1 - 2 * 3 - 1) ^ 2 + 4 * 1) := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    rw [lt_div_iff₀ (by norm_num)]
    linarith
  have hreal : ∀ τ : ℝ, 0 < τ → τ ≤ 4 → ∃ x : QuotientState, x.alpha = 2 ∧ selT p₀ x = τ := by
    intro τ hτ hτ4
    obtain ⟨x, -, h2, hx⟩ := exists_state_selT_eq p₀ 0 2 two_pos τ hτ (by linarith)
    exact ⟨x, h2, hx⟩
  have : Nonempty QuotientState := ⟨⟨0, 1, 1, one_pos, one_pos⟩⟩
  choose! y hy2 hyt using hreal
  let x₁ : Fin 2 → QuotientState := fun i => y (pairT₁ i)
  let x₂ : Fin 2 → QuotientState := fun i => y (pairT₂ i)
  have hT₁ : ∀ i, 0 < pairT₁ i ∧ pairT₁ i ≤ 4 := by
    intro i; fin_cases i <;> norm_num [pairT₁]
  have hT₂ : ∀ i, 0 < pairT₂ i ∧ pairT₂ i ≤ 4 := by
    intro i; fin_cases i <;> norm_num [pairT₂]
  have hα₁ : ∀ i, 1 < (x₁ i).alpha := fun i => by
    simp only [x₁]; rw [hy2 _ (hT₁ i).1 (hT₁ i).2]; norm_num
  have hα₂ : ∀ i, 1 < (x₂ i).alpha := fun i => by
    simp only [x₂]; rw [hy2 _ (hT₂ i).1 (hT₂ i).2]; norm_num
  have ht₁ : ∀ i, selT p₀ (x₁ i) = pairT₁ i := fun i => hyt _ (hT₁ i).1 (hT₁ i).2
  have ht₂ : ∀ i, selT p₀ (x₂ i) = pairT₂ i := fun i => hyt _ (hT₂ i).1 (hT₂ i).2
  -- weights `c_i = w_i / u_var,i` with `w = (1, 100)` and `w = (100, 1)`
  let w₁ : Fin 2 → ℝ := ![1, 100]
  let w₂ : Fin 2 → ℝ := ![100, 1]
  let c₁ : Fin 2 → ℝ := fun i => w₁ i / uVar (selParams p₀ (x₁ i))
  let c₂ : Fin 2 → ℝ := fun i => w₂ i / uVar (selParams p₀ (x₂ i))
  have hw₁ : ∀ i, 0 < w₁ i := by intro i; fin_cases i <;> simp [w₁]
  have hw₂ : ∀ i, 0 < w₂ i := by intro i; fin_cases i <;> simp [w₂]
  have hu₁ := fun i => uVar_selParams_pos p₀ (x₁ i) (hα₁ i)
  have hu₂ := fun i => uVar_selParams_pos p₀ (x₂ i) (hα₂ i)
  have hr : ∀ (x : Fin 2 → QuotientState) (w : Fin 2 → ℝ) (hα : ∀ i, 1 < (x i).alpha),
      aggRatio (fun _ => p₀) x (fun i => w i / uVar (selParams p₀ (x i)))
        = (∑ i, w i * selT p₀ (x i)) / ∑ i, w i := by
    intro x w hα
    rw [(aggregate_ratio_formula (fun _ => p₀) x _ hα).2]
    have hu := fun i => uVar_selParams_pos p₀ (x i) (hα i)
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      field_simp [(hu i).ne']
    · refine Finset.sum_congr rfl fun i _ => ?_
      field_simp [(hu i).ne']
  refine ⟨p₀, x₁, x₂, c₁, c₂, rfl, rfl, hM, fun i => ⟨hy2 _ (hT₁ i).1 (hT₁ i).2,
    hy2 _ (hT₂ i).1 (hT₂ i).2⟩, fun i => ⟨ht₁ i, ht₂ i⟩, ?_, fun i => ⟨div_pos (hw₁ i) (hu₁ i),
    div_pos (hw₂ i) (hu₂ i)⟩, ?_⟩
  · intro i; fin_cases i <;> norm_num [pairT₁, pairT₂]
  · rw [hr x₁ w₁ hα₁, hr x₂ w₂ hα₂]
    simp only [Fin.sum_univ_two, ht₁, ht₂, w₁, w₂, pairT₁, pairT₂]
    norm_num

end WeightCounterexample

end NIGBottleneck
