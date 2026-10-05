import Mathlib
import Official.M06

/-!
# The scalar score, monotone calibration and convexity

The complete prior is reparameterized by `(γ₀, b, A, n)` with `b = 2β₀/n`; the
score is `Q(x) = α((γ−γ₀)² + b)/s = ((γ−γ₀)² + b)/w`, and `d = n(1+Q)`, `t_* = T_A(n(1+Q))`,
`ν_sel = Φ_A(n(1+Q))`. Consequences: strict monotonicity and strict convexity in `Q`; the
dependence on the state only through `(γ−γ₀)²` at fixed `w`; the separation of the ordinal
parameters `(γ₀, b)` from the calibration `(A, n)`; and the comparative statics in `A`, `n`, `b`
and `w`.
-/

noncomputable section

namespace NIGBottleneck

open Set

section Prior

/-- The geometric prior parameter `b = 2β₀/n`. -/
def bParam (p₀ : Parameters) : ℝ := 2 * p₀.beta / p₀.nu

theorem bParam_pos (p₀ : Parameters) : 0 < bParam p₀ :=
  div_pos (mul_pos two_pos p₀.beta_pos) p₀.nu_pos

/-- The complete prior with coordinates `(γ₀, b, A, n)`, `β₀ = nb/2`. -/
def priorOfCoords (g₀ b A n : ℝ) (hb : 0 < b) (hA : 0 < A) (hn : 0 < n) : Parameters where
  gamma := g₀
  nu := n
  alpha := A
  beta := n * b / 2
  nu_pos := hn
  alpha_pos := hA
  beta_pos := by positivity

/-- The coordinates `(γ₀, b, A, n)` range independently over `ℝ × (0,∞)³`, and
the reparameterization is a bijection onto complete priors. -/
theorem prior_reparameterization (g₀ b A n : ℝ) (hb : 0 < b) (hA : 0 < A) (hn : 0 < n) :
    ∃! p₀ : Parameters, p₀.gamma = g₀ ∧ bParam p₀ = b ∧ p₀.alpha = A ∧ p₀.nu = n := by
  refine ⟨priorOfCoords g₀ b A n hb hA hn, ⟨rfl, ?_, rfl, rfl⟩, ?_⟩
  · simp only [bParam, priorOfCoords]
    field_simp
  · rintro p₀ ⟨h1, h2, h3, h4⟩
    have hbeta : p₀.beta = n * b / 2 := by
      rw [← h2, bParam, h4]
      field_simp
    cases p₀
    simp only [priorOfCoords] at *
    subst h1 h3 h4 hbeta
    rfl

theorem beta_eq_of_bParam (p₀ : Parameters) : p₀.beta = p₀.nu * bParam p₀ / 2 := by
  have := p₀.nu_pos
  rw [bParam]
  field_simp

end Prior

section Score

variable (p₀ : Parameters) (x : QuotientState)

/-- The score `Q(x) = α((γ−γ₀)² + b)/s`. -/
def scoreQ : ℝ := x.alpha * ((x.gamma - p₀.gamma) ^ 2 + bParam p₀) / x.s

/-- `Q = ((γ−γ₀)² + b)/w` with `w = s/α`. -/
theorem scoreQ_eq_div_w :
    scoreQ p₀ x = ((x.gamma - p₀.gamma) ^ 2 + bParam p₀) / (x.s / x.alpha) := by
  have := x.alpha_pos
  have := x.s_pos
  rw [scoreQ]
  field_simp

/-- `Q > 0`. -/
theorem scoreQ_pos : 0 < scoreQ p₀ x := by
  have := bParam_pos p₀
  have := x.alpha_pos
  have := x.s_pos
  unfold scoreQ
  positivity

/-- `d = n(1+Q)`. -/
theorem selD_eq_score : selD p₀ x = p₀.nu * (1 + scoreQ p₀ x) := by
  have := p₀.nu_pos
  have := x.s_pos
  rw [selD, priorB, scoreQ, bParam]
  field_simp
  ring

/-- `t_* = T_A(n(1+Q))` and `ν_sel = Φ_A(n(1+Q))`. -/
theorem selT_selNu_eq_score :
    selT p₀ x = TA p₀.alpha (p₀.nu * (1 + scoreQ p₀ x))
      ∧ selNu p₀ x = PhiA p₀.alpha (p₀.nu * (1 + scoreQ p₀ x)) := by
  rw [selT, selNu, selD_eq_score]
  exact ⟨rfl, rfl⟩

end Score

section InverseFunctions

variable {A : ℝ}

/-- `h_A(t) = 2A/(1+t) + 1/t`, whose inverse on `(0,∞)` is `T_A`. -/
def selH (A t : ℝ) : ℝ := 2 * A / (1 + t) + 1 / t

lemma selH_TA {d : ℝ} (hd : 0 < d) : selH A (TA A d) = d := (TA_selection_eq hd).symm

lemma selH_lt_of_lt (hA : 0 ≤ A) {t t' : ℝ} (ht : 0 < t) (htt : t < t') :
    selH A t' < selH A t := by
  have h1 : 1 / t' < 1 / t := one_div_lt_one_div_of_lt ht htt
  have h2 : 2 * A / (1 + t') ≤ 2 * A / (1 + t) :=
    div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  unfold selH
  linarith

/-- The weighted strict convexity inequality for `u ↦ 1/u`. -/
lemma one_div_strict_convex {u v a b : ℝ} (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v) (ha : 0 < a)
    (hb : 0 < b) (hab : a + b = 1) : 1 / (a * u + b * v) < a * (1 / u) + b * (1 / v) := by
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hw : 0 < a * u + (1 - a) * v := by nlinarith
  have key : a * (1 / u) + (1 - a) * (1 / v) - 1 / (a * u + (1 - a) * v)
      = a * (1 - a) * (u - v) ^ 2 / (u * v * (a * u + (1 - a) * v)) := by
    field_simp
    ring
  have hpos : 0 < a * (1 - a) * (u - v) ^ 2 / (u * v * (a * u + (1 - a) * v)) := by
    have : 0 < (u - v) ^ 2 := by
      have : u - v ≠ 0 := sub_ne_zero.mpr huv
      positivity
    positivity
  linarith

lemma one_div_convex {u v a b : ℝ} (hu : 0 < u) (hv : 0 < v) (ha : 0 < a)
    (hb : 0 < b) (hab : a + b = 1) : 1 / (a * u + b * v) ≤ a * (1 / u) + b * (1 / v) := by
  rcases eq_or_ne u v with h | h
  · subst h
    have : a * u + b * u = u := by rw [← add_mul, hab, one_mul]
    rw [this, ← add_mul, hab, one_mul]
  · exact (one_div_strict_convex hu hv h ha hb hab).le

/-- `h_A` is strictly convex on `(0,∞)`. -/
lemma selH_strict_convex (hA : 0 ≤ A) {t t' a b : ℝ} (ht : 0 < t) (ht' : 0 < t') (hne : t ≠ t')
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    selH A (a * t + b * t') < a * selH A t + b * selH A t' := by
  have h1 := one_div_strict_convex ht ht' hne ha hb hab
  have h2 := one_div_convex (by linarith : 0 < 1 + t) (by linarith : 0 < 1 + t') ha hb hab
  have h3 : a * (1 + t) + b * (1 + t') = 1 + (a * t + b * t') := by
    rw [mul_add, mul_add, mul_one, mul_one]
    linarith
  rw [h3] at h2
  have h4 : 2 * A * (1 / (1 + (a * t + b * t')))
      ≤ 2 * A * (a * (1 / (1 + t)) + b * (1 / (1 + t'))) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  unfold selH
  simp only [div_eq_mul_one_div (2 * A)]
  nlinarith

variable (hA : 0 ≤ A)
include hA

/-- `T_A` is strictly decreasing on `(0,∞)`. -/
theorem TA_strictAntiOn : StrictAntiOn (TA A) (Ioi 0) := by
  intro d hd d' hd' hlt
  have hd0 : (0 : ℝ) < d := hd
  have hd0' : (0 : ℝ) < d' := hd'
  by_contra hle
  rw [not_lt] at hle
  rcases hle.lt_or_eq with h | h
  · have := selH_lt_of_lt hA (TA_pos hd0) h
    rw [selH_TA hd0, selH_TA hd0'] at this
    linarith
  · have := congrArg (selH A) h
    rw [selH_TA hd0, selH_TA hd0'] at this
    linarith

/-- `T_A` is strictly convex on `(0,∞)`. -/
theorem TA_strictConvexOn : StrictConvexOn ℝ (Ioi 0) (TA A) := by
  refine ⟨convex_Ioi 0, fun d hd d' hd' hne a b ha hb hab => ?_⟩
  have hd0 : (0 : ℝ) < d := hd
  have hd0' : (0 : ℝ) < d' := hd'
  simp only [smul_eq_mul]
  set t := TA A d
  set t' := TA A d'
  have ht : 0 < t := TA_pos hd0
  have ht' : 0 < t' := TA_pos hd0'
  have htne : t ≠ t' := by
    intro h
    apply hne
    rw [← selH_TA (A := A) hd0, ← selH_TA (A := A) hd0']
    exact congrArg (selH A) h
  have hm : 0 < a * t + b * t' := by positivity
  have hD : 0 < a * d + b * d' := by positivity
  have hconv := selH_strict_convex hA ht ht' htne ha hb hab
  rw [selH_TA hd0, selH_TA hd0'] at hconv
  by_contra hle
  rw [not_lt] at hle
  rcases hle.lt_or_eq with h | h
  · have := selH_lt_of_lt hA hm h
    rw [selH_TA hD] at this
    linarith
  · rw [h, selH_TA hD] at hconv
    exact lt_irrefl _ hconv

/-- `Φ_A = 1/T_A` is strictly increasing on `(0,∞)`. -/
theorem PhiA_strictMonoOn : StrictMonoOn (PhiA A) (Ioi 0) := by
  intro d hd d' hd' hlt
  have hd0 : (0 : ℝ) < d := hd
  have hd0' : (0 : ℝ) < d' := hd'
  rw [PhiA_eq_inv_TA hd0, PhiA_eq_inv_TA hd0']
  exact one_div_lt_one_div_of_lt (TA_pos hd0') (TA_strictAntiOn hA hd hd' hlt)

/-- `g_A(r) = r + 2Ar/(1+r)`, whose inverse on `(0,∞)` is `Φ_A`. -/
def gA (A r : ℝ) : ℝ := r + 2 * A * r / (1 + r)

omit hA in
lemma gA_PhiA {d : ℝ} (hd : 0 < d) : gA A (PhiA A d) = d := by
  have h := TA_selection_eq (A := A) hd
  have ht := TA_pos (A := A) hd
  rw [gA, PhiA_eq_inv_TA hd]
  set T := TA A d
  have e : 1 / T + 2 * A * (1 / T) / (1 + 1 / T) = 2 * A / (1 + T) + 1 / T := by
    field_simp
    ring
  rw [e, ← h]

lemma gA_lt_of_lt {r r' : ℝ} (hr : 0 < r) (hrr : r < r') : gA A r < gA A r' := by
  unfold gA
  have : 2 * A * r / (1 + r) ≤ 2 * A * r' / (1 + r') := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  linarith

omit hA in
/-- `g_A` is strictly concave on `(0,∞)` for `A > 0`. -/
lemma gA_strict_concave (hA : 0 < A) {r r' a b : ℝ} (hr : 0 < r) (hr' : 0 < r') (hne : r ≠ r')
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    a * gA A r + b * gA A r' < gA A (a * r + b * r') := by
  have e : ∀ u : ℝ, 0 < 1 + u → gA A u = u + 2 * A - 2 * A * (1 / (1 + u)) := by
    intro u hu
    unfold gA
    field_simp
    ring
  have h5 := one_div_strict_convex (by linarith : 0 < 1 + r) (by linarith : 0 < 1 + r')
    (fun e' => hne (by linarith)) ha hb hab
  have h3 : a * (1 + r) + b * (1 + r') = 1 + (a * r + b * r') := by
    rw [mul_add, mul_add, mul_one, mul_one]
    linarith
  rw [h3] at h5
  have hm : 0 < a * r + b * r' := by positivity
  rw [e r (by linarith), e r' (by linarith), e _ (by linarith)]
  have h4 : 2 * A * (1 / (1 + (a * r + b * r')))
      < 2 * A * (a * (1 / (1 + r)) + b * (1 / (1 + r'))) :=
    mul_lt_mul_of_pos_left h5 (by linarith)
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith

omit hA in
/-- `Φ_A` is strictly convex on `(0,∞)` for `A > 0` (inverse of the increasing, strictly concave
`g_A`). -/
theorem PhiA_strictConvexOn (hA : 0 < A) : StrictConvexOn ℝ (Ioi 0) (PhiA A) := by
  refine ⟨convex_Ioi 0, fun d hd d' hd' hne a b ha hb hab => ?_⟩
  have hd0 : (0 : ℝ) < d := hd
  have hd0' : (0 : ℝ) < d' := hd'
  simp only [smul_eq_mul]
  set r := PhiA A d
  set r' := PhiA A d'
  have hr : 0 < r := PhiA_pos hd0
  have hr' : 0 < r' := PhiA_pos hd0'
  have hrne : r ≠ r' := by
    intro h
    apply hne
    rw [← gA_PhiA (A := A) hd0, ← gA_PhiA (A := A) hd0']
    exact congrArg (gA A) h
  have hm : 0 < a * r + b * r' := by positivity
  have hD : 0 < a * d + b * d' := by positivity
  have hconc := gA_strict_concave hA hr hr' hrne ha hb hab
  rw [gA_PhiA hd0, gA_PhiA hd0'] at hconc
  by_contra hle
  rw [not_lt] at hle
  rcases hle.lt_or_eq with h | h
  · have := gA_lt_of_lt hA.le hm h
    rw [gA_PhiA hD] at this
    linarith
  · rw [h, gA_PhiA hD] at hconc
    exact lt_irrefl _ hconc

end InverseFunctions

section Consequences

variable (A n : ℝ)

/-- `t_*` as a function of the score, `Q ↦ T_A(n(1+Q))`. -/
def tOfScore (Q : ℝ) : ℝ := TA A (n * (1 + Q))

/-- `ν_sel` as a function of the score, `Q ↦ Φ_A(n(1+Q))`. -/
def nuOfScore (Q : ℝ) : ℝ := PhiA A (n * (1 + Q))

variable {A n} (hA : 0 < A) (hn : 0 < n)
include hA hn

omit hA in
lemma affine_mem {Q : ℝ} (hQ : Q ∈ Ioi (0 : ℝ)) : n * (1 + Q) ∈ Ioi (0 : ℝ) := by
  have : (0 : ℝ) < Q := hQ
  exact mul_pos hn (by linarith)

/-- For a fixed complete prior, `t_*` is strictly decreasing in `Q`. -/
theorem tOfScore_strictAntiOn : StrictAntiOn (tOfScore A n) (Ioi 0) := by
  intro Q hQ Q' hQ' h
  exact TA_strictAntiOn hA.le (affine_mem hn hQ) (affine_mem hn hQ')
    (by nlinarith)

/-- `ν_sel` is strictly increasing in `Q`. -/
theorem nuOfScore_strictMonoOn : StrictMonoOn (nuOfScore A n) (Ioi 0) := by
  intro Q hQ Q' hQ' h
  exact PhiA_strictMonoOn hA.le (affine_mem hn hQ) (affine_mem hn hQ')
    (by nlinarith)

omit hA hn in
lemma affine_combo (Q Q' a b : ℝ) (hab : a + b = 1) :
    n * (1 + (a * Q + b * Q')) = a * (n * (1 + Q)) + b * (n * (1 + Q')) := by
  have : b = 1 - a := by linarith
  subst this
  ring

/-- `t_*` is a strictly convex function of `Q > 0`. -/
theorem tOfScore_strictConvexOn : StrictConvexOn ℝ (Ioi 0) (tOfScore A n) := by
  refine ⟨convex_Ioi 0, fun Q hQ Q' hQ' hne a b ha hb hab => ?_⟩
  have h := (TA_strictConvexOn hA.le).2 (affine_mem hn hQ) (affine_mem hn hQ')
    (fun e => hne (by
      have := mul_left_cancel₀ hn.ne' e
      linarith)) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  unfold tOfScore
  rwa [affine_combo Q Q' a b hab]

/-- `ν_sel` is a strictly convex function of `Q > 0`. -/
theorem nuOfScore_strictConvexOn : StrictConvexOn ℝ (Ioi 0) (nuOfScore A n) := by
  refine ⟨convex_Ioi 0, fun Q hQ Q' hQ' hne a b ha hb hab => ?_⟩
  have h := (PhiA_strictConvexOn hA).2 (affine_mem hn hQ) (affine_mem hn hQ')
    (fun e => hne (by
      have := mul_left_cancel₀ hn.ne' e
      linarith)) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  unfold nuOfScore
  rwa [affine_combo Q Q' a b hab]

end Consequences

section Statements

variable (p₀ : Parameters)

/-- For a fixed complete prior, `t_*` and `ν_sel` are the functions
`tOfScore A n` and `nuOfScore A n` of the score. -/
theorem selT_eq_tOfScore (x : QuotientState) :
    selT p₀ x = tOfScore p₀.alpha p₀.nu (scoreQ p₀ x)
      ∧ selNu p₀ x = nuOfScore p₀.alpha p₀.nu (scoreQ p₀ x) :=
  selT_selNu_eq_score p₀ x

/-- At fixed squared Student scale `w`, the allocation depends on the state
only through `(γ−γ₀)²`, and not on `α`. -/
theorem allocation_depends_on_sq_displacement (x y : QuotientState)
    (hw : x.s / x.alpha = y.s / y.alpha)
    (he : (x.gamma - p₀.gamma) ^ 2 = (y.gamma - p₀.gamma) ^ 2) :
    selT p₀ x = selT p₀ y ∧ selNu p₀ x = selNu p₀ y := by
  have hQ : scoreQ p₀ x = scoreQ p₀ y := by
    rw [scoreQ_eq_div_w, scoreQ_eq_div_w, hw, he]
  rw [(selT_eq_tOfScore p₀ x).1, (selT_eq_tOfScore p₀ y).1, (selT_eq_tOfScore p₀ x).2,
    (selT_eq_tOfScore p₀ y).2, hQ]
  exact ⟨rfl, rfl⟩

/-- At fixed `γ, w`, changing the tail parameter `α` does not change the
allocation. -/
theorem allocation_independent_of_alpha (x y : QuotientState) (hg : x.gamma = y.gamma)
    (hw : x.s / x.alpha = y.s / y.alpha) :
    selT p₀ x = selT p₀ y ∧ selNu p₀ x = selNu p₀ y :=
  allocation_depends_on_sq_displacement p₀ x y hw (by rw [hg])

/-- The score depends on the prior only through `(γ₀, b)`. -/
theorem scoreQ_depends_on_gamma_b (p₀' : Parameters) (hg : p₀.gamma = p₀'.gamma)
    (hb : bParam p₀ = bParam p₀') (x : QuotientState) : scoreQ p₀ x = scoreQ p₀' x := by
  rw [scoreQ, scoreQ, hg, hb]

/-- `(A, n)` give a strictly monotone calibration of the score: for a fixed
prior, the order of the selected inverse allocations is the reverse of the order of the scores. -/
theorem selT_lt_iff_score (x y : QuotientState) :
    selT p₀ x < selT p₀ y ↔ scoreQ p₀ y < scoreQ p₀ x := by
  have hA := p₀.alpha_pos
  have hn := p₀.nu_pos
  rw [(selT_eq_tOfScore p₀ x).1, (selT_eq_tOfScore p₀ y).1]
  exact (tOfScore_strictAntiOn hA hn).lt_iff_gt (scoreQ_pos p₀ x) (scoreQ_pos p₀ y)

theorem selNu_lt_iff_score (x y : QuotientState) :
    selNu p₀ x < selNu p₀ y ↔ scoreQ p₀ x < scoreQ p₀ y := by
  have hA := p₀.alpha_pos
  have hn := p₀.nu_pos
  rw [(selT_eq_tOfScore p₀ x).2, (selT_eq_tOfScore p₀ y).2]
  exact (nuOfScore_strictMonoOn hA hn).lt_iff_lt (scoreQ_pos p₀ x) (scoreQ_pos p₀ y)

/-- Holding `Q` fixed, `t_*` is strictly increasing in `A`, and `ν_sel`
strictly decreasing in `A`. -/
theorem tOfScore_strictMono_A {A A' n Q : ℝ} (hA : 0 < A) (hAA : A < A') (hn : 0 < n)
    (hQ : 0 < Q) :
    tOfScore A n Q < tOfScore A' n Q ∧ nuOfScore A' n Q < nuOfScore A n Q := by
  have hd : 0 < n * (1 + Q) := by positivity
  have key : TA A (n * (1 + Q)) < TA A' (n * (1 + Q)) := by
    set d := n * (1 + Q)
    have h1 := selH_TA (A := A) hd
    have h2 := selH_TA (A := A') hd
    have ht := TA_pos (A := A) hd
    have ht' := TA_pos (A := A') hd
    by_contra hle
    rw [not_lt] at hle
    -- `h_{A'}(T_A) > h_A(T_A) = d = h_{A'}(T_{A'})`, contradicting `T_{A'} ≤ T_A`
    have hgt : d < selH A' (TA A d) := by
      have hlt : selH A (TA A d) < selH A' (TA A d) := by
        unfold selH
        have : 2 * A / (1 + TA A d) < 2 * A' / (1 + TA A d) :=
          div_lt_div_of_pos_right (by linarith) (by linarith)
        linarith
      linarith [h1]
    rcases hle.lt_or_eq with h | h
    · have := selH_lt_of_lt (A := A') (by linarith) ht' h
      linarith
    · rw [← h] at hgt
      linarith
  refine ⟨key, ?_⟩
  unfold nuOfScore
  rw [PhiA_eq_inv_TA hd, PhiA_eq_inv_TA hd]
  exact one_div_lt_one_div_of_lt (TA_pos hd) key

/-- Holding `Q` fixed, `t_*` is strictly decreasing in `n`, and `ν_sel`
strictly increasing in `n`. -/
theorem tOfScore_strictAnti_n {A n n' Q : ℝ} (hA : 0 < A) (hn : 0 < n) (hnn : n < n')
    (hQ : 0 < Q) :
    tOfScore A n' Q < tOfScore A n Q ∧ nuOfScore A n Q < nuOfScore A n' Q := by
  have hd : 0 < n * (1 + Q) := by positivity
  have hd' : 0 < n' * (1 + Q) := by nlinarith
  have hlt : n * (1 + Q) < n' * (1 + Q) := by nlinarith
  exact ⟨TA_strictAntiOn hA.le hd hd' hlt, PhiA_strictMonoOn hA.le hd hd' hlt⟩

/-- Holding `(A, n, γ, w)` fixed, increasing `b` decreases `t_*`. -/
theorem tOfScore_strictAnti_b {A n e w b b' : ℝ} (hA : 0 < A) (hn : 0 < n) (he : 0 ≤ e)
    (hw : 0 < w) (hb : 0 < b) (hbb : b < b') :
    tOfScore A n ((e + b') / w) < tOfScore A n ((e + b) / w) := by
  have hQ : 0 < (e + b) / w := by positivity
  have hQ' : 0 < (e + b') / w := div_pos (by linarith) hw
  exact tOfScore_strictAntiOn hA hn hQ hQ' (div_lt_div_of_pos_right (by linarith) hw)

/-- Increasing `w` at fixed `γ` increases `t_*`. -/
theorem tOfScore_strictMono_w {A n e b w w' : ℝ} (hA : 0 < A) (hn : 0 < n) (he : 0 ≤ e)
    (hb : 0 < b) (hw : 0 < w) (hww : w < w') :
    tOfScore A n ((e + b) / w) < tOfScore A n ((e + b) / w') := by
  have hQ : 0 < (e + b) / w := by positivity
  have hQ' : 0 < (e + b) / w' := div_pos (by linarith) (by linarith)
  exact tOfScore_strictAntiOn hA hn hQ' hQ (div_lt_div_of_pos_left (by linarith) hw hww)

end Statements

end NIGBottleneck
