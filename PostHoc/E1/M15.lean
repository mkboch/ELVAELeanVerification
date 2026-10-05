import Mathlib
import PostHoc.E1.M11
import PostHoc.E1.M12
import PostHoc.E1.M14

/-! -/

noncomputable section

namespace NS1

open Filter Topology Set Asymptotics

section S06

def def_099 (A n : ℝ) : ℝ := def_044 A n

theorem thm_230 (A n : ℝ) :
    def_099 A n = (2 * A + 1 - n + Real.sqrt ((n - 2 * A - 1) ^ 2 + 4 * n)) / (2 * n) := rfl

theorem thm_231 (p₀ p₀' : str_001) (hA : p₀.alpha = p₀'.alpha) (hn : p₀.nu = p₀'.nu) :
    def_099 p₀.alpha p₀.nu = def_099 p₀'.alpha p₀'.nu := by
  rw [hA, hn]

variable (p₀ : str_001)

theorem thm_232 (x : str_002) :
    0 < def_047 p₀ x ∧ def_047 p₀ x < def_099 p₀.alpha p₀.nu := by
  refine ⟨thm_100 p₀ x, ?_⟩
  have hQ := thm_182 p₀ x
  have hn := p₀.nu_pos
  rw [(thm_184 p₀ x).1, def_099]
  exact thm_185 p₀.alpha_pos.le (show (0 : ℝ) < p₀.nu from hn)
    (show 0 < p₀.nu * (1 + def_084 p₀ x) by positivity) (by nlinarith)

theorem thm_233 (x : str_002) : 1 / def_099 p₀.alpha p₀.nu < def_048 p₀ x := by
  obtain ⟨h0, h1⟩ := thm_232 p₀ x
  rw [thm_101]
  exact one_div_lt_one_div_of_lt h0 h1

theorem thm_234 (γ α : ℝ) (hα : 0 < α) (τ : ℝ) (hτ : 0 < τ)
    (hτM : τ < def_099 p₀.alpha p₀.nu) :
    ∃ x : str_002, x.gamma = γ ∧ x.alpha = α ∧ def_047 p₀ x = τ := by
  have hA := p₀.alpha_pos
  have hn := p₀.nu_pos
  set d := def_085 p₀.alpha τ with hd
  have hnd : p₀.nu < d := by
    have h := lem_117 hA.le hτ hτM
    rw [def_099, lem_116 hn] at h
    exact h
  have hd0 : 0 < d := by linarith
  set Q := d / p₀.nu - 1 with hQ
  have hQpos : 0 < Q := by
    rw [hQ, sub_pos, one_lt_div hn]
    exact hnd
  have hb := thm_178 p₀
  have hs : 0 < α * ((γ - p₀.gamma) ^ 2 + def_082 p₀) / Q := by positivity
  refine ⟨⟨γ, α, α * ((γ - p₀.gamma) ^ 2 + def_082 p₀) / Q, hα, hs⟩, rfl, rfl, ?_⟩
  have hscore : def_084 p₀ ⟨γ, α, α * ((γ - p₀.gamma) ^ 2 + def_082 p₀) / Q, hα, hs⟩ = Q := by
    simp only [def_084]
    have : 0 < (γ - p₀.gamma) ^ 2 + def_082 p₀ := by positivity
    field_simp
  rw [(thm_184 p₀ _).1, hscore]
  have hdn : p₀.nu * (1 + Q) = d := by
    rw [hQ]
    field_simp
    ring
  rw [hdn]
  exact ((thm_097 hd0 hτ).mp rfl).symm

theorem thm_235 : range (def_047 p₀) = Ioo 0 (def_099 p₀.alpha p₀.nu) := by
  ext τ
  constructor
  · rintro ⟨x, rfl⟩
    exact thm_232 p₀ x
  · rintro ⟨h0, h1⟩
    obtain ⟨x, -, -, hx⟩ := thm_234 p₀ 0 1 one_pos τ h0 h1
    exact ⟨x, hx⟩

theorem thm_236 :
    def_047 p₀ '' {x | 1 < x.alpha} = Ioo 0 (def_099 p₀.alpha p₀.nu) := by
  ext τ
  constructor
  · rintro ⟨x, -, rfl⟩
    exact thm_232 p₀ x
  · rintro ⟨h0, h1⟩
    obtain ⟨x, -, hα, hx⟩ := thm_234 p₀ 0 2 two_pos τ h0 h1
    exact ⟨x, by simp [hα], hx⟩

lemma lem_132 (S : Set str_002)
    (hS : def_047 p₀ '' S = Ioo 0 (def_099 p₀.alpha p₀.nu)) :
    def_048 p₀ '' S = Ioi (1 / def_099 p₀.alpha p₀.nu) := by
  have hM : 0 < def_099 p₀.alpha p₀.nu := thm_092 p₀.nu_pos
  ext ν
  constructor
  · rintro ⟨x, -, rfl⟩
    exact thm_233 p₀ x
  · intro hν
    have hν' : 1 / def_099 p₀.alpha p₀.nu < ν := hν
    have hν0 : 0 < ν := lt_trans (by positivity) hν'
    have h1 : 1 / ν < def_099 p₀.alpha p₀.nu := by
      rw [div_lt_iff₀ hν0]
      rw [div_lt_iff₀ hM] at hν'
      linarith
    have hmem : 1 / ν ∈ def_047 p₀ '' S := by rw [hS]; exact ⟨by positivity, h1⟩
    obtain ⟨x, hxS, hx⟩ := hmem
    refine ⟨x, hxS, ?_⟩
    rw [thm_101, hx, one_div_one_div]

theorem thm_237 :
    range (def_048 p₀) = Ioi (1 / def_099 p₀.alpha p₀.nu)
      ∧ def_048 p₀ '' {x | 1 < x.alpha} = Ioi (1 / def_099 p₀.alpha p₀.nu) := by
  refine ⟨?_, lem_132 p₀ _ (thm_236 p₀)⟩
  rw [← image_univ]
  exact lem_132 p₀ _ (by rw [image_univ]; exact thm_235 p₀)

theorem thm_238 (x : str_002) :
    def_047 p₀ x ≠ def_099 p₀.alpha p₀.nu ∧ def_048 p₀ x ≠ 1 / def_099 p₀.alpha p₀.nu :=
  ⟨(thm_232 p₀ x).2.ne, (thm_233 p₀ x).ne'⟩

theorem thm_239 (x : str_002) (hα : 1 < x.alpha) :
    0 < def_080 (def_026 x (def_050 p₀ x)) / def_079 (def_026 x (def_050 p₀ x))
      ∧ def_080 (def_026 x (def_050 p₀ x)) / def_079 (def_026 x (def_050 p₀ x))
        < def_099 p₀.alpha p₀.nu
      ∧ def_080 (def_026 x (def_050 p₀ x)) / def_081 (def_026 x (def_050 p₀ x))
        < def_099 p₀.alpha p₀.nu / (1 + def_099 p₀.alpha p₀.nu) := by
  obtain ⟨h1, -, h3, -⟩ := thm_175 x hα p₀
  obtain ⟨ht0, htM⟩ := thm_232 p₀ x
  rw [h1, h3]
  refine ⟨ht0, htM, ?_⟩
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

end S06

section S41

theorem thm_240 {A A' n : ℝ} (hA : 0 ≤ A) (hAA : A < A') (hn : 0 < n) :
    def_099 A n < def_099 A' n := by
  unfold def_099
  have h1 := lem_116 (A := A) hn
  have h2 := lem_116 (A := A') hn
  have ht := thm_092 (A := A) hn
  have ht' := thm_092 (A := A') hn
  by_contra hle
  rw [not_lt] at hle
  have hgt : n < def_085 A' (def_044 A n) := by
    have hlt : def_085 A (def_044 A n) < def_085 A' (def_044 A n) := by
      unfold def_085
      have : 2 * A / (1 + def_044 A n) < 2 * A' / (1 + def_044 A n) :=
        div_lt_div_of_pos_right (by linarith) (by linarith)
      linarith
    linarith [h1]
  rcases hle.lt_or_eq with h | h
  · have := lem_117 (A := A') (by linarith) ht' h
    linarith
  · rw [← h] at hgt
    linarith

theorem thm_241 {A : ℝ} (hA : 0 ≤ A) : StrictAntiOn (def_099 A) (Ioi 0) :=
  thm_185 hA

end S41

section S07

theorem thm_242 {n : ℝ} (hn : 0 < n) :
    Tendsto (fun A => def_099 A n) (𝓝[>] 0) (𝓝 (1 / n)) := by
  have hc : Continuous fun A : ℝ =>
      (2 * A + 1 - n + Real.sqrt ((n - 2 * A - 1) ^ 2 + 4 * n)) / (2 * n) := by fun_prop
  have h0 : (2 * 0 + 1 - n + Real.sqrt ((n - 2 * 0 - 1) ^ 2 + 4 * n)) / (2 * n) = 1 / n := by
    rw [show (n - 2 * 0 - 1) ^ 2 + 4 * n = (n + 1) ^ 2 by ring, Real.sqrt_sq (by linarith)]
    field_simp
    ring
  have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  rw [h0] at h
  exact h

theorem thm_243 {n : ℝ} (hn : 0 < n) :
    (fun A => def_099 A n - (2 * A / n + (1 - n) / n)) =O[atTop] (fun A : ℝ => A⁻¹) := by
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
  have hM : def_099 A n = (H + r) / (2 * n) := by
    rw [thm_230, hr, hH]
    congr 2
    ring_nf
  have hrem : def_099 A n - (2 * A / n + (1 - n) / n) = (r - H) / (2 * n) := by
    rw [hM, hH]
    field_simp
    ring
  rw [hrem, Real.norm_of_nonneg (div_nonneg (by linarith) (by linarith)),
    Real.norm_of_nonneg (inv_nonneg.mpr hApos.le), div_le_iff₀ (by linarith)]
  have hprod : (r - H) * (r + H) = 4 * n := by nlinarith [hr2]
  have : (r - H) * (2 * A) ≤ 4 * n := by nlinarith
  rw [inv_mul_eq_div, le_div_iff₀ hApos]
  nlinarith

lemma lem_133 {A n : ℝ} (hn : 0 < n) :
    n * def_099 A n * (1 + def_099 A n) = 1 + (2 * A + 1) * def_099 A n := by
  have h := thm_098 (A := A) hn
  have hM := thm_092 (A := A) hn
  unfold def_099
  set M := def_044 A n
  rw [h]
  field_simp
  ring

theorem thm_244 {A : ℝ} (hA : 0 < A) :
    (fun n => def_099 A n - ((2 * A + 1) / n - 2 * A / (2 * A + 1)))
      =O[𝓝[>] 0] (fun n : ℝ => n) := by
  have hC0 : 0 < 2 * A + 1 := by linarith
  refine IsBigO.of_bound (4 * A / (2 * A + 1) ^ 2 + 16 * A ^ 2 / (2 * A + 1) ^ 3) ?_
  have hsmall : ∀ᶠ n in 𝓝[>] (0 : ℝ), n < (2 * A + 1) / (4 * A) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
  filter_upwards [self_mem_nhdsWithin, hsmall] with n (hn : 0 < n) hnC
  set M := def_099 A n with hMdef
  have hM : 0 < M := thm_092 hn
  have hdef := lem_133 (A := A) hn
  rw [← hMdef] at hdef
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

theorem thm_245 {A : ℝ} (hA : 0 < A) :
    (fun n => def_099 A n - (1 / n + 2 * A / n ^ 2)) =O[atTop] (fun n : ℝ => (n ^ 3)⁻¹) := by
  refine IsBigO.of_bound (4 * A * (2 * A + 2)) ?_
  filter_upwards [eventually_ge_atTop (max (4 * A) 2)] with n hn
  have hn4 : 4 * A ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : 0 < n := by linarith
  set M := def_099 A n with hMdef
  have hM : 0 < M := thm_092 hn0
  have hdef := lem_133 (A := A) hn0
  rw [← hMdef] at hdef
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

end S07

section S01

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def def_100 (p₀ : str_001) (x : str_002) : str_001 :=
  def_026 x (def_050 p₀ x)

def def_101 (p₀ : ι → str_001) (x : ι → str_002) (c : ι → ℝ) : ℝ :=
  (∑ i, c i * def_080 (def_100 (p₀ i) (x i))) / (∑ i, c i * def_079 (def_100 (p₀ i) (x i)))

def def_102 (p₀ : ι → str_001) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => def_099 (p₀ i).alpha (p₀ i).nu

lemma lem_134 (p₀ : str_001) (x : str_002) (hα : 1 < x.alpha) :
    0 < def_079 (def_100 p₀ x) := by
  rw [def_100, thm_172 x hα]
  have := x.s_pos
  have : (0 : ℝ) < (def_050 p₀ x : ℝ) := (def_050 p₀ x).property
  have : 0 < x.alpha - 1 := by linarith
  positivity

lemma lem_135 (p₀ : str_001) (x : str_002) (hα : 1 < x.alpha) :
    def_080 (def_100 p₀ x) = def_079 (def_100 p₀ x) * def_047 p₀ x := by
  have h := (thm_175 x hα p₀).1
  have hu := lem_134 p₀ x hα
  rw [def_100] at hu ⊢
  rw [← h]
  field_simp

theorem thm_246 (p₀ : ι → str_001) (x : ι → str_002) (c : ι → ℝ)
    (hα : ∀ i, 1 < (x i).alpha) (hc : ∀ i, 0 < c i) : def_101 p₀ x c < def_102 p₀ := by
  unfold def_101
  have hD : 0 < ∑ i, c i * def_079 (def_100 (p₀ i) (x i)) :=
    Finset.sum_pos (fun i _ => mul_pos (hc i) (lem_134 _ _ (hα i)))
      Finset.univ_nonempty
  rw [div_lt_iff₀ hD, Finset.mul_sum]
  refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => ?_
  rw [lem_135 _ _ (hα i)]
  have ht := (thm_232 (p₀ i) (x i)).2
  have hle : def_099 (p₀ i).alpha (p₀ i).nu ≤ def_102 p₀ := by
    unfold def_102
    exact Finset.le_sup' (fun k => def_099 (p₀ k).alpha (p₀ k).nu) (Finset.mem_univ i)
  have hpos := mul_pos (hc i) (lem_134 (p₀ i) _ (hα i))
  nlinarith

omit [Nonempty ι] in
lemma lem_136 [DecidableEq ι] (f : ι → str_002 → ℝ) (x : ι → str_002) (j : ι)
    (y : str_002) :
    ∑ i, f i (Function.update x j y i) = (∑ i ∈ Finset.univ.erase j, f i (x i)) + f j y := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

def def_103 (p₀ : str_001) (u : ℝ) : str_002 :=
  ⟨p₀.gamma, 2, Real.exp u, two_pos, Real.exp_pos u⟩

lemma lem_137 (p₀ : str_001) :
    Tendsto (fun u => def_047 p₀ (def_103 p₀ u)) atTop (𝓝 (def_099 p₀.alpha p₀.nu)) := by
  have hQ : Tendsto (fun u => def_084 p₀ (def_103 p₀ u)) atTop (𝓝 0) := by
    have h : Tendsto (fun u : ℝ => 2 * def_082 p₀ * Real.exp (-u)) atTop (𝓝 (2 * def_082 p₀ * 0)) :=
      (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul _
    rw [mul_zero] at h
    refine h.congr' (Eventually.of_forall fun u => ?_)
    simp only [def_084, def_103, sub_self]
    rw [Real.exp_neg]
    field_simp
    ring
  have hd : Tendsto (fun u => p₀.nu * (1 + def_084 p₀ (def_103 p₀ u))) atTop
      (𝓝 p₀.nu) := by
    have := (hQ.const_add 1).const_mul p₀.nu
    rwa [add_zero, mul_one] at this
  have h := (lem_126 (A := p₀.alpha) p₀.nu_pos).tendsto.comp hd
  refine h.congr' (Eventually.of_forall fun u => ?_)
  exact ((thm_184 p₀ _).1).symm

theorem thm_247 (p₀ : ι → str_001) (x : ι → str_002) (c : ι → ℝ)
    (hα : ∀ i, 1 < (x i).alpha) (hc : ∀ i, 0 < c i) (ε : ℝ) (hε : 0 < ε) :
    ∃ x' : ι → str_002, (∀ i, 1 < (x' i).alpha) ∧ def_102 p₀ - ε < def_101 p₀ x' c := by
  classical
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i => def_099 (p₀ i).alpha (p₀ i).nu)
  set Mj := def_099 (p₀ j).alpha (p₀ j).nu
  have hmax : def_102 p₀ = Mj := hj
  set N := ∑ i ∈ Finset.univ.erase j, c i * def_080 (def_100 (p₀ i) (x i))
  set D := ∑ i ∈ Finset.univ.erase j, c i * def_079 (def_100 (p₀ i) (x i))
  set t := fun u => def_047 (p₀ j) (def_103 (p₀ j) u)
  set U := fun u => def_079 (def_100 (p₀ j) (def_103 (p₀ j) u))
  have hα2 : ∀ u, 1 < (def_103 (p₀ j) u).alpha := fun u => by
    simp [def_103]
  have hU : ∀ u, U u = Real.exp u / (1 + t u) := by
    intro u
    simp only [U, t, def_100]
    rw [thm_172 _ (hα2 u)]
    norm_num [def_103, def_050]
  have ht := lem_137 (p₀ j)
  have hM0 : 0 < Mj := thm_092 (p₀ j).nu_pos
  have hUtop : Tendsto U atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ (Real.tendsto_exp_atTop.atTop_div_const
      (show (0 : ℝ) < 1 + Mj by linarith))
    filter_upwards with u
    rw [hU u]
    have htu := thm_232 (p₀ j) (def_103 (p₀ j) u)
    exact div_le_div_of_nonneg_left (Real.exp_pos u).le (by linarith [htu.1]) (by linarith [htu.2])
  have hratio : Tendsto (fun u => (N / U u + c j * t u) / (D / U u + c j)) atTop
      (𝓝 ((0 + c j * Mj) / (0 + c j))) :=
    ((tendsto_const_nhds.div_atTop hUtop).add (ht.const_mul (c j))).div
      ((tendsto_const_nhds.div_atTop hUtop).add tendsto_const_nhds) (by simp [(hc j).ne'])
  rw [zero_add, zero_add, mul_div_cancel_left₀ _ (hc j).ne'] at hratio
  obtain ⟨u, hu, hUpos⟩ :=
    ((tendsto_order.1 hratio).1 (Mj - ε) (by linarith)).and
      (hUtop.eventually_gt_atTop 0) |>.exists
  refine ⟨Function.update x j (def_103 (p₀ j) u), fun i => ?_, ?_⟩
  · by_cases hi : i = j
    · subst hi; rw [Function.update_self]; exact hα2 u
    · rw [Function.update_of_ne hi]; exact hα i
  · rw [hmax]
    unfold def_101
    rw [lem_136 (fun i y => c i * def_080 (def_100 (p₀ i) y)),
      lem_136 (fun i y => c i * def_079 (def_100 (p₀ i) y))]
    rw [lem_135 _ _ (hα2 u)]
    have e : (N + c j * (U u * t u)) / (D + c j * U u)
        = (N / U u + c j * t u) / (D / U u + c j) := by
      field_simp
    change Mj - ε < (N + c j * (U u * t u)) / (D + c j * U u)
    rw [e]
    exact hu

end S01

end NS1
