import Mathlib
import PostHoc.E1.M05
import PostHoc.E1.M07
import PostHoc.E1.M08
import PostHoc.E1.M13

/-! -/

noncomputable section

namespace NS1

open Filter

section S37

variable (p₀ : str_001)

theorem thm_293 (p : str_001) :
    p₀.nu * p.alpha * (p.gamma - p₀.gamma) ^ 2 / (2 * p.beta) ≤ def_017 p p₀ := by
  let p₁ : str_001 := ⟨p₀.gamma, p₀.nu, p.alpha, p.beta, p₀.nu_pos, p.alpha_pos, p.beta_pos⟩
  have h1 := thm_122 p₁ p₀
  rw [thm_089] at h1 ⊢
  have hn := p₀.nu_pos
  have hν := p.nu_pos
  have hb := p.beta_pos
  have hlog : 0 ≤ p₀.nu / p.nu - 1 - Real.log (p₀.nu / p.nu) :=
    lem_059 (div_pos hn hν)
  have hlog' : Real.log (p.nu / p₀.nu) = -Real.log (p₀.nu / p.nu) := by
    rw [← Real.log_inv, inv_div]
  simp only [def_039, p₁, sub_self, div_self hn.ne', Real.log_one] at h1 ⊢
  rw [hlog']
  have e : p₀.nu * p.alpha * (p.gamma - p₀.gamma) ^ 2 / (2 * p.beta)
      = (1 / 2) * (p₀.nu * p.alpha * (p.gamma - p₀.gamma) ^ 2 / p.beta) := by
    field_simp
  rw [e]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    add_zero] at h1
  linarith

theorem thm_294 (x : str_002) :
    p₀.nu * x.alpha * (x.gamma - p₀.gamma) ^ 2 / (2 * x.s) ≤ def_060 p₀ x := by
  have h := thm_293 p₀ (def_026 x (def_050 p₀ x))
  have ht := (def_050 p₀ x).property
  have hs := x.s_pos
  have hb : x.s / (1 + (def_050 p₀ x : ℝ)) ≤ x.s := div_le_self hs.le (by linarith)
  have hb0 : 0 < x.s / (1 + (def_050 p₀ x : ℝ)) := by positivity
  rw [def_060, def_041]
  refine le_trans ?_ h
  simp only [def_026]
  apply div_le_div_of_nonneg_left (by have := p₀.nu_pos; have := x.alpha_pos; positivity)
    (by positivity) (by linarith)

end S37

section S22

variable (x₀ : str_002)

theorem thm_295 (n : ℝ) (hn : 0 < n) :
    def_057 (def_089 x₀ n hn) = x₀
      ∧ def_026 x₀ (def_050 (def_089 x₀ n hn) x₀) = def_089 x₀ n hn := by
  have h := thm_203 x₀ n hn
  refine ⟨h, ?_⟩
  have := thm_127 (def_089 x₀ n hn)
  rwa [def_057, h] at this

theorem thm_296 :
    def_016 (def_089 x₀ 1 one_pos) = def_016 (def_089 x₀ 2 two_pos)
      ∧ def_026 x₀ (def_050 (def_089 x₀ 1 one_pos) x₀)
        ≠ def_026 x₀ (def_050 (def_089 x₀ 2 two_pos) x₀) := by
  constructor
  · rw [thm_073, thm_203, thm_203]
  · rw [(thm_295 x₀ 1 one_pos).2, (thm_295 x₀ 2 two_pos).2]
    intro h
    have := congrArg str_001.nu h
    simp only [def_089] at this
    norm_num at this

theorem thm_297 (x : str_002) (hγ : x.gamma ≠ x₀.gamma) (K : ℝ) :
    ∃ N, ∀ (n : ℝ) (hn : 0 < n), N ≤ n → K < def_060 (def_089 x₀ n hn) x := by
  have hs := x.s_pos
  have hα := x.alpha_pos
  have hδ : 0 < (x.gamma - x₀.gamma) ^ 2 := by
    have : x.gamma - x₀.gamma ≠ 0 := sub_ne_zero.mpr hγ
    positivity
  set c := x.alpha * (x.gamma - x₀.gamma) ^ 2 / (2 * x.s) with hc
  have hc0 : 0 < c := by positivity
  refine ⟨(|K| + 1) / c, fun n hn hN => ?_⟩
  have h := thm_294 (def_089 x₀ n hn) x
  have e : (def_089 x₀ n hn).nu * x.alpha * (x.gamma - (def_089 x₀ n hn).gamma) ^ 2
      / (2 * x.s) = n * c := by
    simp only [def_089, hc]
    ring
  rw [e] at h
  have : |K| + 1 ≤ n * c := by rwa [div_le_iff₀ hc0] at hN
  have := le_abs_self K
  linarith

theorem thm_298 (x : str_002) (hγ : x.gamma ≠ x₀.gamma) :
    ∃ (n n' : ℝ) (hn : 0 < n) (hn' : 0 < n'),
      def_016 (def_089 x₀ n hn) = def_016 (def_089 x₀ n' hn')
        ∧ def_060 (def_089 x₀ n hn) x ≠ def_060 (def_089 x₀ n' hn') x := by
  obtain ⟨N, hN⟩ := thm_297 x₀ x hγ (def_060 (def_089 x₀ 1 one_pos) x)
  refine ⟨1, max N 1, one_pos, lt_of_lt_of_le one_pos (le_max_right _ _), ?_, ?_⟩
  · rw [thm_073, thm_203, thm_203]
  · exact (hN _ _ (le_max_left _ _)).ne

end S22

end NS1
