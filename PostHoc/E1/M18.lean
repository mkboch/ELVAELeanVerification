import Mathlib
import PostHoc.E1.M11
import PostHoc.E1.M12

/-! -/

noncomputable section

namespace NS1

variable (p₀ : str_001)

theorem thm_270 (p : str_001) (hα : 1 < p.alpha) :
    def_084 p₀ (def_024 p)
      = p.alpha / (p.alpha - 1) * (((p.gamma - p₀.gamma) ^ 2 + def_082 p₀) / def_081 p) := by
  have hs := thm_032 p
  have ha : p.alpha - 1 ≠ 0 := by linarith
  rw [thm_171 p hα, def_084]
  change p.alpha * ((p.gamma - p₀.gamma) ^ 2 + def_082 p₀) / def_022 p = _
  field_simp

theorem thm_271 (γ V α α' : ℝ) (hV : 0 < V) (hα : 1 < α) (hαα : α < α') :
    α' / (α' - 1) * (((γ - p₀.gamma) ^ 2 + def_082 p₀) / V)
      < α / (α - 1) * (((γ - p₀.gamma) ^ 2 + def_082 p₀) / V) := by
  have hb := thm_178 p₀
  have hk : 0 < ((γ - p₀.gamma) ^ 2 + def_082 p₀) / V := by positivity
  have h : α' / (α' - 1) < α / (α - 1) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  exact mul_lt_mul_of_pos_right h hk

theorem thm_272 (γ V : ℝ) (hV : 0 < V) :
    ∃ p p' : str_001, p.gamma = γ ∧ p'.gamma = γ ∧ 1 < p.alpha ∧ 1 < p'.alpha
      ∧ p.alpha ≠ p'.alpha ∧ def_081 p = V ∧ def_081 p' = V
      ∧ def_084 p₀ (def_024 p') < def_084 p₀ (def_024 p)
      ∧ def_047 p₀ (def_024 p) < def_047 p₀ (def_024 p') := by
  let p := def_026 ⟨γ, 2, V, two_pos, hV⟩ ⟨1, one_pos⟩
  let p' := def_026 ⟨γ, 3, 2 * V, by norm_num, by positivity⟩ ⟨1, one_pos⟩
  have hV1 : def_081 p = V := by
    rw [(thm_174 _ (by norm_num : (1 : ℝ) < 2) _).2]
    norm_num
  have hV2 : def_081 p' = V := by
    rw [(thm_174 _ (by norm_num : (1 : ℝ) < 3) _).2]
    ring
  have hQ : def_084 p₀ (def_024 p') < def_084 p₀ (def_024 p) := by
    rw [thm_270 p₀ p' (show (1 : ℝ) < 3 by norm_num),
      thm_270 p₀ p (show (1 : ℝ) < 2 by norm_num), hV1, hV2]
    exact thm_271 p₀ γ V 2 3 hV (by norm_num) (by norm_num)
  refine ⟨p, p', rfl, rfl, (show (1 : ℝ) < 2 by norm_num), (show (1 : ℝ) < 3 by norm_num),
    (show (2 : ℝ) ≠ 3 by norm_num), hV1, hV2, hQ, (thm_197 p₀ _ _).mpr hQ⟩

end NS1
