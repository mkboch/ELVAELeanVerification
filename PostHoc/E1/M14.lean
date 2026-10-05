import Mathlib
import PostHoc.E1.M11
import PostHoc.E1.M13

/-! -/

noncomputable section

namespace NS1

open Filter Topology Set Asymptotics

section S35

variable {A : ℝ}

lemma lem_126 {d : ℝ} (hd : 0 < d) : ContinuousAt (def_044 A) d := by
  unfold def_044 def_043
  have h2 : (2 : ℝ) * d ≠ 0 := by positivity
  exact ((continuous_const.sub continuous_id).add (Real.continuous_sqrt.comp
    (by fun_prop))).continuousAt.div (by fun_prop) h2

lemma lem_127 {d : ℝ} (hd : 0 < d) :
    d * def_044 A d = (2 * A + 1 - d + Real.sqrt (def_043 A d)) / 2 := by
  unfold def_044
  field_simp

lemma lem_128 {d : ℝ} (hd : 0 < d) :
    d * def_044 A d
      = 2 / (Real.sqrt ((1 - (2 * A + 1) * d⁻¹) ^ 2 + 4 * d⁻¹) + 1 - (2 * A + 1) * d⁻¹) := by
  have hD := lem_054 (A := A) hd
  set r := Real.sqrt (def_043 A d) with hr
  have hr2 : r ^ 2 = def_043 A d := Real.sq_sqrt hD.le
  have habs := lem_055 (A := A) hd
  have hpos : 0 < r + d - (2 * A + 1) := by
    have := neg_abs_le (d - 2 * A - 1)
    rw [← hr] at habs
    linarith
  have hsq : Real.sqrt ((1 - (2 * A + 1) * d⁻¹) ^ 2 + 4 * d⁻¹) = r / d := by
    have e : (1 - (2 * A + 1) * d⁻¹) ^ 2 + 4 * d⁻¹ = (r / d) ^ 2 := by
      rw [div_pow, hr2]
      unfold def_043
      field_simp
      ring
    rw [e, Real.sqrt_sq (div_nonneg (Real.sqrt_nonneg _) hd.le)]
  rw [hsq, lem_127 hd, ← hr]
  have hden : r / d + 1 - (2 * A + 1) * d⁻¹ = (r + d - (2 * A + 1)) / d := by
    field_simp
  rw [hden, div_div_eq_mul_div]
  rw [eq_div_iff hpos.ne']
  have hr2' : r ^ 2 = (d - 2 * A - 1) ^ 2 + 4 * d := hr2
  linear_combination (1 / 2) * hr2'

theorem thm_212 (hA : 0 < A) :
    Tendsto (fun d => d * def_044 A d) (𝓝[>] 0) (𝓝 (2 * A + 1)) := by
  have hc : Continuous fun d : ℝ => (2 * A + 1 - d + Real.sqrt (def_043 A d)) / 2 := by
    unfold def_043
    fun_prop
  have h0 : (2 * A + 1 - 0 + Real.sqrt (def_043 A 0)) / 2 = 2 * A + 1 := by
    unfold def_043
    rw [show ((0 : ℝ) - 2 * A - 1) ^ 2 + 4 * 0 = (2 * A + 1) ^ 2 by ring,
      Real.sqrt_sq (by linarith)]
    ring
  have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  rw [h0] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with d hd
  exact (lem_127 hd).symm

theorem thm_213 :
    Tendsto (fun d => d * def_044 A d) atTop (𝓝 1) := by
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
  exact (lem_128 hd).symm

theorem thm_214 (hA : 0 < A) :
    def_044 A ~[𝓝[>] 0] fun d => (2 * A + 1) / d := by
  refine isEquivalent_of_tendsto_one ?_
  have h := (thm_212 hA).div_const (2 * A + 1)
  rw [div_self (by linarith)] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with d (hd : 0 < d)
  simp only [Pi.div_apply]
  field_simp

theorem thm_215 : def_044 A ~[atTop] fun d => 1 / d := by
  refine isEquivalent_of_tendsto_one ?_
  refine (thm_213 (A := A)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  simp only [Pi.div_apply]
  field_simp

end S35

section S56

lemma lem_129 {l : Filter ℝ} {A L : ℝ} (hL : L ≠ 0) {d c : ℝ → ℝ}
    (hdT : Tendsto (fun u => d u * def_044 A (d u)) l (𝓝 L)) (hcd : Tendsto (fun u => c u / d u) l (𝓝 1))
    (hpos : ∀ᶠ u in l, 0 < d u ∧ 0 < c u) :
    (fun u => def_044 A (d u)) ~[l] (fun u => L / c u)
      ∧ (fun u => 1 / def_044 A (d u)) ~[l] (fun u => c u / L) := by
  have h1 : Tendsto (fun u => (d u * def_044 A (d u)) / L * (c u / d u)) l (𝓝 1) := by
    have := (hdT.div_const L).mul hcd
    rwa [div_self hL, one_mul] at this
  have e1 : ∀ᶠ u in l, (d u * def_044 A (d u)) / L * (c u / d u) = def_044 A (d u) / (L / c u) := by
    filter_upwards [hpos] with u ⟨hd, hc⟩
    field_simp
  have h2 : Tendsto (fun u => def_044 A (d u) / (L / c u)) l (𝓝 1) := h1.congr' e1
  refine ⟨isEquivalent_of_tendsto_one h2, isEquivalent_of_tendsto_one ?_⟩
  have h3 := h2.inv₀ one_ne_zero
  rw [inv_one] at h3
  refine h3.congr' ?_
  filter_upwards [hpos] with u ⟨hd, hc⟩
  simp only [Pi.div_apply]
  field_simp

end S56

section S30

variable (A n e w : ℝ)

def def_093 (b : ℝ) : ℝ := (e + b) / w

def def_094 (b : ℝ) : ℝ := def_044 A (n * (1 + def_093 e w b))

theorem thm_216 (g₀ b : ℝ) (hb : 0 < b) (hA : 0 < A) (hn : 0 < n)
    (x : str_002) :
    def_047 (def_083 g₀ b A n hb hA hn) x
      = def_094 A n ((x.gamma - g₀) ^ 2) (x.s / x.alpha) b := by
  rw [(thm_193 _ x).1, thm_181]
  have hbp : def_082 (def_083 g₀ b A n hb hA hn) = b := by
    simp only [def_082, def_083]
    field_simp
  rw [hbp]
  rfl

theorem thm_217 : Tendsto (def_093 e w) (𝓝[>] 0) (𝓝 (e / w)) := by
  have h : Continuous (def_093 e w) := by unfold def_093; fun_prop
  have := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simpa [def_093] using this

theorem thm_218 (hw : 0 < w) :
    Tendsto (fun b => def_093 e w b / b) atTop (𝓝 (1 / w)) := by
  have h : Tendsto (fun b : ℝ => e / w * b⁻¹ + 1 / w) atTop (𝓝 (e / w * 0 + 1 / w)) :=
    (tendsto_inv_atTop_zero.const_mul _).add_const _
  rw [mul_zero, zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with b hb
  unfold def_093
  field_simp

theorem thm_219 (hA : 0 < A) (hn : 0 < n) :
    Tendsto (def_094 A n 0 w) (𝓝[>] 0) (𝓝 (def_044 A n))
      ∧ ∀ Q : ℝ, 0 < Q → def_087 A n Q < def_044 A n := by
  constructor
  · have hc : ContinuousAt (fun b => n * (1 + def_093 0 w b)) 0 := by
      unfold def_093; fun_prop
    have hf : Tendsto (fun b => n * (1 + def_093 0 w b)) (𝓝 0) (𝓝 n) := by
      simpa [def_093] using hc.tendsto
    exact ((lem_126 (A := A) hn).tendsto.comp hf).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
  · intro Q hQ
    have hd : n < n * (1 + Q) := by nlinarith
    exact thm_185 hA.le (show (0 : ℝ) < n from hn) (show 0 < n * (1 + Q) by linarith) hd

theorem thm_220 (hA : 0 < A) (hn : 0 < n) (e₁ e₂ w₁ w₂ : ℝ)
    (he₂ : 0 ≤ e₂) (hw₁ : 0 < w₁) (hw : w₁ < w₂) :
    ∀ᶠ b in atTop, def_093 e₂ w₂ b < def_093 e₁ w₁ b ∧ def_094 A n e₁ w₁ b < def_094 A n e₂ w₂ b := by
  have hw₂ : 0 < w₂ := by linarith
  have hk : 0 < 1 / w₁ - 1 / w₂ := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt hw₁ hw
  have hlin : Tendsto (fun b => (1 / w₁ - 1 / w₂) * b + (e₁ / w₁ - e₂ / w₂)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop hk)
  filter_upwards [hlin.eventually_gt_atTop 0, eventually_gt_atTop 0] with b hb hb0
  have hQ : def_093 e₂ w₂ b < def_093 e₁ w₁ b := by
    unfold def_093
    have : (e₁ + b) / w₁ - (e₂ + b) / w₂ = (1 / w₁ - 1 / w₂) * b + (e₁ / w₁ - e₂ / w₂) := by
      field_simp
      ring
    linarith
  refine ⟨hQ, ?_⟩
  have hQ2 : 0 < def_093 e₂ w₂ b := by unfold def_093; positivity
  exact thm_189 hA hn hQ2 (hQ2.trans hQ) hQ

theorem thm_221 (hn : 0 < n) (he : 0 ≤ e) (hw : 0 < w) :
    def_094 A n e w ~[atTop] (fun b => w / (n * b))
      ∧ (fun b => 1 / def_094 A n e w b) ~[atTop] (fun b => n * b / w) := by
  have hd : Tendsto (fun b => n * (1 + def_093 e w b)) atTop atTop := by
    unfold def_093
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
  have hdT := (thm_213 (A := A)).comp hd
  have hcd : Tendsto (fun b => n * b / w / (n * (1 + def_093 e w b))) atTop (𝓝 1) := by
    have h0 : Tendsto (fun b : ℝ => (w + e) * b⁻¹ + 1) atTop (𝓝 1) := by
      have := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (w + e)).add_const 1
      simpa using this
    have h := h0.inv₀ one_ne_zero
    rw [inv_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with b hb
    unfold def_093
    field_simp
    ring
  have hpos : ∀ᶠ b in atTop, 0 < n * (1 + def_093 e w b) ∧ 0 < n * b / w := by
    filter_upwards [eventually_gt_atTop 0] with b hb
    unfold def_093
    constructor <;> positivity
  obtain ⟨h1, h2⟩ := lem_129 one_ne_zero hdT hcd hpos
  refine ⟨h1.congr_right ?_, h2.congr_right ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with b hb
    field_simp
  · filter_upwards with b
    simp

end S30

section S24

variable (A s₀ e w : ℝ)

def def_095 (n : ℝ) : ℝ := (e + 2 * s₀ / (n + 1)) / w

def def_096 : ℝ := (e + 2 * s₀) / w

def def_097 : ℝ := e / w

def def_098 (n : ℝ) : ℝ := def_044 A (n * (1 + def_095 s₀ e w n))

theorem thm_222 (x₀ x : str_002) (n : ℝ) (hn : 0 < n) :
    def_047 (def_089 x₀ n hn) x
      = def_098 x₀.alpha x₀.s ((x.gamma - x₀.gamma) ^ 2) (x.s / x.alpha) n := by
  rw [(thm_193 _ x).1, thm_181, (thm_205 x₀ n hn).2.2.2]
  rfl

theorem thm_223 (n : ℝ) (hn : 0 ≤ n) : ContinuousAt (def_095 s₀ e w) n := by
  unfold def_095
  have : n + 1 ≠ 0 := by linarith
  fun_prop (disch := assumption)

theorem thm_224 : Tendsto (def_095 s₀ e w) (𝓝[>] 0) (𝓝 (def_096 s₀ e w)) := by
  have h := (thm_223 s₀ e w 0 le_rfl).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi 0))
  have e0 : def_095 s₀ e w 0 = def_096 s₀ e w := by
    simp [def_095, def_096]
  rwa [e0] at h

theorem thm_225 : Tendsto (def_095 s₀ e w) atTop (𝓝 (def_097 e w)) := by
  have h : Tendsto (fun n : ℝ => (e + 2 * s₀ * (n + 1)⁻¹) / w) atTop (𝓝 ((e + 2 * s₀ * 0) / w)) :=
    ((tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)).const_mul _
      |>.const_add e).div_const w
  rw [mul_zero, add_zero] at h
  refine h.congr' (Eventually.of_forall fun n => ?_)
  simp [def_095, div_eq_mul_inv]

variable {A s₀ e w} (hA : 0 < A) (hs : 0 < s₀) (he : 0 ≤ e) (hw : 0 < w)
include hA hs he hw

omit hA in
lemma lem_130 {n : ℝ} (hn : 0 < n) : 0 < def_095 s₀ e w n := by
  unfold def_095
  positivity

theorem thm_226 :
    def_098 A s₀ e w ~[𝓝[>] 0] (fun n => (2 * A + 1) / (n * (1 + def_096 s₀ e w)))
      ∧ (fun n => 1 / def_098 A s₀ e w n) ~[𝓝[>] 0]
          (fun n => n * (1 + def_096 s₀ e w) / (2 * A + 1)) := by
  have hQl : 0 < def_096 s₀ e w := by unfold def_096; positivity
  have hd : Tendsto (fun n => n * (1 + def_095 s₀ e w n)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun n => n * (1 + def_095 s₀ e w n)) 0 :=
        continuousAt_id.mul (continuousAt_const.add (thm_223 s₀ e w 0 le_rfl))
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with n (hn : 0 < n)
      have := lem_130 hs he hw hn
      exact (mul_pos hn (by linarith) : 0 < n * (1 + def_095 s₀ e w n))
  have hdT := (thm_212 hA).comp hd
  have hcd : Tendsto (fun n => n * (1 + def_096 s₀ e w) / (n * (1 + def_095 s₀ e w n)))
      (𝓝[>] 0) (𝓝 1) := by
    have h := ((thm_224 s₀ e w).const_add 1).inv₀ (by linarith)
      |>.const_mul (1 + def_096 s₀ e w)
    rw [mul_inv_cancel₀ (by linarith)] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with n (hn : 0 < n)
    have := lem_130 hs he hw hn
    field_simp
  have hpos : ∀ᶠ n in 𝓝[>] 0, 0 < n * (1 + def_095 s₀ e w n) ∧ 0 < n * (1 + def_096 s₀ e w) := by
    filter_upwards [self_mem_nhdsWithin] with n (hn : 0 < n)
    have := lem_130 hs he hw hn
    constructor <;> positivity
  obtain ⟨h1, h2⟩ := lem_129 (by linarith) hdT hcd hpos
  exact ⟨h1, h2⟩

omit hA in
theorem thm_227 :
    def_098 A s₀ e w ~[atTop] (fun n => 1 / (n * (1 + def_097 e w)))
      ∧ (fun n => 1 / def_098 A s₀ e w n) ~[atTop] (fun n => n * (1 + def_097 e w)) := by
  have hQh : 0 ≤ def_097 e w := by unfold def_097; positivity
  have hd : Tendsto (fun n => n * (1 + def_095 s₀ e w n)) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ tendsto_id
    filter_upwards [eventually_gt_atTop 0] with n hn
    have := lem_130 hs he hw hn
    simp only [id]
    nlinarith
  have hdT := (thm_213 (A := A)).comp hd
  have hcd : Tendsto (fun n => n * (1 + def_097 e w) / (n * (1 + def_095 s₀ e w n)))
      atTop (𝓝 1) := by
    have h := ((thm_225 s₀ e w).const_add 1).inv₀ (by linarith)
      |>.const_mul (1 + def_097 e w)
    rw [mul_inv_cancel₀ (by linarith)] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have := lem_130 hs he hw hn
    field_simp
  have hpos : ∀ᶠ n in atTop, 0 < n * (1 + def_095 s₀ e w n) ∧ 0 < n * (1 + def_097 e w) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have := lem_130 hs he hw hn
    constructor <;> positivity
  obtain ⟨h1, h2⟩ := lem_129 one_ne_zero hdT hcd hpos
  refine ⟨h1, h2.congr_right ?_⟩
  filter_upwards with n
  simp

omit hA hs he hw in
lemma lem_131 {l : Filter ℝ} {f : ℝ → ℝ} (hf : Tendsto f l atTop) :
    Tendsto (fun u => f u / (1 + f u)) l (𝓝 1) := by
  have h : Tendsto (fun u => 1 - 1 / (1 + f u)) l (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub ((tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ 1 hf)))
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [hf.eventually_gt_atTop 0] with u hu
  field_simp
  ring

theorem thm_228 :
    Tendsto (fun n => def_098 A s₀ e w n / (1 + def_098 A s₀ e w n)) (𝓝[>] 0) (𝓝 1)
      ∧ Tendsto (fun n => def_098 A s₀ e w n / (1 + def_098 A s₀ e w n)) atTop (𝓝 0) := by
  have hQl : 0 < def_096 s₀ e w := by unfold def_096; positivity
  have hQh : 0 ≤ def_097 e w := by unfold def_097; positivity
  constructor
  · have hg : Tendsto (fun n => (2 * A + 1) / (n * (1 + def_096 s₀ e w))) (𝓝[>] 0) atTop := by
      have h := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop
        (show 0 < (2 * A + 1) / (1 + def_096 s₀ e w) by positivity)
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with n (hn : 0 < n)
      field_simp
    exact lem_131 ((thm_226 hA hs he hw).1.symm.tendsto_atTop hg)
  · have hg : Tendsto (fun n => 1 / (n * (1 + def_097 e w))) atTop (𝓝 0) := by
      have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).mul_const (1 / (1 + def_097 e w))
      rw [zero_mul] at h
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      field_simp
    have ht := (thm_227 (A := A) hs he hw).1.symm.tendsto_nhds hg
    have h := ht.div (tendsto_const_nhds.add ht) (show (1 : ℝ) + 0 ≠ 0 by norm_num)
    rwa [zero_div] at h

omit hA hs he hw in
theorem thm_229 (x₀ x : str_002) (hα : 1 < x.alpha) (n : ℝ)
    (hn : 0 < n) :
    def_080 (def_026 x (def_050 (def_089 x₀ n hn) x))
        / def_081 (def_026 x (def_050 (def_089 x₀ n hn) x))
      = def_098 x₀.alpha x₀.s ((x.gamma - x₀.gamma) ^ 2) (x.s / x.alpha) n
        / (1 + def_098 x₀.alpha x₀.s ((x.gamma - x₀.gamma) ^ 2) (x.s / x.alpha) n) := by
  rw [(thm_175 x hα (def_089 x₀ n hn)).2.2.1, thm_222]

end S24

end NS1
