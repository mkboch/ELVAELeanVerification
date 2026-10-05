import Mathlib
import PostHoc.E1.M11
import PostHoc.E1.M12
import PostHoc.E1.M15

/-! -/

noncomputable section

namespace NS1

open Filter Topology Set Asymptotics

section S21

variable {A : ℝ}

lemma lem_140 (hA : 0 ≤ A) {d : ℝ} (hd : 0 < d) (hd2 : 2 * A < d) :
    0 ≤ def_044 A d - 1 / d ∧ def_044 A d - 1 / d ≤ 2 * A / (d * (d - 2 * A)) := by
  have hT := thm_092 (A := A) hd
  have hdef := lem_133 (A := A) hd
  simp only [def_099] at hdef
  set T := def_044 A d
  have e : T - 1 / d = 2 * A * T / (d * (1 + T)) := by
    field_simp
    linarith
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

lemma lem_141 (hA : 0 ≤ A) {d : ℝ} (hd : 0 < d) (hd2 : 2 * A < d) :
    0 ≤ def_045 A d - (d - 2 * A) ∧ def_045 A d - (d - 2 * A) ≤ 2 * A / (d - 2 * A) := by
  have h := lem_121 (A := A) hd
  have hr := thm_093 (A := A) hd
  set r := def_045 A d
  unfold def_086 at h
  have e : r - (d - 2 * A) = 2 * A / (1 + r) := by
    rw [← h]
    field_simp
    ring
  have hr' : d - 2 * A ≤ r := by
    have : 0 ≤ 2 * A / (1 + r) := by positivity
    linarith
  rw [e]
  refine ⟨by positivity, div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)⟩

end S21

section S50

variable (A n D : ℝ)

def def_107 (s : ℝ) : ℝ := def_044 A (n + D / s)

def def_108 (s : ℝ) : ℝ := def_045 A (n + D / s)

def def_109 (p₀ : str_001) (γ α : ℝ) : ℝ := α * ((γ - p₀.gamma) ^ 2 + def_082 p₀)

theorem thm_260 (p₀ : str_001) (γ α s : ℝ) (hα : 0 < α) (hs : 0 < s) :
    def_084 p₀ ⟨γ, α, s, hα, hs⟩ = def_109 p₀ γ α / s
      ∧ p₀.nu * def_109 p₀ γ α = 2 * α * def_040 p₀ ⟨γ, α, s, hα, hs⟩
      ∧ def_047 p₀ ⟨γ, α, s, hα, hs⟩ = def_107 p₀.alpha p₀.nu (p₀.nu * def_109 p₀ γ α) s
      ∧ def_048 p₀ ⟨γ, α, s, hα, hs⟩ = def_108 p₀.alpha p₀.nu (p₀.nu * def_109 p₀ γ α) s := by
  have hQ : def_084 p₀ ⟨γ, α, s, hα, hs⟩ = def_109 p₀ γ α / s := rfl
  have hd : p₀.nu * (1 + def_109 p₀ γ α / s) = p₀.nu + p₀.nu * def_109 p₀ γ α / s := by ring
  refine ⟨hQ, ?_, ?_, ?_⟩
  · simp only [def_109, def_040, def_082]
    have := p₀.nu_pos
    field_simp
    ring
  · rw [(thm_184 p₀ _).1, hQ, hd]
    rfl
  · rw [(thm_184 p₀ _).2, hQ, hd]
    rfl

theorem thm_261 (p₀ : str_001) (γ α : ℝ) (hα : 0 < α) : 0 < def_109 p₀ γ α := by
  have := thm_178 p₀
  unfold def_109
  positivity

variable {A n D} (hA : 0 < A) (hn : 0 < n) (hD : 0 < D)
include hA hn hD

omit hA hn hD in
theorem thm_262 (C : ℝ) (hC : 0 < C) :
    Tendsto (fun s => C / s) (𝓝[>] 0) atTop :=
  (tendsto_inv_nhdsGT_zero).const_mul_atTop hC |>.congr fun s => (div_eq_mul_inv C s).symm

theorem thm_263 :
    (fun s => def_107 A n D s - s / D) =O[𝓝[>] 0] (fun s => s ^ 2) := by
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
  obtain ⟨h1, h2⟩ := lem_140 hA.le hd0 (by linarith)
  have hb1 : 2 * A / (d * (d - 2 * A)) ≤ 4 * A * s ^ 2 / D ^ 2 := by
    have hdd : d / 2 ≤ d - 2 * A := by linarith
    have hds : D ≤ d * s := by rw [div_le_iff₀ hs] at hDs; linarith
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    have h5 : D ^ 2 ≤ (d * s) ^ 2 := by nlinarith
    have h6 : d ^ 2 / 2 ≤ d * (d - 2 * A) := by nlinarith
    have h7 := mul_le_mul_of_nonneg_left h6 (by positivity : (0 : ℝ) ≤ 4 * A * s ^ 2)
    have h8 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 2 * A)
    nlinarith
  have e2 : 1 / d - s / D = -(n * s ^ 2 / (D * (n * s + D))) := by
    rw [hd]
    field_simp
    ring
  have hb2 : n * s ^ 2 / (D * (n * s + D)) ≤ n * s ^ 2 / D ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [mul_pos hD (mul_pos hn hs)]
  have hpos2 : 0 ≤ n * s ^ 2 / (D * (n * s + D)) := by positivity
  change ‖def_044 A d - s / D‖ ≤ (4 * A + n) / D ^ 2 * ‖s ^ 2‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg s), abs_le]
  have e3 : def_044 A d - s / D = (def_044 A d - 1 / d) + (1 / d - s / D) := by ring
  have e4 : (4 * A + n) / D ^ 2 * s ^ 2 = 4 * A * s ^ 2 / D ^ 2 + n * s ^ 2 / D ^ 2 := by ring
  rw [e3, e2, e4]
  constructor <;> linarith

theorem thm_264 :
    (fun s => def_108 A n D s - (D / s + n - 2 * A)) =O[𝓝[>] 0] (fun s => s) := by
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
  obtain ⟨h1, h2⟩ := lem_141 hA.le hd0 (by linarith)
  have hb : 2 * A / (d - 2 * A) ≤ 4 * A / D * s := by
    have hdd : d / 2 ≤ d - 2 * A := by linarith
    have hds : D ≤ d * s := by rw [div_le_iff₀ hs] at hDs; linarith
    rw [div_le_iff₀ (by linarith), show 4 * A / D * s * (d - 2 * A) = 4 * A * s * (d - 2 * A) / D
      by ring, le_div_iff₀ hD]
    have h7 := mul_le_mul_of_nonneg_left hdd (by positivity : (0 : ℝ) ≤ 4 * A * s)
    have h8 := mul_le_mul_of_nonneg_left hds (by positivity : (0 : ℝ) ≤ 2 * A)
    nlinarith
  change ‖def_045 A d - (D / s + n - 2 * A)‖ ≤ 4 * A / D * ‖s‖
  have e : D / s + n - 2 * A = d - 2 * A := by rw [hd]; ring
  rw [e, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hs, abs_of_nonneg h1]
  linarith

omit hA hn hD in
lemma lem_142 : Tendsto (fun s => n + D / s) atTop (𝓝 n) := by
  have := (tendsto_const_nhds (x := D)).div_atTop tendsto_id
  simpa using this.const_add n

omit hA in
theorem thm_265 (C : ℝ) :
    Tendsto (fun s => C / s) atTop (𝓝 0)
      ∧ Tendsto (def_107 A n D) atTop (𝓝 (def_099 A n))
      ∧ Tendsto (def_108 A n D) atTop (𝓝 (1 / def_099 A n)) := by
  have hT : Tendsto (def_107 A n D) atTop (𝓝 (def_099 A n)) :=
    (lem_126 hn).tendsto.comp (lem_142 (n := n) (D := D))
  refine ⟨tendsto_const_nhds.div_atTop tendsto_id, hT, ?_⟩
  have hM : def_099 A n ≠ 0 := (thm_092 hn).ne'
  have h := hT.inv₀ hM
  rw [← one_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  have hd : 0 < n + D / s := by positivity
  simp only [def_108, def_107]
  rw [thm_095 hd, one_div]

end S50

section S57

variable {A n D : ℝ} (hA : 0 < A) (hn : 0 < n) (hD : 0 < D) (a : ℝ) (ha : 0 < a)
include hA hn hD ha

def def_110 (A n D a s : ℝ) : ℝ := s / (a * (1 + def_107 A n D s))

def def_111 (A n D a s : ℝ) : ℝ := s * def_107 A n D s / (a * (1 + def_107 A n D s))

omit hA hn hD ha in
theorem thm_266 (p₀ : str_001) (γ α s : ℝ) (hα : 1 < α) (hs : 0 < s) :
    def_079 (def_100 p₀ ⟨γ, α, s, by linarith, hs⟩)
        = def_110 p₀.alpha p₀.nu (p₀.nu * def_109 p₀ γ α) (α - 1) s
      ∧ def_080 (def_100 p₀ ⟨γ, α, s, by linarith, hs⟩)
        = def_111 p₀.alpha p₀.nu (p₀.nu * def_109 p₀ γ α) (α - 1) s := by
  have ht := (thm_260 p₀ γ α s (by linarith) hs).2.2.1
  constructor
  · rw [def_100, thm_172 _ hα, def_110]
    simp only [def_050]
    rw [ht]
  · rw [def_100, thm_173 _ hα, def_111]
    simp only [def_050]
    rw [ht]

omit ha in
lemma lem_143 : Tendsto (def_107 A n D) (𝓝[>] 0) (𝓝 0) := by
  have h := (thm_263 hA hn hD).trans_tendsto
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
lemma lem_144 : Tendsto (fun s => def_107 A n D s * D / s) (𝓝[>] 0) (𝓝 1) := by
  have hO := (thm_263 hA hn hD)
  have hlim : Tendsto (fun s => (def_107 A n D s - s / D) / s) (𝓝[>] 0) (𝓝 0) := by
    have h1 : (fun s => (def_107 A n D s - s / D) / s) =O[𝓝[>] 0] (fun s => s) := by
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

theorem thm_267 :
    def_110 A n D a ~[𝓝[>] 0] (fun s => s / a)
      ∧ def_111 A n D a ~[𝓝[>] 0] (fun s => s ^ 2 / (D * a)) := by
  have ht := lem_143 hA hn hD
  have htD := lem_144 hA hn hD
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ 0 < def_107 A n D s := by
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    exact ⟨hs, thm_092 (by positivity)⟩
  constructor
  · refine isEquivalent_of_tendsto_one ?_
    have h := (ht.const_add 1).inv₀ (by norm_num)
    rw [add_zero, inv_one] at h
    refine h.congr' ?_
    filter_upwards [hpos] with s ⟨hs, hts⟩
    have ha' := ha.ne'
    simp only [Pi.div_apply, def_110]
    field_simp
  · refine isEquivalent_of_tendsto_one ?_
    have h := htD.div (ht.const_add 1) (by norm_num)
    rw [add_zero, div_one] at h
    refine h.congr' ?_
    filter_upwards [hpos] with s ⟨hs, hts⟩
    have ha' := ha.ne'
    simp only [Pi.div_apply, def_111]
    field_simp

omit hA in
theorem thm_268 :
    def_110 A n D a ~[atTop] (fun s => s / (a * (1 + def_099 A n)))
      ∧ def_111 A n D a ~[atTop] (fun s => s * def_099 A n / (a * (1 + def_099 A n))) := by
  have ht := (thm_265 (A := A) hn hD 0).2.1
  have hM := thm_092 (A := A) hn
  have hpos : ∀ᶠ s in atTop, 0 < s ∧ 0 < def_107 A n D s := by
    filter_upwards [eventually_gt_atTop 0] with s hs
    exact ⟨hs, thm_092 (by positivity)⟩
  constructor
  · refine isEquivalent_of_tendsto_one ?_
    have h := (tendsto_const_nhds (x := 1 + def_099 A n)).div (ht.const_add 1) (by positivity)
    rw [div_self (by positivity)] at h
    refine h.congr' ?_
    filter_upwards [hpos] with s ⟨hs, hts⟩
    simp only [Pi.div_apply, def_110]
    field_simp
  · refine isEquivalent_of_tendsto_one ?_
    have h := (ht.mul_const (1 + def_099 A n)).div ((ht.const_add 1).const_mul (def_099 A n))
      (by positivity)
    rw [show def_099 A n * (1 + def_099 A n) / (def_099 A n * (1 + def_099 A n)) = 1 from
      div_self (by positivity)] at h
    refine h.congr' ?_
    filter_upwards [hpos] with s ⟨hs, hts⟩
    simp only [Pi.div_apply, def_111]
    field_simp

omit hA in
theorem thm_269 (K : ℝ) :
    ∃ s, 0 < s ∧ K < def_110 A n D a s ∧ K < def_111 A n D a s := by
  obtain ⟨h1, h2⟩ := thm_268 (A := A) hn hD a ha
  have hM := thm_092 (A := A) hn
  have g1 : Tendsto (fun s => s / (a * (1 + def_099 A n))) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  have g2 : Tendsto (fun s => s * def_099 A n / (a * (1 + def_099 A n))) atTop atTop :=
    (tendsto_id.atTop_mul_const hM).atTop_div_const (by positivity)
  obtain ⟨s, hs1, hs2, hs0⟩ := ((h1.symm.tendsto_atTop g1).eventually_gt_atTop K).and
    (((h2.symm.tendsto_atTop g2).eventually_gt_atTop K).and (eventually_gt_atTop 0)) |>.exists
  exact ⟨s, hs0, hs1, hs2⟩

end S57

end NS1
