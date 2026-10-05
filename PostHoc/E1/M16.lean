import Mathlib
import PostHoc.E1.M11
import PostHoc.E1.M12
import PostHoc.E1.M15

/-! -/

noncomputable section

namespace NS1

open Filter Topology Set

section S05

theorem thm_248 (p₀ : str_001) (γ α : ℝ) (hα : 0 < α) (Q : ℝ) (hQ : 0 < Q) :
    ∃ x : str_002, x.gamma = γ ∧ x.alpha = α ∧ def_084 p₀ x = Q := by
  have hb := thm_178 p₀
  have hs : 0 < α * ((γ - p₀.gamma) ^ 2 + def_082 p₀) / Q := by positivity
  refine ⟨⟨γ, α, α * ((γ - p₀.gamma) ^ 2 + def_082 p₀) / Q, hα, hs⟩, rfl, rfl, ?_⟩
  simp only [def_084]
  have : 0 < (γ - p₀.gamma) ^ 2 + def_082 p₀ := by positivity
  field_simp

theorem thm_249 {A A' d : ℝ} (hA : 0 ≤ A) (hAA : A < A') (hd : 0 < d) :
    def_044 A d < def_044 A' d :=
  thm_240 hA hAA hd

theorem thm_250 {A d : ℝ} (hA : 0 ≤ A) (hd : 0 < d) : d - 2 * A ≤ def_045 A d ∧ def_045 A d ≤ d := by
  have h := lem_121 (A := A) hd
  have hr := thm_093 (A := A) hd
  set r := def_045 A d
  have h1 : 2 * A * r / (1 + r) ≤ 2 * A := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h2 : 0 ≤ 2 * A * r / (1 + r) := by positivity
  unfold def_086 at h
  constructor <;> linarith

end S05

section S44

theorem thm_251 (p p' : str_001) (hA : p.alpha = p'.alpha) (hn : p.nu = p'.nu)
    (x x' : str_002) :
    (def_084 p x < def_084 p' x' ↔ def_048 p x < def_048 p' x')
      ∧ (def_048 p x < def_048 p' x' ↔ def_047 p' x' < def_047 p x) := by
  have hA0 := p.alpha_pos
  have hn0 := p.nu_pos
  rw [(thm_193 p x).1, (thm_193 p' x').1, (thm_193 p x).2,
    (thm_193 p' x').2, ← hA, ← hn]
  have hQ := thm_182 p x
  have hQ' := thm_182 p' x'
  exact ⟨((thm_190 hA0 hn0).lt_iff_lt hQ hQ').symm,
    ((thm_190 hA0 hn0).lt_iff_lt hQ hQ').trans
      ((thm_189 hA0 hn0).lt_iff_gt hQ' hQ).symm⟩

theorem thm_252 (p p' : str_001) (x x' : str_002)
    (hQ : def_084 p x ≤ def_084 p' x') (hn : p.nu ≤ p'.nu) (hA : p'.alpha ≤ p.alpha) :
    def_048 p x ≤ def_048 p' x' ∧ def_047 p' x' ≤ def_047 p x := by
  have hQ0 := thm_182 p x
  have hd : p.nu * (1 + def_084 p x) ≤ p'.nu * (1 + def_084 p' x') := by
    have := p.nu_pos
    nlinarith
  have hd0 : 0 < p.nu * (1 + def_084 p x) := by have := p.nu_pos; positivity
  have ht : def_047 p' x' ≤ def_047 p x := by
    rw [(thm_184 p x).1, (thm_184 p' x').1]
    calc def_044 p'.alpha (p'.nu * (1 + def_084 p' x'))
        ≤ def_044 p.alpha (p'.nu * (1 + def_084 p' x')) := by
          rcases hA.lt_or_eq with h | h
          · exact (thm_249 p'.alpha_pos.le h (by linarith)).le
          · rw [h]
      _ ≤ def_044 p.alpha (p.nu * (1 + def_084 p x)) :=
          (thm_185 p.alpha_pos.le).antitoneOn hd0 (show (0 : ℝ) < _ by linarith) hd
  refine ⟨?_, ht⟩
  rw [thm_101, thm_101]
  exact one_div_le_one_div_of_le (thm_100 p' x') ht

theorem thm_253 :
    ∃ (p p' : str_001) (x x' : str_002), p.alpha = p'.alpha
      ∧ def_084 p x < def_084 p' x' ∧ def_048 p' x' < def_048 p x := by
  let p := def_083 0 1 1 3 one_pos one_pos (by norm_num)
  let p' := def_083 0 1 1 1 one_pos one_pos one_pos
  obtain ⟨x, -, -, hx⟩ := thm_248 p 0 1 one_pos 1 one_pos
  obtain ⟨x', -, -, hx'⟩ := thm_248 p' 0 1 one_pos 2 two_pos
  refine ⟨p, p', x, x', rfl, by rw [hx, hx']; norm_num, ?_⟩
  rw [(thm_184 p x).2, (thm_184 p' x').2, hx, hx']
  have h1 := (thm_250 (A := 1) zero_le_one (show (0 : ℝ) < 1 * (1 + 2) by norm_num)).2
  have h2 := (thm_250 (A := 1) zero_le_one (show (0 : ℝ) < 3 * (1 + 1) by norm_num)).1
  change def_045 1 (1 * (1 + 2)) < def_045 1 (3 * (1 + 1))
  linarith

end S44

section S08

variable {ι : Type*} [Fintype ι]

theorem thm_254 (A n Q Q' c : ι → ℝ) (hA : ∀ i, 0 < A i) (hn : ∀ i, 0 < n i)
    (hQ : ∀ i, 0 < Q i) (hQQ : ∀ i, Q i ≤ Q' i) (hc : ∀ i, 0 ≤ c i) :
    ∑ i, c i * def_087 (A i) (n i) (Q' i) ≤ ∑ i, c i * def_087 (A i) (n i) (Q i)
      ∧ ∑ i, c i * def_088 (A i) (n i) (Q i) ≤ ∑ i, c i * def_088 (A i) (n i) (Q' i) := by
  constructor
  · refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hc i)
    exact (thm_189 (hA i) (hn i)).antitoneOn (hQ i)
      (show (0 : ℝ) < Q' i from lt_of_lt_of_le (hQ i) (hQQ i)) (hQQ i)
  · refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hc i)
    exact (thm_190 (hA i) (hn i)).monotoneOn (hQ i)
      (show (0 : ℝ) < Q' i from lt_of_lt_of_le (hQ i) (hQQ i)) (hQQ i)

omit [Fintype ι] in
theorem thm_255 {A n : ℝ} (hA : 0 < A) (hn : 0 < n) :
    def_087 A n 2 < (def_087 A n 1 + def_087 A n 3) / 2
      ∧ def_088 A n 2 < (def_088 A n 1 + def_088 A n 3) / 2 := by
  have h1 := (thm_191 hA hn).2 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show (3 : ℝ) ∈ Ioi 0 by norm_num) (by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num)
  have h2 := (thm_192 hA hn).2 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show (3 : ℝ) ∈ Ioi 0 by norm_num) (by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at h1 h2
  norm_num at h1 h2
  constructor <;> linarith

omit [Fintype ι] in
lemma lem_138 {A n Q : ℝ} (hn : 0 < n) (hQ : 0 < Q) :
    ContinuousAt (def_087 A n) Q := by
  have hd : 0 < n * (1 + Q) := by positivity
  unfold def_087
  exact (lem_126 hd).comp (f := fun Q => n * (1 + Q)) (by fun_prop)

omit [Fintype ι] in
lemma lem_139 {A n Q : ℝ} (hn : 0 < n) (hQ : 0 < Q) :
    ContinuousAt (def_088 A n) Q := by
  have hd : 0 < n * (1 + Q) := by positivity
  have hc : ContinuousAt (def_045 A) (n * (1 + Q)) := by
    have hT := lem_126 (A := A) hd
    have hT0 := thm_092 (A := A) hd
    refine (hT.inv₀ hT0.ne').congr ?_
    filter_upwards [Ioi_mem_nhds hd] with d (hd' : 0 < d)
    rw [thm_095 hd', one_div]
    rfl
  unfold def_088
  exact hc.comp (f := fun Q => n * (1 + Q)) (by fun_prop)

omit [Fintype ι] in
theorem thm_256 {A n : ℝ} (hA : 0 < A) (hn : 0 < n) :
    (∃ ε, 0 < ε ∧ ε < 1 ∧ def_087 A n (2 - ε) < (def_087 A n 1 + def_087 A n 3) / 2)
      ∧ (∃ ε, 0 < ε ∧ ε < 1 ∧ def_088 A n (2 + ε) < (def_088 A n 1 + def_088 A n 3) / 2) := by
  obtain ⟨h1, h2⟩ := thm_255 hA hn
  constructor
  · have hev := (lem_138 (A := A) hn two_pos).eventually (gt_mem_nhds h1)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨min (δ / 2) (1 / 2), lt_min (by linarith) (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num), hball ?_⟩
    rw [Real.dist_eq, show 2 - min (δ / 2) (1 / 2) - 2 = -min (δ / 2) (1 / 2) by ring, abs_neg,
      abs_of_pos (lt_min (by linarith) (by norm_num))]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  · have hev := (lem_139 (A := A) hn two_pos).eventually (gt_mem_nhds h2)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨min (δ / 2) (1 / 2), lt_min (by linarith) (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num), hball ?_⟩
    rw [Real.dist_eq, show 2 + min (δ / 2) (1 / 2) - 2 = min (δ / 2) (1 / 2) by ring,
      abs_of_pos (lt_min (by linarith) (by norm_num))]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

end S08

section S02

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem thm_257 (p₀ : ι → str_001) (x : ι → str_002) (c : ι → ℝ)
    (hα : ∀ i, 1 < (x i).alpha) :
    def_101 p₀ x c
        = (∑ i, c i * ((x i).s / ((x i).alpha - 1)) * (def_047 (p₀ i) (x i) / (1 + def_047 (p₀ i) (x i))))
          / (∑ i, c i * ((x i).s / ((x i).alpha - 1)) * (1 / (1 + def_047 (p₀ i) (x i))))
      ∧ def_101 p₀ x c
        = (∑ i, c i * def_079 (def_100 (p₀ i) (x i)) * def_047 (p₀ i) (x i))
          / (∑ i, c i * def_079 (def_100 (p₀ i) (x i))) := by
  have hV : ∀ i, def_079 (def_100 (p₀ i) (x i))
      = (x i).s / ((x i).alpha - 1) * (1 / (1 + def_047 (p₀ i) (x i))) := by
    intro i
    rw [def_100, thm_172 _ (hα i)]
    have : (x i).alpha - 1 ≠ 0 := by linarith [hα i]
    have : 1 + def_047 (p₀ i) (x i) ≠ 0 := by linarith [thm_100 (p₀ i) (x i)]
    simp only [def_050]
    field_simp
  have hE : ∀ i, def_080 (def_100 (p₀ i) (x i))
      = (x i).s / ((x i).alpha - 1) * (def_047 (p₀ i) (x i) / (1 + def_047 (p₀ i) (x i))) := by
    intro i
    rw [def_100, thm_173 _ (hα i)]
    have : (x i).alpha - 1 ≠ 0 := by linarith [hα i]
    have : 1 + def_047 (p₀ i) (x i) ≠ 0 := by linarith [thm_100 (p₀ i) (x i)]
    simp only [def_050]
    field_simp
  constructor
  · unfold def_101
    simp only [hV, hE, mul_assoc]
  · unfold def_101
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lem_135 _ _ (hα i)]
    ring

def def_104 (a t : ι → ℝ) : ℝ :=
  (∑ i, a i * (t i / (1 + t i))) / (∑ i, a i * (1 / (1 + t i)))

theorem thm_258 (a t t' : ι → ℝ) (ha : ∀ i, 0 < a i) (ht : ∀ i, 0 < t i)
    (htt : ∀ i, t i ≤ t' i) : def_104 a t ≤ def_104 a t'
      ∧ ((∃ k, t k < t' k) → def_104 a t < def_104 a t') := by
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
  unfold def_104
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

end S02

section S58

def def_105 : Fin 2 → ℝ := ![1, 3]
def def_106 : Fin 2 → ℝ := ![2, 4]

theorem thm_259 :
    ∃ (p₀ : str_001) (x₁ x₂ : Fin 2 → str_002) (c₁ c₂ : Fin 2 → ℝ),
      p₀.alpha = 3 ∧ p₀.nu = 1 ∧ 4 < def_099 p₀.alpha p₀.nu
      ∧ (∀ i, (x₁ i).alpha = 2 ∧ (x₂ i).alpha = 2)
      ∧ (∀ i, def_047 p₀ (x₁ i) = def_105 i ∧ def_047 p₀ (x₂ i) = def_106 i)
      ∧ (∀ i, def_105 i < def_106 i) ∧ (∀ i, 0 < c₁ i ∧ 0 < c₂ i)
      ∧ def_101 (fun _ => p₀) x₂ c₂ < def_101 (fun _ => p₀) x₁ c₁ := by
  let p₀ := def_083 0 1 3 1 one_pos (by norm_num) one_pos
  have hM : 4 < def_099 p₀.alpha p₀.nu := by
    change 4 < def_099 3 1
    rw [thm_230]
    have h : (6 : ℝ) < Real.sqrt ((1 - 2 * 3 - 1) ^ 2 + 4 * 1) := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    rw [lt_div_iff₀ (by norm_num)]
    linarith
  have hreal : ∀ τ : ℝ, 0 < τ → τ ≤ 4 → ∃ x : str_002, x.alpha = 2 ∧ def_047 p₀ x = τ := by
    intro τ hτ hτ4
    obtain ⟨x, -, h2, hx⟩ := thm_234 p₀ 0 2 two_pos τ hτ (by linarith)
    exact ⟨x, h2, hx⟩
  have : Nonempty str_002 := ⟨⟨0, 1, 1, one_pos, one_pos⟩⟩
  choose! y hy2 hyt using hreal
  let x₁ : Fin 2 → str_002 := fun i => y (def_105 i)
  let x₂ : Fin 2 → str_002 := fun i => y (def_106 i)
  have hT₁ : ∀ i, 0 < def_105 i ∧ def_105 i ≤ 4 := by
    intro i; fin_cases i <;> norm_num [def_105]
  have hT₂ : ∀ i, 0 < def_106 i ∧ def_106 i ≤ 4 := by
    intro i; fin_cases i <;> norm_num [def_106]
  have hα₁ : ∀ i, 1 < (x₁ i).alpha := fun i => by
    simp only [x₁]; rw [hy2 _ (hT₁ i).1 (hT₁ i).2]; norm_num
  have hα₂ : ∀ i, 1 < (x₂ i).alpha := fun i => by
    simp only [x₂]; rw [hy2 _ (hT₂ i).1 (hT₂ i).2]; norm_num
  have ht₁ : ∀ i, def_047 p₀ (x₁ i) = def_105 i := fun i => hyt _ (hT₁ i).1 (hT₁ i).2
  have ht₂ : ∀ i, def_047 p₀ (x₂ i) = def_106 i := fun i => hyt _ (hT₂ i).1 (hT₂ i).2
  let w₁ : Fin 2 → ℝ := ![1, 100]
  let w₂ : Fin 2 → ℝ := ![100, 1]
  let c₁ : Fin 2 → ℝ := fun i => w₁ i / def_079 (def_100 p₀ (x₁ i))
  let c₂ : Fin 2 → ℝ := fun i => w₂ i / def_079 (def_100 p₀ (x₂ i))
  have hw₁ : ∀ i, 0 < w₁ i := by intro i; fin_cases i <;> simp [w₁]
  have hw₂ : ∀ i, 0 < w₂ i := by intro i; fin_cases i <;> simp [w₂]
  have hu₁ := fun i => lem_134 p₀ (x₁ i) (hα₁ i)
  have hu₂ := fun i => lem_134 p₀ (x₂ i) (hα₂ i)
  have hr : ∀ (x : Fin 2 → str_002) (w : Fin 2 → ℝ) (hα : ∀ i, 1 < (x i).alpha),
      def_101 (fun _ => p₀) x (fun i => w i / def_079 (def_100 p₀ (x i)))
        = (∑ i, w i * def_047 p₀ (x i)) / ∑ i, w i := by
    intro x w hα
    rw [(thm_257 (fun _ => p₀) x _ hα).2]
    have hu := fun i => lem_134 p₀ (x i) (hα i)
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      field_simp [(hu i).ne']
    · refine Finset.sum_congr rfl fun i _ => ?_
      field_simp [(hu i).ne']
  refine ⟨p₀, x₁, x₂, c₁, c₂, rfl, rfl, hM, fun i => ⟨hy2 _ (hT₁ i).1 (hT₁ i).2,
    hy2 _ (hT₂ i).1 (hT₂ i).2⟩, fun i => ⟨ht₁ i, ht₂ i⟩, ?_, fun i => ⟨div_pos (hw₁ i) (hu₁ i),
    div_pos (hw₂ i) (hu₂ i)⟩, ?_⟩
  · intro i; fin_cases i <;> norm_num [def_105, def_106]
  · rw [hr x₁ w₁ hα₁, hr x₂ w₂ hα₂]
    simp only [Fin.sum_univ_two, ht₁, ht₂, w₁, w₂, def_105, def_106]
    norm_num

end S58

end NS1
