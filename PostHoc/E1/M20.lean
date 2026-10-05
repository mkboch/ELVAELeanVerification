import Mathlib
import PostHoc.E1.M07
import PostHoc.E1.M08
import PostHoc.E1.M12

/-! -/

noncomputable section

namespace NS1

variable (p₀ : str_001)

def def_116 : str_002 :=
  ⟨p₀.gamma, p₀.alpha, 4 * (def_057 p₀).s, p₀.alpha_pos,
    by have := (def_057 p₀).s_pos; positivity⟩

def def_117 : str_002 :=
  ⟨p₀.gamma, p₀.alpha, 2 * (def_057 p₀).s, p₀.alpha_pos,
    by have := (def_057 p₀).s_pos; positivity⟩

lemma lem_145 : def_116 p₀ ≠ def_057 p₀ ∧ def_117 p₀ ≠ def_057 p₀
    ∧ def_116 p₀ ≠ def_117 p₀ := by
  have hs := (def_057 p₀).s_pos
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := congrArg str_002.s h
    simp only [def_116] at this
    linarith
  · have := congrArg str_002.s h
    simp only [def_117] at this
    linarith
  · have := congrArg str_002.s h
    simp only [def_116, def_117] at this
    linarith

theorem thm_285 :
    def_084 p₀ (def_116 p₀) < def_084 p₀ (def_117 p₀)
      ∧ def_084 p₀ (def_117 p₀) < def_084 p₀ (def_057 p₀)
      ∧ def_048 p₀ (def_116 p₀) < def_048 p₀ (def_117 p₀)
      ∧ def_048 p₀ (def_117 p₀) < def_048 p₀ (def_057 p₀) := by
  have hs := (def_057 p₀).s_pos
  have hb := thm_178 p₀
  have hA := p₀.alpha_pos
  have hQ1 : def_084 p₀ (def_116 p₀) < def_084 p₀ (def_117 p₀) := by
    simp only [def_084, def_116, def_117, sub_self]
    apply div_lt_div_of_pos_left (by positivity) (by positivity) (by linarith)
  have hQ2 : def_084 p₀ (def_117 p₀) < def_084 p₀ (def_057 p₀) := by
    have e : (def_057 p₀).gamma = p₀.gamma := rfl
    have e' : (def_057 p₀).alpha = p₀.alpha := rfl
    simp only [def_084, def_117, e, e', sub_self]
    apply div_lt_div_of_pos_left (by positivity) (by positivity) (by linarith)
  exact ⟨hQ1, hQ2, (thm_198 p₀ _ _).mpr hQ1, (thm_198 p₀ _ _).mpr hQ2⟩

lemma lem_146 (x : str_002) (hx : x ≠ def_057 p₀) :
    0 < def_060 p₀ x := by
  rcases (thm_133 p₀ x).lt_or_eq with h | h
  · exact h
  · exact absurd ((thm_131 p₀ x).mp h.symm) hx

def def_118 : abb_001 :=
  ⟨1 / (2 * def_060 p₀ (def_116 p₀)), by
    have := lem_146 p₀ _ (lem_145 p₀).1; positivity⟩

def def_119 : abb_001 :=
  ⟨2 / def_060 p₀ (def_116 p₀), by
    have := lem_146 p₀ _ (lem_145 p₀).1; positivity⟩

open Classical in
def def_120 : abb_003 Bool := fun μ y =>
  if y then
    (if μ = def_035 (def_116 p₀) then 0 else if μ = def_035 (def_057 p₀) then 1 else 2)
  else
    (if μ = def_035 (def_117 p₀) then 0
      else (((1 + (def_119 p₀).val * def_060 p₀ (def_117 p₀) : ℝ)) : EReal))

theorem thm_286 (μ : MeasureTheory.Measure ℝ) (y : Bool) :
    0 ≤ def_120 p₀ μ y ∧ def_120 p₀ μ y ≠ ⊤ := by
  classical
  have hR2 := thm_133 p₀ (def_117 p₀)
  have hw := (def_119 p₀).property
  unfold def_120
  cases y <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split_ifs
  · exact ⟨le_rfl, EReal.zero_ne_top⟩
  · exact ⟨EReal.coe_nonneg.mpr (by positivity), EReal.coe_ne_top _⟩
  · exact ⟨le_rfl, EReal.zero_ne_top⟩
  · exact ⟨zero_le_one, ne_of_lt (EReal.coe_lt_top 1)⟩
  · exact ⟨by norm_num, ne_of_lt (EReal.coe_lt_top 2)⟩

open Classical in
lemma lem_147 (x : str_002) (y : Bool) :
    def_059 (def_120 p₀) x y = if y then
      (if x = def_116 p₀ then 0 else if x = def_057 p₀ then 1 else 2)
    else (if x = def_117 p₀ then 0
      else (((1 + (def_119 p₀).val * def_060 p₀ (def_117 p₀) : ℝ)) : EReal)) := by
  classical
  simp only [def_059, def_120, thm_072.eq_iff]

lemma lem_148 {a b : ℝ} (hab : a < b) {c : ℝ} (hc : 0 ≤ c) :
    ((a : ℝ) : EReal) < ((b : ℝ) : EReal) + ((c : ℝ) : EReal) := by
  rw [← EReal.coe_add, EReal.coe_lt_coe_iff]
  linarith

def def_121 (w : abb_001) (y : Bool) (x : str_002) : Prop :=
  ∀ x', x' ≠ x → def_061 (def_120 p₀) p₀ w x y < def_061 (def_120 p₀) p₀ w x' y

theorem thm_287 : def_121 p₀ (def_118 p₀) true (def_116 p₀) := by
  classical
  obtain ⟨hne1, -, -⟩ := lem_145 p₀
  have hR1 := lem_146 p₀ _ hne1
  have hRnn := thm_133 p₀
  intro x hx
  have hval : (def_118 p₀).val * def_060 p₀ (def_116 p₀) = 1 / 2 := by
    change 1 / (2 * def_060 p₀ (def_116 p₀)) * def_060 p₀ (def_116 p₀) = 1 / 2
    field_simp
  have hv : def_061 (def_120 p₀) p₀ (def_118 p₀) (def_116 p₀) true
      = ((1 / 2 : ℝ) : EReal) := by
    rw [def_061, lem_147]
    simp only [↓reduceIte]
    rw [hval, zero_add]
  rw [hv, def_061, lem_147]
  simp only [hx, ↓reduceIte]
  have hw : 0 ≤ (def_118 p₀).val * def_060 p₀ x :=
    mul_nonneg (def_118 p₀).property.le (hRnn x)
  split_ifs
  · rw [← EReal.coe_one]
    exact lem_148 (by norm_num) hw
  · rw [show (2 : EReal) = ((2 : ℝ) : EReal) by norm_cast]
    exact lem_148 (by norm_num) hw

theorem thm_288 : def_121 p₀ (def_119 p₀) true (def_057 p₀) := by
  classical
  obtain ⟨hne1, -, -⟩ := lem_145 p₀
  have hR1 := lem_146 p₀ _ hne1
  have hRnn := thm_133 p₀
  have hR0 : def_060 p₀ (def_057 p₀) = 0 := thm_130 p₀
  intro x hx
  have hv : def_061 (def_120 p₀) p₀ (def_119 p₀) (def_057 p₀) true
      = ((1 : ℝ) : EReal) := by
    rw [def_061, lem_147]
    simp only [Ne.symm hne1, ↓reduceIte, hR0, mul_zero, EReal.coe_zero, add_zero, EReal.coe_one]
  rw [hv, def_061, lem_147]
  have hw : 0 ≤ (def_119 p₀).val * def_060 p₀ x :=
    mul_nonneg (def_119 p₀).property.le (hRnn x)
  simp only [hx, ↓reduceIte]
  by_cases h1 : x = def_116 p₀
  · subst h1
    simp only [↓reduceIte]
    have : (def_119 p₀).val * def_060 p₀ (def_116 p₀) = 2 := by
      change 2 / def_060 p₀ (def_116 p₀) * def_060 p₀ (def_116 p₀) = 2
      field_simp
    rw [this, zero_add, EReal.coe_lt_coe_iff]
    norm_num
  · simp only [h1, ↓reduceIte]
    rw [show (2 : EReal) = ((2 : ℝ) : EReal) by norm_cast]
    exact lem_148 (by norm_num) hw

theorem thm_289 (w : abb_001) (hw : w.val ≤ (def_119 p₀).val) :
    def_121 p₀ w false (def_117 p₀) := by
  classical
  have hRnn := thm_133 p₀
  intro x hx
  rw [def_061, def_061, lem_147, lem_147]
  simp only [Bool.false_eq_true, ↓reduceIte, hx]
  rw [zero_add, ← EReal.coe_add, EReal.coe_lt_coe_iff]
  have h1 : w.val * def_060 p₀ (def_117 p₀) ≤ (def_119 p₀).val * def_060 p₀ (def_117 p₀) :=
    mul_le_mul_of_nonneg_right hw (hRnn _)
  have h2 : 0 ≤ w.val * def_060 p₀ x := mul_nonneg w.property.le (hRnn x)
  linarith

theorem thm_290 : (def_118 p₀).val ≤ (def_119 p₀).val := by
  have := lem_146 p₀ _ (lem_145 p₀).1
  simp only [def_118, def_119]
  rw [div_le_div_iff₀ (by positivity) this]
  nlinarith

theorem thm_291 (w : abb_001) (y : Bool) (x : str_002)
    (hx : def_121 p₀ w y x) (p : str_001) :
    def_018 (def_120 p₀) p p₀ w y = ⨅ q, def_018 (def_120 p₀) q p₀ w y
      ↔ p = def_026 x (def_050 p₀ x) := by
  have hmin : ⨅ x', def_061 (def_120 p₀) p₀ w x' y
      = def_061 (def_120 p₀) p₀ w x y := by
    refine le_antisymm (iInf_le _ _) (le_iInf fun x' => ?_)
    by_cases h : x' = x
    · rw [h]
    · exact (hx x' h).le
  have hℓ : ∀ x', def_059 (def_120 p₀) x' y ≠ ⊥ := fun x' =>
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (thm_286 p₀ _ y).1)
  have hval : def_061 (def_120 p₀) p₀ w x y ≠ ⊥
      ∧ def_061 (def_120 p₀) p₀ w x y ≠ ⊤ := by
    rw [def_061]
    exact ⟨EReal.add_ne_bot_iff.mpr ⟨hℓ x, EReal.coe_ne_bot _⟩,
      EReal.add_ne_top_iff_ne_top₂ (hℓ x) (EReal.coe_ne_bot _) |>.mpr
        ⟨(thm_286 p₀ _ y).2, EReal.coe_ne_top _⟩⟩
  rw [thm_143 (def_120 p₀) p₀ w y hℓ (by rw [hmin]; exact hval) p, hmin]
  constructor
  · rintro ⟨h3, hp⟩
    have hq : def_024 p = x := by
      by_contra hne
      exact (hx _ hne).ne' h3
    rw [hp, hq]
  · rintro rfl
    rw [thm_036]
    exact ⟨rfl, rfl⟩

theorem thm_292 :
    (∀ μ y, 0 ≤ def_120 p₀ μ y ∧ def_120 p₀ μ y ≠ ⊤)
      ∧ def_121 p₀ (def_118 p₀) true (def_116 p₀)
      ∧ def_121 p₀ (def_118 p₀) false (def_117 p₀)
      ∧ def_121 p₀ (def_119 p₀) true (def_057 p₀)
      ∧ def_121 p₀ (def_119 p₀) false (def_117 p₀)
      ∧ def_048 p₀ (def_116 p₀) < def_048 p₀ (def_117 p₀)
      ∧ def_048 p₀ (def_117 p₀) < def_048 p₀ (def_057 p₀)
      ∧ (∀ p, def_018 (def_120 p₀) p p₀ (def_118 p₀) true
            = ⨅ q, def_018 (def_120 p₀) q p₀ (def_118 p₀) true
          ↔ p = def_026 (def_116 p₀) (def_050 p₀ (def_116 p₀)))
      ∧ (∀ p, def_018 (def_120 p₀) p p₀ (def_119 p₀) true
            = ⨅ q, def_018 (def_120 p₀) q p₀ (def_119 p₀) true
          ↔ p = def_026 (def_057 p₀) (def_050 p₀ (def_057 p₀)))
      ∧ (∀ w : abb_001, w.val ≤ (def_119 p₀).val → ∀ p,
          def_018 (def_120 p₀) p p₀ w false
            = ⨅ q, def_018 (def_120 p₀) q p₀ w false
          ↔ p = def_026 (def_117 p₀) (def_050 p₀ (def_117 p₀)))
      ∧ ∀ x t, (def_026 x t).nu = 1 / (t : ℝ) := by
  obtain ⟨-, -, h3, h4⟩ := thm_285 p₀
  refine ⟨thm_286 p₀, thm_287 p₀,
    thm_289 p₀ _ (thm_290 p₀), thm_288 p₀, thm_289 p₀ _ le_rfl, h3, h4,
    thm_291 p₀ _ _ _ (thm_287 p₀),
    thm_291 p₀ _ _ _ (thm_288 p₀),
    fun w hw => thm_291 p₀ _ _ _ (thm_289 p₀ w hw), fun x t => rfl⟩

end NS1
