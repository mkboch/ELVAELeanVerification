import Mathlib
import PostHoc.E1.M07

/-! -/

noncomputable section

namespace NS1

open MeasureTheory

section S15

variable {Y : Type*}

def def_059 (L : abb_003 Y) (x : str_002) (y : Y) : EReal :=
  L (def_035 x) y

def def_060 (p₀ : str_001) (x : str_002) : ℝ :=
  def_041 p₀ x (def_050 p₀ x)

def def_061 (L : abb_003 Y) (p₀ : str_001) (w : abb_001)
    (x : str_002) (y : Y) : EReal :=
  def_059 L x y + ((w.val * def_060 p₀ x : ℝ) : EReal)

end S15

section S48

variable {Y : Type*} (L : abb_003 Y) (p₀ : str_001) (w : abb_001) (y : Y)

theorem thm_132 (x : str_002) : def_060 p₀ x = def_058 p₀ x :=
  rfl

theorem thm_133 (x : str_002) : 0 ≤ def_060 p₀ x :=
  thm_129 p₀ x

theorem thm_134 (p : str_001) :
    def_018 L p p₀ w y
      = def_059 L (def_024 p) y
        + ((w.val * def_017 p p₀ : ℝ) : EReal) := by
  rw [def_018, def_059, thm_068]

theorem thm_135 (p : str_001) :
    def_017 p p₀ = def_041 p₀ (def_024 p) (def_025 p) := by
  rw [def_041, thm_038]

theorem thm_136 (p : str_001) :
    def_060 p₀ (def_024 p) ≤ def_017 p p₀ := by
  rw [thm_135]
  by_cases h : (def_025 p : ℝ) = def_047 p₀ (def_024 p)
  · have : def_025 p = def_050 p₀ (def_024 p) := Subtype.ext h
    rw [def_060, this]
  · exact (thm_108 p₀ _ _ h).le

theorem thm_137 (x : str_002) :
    def_018 L (def_026 x (def_050 p₀ x)) p₀ w y
      = def_061 L p₀ w x y := by
  rw [thm_134, thm_036, def_061, def_060,
    def_041]

theorem thm_138 (p : str_001) :
    def_061 L p₀ w (def_024 p) y ≤ def_018 L p p₀ w y := by
  rw [thm_134, def_061]
  exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr
    (mul_le_mul_of_nonneg_left (thm_136 p₀ p) w.property.le))

theorem thm_139 :
    ⨅ p, def_018 L p p₀ w y = ⨅ x, def_061 L p₀ w x y := by
  apply le_antisymm
  · refine le_iInf fun x => ?_
    rw [← thm_137]
    exact iInf_le _ _
  · refine le_iInf fun p => ?_
    exact (iInf_le _ (def_024 p)).trans
      (thm_138 L p₀ w y p)

theorem thm_140 (x : str_002) (t : abb_001) :
    def_018 L (def_026 x t) p₀ w y
      = def_061 L p₀ w x y
        + ((w.val * (def_041 p₀ x t - def_060 p₀ x) : ℝ) : EReal) := by
  rw [thm_134, thm_036, def_061, add_assoc,
    ← EReal.coe_add, def_041]
  congr 2
  ring

theorem thm_141 (x : str_002) (t : abb_001) :
    def_041 p₀ x t - def_060 p₀ x = def_051 p₀ x t :=
  thm_107 p₀ x t

theorem thm_142 (x : str_002) (t : abb_001) :
    (∀ t' : abb_001, w.val * def_041 p₀ x t ≤ w.val * def_041 p₀ x t') ↔ t = def_050 p₀ x := by
  have hw := w.property
  constructor
  · intro h
    by_contra hne
    have hne' : (t : ℝ) ≠ def_047 p₀ x := fun h' => hne (Subtype.ext h')
    have h1 := thm_108 p₀ x t hne'
    have h2 := h (def_050 p₀ x)
    nlinarith
  · rintro rfl t'
    by_cases h : (t' : ℝ) = def_047 p₀ x
    · have : t' = def_050 p₀ x := Subtype.ext h
      rw [this]
    · exact mul_le_mul_of_nonneg_left (thm_108 p₀ x t' h).le hw.le

lemma lem_075 {a : EReal} (ha : a ≠ ⊥) (ha' : a ≠ ⊤) {b c : ℝ}
    (h : a + (b : EReal) = a + (c : EReal)) : b = c := by
  lift a to ℝ using ⟨ha', ha⟩
  rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_eq_coe_iff] at h
  linarith

theorem thm_143
    (hℓ : ∀ x, def_059 L x y ≠ ⊥)
    (hfin : (⨅ x, def_061 L p₀ w x y) ≠ ⊥ ∧ (⨅ x, def_061 L p₀ w x y) ≠ ⊤)
    (p : str_001) :
    def_018 L p p₀ w y = ⨅ q, def_018 L q p₀ w y ↔
      def_061 L p₀ w (def_024 p) y = ⨅ x, def_061 L p₀ w x y ∧
        p = def_026 (def_024 p) (def_050 p₀ (def_024 p)) := by
  rw [thm_139]
  set m := ⨅ x, def_061 L p₀ w x y with hm
  constructor
  · intro h
    have hle := thm_138 L p₀ w y p
    have hge : m ≤ def_061 L p₀ w (def_024 p) y := iInf_le _ _
    have hJ3 : def_061 L p₀ w (def_024 p) y = m := le_antisymm (h ▸ hle) hge
    refine ⟨hJ3, ?_⟩
    have heq : def_018 L p p₀ w y
        = def_061 L p₀ w (def_024 p) y := by
      rw [h, hJ3]
    rw [thm_134, def_061] at heq
    have htop : def_059 L (def_024 p) y ≠ ⊤ := by
      intro htop
      apply hfin.2
      rw [← hJ3, def_061, htop, EReal.top_add_coe]
    have hKR := lem_075 (hℓ _) htop heq
    have hK : def_017 p p₀ = def_060 p₀ (def_024 p) :=
      mul_left_cancel₀ w.property.ne' hKR
    rw [thm_135] at hK
    have ht : def_025 p = def_050 p₀ (def_024 p) := by
      by_contra hne
      have hne' : (def_025 p : ℝ) ≠ def_047 p₀ (def_024 p) :=
        fun h' => hne (Subtype.ext h')
      have := thm_108 p₀ _ _ hne'
      rw [def_060] at hK
      linarith
    conv_lhs => rw [← thm_038 p]
    rw [ht]
  · rintro ⟨hJ3, hp⟩
    rw [hp, thm_137]
    exact hJ3

theorem thm_144 (x : str_002)
    (hx : def_061 L p₀ w x y = ⨅ x', def_061 L p₀ w x' y) :
    def_018 L (def_026 x (def_050 p₀ x)) p₀ w y
      = ⨅ q, def_018 L q p₀ w y := by
  rw [thm_137, thm_139, hx]

theorem thm_145 (hℓ : ∀ x, def_059 L x y ≠ ⊥)
    (hbot : (⨅ x, def_061 L p₀ w x y) = ⊥) :
    (∀ p, def_018 L p p₀ w y ≠ ⨅ q, def_018 L q p₀ w y) ∧
      (∀ x, def_061 L p₀ w x y ≠ ⨅ x', def_061 L p₀ w x' y) := by
  have h4 : ∀ p, def_018 L p p₀ w y ≠ ⊥ := fun p => by
    rw [thm_134]
    exact EReal.add_ne_bot_iff.mpr ⟨hℓ _, EReal.coe_ne_bot _⟩
  have h3 : ∀ x, def_061 L p₀ w x y ≠ ⊥ := fun x => by
    rw [def_061]
    exact EReal.add_ne_bot_iff.mpr ⟨hℓ _, EReal.coe_ne_bot _⟩
  refine ⟨fun p => ?_, fun x => ?_⟩
  · rw [thm_139, hbot]; exact h4 p
  · rw [hbot]; exact h3 x

end S48

section S43

variable (p₀ : str_001)

def def_062 (r : ℝ) (hr : 0 < r) : str_002 :=
  ⟨p₀.gamma, p₀.alpha, (def_057 p₀).s / r, p₀.alpha_pos,
    div_pos (def_057 p₀).s_pos hr⟩

lemma lem_076 (r : ℝ) (hr : 0 < r) :
    def_041 p₀ (def_062 p₀ r hr) ⟨1 / p₀.nu, one_div_pos.mpr p₀.nu_pos⟩
      = p₀.alpha * (r - 1 - Real.log r) := by
  have hn := p₀.nu_pos
  have hb := p₀.beta_pos
  have hs0 := (def_057 p₀).s_pos
  rw [thm_091, def_042, def_040]
  simp only [def_062, def_057, def_024, def_022, sub_self]
  have h1 : 1 + 1 / p₀.nu ≠ 0 := by positivity
  rw [div_self (Real.Gamma_pos_of_pos p₀.alpha_pos).ne', Real.log_one,
    show p₀.nu * (1 / p₀.nu) = 1 by field_simp, Real.log_one,
    Real.log_div (by positivity) hb.ne', Real.log_div (by positivity) hr.ne',
    Real.log_mul hb.ne' h1]
  field_simp
  ring

lemma lem_077 (r : ℝ) (hr : 0 < r) (hr1 : r ≠ 1) : def_062 p₀ r hr ≠ def_057 p₀ := by
  intro h
  have hs := congrArg str_002.s h
  simp only [def_062] at hs
  have hs0 := (def_057 p₀).s_pos
  rw [div_eq_iff hr.ne'] at hs
  exact hr1 (by nlinarith)

theorem thm_146 (ε : ℝ) (hε : 0 < ε) :
    ∃ x : str_002, x ≠ def_057 p₀ ∧ def_060 p₀ x < ε := by
  have hA := p₀.alpha_pos
  set h : ℝ := min 1 (ε / (2 * p₀.alpha)) / 2 with hh
  have hpos : 0 < h := by positivity
  have hle1 : h ≤ 1 / 2 := by
    have := min_le_left 1 (ε / (2 * p₀.alpha)); linarith
  have hleε : h ≤ ε / (2 * p₀.alpha) := by
    have := min_le_right 1 (ε / (2 * p₀.alpha)); linarith
  have hr : 0 < 1 + h := by linarith
  refine ⟨def_062 p₀ (1 + h) hr, lem_077 p₀ _ hr (by linarith), ?_⟩
  have hR : def_060 p₀ (def_062 p₀ (1 + h) hr)
      ≤ def_041 p₀ (def_062 p₀ (1 + h) hr) ⟨1 / p₀.nu, one_div_pos.mpr p₀.nu_pos⟩ := by
    rw [def_060]
    by_cases hc : (1 / p₀.nu : ℝ) = def_047 p₀ (def_062 p₀ (1 + h) hr)
    · have : (⟨1 / p₀.nu, one_div_pos.mpr p₀.nu_pos⟩ : abb_001)
          = def_050 p₀ (def_062 p₀ (1 + h) hr) := Subtype.ext hc
      rw [this]
    · exact (thm_108 p₀ _ _ hc).le
  rw [lem_076] at hR
  have hlog : 1 - 1 / (1 + h) ≤ Real.log (1 + h) := by
    have := Real.one_sub_inv_le_log_of_pos hr
    simpa [one_div] using this
  have hbound : 1 + h - 1 - Real.log (1 + h) ≤ h ^ 2 := by
    have : 1 - 1 / (1 + h) = h / (1 + h) := by field_simp; ring
    rw [this] at hlog
    have hdiv : h - h / (1 + h) = h ^ 2 / (1 + h) := by field_simp; ring
    have : h ^ 2 / (1 + h) ≤ h ^ 2 := div_le_self (sq_nonneg h) (by linarith)
    linarith
  have hsq : h ^ 2 ≤ h := by nlinarith
  calc def_060 p₀ (def_062 p₀ (1 + h) hr) ≤ p₀.alpha * (1 + h - 1 - Real.log (1 + h)) := hR
    _ ≤ p₀.alpha * h := by nlinarith
    _ ≤ p₀.alpha * (ε / (2 * p₀.alpha)) := by nlinarith
    _ < ε := by field_simp; linarith

open Classical in
def def_063 : abb_003 Unit :=
  fun μ _ => if μ = def_035 (def_057 p₀) then 1 else 0

theorem thm_147 (w : abb_001) :
    ∃ L : abb_003 Unit, (∀ μ, 0 ≤ L μ () ∧ L μ () ≠ ⊤) ∧
      ¬ ∃ p : str_001, ∀ q : str_001,
        def_018 L p p₀ w () ≤ def_018 L q p₀ w () := by
  classical
  have hw := w.property
  refine ⟨def_063 p₀, fun μ => ?_, ?_⟩
  · unfold def_063
    split_ifs
    · exact ⟨zero_le_one, ne_of_lt (EReal.coe_lt_top 1)⟩
    · exact ⟨le_rfl, EReal.zero_ne_top⟩
  · rintro ⟨p, hp⟩
    have hloss : ∀ x, def_059 (def_063 p₀) x () = if x = def_057 p₀ then 1 else 0 := by
      intro x
      simp only [def_059, def_063, thm_072.eq_iff]
    have hval : ∀ x, x ≠ def_057 p₀ →
        def_018 (def_063 p₀) (def_026 x (def_050 p₀ x)) p₀ w ()
          = ((w.val * def_060 p₀ x : ℝ) : EReal) := by
      intro x hx
      rw [thm_137, def_061, hloss]
      simp [hx]
    set x := def_024 p with hxdef
    have hlow := thm_138 (def_063 p₀) p₀ w () p
    by_cases hx0 : x = def_057 p₀
    · obtain ⟨z, hz, hRz⟩ := thm_146 p₀ (1 / w.val) (by positivity)
      have h1 := hp (def_026 z (def_050 p₀ z))
      rw [hval z hz] at h1
      have h2 : (1 : EReal) ≤ def_018 (def_063 p₀) p p₀ w () := by
        refine le_trans ?_ hlow
        rw [def_061, hloss, ← hxdef]
        simp only [hx0, ↓reduceIte]
        exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr
          (mul_nonneg hw.le (thm_133 p₀ _)))
      have h3 : w.val * def_060 p₀ z < 1 := by
        rw [lt_div_iff₀ hw] at hRz
        linarith
      have := lt_of_le_of_lt (h2.trans h1) (EReal.coe_lt_coe_iff.mpr h3)
      exact lt_irrefl _ this
    · have hRpos : 0 < def_060 p₀ x := by
        rcases (thm_133 p₀ x).lt_or_eq with h | h
        · exact h
        · exact absurd ((thm_131 p₀ x).mp h.symm) hx0
      obtain ⟨z, hz, hRz⟩ := thm_146 p₀ (def_060 p₀ x) hRpos
      have h1 := hp (def_026 z (def_050 p₀ z))
      rw [hval z hz] at h1
      have h2 : ((w.val * def_060 p₀ x : ℝ) : EReal)
          ≤ def_018 (def_063 p₀) p p₀ w () := by
        refine le_trans ?_ hlow
        rw [def_061, hloss, ← hxdef]
        simp [hx0]
      have h3 : w.val * def_060 p₀ z < w.val * def_060 p₀ x :=
        mul_lt_mul_of_pos_left hRz hw
      have := lt_of_le_of_lt (h2.trans h1) (EReal.coe_lt_coe_iff.mpr h3)
      exact lt_irrefl _ this

end S43

end NS1
