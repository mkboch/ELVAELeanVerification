import Mathlib
import PostHoc.E1.M06

/-! -/

noncomputable section

namespace NS1

open Set

section S47

def def_082 (p₀ : str_001) : ℝ := 2 * p₀.beta / p₀.nu

theorem thm_178 (p₀ : str_001) : 0 < def_082 p₀ :=
  div_pos (mul_pos two_pos p₀.beta_pos) p₀.nu_pos

def def_083 (g₀ b A n : ℝ) (hb : 0 < b) (hA : 0 < A) (hn : 0 < n) : str_001 where
  gamma := g₀
  nu := n
  alpha := A
  beta := n * b / 2
  nu_pos := hn
  alpha_pos := hA
  beta_pos := by positivity

theorem thm_179 (g₀ b A n : ℝ) (hb : 0 < b) (hA : 0 < A) (hn : 0 < n) :
    ∃! p₀ : str_001, p₀.gamma = g₀ ∧ def_082 p₀ = b ∧ p₀.alpha = A ∧ p₀.nu = n := by
  refine ⟨def_083 g₀ b A n hb hA hn, ⟨rfl, ?_, rfl, rfl⟩, ?_⟩
  · simp only [def_082, def_083]
    field_simp
  · rintro p₀ ⟨h1, h2, h3, h4⟩
    have hbeta : p₀.beta = n * b / 2 := by
      rw [← h2, def_082, h4]
      field_simp
    cases p₀
    simp only [def_083] at *
    subst h1 h3 h4 hbeta
    rfl

theorem thm_180 (p₀ : str_001) : p₀.beta = p₀.nu * def_082 p₀ / 2 := by
  have := p₀.nu_pos
  rw [def_082]
  field_simp

end S47

section S51

variable (p₀ : str_001) (x : str_002)

def def_084 : ℝ := x.alpha * ((x.gamma - p₀.gamma) ^ 2 + def_082 p₀) / x.s

theorem thm_181 :
    def_084 p₀ x = ((x.gamma - p₀.gamma) ^ 2 + def_082 p₀) / (x.s / x.alpha) := by
  have := x.alpha_pos
  have := x.s_pos
  rw [def_084]
  field_simp

theorem thm_182 : 0 < def_084 p₀ x := by
  have := thm_178 p₀
  have := x.alpha_pos
  have := x.s_pos
  unfold def_084
  positivity

theorem thm_183 : def_046 p₀ x = p₀.nu * (1 + def_084 p₀ x) := by
  have := p₀.nu_pos
  have := x.s_pos
  rw [def_046, def_040, def_084, def_082]
  field_simp
  ring

theorem thm_184 :
    def_047 p₀ x = def_044 p₀.alpha (p₀.nu * (1 + def_084 p₀ x))
      ∧ def_048 p₀ x = def_045 p₀.alpha (p₀.nu * (1 + def_084 p₀ x)) := by
  rw [def_047, def_048, thm_183]
  exact ⟨rfl, rfl⟩

end S51

section S32

variable {A : ℝ}

def def_085 (A t : ℝ) : ℝ := 2 * A / (1 + t) + 1 / t

lemma lem_116 {d : ℝ} (hd : 0 < d) : def_085 A (def_044 A d) = d := (thm_098 hd).symm

lemma lem_117 (hA : 0 ≤ A) {t t' : ℝ} (ht : 0 < t) (htt : t < t') :
    def_085 A t' < def_085 A t := by
  have h1 : 1 / t' < 1 / t := one_div_lt_one_div_of_lt ht htt
  have h2 : 2 * A / (1 + t') ≤ 2 * A / (1 + t) :=
    div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  unfold def_085
  linarith

lemma lem_118 {u v a b : ℝ} (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v) (ha : 0 < a)
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

lemma lem_119 {u v a b : ℝ} (hu : 0 < u) (hv : 0 < v) (ha : 0 < a)
    (hb : 0 < b) (hab : a + b = 1) : 1 / (a * u + b * v) ≤ a * (1 / u) + b * (1 / v) := by
  rcases eq_or_ne u v with h | h
  · subst h
    have : a * u + b * u = u := by rw [← add_mul, hab, one_mul]
    rw [this, ← add_mul, hab, one_mul]
  · exact (lem_118 hu hv h ha hb hab).le

lemma lem_120 (hA : 0 ≤ A) {t t' a b : ℝ} (ht : 0 < t) (ht' : 0 < t') (hne : t ≠ t')
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    def_085 A (a * t + b * t') < a * def_085 A t + b * def_085 A t' := by
  have h1 := lem_118 ht ht' hne ha hb hab
  have h2 := lem_119 (by linarith : 0 < 1 + t) (by linarith : 0 < 1 + t') ha hb hab
  have h3 : a * (1 + t) + b * (1 + t') = 1 + (a * t + b * t') := by
    rw [mul_add, mul_add, mul_one, mul_one]
    linarith
  rw [h3] at h2
  have h4 : 2 * A * (1 / (1 + (a * t + b * t')))
      ≤ 2 * A * (a * (1 / (1 + t)) + b * (1 / (1 + t'))) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  unfold def_085
  simp only [div_eq_mul_one_div (2 * A)]
  nlinarith

variable (hA : 0 ≤ A)
include hA

theorem thm_185 : StrictAntiOn (def_044 A) (Ioi 0) := by
  intro d hd d' hd' hlt
  have hd0 : (0 : ℝ) < d := hd
  have hd0' : (0 : ℝ) < d' := hd'
  by_contra hle
  rw [not_lt] at hle
  rcases hle.lt_or_eq with h | h
  · have := lem_117 hA (thm_092 hd0) h
    rw [lem_116 hd0, lem_116 hd0'] at this
    linarith
  · have := congrArg (def_085 A) h
    rw [lem_116 hd0, lem_116 hd0'] at this
    linarith

theorem thm_186 : StrictConvexOn ℝ (Ioi 0) (def_044 A) := by
  refine ⟨convex_Ioi 0, fun d hd d' hd' hne a b ha hb hab => ?_⟩
  have hd0 : (0 : ℝ) < d := hd
  have hd0' : (0 : ℝ) < d' := hd'
  simp only [smul_eq_mul]
  set t := def_044 A d
  set t' := def_044 A d'
  have ht : 0 < t := thm_092 hd0
  have ht' : 0 < t' := thm_092 hd0'
  have htne : t ≠ t' := by
    intro h
    apply hne
    rw [← lem_116 (A := A) hd0, ← lem_116 (A := A) hd0']
    exact congrArg (def_085 A) h
  have hm : 0 < a * t + b * t' := by positivity
  have hD : 0 < a * d + b * d' := by positivity
  have hconv := lem_120 hA ht ht' htne ha hb hab
  rw [lem_116 hd0, lem_116 hd0'] at hconv
  by_contra hle
  rw [not_lt] at hle
  rcases hle.lt_or_eq with h | h
  · have := lem_117 hA hm h
    rw [lem_116 hD] at this
    linarith
  · rw [h, lem_116 hD] at hconv
    exact lt_irrefl _ hconv

theorem thm_187 : StrictMonoOn (def_045 A) (Ioi 0) := by
  intro d hd d' hd' hlt
  have hd0 : (0 : ℝ) < d := hd
  have hd0' : (0 : ℝ) < d' := hd'
  rw [thm_095 hd0, thm_095 hd0']
  exact one_div_lt_one_div_of_lt (thm_092 hd0') (thm_185 hA hd hd' hlt)

def def_086 (A r : ℝ) : ℝ := r + 2 * A * r / (1 + r)

omit hA in
lemma lem_121 {d : ℝ} (hd : 0 < d) : def_086 A (def_045 A d) = d := by
  have h := thm_098 (A := A) hd
  have ht := thm_092 (A := A) hd
  rw [def_086, thm_095 hd]
  set T := def_044 A d
  have e : 1 / T + 2 * A * (1 / T) / (1 + 1 / T) = 2 * A / (1 + T) + 1 / T := by
    field_simp
    ring
  rw [e, ← h]

lemma lem_122 {r r' : ℝ} (hr : 0 < r) (hrr : r < r') : def_086 A r < def_086 A r' := by
  unfold def_086
  have : 2 * A * r / (1 + r) ≤ 2 * A * r' / (1 + r') := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  linarith

omit hA in
lemma lem_123 (hA : 0 < A) {r r' a b : ℝ} (hr : 0 < r) (hr' : 0 < r') (hne : r ≠ r')
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    a * def_086 A r + b * def_086 A r' < def_086 A (a * r + b * r') := by
  have e : ∀ u : ℝ, 0 < 1 + u → def_086 A u = u + 2 * A - 2 * A * (1 / (1 + u)) := by
    intro u hu
    unfold def_086
    field_simp
    ring
  have h5 := lem_118 (by linarith : 0 < 1 + r) (by linarith : 0 < 1 + r')
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
theorem thm_188 (hA : 0 < A) : StrictConvexOn ℝ (Ioi 0) (def_045 A) := by
  refine ⟨convex_Ioi 0, fun d hd d' hd' hne a b ha hb hab => ?_⟩
  have hd0 : (0 : ℝ) < d := hd
  have hd0' : (0 : ℝ) < d' := hd'
  simp only [smul_eq_mul]
  set r := def_045 A d
  set r' := def_045 A d'
  have hr : 0 < r := thm_093 hd0
  have hr' : 0 < r' := thm_093 hd0'
  have hrne : r ≠ r' := by
    intro h
    apply hne
    rw [← lem_121 (A := A) hd0, ← lem_121 (A := A) hd0']
    exact congrArg (def_086 A) h
  have hm : 0 < a * r + b * r' := by positivity
  have hD : 0 < a * d + b * d' := by positivity
  have hconc := lem_123 hA hr hr' hrne ha hb hab
  rw [lem_121 hd0, lem_121 hd0'] at hconc
  by_contra hle
  rw [not_lt] at hle
  rcases hle.lt_or_eq with h | h
  · have := lem_122 hA.le hm h
    rw [lem_121 hD] at this
    linarith
  · rw [h, lem_121 hD] at hconc
    exact lt_irrefl _ hconc

end S32

section S09

variable (A n : ℝ)

def def_087 (Q : ℝ) : ℝ := def_044 A (n * (1 + Q))

def def_088 (Q : ℝ) : ℝ := def_045 A (n * (1 + Q))

variable {A n} (hA : 0 < A) (hn : 0 < n)
include hA hn

omit hA in
lemma lem_124 {Q : ℝ} (hQ : Q ∈ Ioi (0 : ℝ)) : n * (1 + Q) ∈ Ioi (0 : ℝ) := by
  have : (0 : ℝ) < Q := hQ
  exact mul_pos hn (by linarith)

theorem thm_189 : StrictAntiOn (def_087 A n) (Ioi 0) := by
  intro Q hQ Q' hQ' h
  exact thm_185 hA.le (lem_124 hn hQ) (lem_124 hn hQ')
    (by nlinarith)

theorem thm_190 : StrictMonoOn (def_088 A n) (Ioi 0) := by
  intro Q hQ Q' hQ' h
  exact thm_187 hA.le (lem_124 hn hQ) (lem_124 hn hQ')
    (by nlinarith)

omit hA hn in
lemma lem_125 (Q Q' a b : ℝ) (hab : a + b = 1) :
    n * (1 + (a * Q + b * Q')) = a * (n * (1 + Q)) + b * (n * (1 + Q')) := by
  have : b = 1 - a := by linarith
  subst this
  ring

theorem thm_191 : StrictConvexOn ℝ (Ioi 0) (def_087 A n) := by
  refine ⟨convex_Ioi 0, fun Q hQ Q' hQ' hne a b ha hb hab => ?_⟩
  have h := (thm_186 hA.le).2 (lem_124 hn hQ) (lem_124 hn hQ')
    (fun e => hne (by
      have := mul_left_cancel₀ hn.ne' e
      linarith)) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  unfold def_087
  rwa [lem_125 Q Q' a b hab]

theorem thm_192 : StrictConvexOn ℝ (Ioi 0) (def_088 A n) := by
  refine ⟨convex_Ioi 0, fun Q hQ Q' hQ' hne a b ha hb hab => ?_⟩
  have h := (thm_188 hA).2 (lem_124 hn hQ) (lem_124 hn hQ')
    (fun e => hne (by
      have := mul_left_cancel₀ hn.ne' e
      linarith)) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  unfold def_088
  rwa [lem_125 Q Q' a b hab]

end S09

section S54

variable (p₀ : str_001)

theorem thm_193 (x : str_002) :
    def_047 p₀ x = def_087 p₀.alpha p₀.nu (def_084 p₀ x)
      ∧ def_048 p₀ x = def_088 p₀.alpha p₀.nu (def_084 p₀ x) :=
  thm_184 p₀ x

theorem thm_194 (x y : str_002)
    (hw : x.s / x.alpha = y.s / y.alpha)
    (he : (x.gamma - p₀.gamma) ^ 2 = (y.gamma - p₀.gamma) ^ 2) :
    def_047 p₀ x = def_047 p₀ y ∧ def_048 p₀ x = def_048 p₀ y := by
  have hQ : def_084 p₀ x = def_084 p₀ y := by
    rw [thm_181, thm_181, hw, he]
  rw [(thm_193 p₀ x).1, (thm_193 p₀ y).1, (thm_193 p₀ x).2,
    (thm_193 p₀ y).2, hQ]
  exact ⟨rfl, rfl⟩

theorem thm_195 (x y : str_002) (hg : x.gamma = y.gamma)
    (hw : x.s / x.alpha = y.s / y.alpha) :
    def_047 p₀ x = def_047 p₀ y ∧ def_048 p₀ x = def_048 p₀ y :=
  thm_194 p₀ x y hw (by rw [hg])

theorem thm_196 (p₀' : str_001) (hg : p₀.gamma = p₀'.gamma)
    (hb : def_082 p₀ = def_082 p₀') (x : str_002) : def_084 p₀ x = def_084 p₀' x := by
  rw [def_084, def_084, hg, hb]

theorem thm_197 (x y : str_002) :
    def_047 p₀ x < def_047 p₀ y ↔ def_084 p₀ y < def_084 p₀ x := by
  have hA := p₀.alpha_pos
  have hn := p₀.nu_pos
  rw [(thm_193 p₀ x).1, (thm_193 p₀ y).1]
  exact (thm_189 hA hn).lt_iff_gt (thm_182 p₀ x) (thm_182 p₀ y)

theorem thm_198 (x y : str_002) :
    def_048 p₀ x < def_048 p₀ y ↔ def_084 p₀ x < def_084 p₀ y := by
  have hA := p₀.alpha_pos
  have hn := p₀.nu_pos
  rw [(thm_193 p₀ x).2, (thm_193 p₀ y).2]
  exact (thm_190 hA hn).lt_iff_lt (thm_182 p₀ x) (thm_182 p₀ y)

theorem thm_199 {A A' n Q : ℝ} (hA : 0 < A) (hAA : A < A') (hn : 0 < n)
    (hQ : 0 < Q) :
    def_087 A n Q < def_087 A' n Q ∧ def_088 A' n Q < def_088 A n Q := by
  have hd : 0 < n * (1 + Q) := by positivity
  have key : def_044 A (n * (1 + Q)) < def_044 A' (n * (1 + Q)) := by
    set d := n * (1 + Q)
    have h1 := lem_116 (A := A) hd
    have h2 := lem_116 (A := A') hd
    have ht := thm_092 (A := A) hd
    have ht' := thm_092 (A := A') hd
    by_contra hle
    rw [not_lt] at hle
    have hgt : d < def_085 A' (def_044 A d) := by
      have hlt : def_085 A (def_044 A d) < def_085 A' (def_044 A d) := by
        unfold def_085
        have : 2 * A / (1 + def_044 A d) < 2 * A' / (1 + def_044 A d) :=
          div_lt_div_of_pos_right (by linarith) (by linarith)
        linarith
      linarith [h1]
    rcases hle.lt_or_eq with h | h
    · have := lem_117 (A := A') (by linarith) ht' h
      linarith
    · rw [← h] at hgt
      linarith
  refine ⟨key, ?_⟩
  unfold def_088
  rw [thm_095 hd, thm_095 hd]
  exact one_div_lt_one_div_of_lt (thm_092 hd) key

theorem thm_200 {A n n' Q : ℝ} (hA : 0 < A) (hn : 0 < n) (hnn : n < n')
    (hQ : 0 < Q) :
    def_087 A n' Q < def_087 A n Q ∧ def_088 A n Q < def_088 A n' Q := by
  have hd : 0 < n * (1 + Q) := by positivity
  have hd' : 0 < n' * (1 + Q) := by nlinarith
  have hlt : n * (1 + Q) < n' * (1 + Q) := by nlinarith
  exact ⟨thm_185 hA.le hd hd' hlt, thm_187 hA.le hd hd' hlt⟩

theorem thm_201 {A n e w b b' : ℝ} (hA : 0 < A) (hn : 0 < n) (he : 0 ≤ e)
    (hw : 0 < w) (hb : 0 < b) (hbb : b < b') :
    def_087 A n ((e + b') / w) < def_087 A n ((e + b) / w) := by
  have hQ : 0 < (e + b) / w := by positivity
  have hQ' : 0 < (e + b') / w := div_pos (by linarith) hw
  exact thm_189 hA hn hQ hQ' (div_lt_div_of_pos_right (by linarith) hw)

theorem thm_202 {A n e b w w' : ℝ} (hA : 0 < A) (hn : 0 < n) (he : 0 ≤ e)
    (hb : 0 < b) (hw : 0 < w) (hww : w < w') :
    def_087 A n ((e + b) / w) < def_087 A n ((e + b) / w') := by
  have hQ : 0 < (e + b) / w := by positivity
  have hQ' : 0 < (e + b) / w' := div_pos (by linarith) (by linarith)
  exact thm_189 hA hn hQ' hQ (div_lt_div_of_pos_left (by linarith) hw hww)

end S54

end NS1
