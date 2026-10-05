import Official.M12
import Official.M13
import Official.M14
import Official.M15
import Official.M16
import Official.M17
import Official.M18
import PostHoc.Relations.GroupB

/-!
# L1 ↔ B2 formal relation certificates, group C

Items: theorem-4, theorem-5, proposition-7, theorem-6, proposition-6, proposition-8, corollary-2.
Method as in
`GroupA`.
-/

-- cosmetic only: long statement lines are kept verbatim-readable
set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory NIGBottleneck Filter Topology Asymptotics Set

namespace PostHocFidelity

/-- L1's b = 2β₀/n (theorem-4), literally. -/
def l1b (p₀ : Parameters) : ℝ := 2 * p₀.beta / p₀.nu

/-- L1's score Q(x) = α((γ−γ₀)² + b)/s, literally. -/
def l1Q (p₀ : Parameters) (x : QuotientState) : ℝ := x.alpha * ((x.gamma - p₀.gamma) ^ 2 + l1b p₀) / x.s

/-- L1's t_* and ν_sel as functions of the score: T_A(n(1+Q)), Φ_A(n(1+Q)). -/
def l1tQ (A n Q : ℝ) : ℝ := l1TA A (n * (1 + Q))
def l1nuQ (A n Q : ℝ) : ℝ := l1PhiA A (n * (1 + Q))

/-! ## theorem-4

Interpretation: "(γ₀,b) determine the ordinal geometry" is read as: Q depends on the prior only through (γ₀,b),
and the t_*/ν_sel orders are the Q order. "(A,n) determine the calibration" is the monotone maps in (1). The b- and
w-monotonicity of (4) are stated for δ² = e ≥ 0, w > 0, b > 0 (the admissible values). -/

def L1_theorem4 : Prop :=
  (∀ g₀ b A n : ℝ, 0 < b → 0 < A → 0 < n →
      ∃! p₀ : Parameters, p₀.gamma = g₀ ∧ l1b p₀ = b ∧ p₀.alpha = A ∧ p₀.nu = n)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState),
      l1Q p₀ x = ((x.gamma - p₀.gamma) ^ 2 + l1b p₀) / (x.s / x.alpha) ∧ 0 < l1Q p₀ x
      ∧ l1d p₀ x = p₀.nu * (1 + l1Q p₀ x)
      ∧ l1TA p₀.alpha (l1d p₀ x) = l1tQ p₀.alpha p₀.nu (l1Q p₀ x)
      ∧ l1PhiA p₀.alpha (l1d p₀ x) = l1nuQ p₀.alpha p₀.nu (l1Q p₀ x))
  ∧ (∀ A n : ℝ, 0 < A → 0 < n →
      StrictMonoOn (l1nuQ A n) (Ioi 0) ∧ StrictAntiOn (l1tQ A n) (Ioi 0)
      ∧ StrictConvexOn ℝ (Ioi 0) (l1nuQ A n) ∧ StrictConvexOn ℝ (Ioi 0) (l1tQ A n))
  ∧ (∀ (p₀ : Parameters) (x y : QuotientState), x.s / x.alpha = y.s / y.alpha →
      (x.gamma - p₀.gamma) ^ 2 = (y.gamma - p₀.gamma) ^ 2 →
      l1TA p₀.alpha (l1d p₀ x) = l1TA p₀.alpha (l1d p₀ y) ∧ l1PhiA p₀.alpha (l1d p₀ x) = l1PhiA p₀.alpha (l1d p₀ y))
  ∧ (∀ (p₀ : Parameters) (x y : QuotientState), x.gamma = y.gamma → x.s / x.alpha = y.s / y.alpha →
      l1TA p₀.alpha (l1d p₀ x) = l1TA p₀.alpha (l1d p₀ y) ∧ l1PhiA p₀.alpha (l1d p₀ x) = l1PhiA p₀.alpha (l1d p₀ y))
  ∧ (∀ p₀ p₀' : Parameters, p₀.gamma = p₀'.gamma → l1b p₀ = l1b p₀' → ∀ x, l1Q p₀ x = l1Q p₀' x)
  ∧ (∀ (p₀ : Parameters) (x y : QuotientState),
      (l1TA p₀.alpha (l1d p₀ x) < l1TA p₀.alpha (l1d p₀ y) ↔ l1Q p₀ y < l1Q p₀ x)
      ∧ (l1PhiA p₀.alpha (l1d p₀ x) < l1PhiA p₀.alpha (l1d p₀ y) ↔ l1Q p₀ x < l1Q p₀ y))
  ∧ (∀ {A A' n Q : ℝ}, 0 < A → A < A' → 0 < n → 0 < Q → l1tQ A n Q < l1tQ A' n Q ∧ l1nuQ A' n Q < l1nuQ A n Q)
  ∧ (∀ {A n n' Q : ℝ}, 0 < A → 0 < n → n < n' → 0 < Q → l1tQ A n' Q < l1tQ A n Q ∧ l1nuQ A n Q < l1nuQ A n' Q)
  ∧ (∀ {A n e w b b' : ℝ}, 0 < A → 0 < n → 0 ≤ e → 0 < w → 0 < b → b < b' →
      l1tQ A n ((e + b') / w) < l1tQ A n ((e + b) / w))
  ∧ (∀ {A n e b w w' : ℝ}, 0 < A → 0 < n → 0 ≤ e → 0 < b → 0 < w → w < w' →
      l1tQ A n ((e + b) / w) < l1tQ A n ((e + b) / w'))

def B2_theorem4 : Prop :=
  (∀ g₀ b A n : ℝ, 0 < b → 0 < A → 0 < n → ∃! p₀ : Parameters, p₀.gamma = g₀ ∧ bParam p₀ = b ∧ p₀.alpha = A ∧ p₀.nu = n)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), scoreQ p₀ x = ((x.gamma - p₀.gamma) ^ 2 + bParam p₀) / (x.s / x.alpha))
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), 0 < scoreQ p₀ x)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), selD p₀ x = p₀.nu * (1 + scoreQ p₀ x))
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), selT p₀ x = TA p₀.alpha (p₀.nu * (1 + scoreQ p₀ x))
      ∧ selNu p₀ x = PhiA p₀.alpha (p₀.nu * (1 + scoreQ p₀ x)))
  ∧ (∀ {A n : ℝ}, 0 < A → 0 < n → StrictAntiOn (tOfScore A n) (Ioi 0))
  ∧ (∀ {A n : ℝ}, 0 < A → 0 < n → StrictMonoOn (nuOfScore A n) (Ioi 0))
  ∧ (∀ {A n : ℝ}, 0 < A → 0 < n → StrictConvexOn ℝ (Ioi 0) (tOfScore A n))
  ∧ (∀ {A n : ℝ}, 0 < A → 0 < n → StrictConvexOn ℝ (Ioi 0) (nuOfScore A n))
  ∧ (∀ (p₀ : Parameters) (x y : QuotientState), x.s / x.alpha = y.s / y.alpha →
      (x.gamma - p₀.gamma) ^ 2 = (y.gamma - p₀.gamma) ^ 2 → selT p₀ x = selT p₀ y ∧ selNu p₀ x = selNu p₀ y)
  ∧ (∀ (p₀ : Parameters) (x y : QuotientState), x.gamma = y.gamma → x.s / x.alpha = y.s / y.alpha →
      selT p₀ x = selT p₀ y ∧ selNu p₀ x = selNu p₀ y)
  ∧ (∀ (p₀ p₀' : Parameters), p₀.gamma = p₀'.gamma → bParam p₀ = bParam p₀' → ∀ (x : QuotientState),
      scoreQ p₀ x = scoreQ p₀' x)
  ∧ (∀ (p₀ : Parameters) (x y : QuotientState), selT p₀ x < selT p₀ y ↔ scoreQ p₀ y < scoreQ p₀ x)
  ∧ (∀ (p₀ : Parameters) (x y : QuotientState), selNu p₀ x < selNu p₀ y ↔ scoreQ p₀ x < scoreQ p₀ y)
  ∧ (∀ {A A' n Q : ℝ}, 0 < A → A < A' → 0 < n → 0 < Q →
      tOfScore A n Q < tOfScore A' n Q ∧ nuOfScore A' n Q < nuOfScore A n Q)
  ∧ (∀ {A n n' Q : ℝ}, 0 < A → 0 < n → n < n' → 0 < Q →
      tOfScore A n' Q < tOfScore A n Q ∧ nuOfScore A n Q < nuOfScore A n' Q)
  ∧ (∀ {A n e w b b' : ℝ}, 0 < A → 0 < n → 0 ≤ e → 0 < w → 0 < b → b < b' →
      tOfScore A n ((e + b') / w) < tOfScore A n ((e + b) / w))
  ∧ (∀ {A n e b w w' : ℝ}, 0 < A → 0 < n → 0 ≤ e → 0 < b → 0 < w → w < w' →
      tOfScore A n ((e + b) / w) < tOfScore A n ((e + b) / w'))

theorem rel_theorem4 : B2_theorem4 → L1_theorem4 := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
  refine ⟨h0, fun p₀ x => ⟨h1 p₀ x, h2 p₀ x, h3 p₀ x, (h4 p₀ x).1, (h4 p₀ x).2⟩,
    fun A n hA hn => ⟨h6 hA hn, h5 hA hn, h8 hA hn, h7 hA hn⟩, h9, h10, h11, fun p₀ x y => ⟨h12 p₀ x y, h13 p₀ x y⟩,
    h14, h15, h16, h17⟩

#relation_audit rel_theorem4 [NIGBottleneck.prior_reparameterization, NIGBottleneck.scoreQ_eq_div_w,
  NIGBottleneck.scoreQ_pos, NIGBottleneck.selD_eq_score, NIGBottleneck.selT_selNu_eq_score,
  NIGBottleneck.tOfScore_strictAntiOn, NIGBottleneck.nuOfScore_strictMonoOn, NIGBottleneck.tOfScore_strictConvexOn,
  NIGBottleneck.nuOfScore_strictConvexOn, NIGBottleneck.allocation_depends_on_sq_displacement,
  NIGBottleneck.allocation_independent_of_alpha, NIGBottleneck.scoreQ_depends_on_gamma_b,
  NIGBottleneck.selT_lt_iff_score, NIGBottleneck.selNu_lt_iff_score, NIGBottleneck.tOfScore_strictMono_A,
  NIGBottleneck.tOfScore_strictAnti_n, NIGBottleneck.tOfScore_strictAnti_b, NIGBottleneck.tOfScore_strictMono_w]

theorem B2_theorem4_holds : B2_theorem4 :=
  ⟨prior_reparameterization, scoreQ_eq_div_w, scoreQ_pos, selD_eq_score, selT_selNu_eq_score,
    tOfScore_strictAntiOn, nuOfScore_strictMonoOn, tOfScore_strictConvexOn, nuOfScore_strictConvexOn,
    allocation_depends_on_sq_displacement, allocation_independent_of_alpha, scoreQ_depends_on_gamma_b,
    selT_lt_iff_score, selNu_lt_iff_score, tOfScore_strictMono_A, tOfScore_strictAnti_n, tOfScore_strictAnti_b,
    tOfScore_strictMono_w⟩

theorem L1_theorem4_holds : L1_theorem4 := rel_theorem4 B2_theorem4_holds

/-! ## theorem-5

L1_form: the family is written field by field. "Changes sign at most once" is read as: the affine map has at most
one zero unless it is identically zero. "Strict ordering reversal" is read as: two parameters b, b′ ∈ (0,2s₀) at
which the difference has opposite strict signs. "Reversals do occur" is read as: there exist a predictive law,
two states and two members of its family that order the two states' allocations oppositely. -/

def l1Family (x₀ : QuotientState) (n : ℝ) (hn : 0 < n) : Parameters :=
  ⟨x₀.gamma, n, x₀.alpha, x₀.s * n / (n + 1), hn, x₀.alpha_pos, by have := x₀.s_pos; positivity⟩

def L1_theorem5 : Prop :=
  (∀ (x₀ : QuotientState) (p₀ : Parameters), predictiveLaw p₀ = l1PredLaw x₀ ↔
      ∃ n : ℝ, 0 < n ∧ p₀.gamma = x₀.gamma ∧ p₀.nu = n ∧ p₀.alpha = x₀.alpha ∧ p₀.beta = x₀.s * n / (n + 1))
  ∧ (∀ (x₀ : QuotientState) (n : ℝ) (hn : 0 < n), l1b (l1Family x₀ n hn) = 2 * x₀.s / (n + 1)
      ∧ 0 < l1b (l1Family x₀ n hn) ∧ l1b (l1Family x₀ n hn) < 2 * x₀.s
      ∧ n = 2 * x₀.s / l1b (l1Family x₀ n hn) - 1 ∧ (l1Family x₀ n hn).beta = x₀.s - l1b (l1Family x₀ n hn) / 2)
  ∧ (∀ (x₀ : QuotientState) (b : ℝ), 0 < b → b < 2 * x₀.s →
      ∃ (n : ℝ) (hn : 0 < n), n = 2 * x₀.s / b - 1 ∧ l1b (l1Family x₀ n hn) = b)
  ∧ (∀ (x₀ : QuotientState) (n : ℝ) (hn : 0 < n) (x₁ x₂ : QuotientState),
      l1Q (l1Family x₀ n hn) x₁ - l1Q (l1Family x₀ n hn) x₂ =
        (1 / (x₁.s / x₁.alpha) * (x₁.gamma - x₀.gamma) ^ 2 - 1 / (x₂.s / x₂.alpha) * (x₂.gamma - x₀.gamma) ^ 2)
          + l1b (l1Family x₀ n hn) * (1 / (x₁.s / x₁.alpha) - 1 / (x₂.s / x₂.alpha)))
  ∧ (∀ c₀ c₁ : ℝ, ¬ (c₀ = 0 ∧ c₁ = 0) → {b : ℝ | c₀ + b * c₁ = 0}.Subsingleton)
  ∧ (∀ c₀ c₁ S : ℝ, (∃ b ∈ Ioo 0 S, ∃ b' ∈ Ioo 0 S, (c₀ + b * c₁) * (c₀ + b' * c₁) < 0) ↔
      (c₁ ≠ 0 ∧ ∃ b ∈ Ioo 0 S, c₀ + b * c₁ = 0))
  ∧ (∃ (x₀ x₁ x₂ : QuotientState) (n n' : ℝ) (hn : 0 < n) (hn' : 0 < n'),
      l1Q (l1Family x₀ n hn) x₂ < l1Q (l1Family x₀ n hn) x₁
      ∧ l1Q (l1Family x₀ n' hn') x₁ < l1Q (l1Family x₀ n' hn') x₂
      ∧ l1TA (l1Family x₀ n hn).alpha (l1d (l1Family x₀ n hn) x₁) < l1TA (l1Family x₀ n hn).alpha (l1d (l1Family x₀ n hn) x₂)
      ∧ l1TA (l1Family x₀ n' hn').alpha (l1d (l1Family x₀ n' hn') x₂) < l1TA (l1Family x₀ n' hn').alpha (l1d (l1Family x₀ n' hn') x₁))

def B2_theorem5 : Prop :=
  (∀ (x₀ : QuotientState) (p₀ : Parameters), predictiveLaw p₀ = quotientLaw x₀ ↔ ∃ n, ∃ (hn : 0 < n), p₀ = priorFamily x₀ n hn)
  ∧ (∀ (x₀ : QuotientState) (n : ℝ) (hn : 0 < n), (priorFamily x₀ n hn).gamma = x₀.gamma ∧
      (priorFamily x₀ n hn).alpha = x₀.alpha ∧ (priorFamily x₀ n hn).beta = x₀.s * n / (n + 1) ∧
      bParam (priorFamily x₀ n hn) = 2 * x₀.s / (n + 1))
  ∧ (∀ (x₀ : QuotientState) (n : ℝ) (hn : 0 < n), 0 < bParam (priorFamily x₀ n hn) ∧
      bParam (priorFamily x₀ n hn) < 2 * x₀.s ∧ n = 2 * x₀.s / bParam (priorFamily x₀ n hn) - 1 ∧
      (priorFamily x₀ n hn).beta = x₀.s - bParam (priorFamily x₀ n hn) / 2)
  ∧ (∀ (x₀ : QuotientState) (b : ℝ), 0 < b → b < 2 * x₀.s →
      ∃ n, ∃ (hn : 0 < n), n = 2 * x₀.s / b - 1 ∧ bParam (priorFamily x₀ n hn) = b)
  ∧ (∀ (x₀ : QuotientState) (n : ℝ) (hn : 0 < n) (x₁ x₂ : QuotientState),
      scoreQ (priorFamily x₀ n hn) x₁ - scoreQ (priorFamily x₀ n hn) x₂ =
        1 / (x₁.s / x₁.alpha) * (x₁.gamma - x₀.gamma) ^ 2 - 1 / (x₂.s / x₂.alpha) * (x₂.gamma - x₀.gamma) ^ 2 +
          bParam (priorFamily x₀ n hn) * (1 / (x₁.s / x₁.alpha) - 1 / (x₂.s / x₂.alpha)))
  ∧ (∀ (c₀ c₁ : ℝ), ¬(c₀ = 0 ∧ c₁ = 0) → {b | c₀ + b * c₁ = 0}.Subsingleton)
  ∧ (∀ (c₀ c₁ S : ℝ), (∃ b ∈ Ioo 0 S, ∃ b' ∈ Ioo 0 S, (c₀ + b * c₁) * (c₀ + b' * c₁) < 0) ↔
      c₁ ≠ 0 ∧ ∃ b ∈ Ioo 0 S, c₀ + b * c₁ = 0)
  ∧ (∀ (A : ℝ) (hA : 0 < A),
      bParam (priorFamily (exampleX₀ A hA) 3 (by norm_num)) = 1 / 2 ∧
      bParam (priorFamily (exampleX₀ A hA) (1 / 3) (by norm_num)) = 3 / 2 ∧
      scoreQ (priorFamily (exampleX₀ A hA) 3 (by norm_num)) exampleX₂ < scoreQ (priorFamily (exampleX₀ A hA) 3 (by norm_num)) exampleX₁ ∧
      scoreQ (priorFamily (exampleX₀ A hA) (1 / 3) (by norm_num)) exampleX₁ < scoreQ (priorFamily (exampleX₀ A hA) (1 / 3) (by norm_num)) exampleX₂ ∧
      selT (priorFamily (exampleX₀ A hA) 3 (by norm_num)) exampleX₁ < selT (priorFamily (exampleX₀ A hA) 3 (by norm_num)) exampleX₂ ∧
      selT (priorFamily (exampleX₀ A hA) (1 / 3) (by norm_num)) exampleX₂ < selT (priorFamily (exampleX₀ A hA) (1 / 3) (by norm_num)) exampleX₁)

theorem rel_theorem5 : B2_theorem5 → L1_theorem5 := by
  rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  refine ⟨fun x₀ p₀ => ?_, fun x₀ n hn => ?_, h4, h5, h6, h7, ?_⟩
  · rw [show l1PredLaw x₀ = quotientLaw x₀ from rfl, h1 x₀ p₀]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, hn, rfl, rfl, rfl, rfl⟩
    · rintro ⟨n, hn, hg, hnu, ha, hb⟩
      refine ⟨n, hn, ?_⟩
      obtain ⟨g', n', a', b', hn0, ha0, hb0⟩ := p₀
      simp only at hg hnu ha hb
      subst hg hnu ha hb
      rfl
  · obtain ⟨-, -, -, hb⟩ := h2 x₀ n hn
    obtain ⟨hb1, hb2, hb3, hb4⟩ := h3 x₀ n hn
    exact ⟨hb, hb1, hb2, hb3, hb4⟩
  · obtain ⟨-, -, hq1, hq2, ht1, ht2⟩ := h8 1 one_pos
    exact ⟨exampleX₀ 1 one_pos, exampleX₁, exampleX₂, 3, 1 / 3, by norm_num, by norm_num, hq1, hq2, ht1, ht2⟩

#relation_audit rel_theorem5 [NIGBottleneck.predictiveLaw_eq_iff_priorFamily, NIGBottleneck.priorFamily_coords,
  NIGBottleneck.priorFamily_b_form, NIGBottleneck.priorFamily_of_b, NIGBottleneck.score_difference,
  NIGBottleneck.affine_zero_subsingleton, NIGBottleneck.reversal_iff, NIGBottleneck.reversal_occurs]

theorem B2_theorem5_holds : B2_theorem5 :=
  ⟨predictiveLaw_eq_iff_priorFamily, priorFamily_coords, priorFamily_b_form, priorFamily_of_b, score_difference,
    affine_zero_subsingleton, reversal_iff, reversal_occurs⟩

theorem L1_theorem5_holds : L1_theorem5 := rel_theorem5 B2_theorem5_holds

/-! ## theorem-6

L1_form: M is written literally. "Strictly increasing in A" is stated on A > 0 (L1's admissible range). The
aggregate ratio is Σcᵢu_epi,ᵢ / Σcᵢu_var,ᵢ at the selected points (`aggRatio`, the L1 prop-6 formula), with a
nonempty finite index type. -/

def l1M (A n : ℝ) : ℝ := (2 * A + 1 - n + Real.sqrt ((n - 2 * A - 1) ^ 2 + 4 * n)) / (2 * n)

def L1_theorem6 : Prop :=
  (∀ (p₀ : Parameters) (x : QuotientState),
      0 < l1TA p₀.alpha (l1d p₀ x) ∧ l1TA p₀.alpha (l1d p₀ x) < l1M p₀.alpha p₀.nu
      ∧ 1 / l1M p₀.alpha p₀.nu < l1PhiA p₀.alpha (l1d p₀ x))
  ∧ (∀ p₀ : Parameters, range (fun x => l1TA p₀.alpha (l1d p₀ x)) = Ioo 0 (l1M p₀.alpha p₀.nu)
      ∧ range (fun x => l1PhiA p₀.alpha (l1d p₀ x)) = Ioi (1 / l1M p₀.alpha p₀.nu)
      ∧ (fun x => l1TA p₀.alpha (l1d p₀ x)) '' {x | 1 < x.alpha} = Ioo 0 (l1M p₀.alpha p₀.nu)
      ∧ (fun x => l1PhiA p₀.alpha (l1d p₀ x)) '' {x | 1 < x.alpha} = Ioi (1 / l1M p₀.alpha p₀.nu))
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), l1TA p₀.alpha (l1d p₀ x) ≠ l1M p₀.alpha p₀.nu
      ∧ l1PhiA p₀.alpha (l1d p₀ x) ≠ 1 / l1M p₀.alpha p₀.nu)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), 1 < x.alpha →
      0 < l1uEpi (fiberParameters x (l1tStar p₀ x)) / l1uVar (fiberParameters x (l1tStar p₀ x))
      ∧ l1uEpi (fiberParameters x (l1tStar p₀ x)) / l1uVar (fiberParameters x (l1tStar p₀ x)) < l1M p₀.alpha p₀.nu
      ∧ l1uEpi (fiberParameters x (l1tStar p₀ x)) / l1Vz (fiberParameters x (l1tStar p₀ x))
          < l1M p₀.alpha p₀.nu / (1 + l1M p₀.alpha p₀.nu))
  ∧ (∀ p₀ p₀' : Parameters, p₀.alpha = p₀'.alpha → p₀.nu = p₀'.nu → l1M p₀.alpha p₀.nu = l1M p₀'.alpha p₀'.nu)
  ∧ (∀ {A A' n : ℝ}, 0 < A → A < A' → 0 < n → l1M A n < l1M A' n)
  ∧ (∀ {A : ℝ}, 0 < A → StrictAntiOn (l1M A) (Ioi 0))
  ∧ (∀ {n : ℝ}, 0 < n → Tendsto (fun A => l1M A n) (𝓝[>] 0) (𝓝 (1 / n)))
  ∧ (∀ {n : ℝ}, 0 < n → (fun A => l1M A n - (2 * A / n + (1 - n) / n)) =O[atTop] fun A : ℝ => A⁻¹)
  ∧ (∀ {A : ℝ}, 0 < A → (fun n => l1M A n - ((2 * A + 1) / n - 2 * A / (2 * A + 1))) =O[𝓝[>] 0] fun n : ℝ => n)
  ∧ (∀ {A : ℝ}, 0 < A → (fun n => l1M A n - (1 / n + 2 * A / n ^ 2)) =O[atTop] fun n : ℝ => (n ^ 3)⁻¹)
  ∧ (∀ {ι : Type} [Fintype ι] [Nonempty ι] (p₀ : ι → Parameters) (x : ι → QuotientState) (c : ι → ℝ),
      (∀ i, 1 < (x i).alpha) → (∀ i, 0 < c i) →
      aggRatio p₀ x c < Finset.univ.sup' Finset.univ_nonempty (fun i => l1M (p₀ i).alpha (p₀ i).nu)
      ∧ ∀ ε : ℝ, 0 < ε → ∃ x' : ι → QuotientState, (∀ i, 1 < (x' i).alpha)
          ∧ Finset.univ.sup' Finset.univ_nonempty (fun i => l1M (p₀ i).alpha (p₀ i).nu) - ε < aggRatio p₀ x' c)

def B2_theorem6 : Prop :=
  (∀ (A n : ℝ), boundM A n = (2 * A + 1 - n + √((n - 2 * A - 1) ^ 2 + 4 * n)) / (2 * n))
  ∧ (∀ (p₀ p₀' : Parameters), p₀.alpha = p₀'.alpha → p₀.nu = p₀'.nu → boundM p₀.alpha p₀.nu = boundM p₀'.alpha p₀'.nu)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), 0 < selT p₀ x ∧ selT p₀ x < boundM p₀.alpha p₀.nu)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), 1 / boundM p₀.alpha p₀.nu < selNu p₀ x)
  ∧ (∀ (p₀ : Parameters), range (selT p₀) = Ioo 0 (boundM p₀.alpha p₀.nu))
  ∧ (∀ (p₀ : Parameters), selT p₀ '' {x | 1 < x.alpha} = Ioo 0 (boundM p₀.alpha p₀.nu))
  ∧ (∀ (p₀ : Parameters), range (selNu p₀) = Ioi (1 / boundM p₀.alpha p₀.nu) ∧
      selNu p₀ '' {x | 1 < x.alpha} = Ioi (1 / boundM p₀.alpha p₀.nu))
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), selT p₀ x ≠ boundM p₀.alpha p₀.nu ∧ selNu p₀ x ≠ 1 / boundM p₀.alpha p₀.nu)
  ∧ (∀ (p₀ : Parameters) (x : QuotientState), 1 < x.alpha →
      0 < uEpi (fiberParameters x (selTPos p₀ x)) / uVar (fiberParameters x (selTPos p₀ x)) ∧
      uEpi (fiberParameters x (selTPos p₀ x)) / uVar (fiberParameters x (selTPos p₀ x)) < boundM p₀.alpha p₀.nu ∧
      uEpi (fiberParameters x (selTPos p₀ x)) / totalVar (fiberParameters x (selTPos p₀ x)) <
        boundM p₀.alpha p₀.nu / (1 + boundM p₀.alpha p₀.nu))
  ∧ (∀ {A A' n : ℝ}, 0 ≤ A → A < A' → 0 < n → boundM A n < boundM A' n)
  ∧ (∀ {A : ℝ}, 0 ≤ A → StrictAntiOn (boundM A) (Ioi 0))
  ∧ (∀ {n : ℝ}, 0 < n → Tendsto (fun A => boundM A n) (𝓝[>] 0) (𝓝 (1 / n)))
  ∧ (∀ {n : ℝ}, 0 < n → (fun A => boundM A n - (2 * A / n + (1 - n) / n)) =O[atTop] fun A => A⁻¹)
  ∧ (∀ {A : ℝ}, 0 < A → (fun n => boundM A n - ((2 * A + 1) / n - 2 * A / (2 * A + 1))) =O[𝓝[>] 0] fun n => n)
  ∧ (∀ {A : ℝ}, 0 < A → (fun n => boundM A n - (1 / n + 2 * A / n ^ 2)) =O[atTop] fun n => (n ^ 3)⁻¹)
  ∧ (∀ {ι : Type} [Fintype ι] [Nonempty ι] (p₀ : ι → Parameters) (x : ι → QuotientState) (c : ι → ℝ),
      (∀ (i : ι), 1 < (x i).alpha) → (∀ (i : ι), 0 < c i) → aggRatio p₀ x c < maxBound p₀)
  ∧ (∀ {ι : Type} [Fintype ι] [Nonempty ι] (p₀ : ι → Parameters) (x : ι → QuotientState) (c : ι → ℝ),
      (∀ (i : ι), 1 < (x i).alpha) → (∀ (i : ι), 0 < c i) → ∀ (ε : ℝ), 0 < ε →
        ∃ x', (∀ (i : ι), 1 < (x' i).alpha) ∧ maxBound p₀ - ε < aggRatio p₀ x' c)

theorem rel_theorem6 : B2_theorem6 → L1_theorem6 := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
  have hM : ∀ A n, l1M A n = boundM A n := fun A n => (h0 A n).symm
  have hMf : ∀ A, l1M A = boundM A := fun A => funext (hM A)
  refine ⟨fun p₀ x => ⟨(h2 p₀ x).1, by rw [hM]; exact (h2 p₀ x).2, by rw [hM]; exact h3 p₀ x⟩,
    fun p₀ => ⟨by rw [hM]; exact h4 p₀, by rw [hM]; exact (h6 p₀).1, by rw [hM]; exact h5 p₀,
      by rw [hM]; exact (h6 p₀).2⟩,
    fun p₀ x => by rw [hM]; exact h7 p₀ x,
    fun p₀ x hx => by rw [hM]; exact h8 p₀ x hx,
    fun p₀ p₀' ha hn => by rw [hM, hM]; exact h1 p₀ p₀' ha hn,
    fun hA hAA hn => by rw [hM, hM]; exact h9 hA.le hAA hn,
    fun hA => by rw [hMf]; exact h10 hA.le,
    fun hn => by simp only [hM]; exact h11 hn,
    fun hn => by simp only [hM]; exact h12 hn,
    fun hA => by simp only [hM]; exact h13 hA,
    fun hA => by simp only [hM]; exact h14 hA,
    fun p₀ x c hx hc => ⟨by simp only [hM]; exact h15 p₀ x c hx hc, fun ε hε => by simp only [hM]; exact h16 p₀ x c hx hc ε hε⟩⟩

#relation_audit rel_theorem6 [NIGBottleneck.boundM_eq, NIGBottleneck.boundM_prior, NIGBottleneck.selT_lt_boundM,
  NIGBottleneck.inv_boundM_lt_selNu, NIGBottleneck.range_selT, NIGBottleneck.range_selT_alpha_gt_one,
  NIGBottleneck.range_selNu, NIGBottleneck.endpoints_not_attained, NIGBottleneck.uncertainty_bound,
  NIGBottleneck.boundM_strictMono_A, NIGBottleneck.boundM_strictAnti_n, NIGBottleneck.boundM_tendsto_A_zero,
  NIGBottleneck.boundM_isBigO_A_atTop, NIGBottleneck.boundM_isBigO_n_zero, NIGBottleneck.boundM_isBigO_n_atTop,
  NIGBottleneck.aggRatio_lt_maxBound, NIGBottleneck.aggRatio_sharp]

theorem B2_theorem6_holds : B2_theorem6 :=
  ⟨boundM_eq, boundM_prior, selT_lt_boundM, inv_boundM_lt_selNu, range_selT, range_selT_alpha_gt_one, range_selNu,
    endpoints_not_attained, uncertainty_bound, boundM_strictMono_A, boundM_strictAnti_n, boundM_tendsto_A_zero,
    boundM_isBigO_A_atTop, boundM_isBigO_n_zero, boundM_isBigO_n_atTop,
    fun p₀ x c hx hc => aggRatio_lt_maxBound p₀ x c hx hc, fun p₀ x c hx hc => aggRatio_sharp p₀ x c hx hc⟩

theorem L1_theorem6_holds : L1_theorem6 := rel_theorem6 B2_theorem6_holds

/-! ## corollary-2

L1_form: the identity uses V_z = Var of the predictive law. is read as: for every γ and V>0 there are two parameters with that γ, distinct α>1 and the same V,
whose scores and allocations differ. -/

def L1_cor2 : Prop :=
  (∀ (p₀ p : Parameters), 1 < p.alpha →
      l1Q p₀ (quotientCoordinates p) = p.alpha / (p.alpha - 1) * (((p.gamma - p₀.gamma) ^ 2 + l1b p₀) / l1Vz p))
  ∧ (∀ (p₀ : Parameters) (γ V : ℝ), 0 < V → ∃ p p' : Parameters, p.gamma = γ ∧ p'.gamma = γ ∧ 1 < p.alpha
      ∧ 1 < p'.alpha ∧ p.alpha ≠ p'.alpha ∧ l1Vz p = V ∧ l1Vz p' = V
      ∧ l1Q p₀ (quotientCoordinates p') ≠ l1Q p₀ (quotientCoordinates p)
      ∧ l1TA p₀.alpha (l1d p₀ (quotientCoordinates p)) ≠ l1TA p₀.alpha (l1d p₀ (quotientCoordinates p')))

def B2_cor2 : Prop :=
  (∀ (p₀ p : Parameters), 1 < p.alpha →
      scoreQ p₀ (quotientCoordinates p) = p.alpha / (p.alpha - 1) * (((p.gamma - p₀.gamma) ^ 2 + bParam p₀) / totalVar p))
  ∧ (∀ (p₀ : Parameters) (γ V α α' : ℝ), 0 < V → 1 < α → α < α' →
      α' / (α' - 1) * (((γ - p₀.gamma) ^ 2 + bParam p₀) / V) < α / (α - 1) * (((γ - p₀.gamma) ^ 2 + bParam p₀) / V))
  ∧ (∀ (p₀ : Parameters) (γ V : ℝ), 0 < V → ∃ p p', p.gamma = γ ∧ p'.gamma = γ ∧ 1 < p.alpha ∧ 1 < p'.alpha
      ∧ p.alpha ≠ p'.alpha ∧ totalVar p = V ∧ totalVar p' = V
      ∧ scoreQ p₀ (quotientCoordinates p') < scoreQ p₀ (quotientCoordinates p)
      ∧ selT p₀ (quotientCoordinates p) < selT p₀ (quotientCoordinates p'))

theorem rel_cor2 : B2_cor2 → L1_cor2 := by
  rintro ⟨h1, -, h3⟩
  refine ⟨h1, fun p₀ γ V hV => ?_⟩
  obtain ⟨p, p', hg, hg', ha, ha', hne, hV1, hV2, hq, ht⟩ := h3 p₀ γ V hV
  exact ⟨p, p', hg, hg', ha, ha', hne, hV1, hV2, hq.ne, ht.ne⟩

#relation_audit rel_cor2 [NIGBottleneck.scoreQ_moment_form, NIGBottleneck.scoreQ_strictAnti_alpha,
  NIGBottleneck.variance_does_not_determine_allocation]

theorem B2_cor2_holds : B2_cor2 :=
  ⟨scoreQ_moment_form, scoreQ_strictAnti_alpha, variance_does_not_determine_allocation⟩

theorem L1_cor2_holds : L1_cor2 := rel_cor2 B2_cor2_holds

end PostHocFidelity
